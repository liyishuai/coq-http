From App Require Export
     AppMessage.
From ITree Require Export
     ITree.
From HTTP Require Export
     Semantics.

Variant appE {requestT responseT server_state} : Type -> Type :=
  App__Recv : server_state -> appE (clientT * requestT)
| App__Send : clientT -> responseT -> appE unit.
Arguments appE : clear implicits.

Inductive exp : Type -> Set :=
  Exp__Var   : var -> exp N
| Exp__Const : N   -> exp N
| Exp__Add   : exp N ->   N -> exp N
| Exp__Sub   : exp N ->   N -> exp N
| Exp__Leb   : N   -> exp N -> exp bool.

Variant symE : Type -> Type :=
  Sym__Fresh  : symE (exp N)
| Sym__Decide : exp bool -> symE bool.

Class  Is__smE q r s E `{appE q r s -< E} `{symE -< E}.
Notation smE q r s := (appE q r s +' symE).
Instance smE_Is__smE {q r s} : Is__smE q r s (smE q r s). Defined.

Definition server_smi {q r s E} `{Is__smE q r s E}
           (handler : forall {F} `{symE -< F}, q -> Monads.stateT s (itree F) r)
  : s -> itree E void :=
  iter_forever
    (fun ss : s =>
       '(c, req) <- embed App__Recv ss;;
       '(ss', res) <- handler req ss;;
       embed App__Send c res;;
       ret ss) .

Definition swap_state exp_ : Type :=
  list (accountT exp_) * list (orderT exp_).

Definition findAccount {exp_} (uid : user_id) (ticker : assetT)
           (a : accountT exp_) : bool :=
  let '(_, (u, t, _)) := a in
  (uid =? u) &&& (ticker =? t).

Fixpoint eqb_exp {X Y} (x : exp X) (y : exp Y) : bool :=
  match x, y with
  | Exp__Var   a, Exp__Var   b
  | Exp__Const a, Exp__Const b => a =? b
  | Exp__Add x a, Exp__Add y b
  | Exp__Sub x a, Exp__Sub y b
  | Exp__Leb a x, Exp__Leb b y => eqb_exp x y &&& (a =? b)
  | _, _ => false
  end.

Definition getx {V} : exp N -> list (exp N * V) -> option V := get' eqb_exp.
Definition updatex {V} : exp N -> V -> list (exp N * V) -> list (exp N * V) :=
  update' eqb_exp.

Definition credit (aid : exp account_id) (amount : amountT)
  : Monads.state (swap_state exp) (swap_response exp) :=
  fun ss =>
    let (accounts, orders) := ss in
    if getx aid accounts is Some (uid, ticker, x)
    then let acnt' := (uid, ticker, Exp__Add x amount) in
         (updatex aid acnt' accounts, orders,
          Response__Account (aid, acnt'))
    else (ss, Response__NotFound).

Definition create {E} `{symE -< E} (uid : user_id) (ticker : assetT)
  : Monads.stateT (swap_state exp) (itree E) (exp account_id) :=
  fun ss =>
    let (accounts, orders) := ss in
    xaid <- trigger Sym__Fresh;;
    ret (put xaid (uid, ticker, Exp__Const 0) accounts, orders, xaid).

Definition locate {E} `{symE -< E} (uid : user_id) (ticker : assetT)
  : Monads.stateT (swap_state exp) (itree E) (exp account_id) :=
  fun ss =>
    let (accounts, orders) := ss in
    if find (findAccount uid ticker) accounts is Some (aid, _)
    then ret (ss, aid)
    else create uid ticker ss.

Definition deposit {E} `{symE -< E}
           (uid : user_id) (ticker : assetT) (amount : amountT)
  : Monads.stateT (swap_state exp) (itree E) (swap_response exp) :=
  fun ss =>
    let (accounts, orders) := ss in
    '(s1, aid) <- locate uid ticker ss;;
    ret (credit aid amount s1).

Definition debit {E} `{symE -< E} (aid : exp account_id) (amount : amountT)
  : Monads.stateT (swap_state exp) (itree E) (swap_response exp) :=
  fun ss =>
    let (accounts, orders) := ss in
    if getx aid accounts is Some (uid, ticker, x)
    then b <- embed Sym__Decide (Exp__Leb amount x);;
         if b : bool
         then let acnt' := (uid, ticker, Exp__Sub x amount) in
              ret (updatex aid acnt' accounts, orders,
                   Response__Account (aid, acnt'))
         else ret (ss, Response__InsufficientFund)
    else ret (ss, Response__NotFound).

Definition withdraw {E} `{symE -< E}
           (uid : user_id) (ticker : assetT) (amount : amountT)
  : Monads.stateT (swap_state exp) (itree E) (swap_response exp) :=
  fun ss =>
    let (accounts, orders) := ss in
    if find (findAccount uid ticker) accounts is Some (aid, _)
    then debit aid amount ss
    else ret (ss, Response__NotFound).

Definition swap_handler E `(symE -< E) (req : swap_request id)
  : Monads.stateT (swap_state exp) (itree E) (swap_response exp) :=
  fun ss =>
    let (accounts, orders) := ss in
    match req with
    | Request__ListOrders => ret (ss, Response__ListOrders orders)
    | Request__ListAccount uid =>
      let acs : list (accountT exp) :=
          filter (N.eqb uid ∘ fst ∘ fst ∘ snd) accounts in
      ret (ss, Response__ListAccount acs)
    | Request__Deposit  uid ticker amount => deposit  uid ticker amount ss
    | Request__Withdraw uid ticker amount => withdraw uid ticker amount ss
    | Request__MakeOrder uid bt ba st sa =>
      '(s1, r1) <- withdraw uid st sa ss;;
      if r1 is Response__Account (sid, _)
      then '(s2, bid) <- locate uid bt s1;;
           let (a2, o2) := s2 : swap_state exp in
           oid <- trigger Sym__Fresh;;
           let order : orderT exp := (oid, (bid, ba, sid, sa)) in
           ret (a2, order::o2, Response__Order order)
      else ret (ss, r1)
    | Request__TakeOrder uid oid =>
      let coid : exp order_id := Exp__Const oid in
      if getx coid orders is Some (bid, ba, sid, sa)
      then if (getx bid accounts, getx sid accounts)
                is (Some (_, bt, _), Some (_, st, _))
           then '(s1, r1) <- withdraw uid bt ba ss;;
                if r1 is Response__Account _
                then let (s2, r2) := credit bid ba s1 in
                     if r2 is Response__Account _
                     then '(s3, r3) <- deposit uid st sa s2;;
                          ret (if r3 is Response__Account _ then s3 else ss, r3)
                     else ret (ss, r2)
                else ret (ss, r1)
           else ret (ss, Response__NotFound)
      else ret (ss, Response__NotFound)
    end.

Definition swap_smi := server_smi swap_handler.
