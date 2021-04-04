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

Inductive exp : Type -> Type :=
  Exp__Var   : var -> exp N
| Exp__Const : N   -> exp N
| Exp__Nth   : exp N -> list (exp N) -> exp nat.

Fixpoint exp_to_sexp {T} (e : exp T) : sexp :=
  match e with
  | Exp__Var   x => [Atom "Variable"; to_sexp x]
  | Exp__Const n => [Atom "Number"; to_sexp n]
  | Exp__Nth x l => [Atom "Nth"; exp_to_sexp x; List (map exp_to_sexp l)]
  end%sexp.

Instance Serialzie__exp {T} : Serialize (exp T) := exp_to_sexp.

Variant symE : Type -> Type :=
  Sym__Fresh : symE (exp N)
| Sym__Eval  : exp nat -> symE nat.

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

Definition getx {V E} `{symE -< E} (k : exp N) (l : list (exp N * V))
  : itree E (option V) :=
  n <- embed Sym__Eval (Exp__Nth k (map fst l));;
  ret (snd <$> nth_error l n).

Definition replace {V} (n : nat) (v : V) (l : list V) : list V :=
  firstn n l ++ v :: skipn (S n) l.

Definition updatex {V E} `{symE -< E} (k : exp N) (v : V) (l : list (exp N * V))
  : itree E (list (exp N * V)) :=
  n <- embed Sym__Eval (Exp__Nth k (map fst l));;
  ret (replace n (k, v) l).

Definition credit {E} `{symE -< E} (aid : exp account_id) (amount : amountT)
  : Monads.stateT (swap_state exp) (itree E) (swap_response exp) :=
  fun ss =>
    let (accounts, orders) := ss in
    oa <- getx aid accounts;;
    if oa is Some (uid, ticker, x)
    then let acnt' := (uid, ticker, x + amount) in
         accounts' <- updatex aid acnt' accounts;;
         ret (accounts', orders, Response__Account (aid, acnt'))
    else ret (ss, Response__NotFound).

Definition create {E} `{symE -< E} (uid : user_id) (ticker : assetT)
  : Monads.stateT (swap_state exp) (itree E) (exp account_id) :=
  fun ss =>
    let (accounts, orders) := ss in
    xaid <- trigger Sym__Fresh;;
    ret (put xaid (uid, ticker, 0) accounts, orders, xaid).

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
    credit aid amount s1.

Definition debit {E} `{symE -< E} (aid : exp account_id) (amount : amountT)
  : Monads.stateT (swap_state exp) (itree E) (swap_response exp) :=
  fun ss =>
    let (accounts, orders) := ss in
    oa <- getx aid accounts;;
    if oa is Some (uid, ticker, x)
    then if amount <=? x
         then let acnt' := (uid, ticker, x - amount) in
              accounts' <- updatex aid acnt' accounts;;
              ret (accounts', orders, Response__Account (aid, acnt'))
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
    | Request__Deposit  uid ticker amount => deposit uid ticker amount ss
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
      oo <- getx coid orders;;
      if oo is Some (bid, ba, sid, sa)
      then
        ob <- getx bid accounts;;
        os <- getx sid accounts;;
        if (ob, os) is (Some (_, bt, _), Some (_, st, _))
        then
          '(s1, r1) <- withdraw uid bt ba ss;;
          if r1 is Response__Account _
          then
            '(s2, r2) <- credit bid ba s1;;
            if r2 is Response__Account _
            then
              '(s3, r3) <- deposit uid st sa s2;;
              ret (if r3 is Response__Account _ then s3 else ss, r3)
            else ret (ss, r2)
          else ret (ss, r1)
        else ret (ss, Response__NotFound)
      else ret (ss, Response__NotFound)
    end.

Definition swap_smi := server_smi swap_handler.
