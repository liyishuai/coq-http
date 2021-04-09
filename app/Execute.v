From HTTP Require Import
     Execute.
From App Require Import
     Tester.

Variant texp : Type -> Type :=
  Texp__Const   : N -> texp N
| Texp__Order   : labelT -> nat -> texp order_id
| Texp__Account : labelT -> nat -> texp account_id
| Texp__Amount  : labelT -> nat -> N -> texp amountT.

Instance Serialize__texp : Serialize (texp N) :=
  fun tx => match tx with
         | Texp__Const    n   => Atom n
         | Texp__Order    x n => [Atom "Order"  ; Atom x; Atom n]
         | Texp__Account  x n => [Atom "Account"; Atom x; Atom n]
         | Texp__Amount x n p => [Atom "Amount" ; Atom x; Atom n; Atom p]
         end%sexp.

Instance Serialize__request {exp_} `{Serialize (exp_ N)}
  : Serialize (swap_request exp_) :=
  fun req => match req with
          | Request__ListOrders        =>  Atom "listOrders"
          | Request__ListAccount uid   => [Atom "listAccount"; Atom uid]
          | Request__TakeOrder uid oid => [Atom "takeOrder"; Atom uid; to_sexp oid]
          | Request__MakeOrder uid bt ba st sa =>
            [Atom "makeOrder"; Atom uid; Atom bt; Atom ba; Atom st; to_sexp sa]
          | Request__Deposit uid t a => [Atom "deposit"; Atom uid; Atom t; Atom a]
          | Request__Withdraw uid t a =>
            [Atom "withdraw"; Atom uid; Atom t; to_sexp a]
          end%sexp.

Instance Serialize__symreq : Serialize (swap_request texp) := Serialize__request.

Instance Shrink__texp : Shrink (texp N) := {
  shrink x :=
    match x with
    | Texp__Const      n => Texp__Const   <$> shrink n
    | Texp__Order    x n => Texp__Order x <$> shrink n ++
                         Texp__Order   <$> shrink x <*> [n]
    | Texp__Account  x n => Texp__Account x <$> shrink n ++
                         Texp__Account   <$> shrink x <*> [n]
    | Texp__Amount x n p => Texp__Amount x n <$> shrink p ++
                         Texp__Amount x   <$> shrink n <*> [p] ++
                         Texp__Amount     <$> shrink x <*> [n] <*> [p]
    end }.

Instance Shrink__request : Shrink (swap_request texp) :=
  { shrink req :=
      match req with
      | Request__TakeOrder u o => Request__TakeOrder u <$> shrink o
      | Request__MakeOrder u bt ba st sa =>
        Request__MakeOrder u bt ba st <$> shrink sa ++
        Request__MakeOrder u bt       <$> shrink ba <*> [st] <*> [sa]
      | Request__Deposit   u t a => Request__Deposit  u t <$> shrink a
      | Request__Withdraw  u t a => Request__Withdraw u t <$> shrink a
      | _ => []
      end }.

Notation packetT := (packetT (swap_request id) (swap_response id)).
Notation traceT  := (@traceT packetT).

Fixpoint fallback {A B} (f : A -> option B) (l : list A) : B -> B :=
  if l is a::l'
  then if f a is Some b then const b else fallback f l'
  else id.

Definition instantiate_exp (tr : traceT) (nx : texp N) : N :=
  match nx with
  | Texp__Const n => n
  | Texp__Order l k =>
    fallback
      (fun lp =>
         let '(l0, Packet _ _ p) := lp in
         if l0 = l? then
           match p with
           | inr (Response__Order (n, _)) => Some n
           | inr (Response__ListOrders l) =>
             fst <$> nth_error l (min k (pred (length l)))
           | _ => None
           end
         else None) tr 0
  | Texp__Account l k =>
    fallback
      (fun lp =>
         let '(l0, Packet _ _ p) := lp in
         if l0 = l? then
           match p with
           | inr (Response__Account (n, _)) => Some n
           | inr (Response__ListAccount l)  =>
             fst <$> nth_error l (min k (pred (length l)))
           | _ => None
           end
         else None) tr 0
  | Texp__Amount l k x =>
    (fallback
      (fun lp =>
         let '(l0, Packet _ _ p) := lp in
         if l0 = l? then
           match p with
           | inr (Response__Account (_, (_, _, a))) => Some a
           | inr (Response__ListAccount l) =>
             snd ∘ snd <$> nth_error l (min k (pred (length l)))
           | _ => None
           end
         else None) tr 100) * x / 4
  end.

Definition instantiate_request (tr : traceT) (rx : swap_request texp)
  : swap_request id :=
  match rx with
  | Request__ListOrders =>
    Request__ListOrders
  | Request__ListAccount uid =>
    Request__ListAccount uid
  | Request__TakeOrder   uid ox =>
    Request__TakeOrder   uid          $ instantiate_exp tr ox
  | Request__MakeOrder   uid bt ba st sax =>
    Request__MakeOrder   uid bt ba st $ instantiate_exp tr sax
  | Request__Deposit     uid t a =>
    Request__Deposit     uid t a
  | Request__Withdraw    uid t ax =>
    Request__Withdraw    uid t        $ instantiate_exp tr ax
  end.

Definition randomN : N -> IO N := fmap n_of_int ∘ ORandom.int ∘ int_of_n.

Definition gen_request (ss : swap_state exp) (tr : traceT)
  : IO (swap_request texp) :=
  let (accounts, orders) := ss in
  let getOrder (lp : labelT * packetT) : IO (option (texp order_id)) :=
      let '(l, Packet _ _ p) := lp in
      match p with
      | inr (Response__Order _) => ret $ Some (Texp__Order l O)
      | inr (Response__ListOrders ((_::_) as os)) =>
        Some ∘ Texp__Order l ∘ fst <$> io_choose' os
      | _ => ret None
      end in
  let genOrder : IO order_id :=
      let getOid (o : orderT exp) : option order_id :=
          if fst o is Exp__Const n then Some n else None in
      io_choose_ (ret 0) (map_if getOid orders) in
  let getAmount (lp : labelT * packetT) : IO (option (texp amountT)) :=
      let '(l, Packet _ _ p) := lp in
      pc <- randomN 8;;
      match p with
      | inr (Response__Account _) => ret $ Some (Texp__Amount l O pc)
      | inr (Response__ListAccount ((_::_) as la)) =>
             Some <$> (Texp__Amount l <$> (fst <$> io_choose' la) <*> (ret pc))
      | _ => ret None
      end in
  let genAmount : IO amountT :=
      io_choose_ (ret 100) (map (snd ∘ snd) accounts) in
  uid <- io_choose [0;1;2;3;4];;
  lox <- map_if id <$> sequence (map getOrder tr);;
  oid <- io_choose_ (Texp__Const <$> genOrder) lox;;
  bt <- io_choose ["CNY";"USD";"JPY";"EUR";"ETH"];;
  ba <- randomN 1000;;
  st <- io_choose ["CNY";"USD";"JPY";"EUR";"ETH"];;
  ams <- map_if id <$> sequence (map getAmount tr);;
  ax <- io_choose_ (Texp__Const <$> genAmount) ams;;
  io_choose
    [Request__ListOrders;
     Request__ListAccount uid;
     Request__TakeOrder   uid oid;
     Request__MakeOrder   uid bt ba st ax;
     Request__Deposit     uid bt ba;
     Request__Withdraw    uid st ax].
