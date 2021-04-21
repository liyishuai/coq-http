From HTTP Require Export
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
  { shrink _ := [] }.

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
  | Request__Clean =>
    Request__Clean
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

Definition randomN : N -> IO N := fmap (N.add 1 ∘ n_of_int) ∘ ORandom.int.

Definition users : list user_id := [1;2;3;4].
Definition tickers : list assetT := ["CNY";"USD";"JPY";"EUR"].

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
      pc <- randomN 6;;
      match p with
      | inr (Response__Account _) => ret $ Some (Texp__Amount l O pc)
      | inr (Response__ListAccount ((_::_) as la)) =>
             Some <$> (Texp__Amount l <$> (fst <$> io_choose' la) <*> (ret pc))
      | _ => ret None
      end in
  let genAmount : IO amountT :=
      io_choose_ (ret 100) (map (snd ∘ snd) accounts) in
  uid <- io_choose (0::users);;
  lox <- map_if id <$> sequence (map getOrder tr);;
  oid <- io_choose_ (Texp__Const <$> genOrder) lox;;
  bt <- io_choose tickers;;
  ba <- randomN 1000;;
  st <- io_choose tickers;;
  ams <- map_if id <$> sequence (map getAmount tr);;
  ax <- io_choose_ (Texp__Const <$> genAmount) ams;;
  io_choose
    [Request__ListOrders;
     Request__ListAccount uid;
     Request__TakeOrder   uid oid;
     Request__MakeOrder   uid bt ba st ax;
     Request__Deposit     uid bt ba;
     Request__Withdraw    uid st ax].

Definition send_request : swap_request id ->
                          Monads.stateT conn_state IO (option connT) :=
  send_request ∘ encode_request.

Definition recv_response : Monads.stateT conn_state IO (option packetT) :=
  op <- recv_http_response;;
  if op is Some (HTTP.Tcp.Packet s d (inr res))
  then
    (* if decode_response res is Some sres *)
    (* then liftState (prerr_endline (to_string sres));; *)
    (*      ret (Some (Packet s d (inr sres))) *)
    (* else *)
    (*   liftState (prerr_endline "Invalid response");; *)
    (*   ret None *)
    ret (decode_response res >>= Some ∘ Packet s d ∘ inr)
  else ret None.

Definition wrap_order (o : orderT id) : orderT exp :=
  let '(oid, (b, ba, s, sa)) := o in
  (Exp__Const oid, (Exp__Const b, ba, Exp__Const s, sa)).

Definition wrap_account (a : accountT id) : accountT exp :=
  let '(aid, av) := a in
  (Exp__Const aid, av).

Definition tester_init : IO (swap_state exp) :=
  OUnix.sleep 1;;
  s1 <- IO.fix_io
         (fun send_rec s =>
            '(s1, oc) <- send_request Request__Clean s;;
            if oc is Some _
            then ret s1
            else send_rec s1) [];;
  's2 <- IO.fix_io
          (fun recv_rec s =>
             '(s2, op) <- recv_response s;;
             if op is Some _ then ret s2
             else recv_rec s2) s1;;
  cleanup s2;;
  ret ([], []).

Definition MyType := Type.
Definition nondetE' : Type -> MyType := nondetE.

Module SwapTypes : IShrinkSIG.

Definition requestT            := swap_request id.
Definition responseT           := swap_response id.

Definition connT               := connT.
Definition Conn__Server          := Conn__Server.
Definition Serialize__connT      := Serialize__connT.
Definition Dec_Eq__connT         := Dec_Eq__connT.

Definition packetT             := packetT.
Definition Packet              := @Packet requestT responseT.
Definition packet__payload       := @packet__payload requestT responseT.
Definition packet__src           := @packet__src requestT responseT.
Definition packet__dst           := @packet__dst requestT responseT.
Definition Serialize__packetT    := Serialize__packetT.

Definition gen_state           := swap_state exp.

Definition otherE              := nondetE +' logE.
Definition other_handler       := other_handler.

Definition conn_state          := conn_state.
Definition init_state          := [] : conn_state.
Definition recv_response       := recv_response.
Definition send_request        := send_request.
Definition cleanup             := cleanup.

Definition symreqT             := swap_request texp.
Definition Shrink__symreqT       := Shrink__request.
Definition Serialize__symreqT    := Serialize__request : Serialize symreqT.

Definition instantiate_request := instantiate_request.
Definition gen_request         := gen_request.

Definition tester_state        := swap_state exp.
Definition tester_init         := tester_init.
Definition tester              := swap_tester.

End SwapTypes.

Module TestSwap := IShrink SwapTypes.

Definition test_swap : IO bool := TestSwap.test.
