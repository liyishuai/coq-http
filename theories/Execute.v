From SimpleIO Require Export
     IO_Float
     IO_Random.
From HTTP Require Export
     NetUnix
     Parser
     Tester.
Open Scope string_scope.

Fixpoint findResponse (s : conn_state)
  : IO (conn_state * option (packetT id)) :=
  match s with
  | [] => ret ([], None)
  | cfs :: t =>
    let '(c, (f, str)) := cfs in
    match parse parseResponse str with
    | inl (Some err) =>
      failwith $ "Bad response " ++ to_string str ++ " received on connection "
               ++ to_string c ++ ", error message: " ++ err
    | inl None => '(t', op) <- findResponse t;;
                 ret (cfs :: t', op)
    | inr (r, str') =>
      (* curr <- OFloat.to_string <$> OUnix.gettimeofday;; *)
      (* prerr_endline curr;; *)
      (* prerr_endline ("==============RECEIVED==============" *)
      (*                  ++ to_string c ++ CRLF ++ response_to_string r);; *)
      ret ((c, (f, str')) :: t, Some (Packet Conn__Server (Conn__User c) (inr r)))
    end
  end.

Definition io_choose_ {A} (default : IO A) (l : list A) : IO A :=
  match l with
  | [] => default
  | a :: _ =>
    i <- nat_of_int <$> ORandom.int (int_of_nat (length l));;
    ret (nth i l a)
  end.

Definition io_choose' {A} (l : list A) : IO (nat * A) :=
  match l with
  | [] => failwith "Cannot choose from empty list"
  | a :: _ =>
    i <- nat_of_int <$> ORandom.int (int_of_nat (length l));;
    ret (i, nth i l a)
  end.

Definition io_choose {A} : list A -> IO A :=
  fmap snd ∘ io_choose'.

Definition io_or {A} (x y : IO A) : IO A :=
  b <- ORandom.bool tt;;
  if b : bool then x else y.

Definition gen_string' : IO string :=
  io_choose ["Hello"; "World"].

Fixpoint gen_many {A} (n : nat) (ma : IO A) : IO (list A) :=
  match n with
  | O => ret []
  | S n' => liftA2 cons ma $ io_or (ret []) (gen_many n' ma)
  end.

Definition gen_string : IO string :=
  String "~" ∘ String.concat "" <$> gen_many 3 gen_string'.

Definition gen_path (s : server_state exp) : IO path :=
  io_choose_ gen_string (map fst s).

Fixpoint pick_some {A} (l : list (option A)) : list A :=
  match l with
  | [] => []
  | Some a :: l' => a :: pick_some l'
  | None   :: l' =>     pick_some l'
  end.

Variant texp : Type -> Set :=
  Texp__Const  : field_value -> texp field_value
| Texp__Var    : labelT      -> texp field_value
| Texp__Random :               texp field_value.

Instance Serialize__texp : Serialize (texp field_value) :=
  fun tx => match tx with
         | Texp__Const v => Atom v
         | Texp__Var x   => [Atom "Step"; to_sexp x]%sexp
         | Texp__Random  => Atom "Random"
         end.

Instance Serialize__request {exp_} `{Serialize (exp_ field_value)}
  : Serialize (http_request exp_) :=
  fun req =>
    let 'Request line fields obody := req in
    [Atom $ line_to_string line;
    to_sexp fields;
    Atom $ body_to_string obody]%sexp.

Definition get_tag (pkt : packetT id) : option field_value :=
  if packet__payload pkt is inr res
  then findField "ETag" $ response__fields res
  else None.

Definition has_tag (pkt : packetT id) : bool :=
  if get_tag pkt is Some _ then true else false.

Definition gen_request (ss : server_state exp) (tr : traceT)
  : IO (http_request texp) :=
  p <- gen_path ss;;
  m <- io_choose [Method__GET; Method__PUT];;
  let l : request_line :=
      RequestLine m (RequestTarget__Origin p None) (Version 1 1) in
  let host_field := @Field texp "Host" $ Texp__Const "localhost" in
  let rs := filter (has_tag ∘ snd) tr in
  t <- io_choose_ (pure Texp__Random) (map (Texp__Var ∘ fst) rs);;
  tag_field <- (io_choose [[Field "If-Match" t];
                         [Field "If-None-Match" t];
                         []]);;
  match m with
  | Method__PUT =>
    str0 <- gen_string;;
    let str1 : string := p ++ ": " ++ str0 in
    ret $ Request
        l (host_field
             ::(@Field texp "Content-Length" $ Texp__Const $
                      to_string $ String.length str1)
             ::tag_field)
        (Some str1)
  | Method__GET =>
    ret $ Request l (host_field::tag_field) None
  | _ => ret $ Request l [host_field] None
  end%string.

Fixpoint map_if {A B} (f : A -> option B) (l : list A) : list B :=
  if l is a::l'
  then (if f a is Some b then cons b else id) (map_if f l')
  else [].

Definition instantiate_field (tr : traceT) (tx : texp field_value)
  : field_value :=
  match tx with
  | Texp__Random  => """Random"""
  | Texp__Const v => v
  | Texp__Var x   =>
    if map_if (get_tag ∘ snd) tr is t::_ then t else """Unknown"""
  end.

Definition instantiate_request (tr : traceT) (rx : http_request texp)
  : http_request id :=
  let 'Request l fx b := rx in
  let fs := map (fun '(Field n vx) => Field n (instantiate_field tr vx)) fx in
  Request l fs b.

Definition http_tester {E} `{Is__tE E} : itree E void :=
  tester $ observer $ compose_switch tcp http_smi.

Instance Shrink__request : Shrink (http_request texp) := { shrink _ := [] }.

Definition other_handler : nondetE +' logE ~> IO :=
  fun _ e => match e with
          | (ne|) => let 'Or := ne in ORandom.bool tt
          | (|le) => let 'Log str := le in
                    prerr_endline str
          end.

Definition cleanup (s : conn_state) : IO unit :=
  fold_left (fun m fd => OUnix.close fd;; m)
            (map (fst ∘ snd) s) (ret tt).

Module HttpTypes : IShrinkSIG.

Definition requestT            := http_request id.
Definition responseT           := http_response id.

Definition symreqT             := http_request texp.
Definition Shrink__symreqT       := Shrink__request.
Definition Serialize__symreqT    := @Serialize__request texp _.
Definition instantiate_request := instantiate_request.
Definition gen_state           := server_state exp.
Definition gen_request         := gen_request.

Definition connT               := connT.
Definition Conn__Server          := Conn__Server.
Definition Serialize__connT      := Serialize__connT.
Definition Dec_Eq__connT         := Dec_Eq__connT.

Definition packetT             := packetT id.
Definition Packet              := @Packet id.
Definition packet__payload       := @packet__payload id.
Definition packet__src           := @packet__src id.
Definition packet__dst           := @packet__dst id.
Definition Serialize__packetT    := Serialize__packetT.

Definition otherE              := nondetE +' logE.
Definition other_handler       := other_handler.

Definition conn_state          := conn_state.
Definition init_state          := [] : conn_state.
Definition recv_response       := recv_bytes;; findResponse.
Definition send_request        := send_request.
Definition cleanup             := cleanup.

Definition tester              := http_tester.

End HttpTypes.

Module TestHTTP := IShrink HttpTypes.

Definition test_http : IO bool :=
  TestHTTP.test.
