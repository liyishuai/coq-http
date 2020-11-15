From Coq Require Export
     Nat.
From HTTP Require Export
     Instances
     Semantics.
Export SumNotations.
Open Scope nat_scope.
Open Scope sum_scope.

Definition payloadT exp_ : Type := http_request + http_response exp_.

Variant connT :=
  Conn__User      : clientT -> connT
| Conn__Server
| Conn__Proxy     : clientT -> connT
| Conn__Authority : authority -> connT.

Program Instance Decidable_eq__connT (x y : connT) : Decidable (x = y) := {
  Decidable_witness :=
    match x, y with
    | Conn__Server     , Conn__Server => true
    | Conn__User      x, Conn__User      y
    | Conn__Proxy     x, Conn__Proxy     y
    | Conn__Authority x, Conn__Authority y => x = y?
    | _, _ => false
    end }.
Solve Obligations with split; intuition; discriminate.
Next Obligation.
  intuition.
  - destruct x, y; f_equal; try apply Decidable_spec; intuition.
  - subst.
    destruct y; try apply Nat.eqb_eq; intuition.
    destruct a.
    destruct authority__userinfo, authority__port;
      repeat (apply andb_true_iff; intuition);
      try apply eqb_eq; try apply N.eqb_eq; reflexivity.
Qed.

Record packetT {exp_} :=
  Packet {
      packet__src : connT;
      packet__dst : connT;
      packet__payload : payloadT exp_
    }.
Arguments packetT : clear implicits.
Arguments Packet {_}.

Instance Serialize__payloadT : Serialize (payloadT id) :=
  fun p =>
    match p with
    | inl (Request  line   _ _) => Atom $ line_to_string   line
    | inr (Response status _ _) => Atom $ status_to_string status
    end.

Instance Serialize__connT : Serialize connT :=
  fun c =>
    match c with
    | Conn__User      c => [Atom "User"; to_sexp c]
    | Conn__Server      => [Atom "Server"]
    | Conn__Proxy     c => [Atom "Proxy"; to_sexp c]
    | Conn__Authority a => [Atom "Authority"; to_sexp a]
    end%sexp.

Instance Serialize__packetT : Serialize (packetT id) :=
  fun pkt =>
    let 'Packet s d p := pkt in
    [[Atom "Src"; to_sexp s];
    [Atom "Dst"; to_sexp d];
    [Atom "Msg"; to_sexp p]]%sexp.

Variant switchE : Type -> Type :=
  Switch__In  : switchE (packetT exp)
| Switch__Out : packetT exp -> switchE unit.

Lemma filter_length {A} (f : A -> bool) (l : list A) :
  length (filter f l) <= length l.
Proof.
  induction l; simpl; intuition.
  destruct (f a); simpl; intuition.
Qed.

Program Fixpoint nodup {A} `{forall x y : A, Decidable (x = y)}
        (l : list A) {measure (length l)} : list A :=
  match l with
  | [] => []
  | a :: l' => a :: nodup (filter (fun b => negb (a = b?)) l')
  end.
Next Obligation.
  apply le_n_S.
  apply filter_length.
Defined.

Fixpoint choose_from_list {E A} `{nondetE -< E} (l : list A)
  : itree E (option A) :=
  match l with
  | []  => ret None
  | [a] => ret (Some a)
  | a :: l' => or (ret (Some a)) (choose_from_list l')
  end.

Definition tcp {E R} `{switchE -< E} `{nondetE -< E} : itree E R :=
  rec
    (fun in_pkt0 =>
       let input :=
           pkt <- trigger Switch__In;;
           call (in_pkt0 ++ [pkt]) in
       let conns : list connT := nodup (map packet__src in_pkt0) in
       out <- choose_from_list conns;;
       match out with
       | None => input
       | Some c =>
         match pick (fun p => packet__src p = c?) in_pkt0 with
         | None => input         (* should not happen *)
         | Some (p, in_pkt1) =>
           embed Switch__Out p;;
           call in_pkt1
         end
       end) ([] : list (packetT exp)).

Variant netE : Type -> Type :=
  Net__In  : server_state exp -> connT -> netE (packetT exp)
| Net__Out : packetT exp -> netE unit.

Class Is__nE E `{netE -< E} `{nondetE -< E} `{logE -< E} `{symE exp -< E}.
Notation nE := (netE +' nondetE +' logE +' symE exp).
Instance nE_Is__nE : Is__nE nE. Defined.

Definition packet_to_server {exp_} (p : packetT exp_) : bool :=
  match packet__dst p with
  | Conn__Server | Conn__Proxy _ => true
  | _ => false
  end.
Definition packet_from_user {exp_} (p : packetT exp_) : bool :=
  match packet__src p with
  | Conn__User _ => true
  | _            => false
  end.
Definition packet_to_proxy {exp_} (c0 : clientT) (p : packetT exp_) : bool :=
  match packet__dst p with
  | Conn__Proxy c => c0 = c?
  | _            => false
  end.

CoFixpoint compose' {E R} `{Is__nE E}
           (conns : list (clientT * authority))
           (bfi bfo : list (@packetT exp))
           (net : itree (switchE +' nondetE) R)
           (app : itree smE R) : itree E R :=
  match observe net, observe app with
  | RetF r, _
  | _, RetF r => Ret r
  | TauF net', _ => Tau (compose' conns bfi bfo net' app)
  | _, TauF app' => Tau (compose' conns bfi bfo net  app')
  | VisF vn kn, VisF va ka =>
    let step__net st c :=
        match vn with
        | (se|) =>
          match se in switchE Y return (Y -> _) -> _ with
          | Switch__In =>
            fun k =>
              match bfo with
              | [] =>
                pkt <- embed Net__In st c;;
                Tau (compose' conns bfi []  (k pkt) app)
              | pkt :: bo' =>
                Tau (compose' conns bfi bo' (k pkt) app)
              end
          | Switch__Out pkt =>
            fun k =>
              if packet_to_server pkt
              then Tau (compose' conns (bfi ++ [pkt]) bfo (k tt) app)
              else (* embed Log ("Network emitting packet to " *)
                   (*              ++ to_string (packet__dst pkt));; *)
                   embed Net__Out pkt;;
                   Tau (compose' conns bfi bfo (k tt) app)
          end kn
        | (|ne) =>
          match ne in nondetE Y return (Y -> _) -> _ with
          | Or =>
            fun k =>
              b <- trigger Or;;
              Tau (compose' conns bfi bfo (k b) app)
          end kn
        end in
    match va with
    | (ae|) =>
      match ae in appE _ Y return (Y -> _) -> _ with
      | App__Recv st =>
        fun k =>
          match pick packet_from_user bfi with
          | None => step__net st Conn__Server
          | Some (pkt, bi') =>
            let 'Packet s _ p := pkt in
            match s, p with
            | Conn__User c, inl r => Tau (compose' conns bi' bfo net (k (c, r)))
            | _, _ => Tau (compose' conns bi' bfo net app) (* drop the packet *)
            end
          end
      | App__Send c r =>
        fun k =>
          Tau (compose' conns bfi (bfo ++ [Packet Conn__Server (Conn__User c) (inr r)])
                        net (k tt))
      | App__Forward h r =>
        fun k =>
          let c := length conns in
          Tau (compose' (put c h conns) bfi
                        (bfo ++ [Packet (Conn__Proxy c) (Conn__Authority h) (inl r)])
                        net (k c))
      | App__Backward st c =>
        fun k =>
          match pick (packet_to_proxy c) bfi with
          | None => step__net st (Conn__Proxy c)
          | Some (pkt, bi') =>
            match packet__payload pkt with
            | inr r =>
              Tau (compose' conns bi' bfo net (k (unwrap_response r)))
            | _ => Tau (compose' conns bi' bfo net app) (* drop the packet *)
            end
          end
      end ka
    | (|ne|) =>
      match ne in nondetE Y return (Y -> _) -> _ with
      | Or =>
        fun k =>
          b <- trigger Or;;
          Tau (compose' conns bfi bfo net (k b))
      end ka
    | (||le|) =>
      match le in logE Y return (Y -> _) -> _ with
      | Log str =>
        fun k =>
          embed Log ("App: " ++ str);;
          Tau (compose' conns bfi bfo net (k tt))
      end ka
    | (|||se) =>
      match se in symE _ Y return (Y -> _) -> _ with
      | Sym__New =>
        fun k =>
          x <- trigger Sym__New;;
          Tau (compose' conns bfi bfo net (k x))
      end ka
    end
  end%string.

Definition compose_switch {E T} `{Is__nE E} :
  itree (switchE +' nondetE) T -> itree smE T -> itree E T :=
  compose' [] [] [].
