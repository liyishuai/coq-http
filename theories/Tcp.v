From Coq Require Export
     Nat.
From HTTP Require Export
     Instances
     Semantics.
Export SumNotations.
Open Scope nat_scope.
Open Scope sum_scope.

Definition payloadT exp_ : Type := http_request id + http_response exp_.

Record packetT {exp_} :=
  Packet {
      packet__src : connT;
      packet__dst : connT;
      packet__payload : payloadT exp_
    }.
Arguments packetT : clear implicits.
Arguments Packet        {_}.
Arguments packet__src     {_}.
Arguments packet__dst     {_}.
Arguments packet__payload {_}.

#[global]
Instance Serialize__payloadT : Serialize (payloadT id) :=
  fun p =>
    match p with
    | inl (Request  line   _ _) => Atom $ line_to_string   line
    | inr (Response status _ _) => Atom $ status_to_string status
    end.

#[global]
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

Program Fixpoint nodup {A} `{Dec_Eq A}
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
  Net__In  : server_state exp -> netE (packetT exp)
| Net__Out : packetT exp -> netE unit.

Class Is__nE E `{netE -< E} `{nondetE -< E} `{logE -< E} `{symE exp -< E}.
Notation nE := (netE +' nondetE +' logE +' symE exp).
#[global]
Instance nE_Is__nE : Is__nE nE. Defined.

Definition packet_to_server {exp_} (p : packetT exp_) : bool :=
  match p.(packet__dst) with
  | Conn__Server => true
  | Conn__Client _ => false
  end.
Definition packet_from_user {exp_} (p : packetT exp_) : bool :=
  match p.(packet__src) with
  | Conn__Client _ => true
  | Conn__Server => false
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
    let step__net st :=
        match vn with
        | (se|) =>
          match se in switchE Y return (Y -> _) -> _ with
          | Switch__In =>
            fun k =>
              match bfo with
              | [] =>
                pkt <- embed Net__In st;;
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
          | None => step__net st
          | Some (pkt, bi') =>
            let 'Packet s _ p := pkt in
            match s, p with
            | Conn__Client c, inl r => Tau (compose' conns bi' bfo net (k (c, r)))
            | _, _ => Tau (compose' conns bi' bfo net app) (* drop the packet *)
            end
          end
      | App__Send c r =>
        fun k =>
          Tau (compose' conns bfi (bfo ++ [Packet Conn__Server (Conn__Client c) (inr r)])
                        net (k tt))
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
