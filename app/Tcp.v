From HTTP Require Import
     Tcp.
From App Require Export
     Semantics.
From QuickChick Require Export
     Decidability.

Record packetT {requestT responseT} :=
  Packet {
      packet__src     : connT;
      packet__dst     : connT;
      packet__payload : requestT + responseT
    }.
Arguments packetT : clear implicits.
Arguments Packet {_ _}.

Variant switchE {requestT responseT} : Type -> Type :=
  Switch__In  : switchE (packetT requestT responseT)
| Switch__Out : packetT requestT responseT -> switchE unit.
Arguments switchE : clear implicits.

Definition dec_connT (x y : connT) : {x = y} + {x <> y} :=
  dec_if_dec_eq x y (Eq__Dec x y).

Definition tcp {q r E} `{switchE q r -< E} `{nondetE -< E}
  : itree E void :=
  iter_forever
    (fun in_pkt0 =>
       let input := pkt <- trigger Switch__In;; ret (in_pkt0 ++ [pkt]) in
       let conns : list connT := nodup dec_connT (map packet__src in_pkt0) in
       let output :=
           out <- choose_from_list conns;;
           match out with
           | None => input
           | Some c =>
             match pick (fun p => packet__src p = c?) in_pkt0 with
             | None => input         (* should not happen *)
             | Some (p, in_pkt1) => embed Switch__Out p;; ret in_pkt1
             end
           end in
       or input output) ([] : list (packetT q r)).

Variant netE {q r server_state} : Type -> Type :=
  Net__Recv : server_state -> netE (packetT q r)
| Net__Send : packetT q r -> netE unit.
Arguments netE : clear implicits.

Class  Is__nE q r s E NE `{netE q r s -< NE} `{nondetE -< NE} `{E -< NE}.
Notation nE q r s E := (netE q r s +' nondetE +' E).
Instance nE_Is__nE {q r s E} : Is__nE q r s E (nE q r s E). Defined.

CoFixpoint compose' {q r s E NE} `{Is__nE q r s E NE}
           (bi bo : list (packetT q r))
           (net : itree (switchE q r +' nondetE) void)
           (app : itree (appE q r s +' E) void) : itree NE void :=
  match observe net, observe app with
  | RetF vd, _ | _, RetF vd => match vd in void with end
  | TauF net', _ => Tau (compose' bi bo net' app)
  | _, TauF app' => Tau (compose' bi bo net  app')
  | VisF vn kn, VisF va ka =>
    let step__net st :=
        match vn with
        | (se|) =>
          match se in switchE _ _ Y return (Y -> _) -> _ with
          | Switch__In =>
            fun k =>
              match bo with
              | [] =>
                pkt <- embed Net__Recv st;;
                Tau (compose' bi []  (k pkt) app)
              | pkt :: bo' =>
                Tau (compose' bi bo' (k pkt) app)
              end
          | Switch__Out pkt =>
            fun k =>
              if packet__dst pkt is Conn__Server
              then Tau (compose' (bi ++ [pkt]) bo (k tt) app)
              else embed Net__Send pkt;;
                   Tau (compose' bi bo (k tt) app)
          end kn
        | (|ne) =>
          match ne in nondetE Y return (Y -> _) -> _ with
          | Or => fun k => b <- trigger Or;;
                       Tau (compose' bi bo (k b) app)
          end kn
        end in
    match va with
    | (ae|) =>
      match ae in appE _ _ _ Y return (Y -> _) -> _ with
      | App__Recv st =>
        fun k =>
          match pick (fun p => packet__src p <> Conn__Server?) bi with
          | None => step__net st
          | Some (Packet s _ p, bi') =>
            match s, p with
            | Conn__User c, inl r => Tau (compose' bi' bo net (k (c, r)))
            | _, _ => Tau (compose' bi' bo net app) (* drop the packet *)
            end
          end
      | App__Send c r =>
        fun k =>
          Tau (compose' bi (bo ++ [Packet Conn__Server (Conn__User c) (inr r)])
                        net (k tt))
      end ka
    | (|e) => r <- trigger e;; Tau (compose' bi bo net (ka r))
    end
  end.

Definition compose_switch {q r s E NE} `{Is__nE q r s E NE}
  : itree (appE q r s +' E) void -> itree NE void :=
  compose' (q:=q) (r:=r) (s:=s) [] [] tcp.

Definition tcp_swap := compose_switch ∘ swap_smi.
