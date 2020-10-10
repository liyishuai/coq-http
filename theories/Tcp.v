From Coq Require Export
     Nat.
From HTTP Require Export
     Semantics.
Export SumNotations.
Open Scope nat_scope.
Open Scope sum_scope.

Definition payloadT exp_ : Type := http_request + http_response exp_.

Definition connT := option (clientT + string).

Record packetT {exp_} :=
  Packet {
      packet__src : connT;
      packet__dst : connT;
      packet__payload : payloadT exp_
    }.
Arguments packetT : clear implicits.
Arguments Packet {_}.

Variant switchE : Type -> Type :=
  Switch__In  : switchE (packetT exp)
| Switch__Out : packetT exp -> switchE unit.

Definition tcp {E R} `{switchE -< E} `{nondetE -< E} : itree E R :=
  (rec-fix loop in_pkt0 :=
     let input :=
         pkt <- trigger Switch__In;;
         call (pkt :: in_pkt0) in
     let output :=
         '(in_pkt1, out_pkt1, _) <-
           fold_right
             (fun pkt i_o_f =>
                '(in_pkt, out_pkt, f) <- i_o_f;;
                if f pkt : bool
                then
                  or (ret (pkt :: in_pkt, out_pkt,
                           fun pkt' =>
                             if (packet__src pkt' = packet__src pkt?) &&&
                                (packet__dst pkt' = packet__dst pkt?)
                             then false
                             else f pkt'))
                     (ret (in_pkt, pkt :: out_pkt, f))
                else ret (pkt :: in_pkt, out_pkt, f))
             (ret ([], [], const true)) in_pkt0;;
         match out_pkt1 with
         | _ :: _ =>
           fold_right (fun pkt r =>
                         r;;
                         embed Switch__Out pkt) (ret tt) out_pkt1;;
           call in_pkt1
         | [] =>
           match rev' in_pkt1 with
           | [] => input
           | pkt :: in_pkt2 =>
             embed Switch__Out pkt;;
             call (rev' in_pkt2)
           end
         end in
     or input output) [].

Variant netE : Type -> Type :=
  Net__In  : server_state exp -> option string -> netE (packetT exp)
| Net__Out : packetT exp -> netE unit.

Class Is__nE E `{netE -< E} `{nondetE -< E} `{logE -< E} `{symE exp -< E}.
Notation nE := (netE +' nondetE +' logE +' symE exp).
Instance nE_Is__nE : Is__nE nE. Defined.

Definition packet_to_app      {exp_} (p : packetT exp_) : bool :=
  packet__dst p = None?.
Definition packet_from_client {exp_} (p : packetT exp_) : bool :=
  match packet__src p with
  | Some (inl _) => true
  | _            => false
  end.
Definition packet_from_origin {exp_} (p : packetT exp_) : bool :=
  match packet__src p with
  | Some (inr _) => true
  | _            => false
  end.

CoFixpoint compose' {E R} `{Is__nE E}
           (bfi bfo : list (@packetT exp))
           (net : itree (switchE +' nondetE) R)
           (app : itree smE R) : itree E R :=
  match observe net, observe app with
  | RetF r, _
  | _, RetF r => Ret r
  | TauF net', _ => Tau (compose' bfi bfo net' app)
  | _, TauF app' => Tau (compose' bfi bfo net  app')
  | VisF vn kn, VisF va ka =>
    let step__net st oh :=
        match vn with
        | (se|) =>
          match se in switchE Y return (Y -> _) -> _ with
          | Switch__In =>
            fun k =>
              match bfo with
              | [] =>
                pkt <- embed Net__In st oh;;
                Tau (compose' bfi []  (k pkt) app)
              | pkt :: bo' =>
                Tau (compose' bfi bo' (k pkt) app)
              end
          | Switch__Out pkt =>
            fun k =>
              if packet_to_app pkt
              then Tau (compose' (bfi ++ [pkt]) bfo (k tt) app)
              else embed Net__Out pkt;;
                   Tau (compose' bfi bfo (k tt) app)
          end kn
        | (|ne) =>
          match ne in nondetE Y return (Y -> _) -> _ with
          | Or =>
            fun k =>
              b <- trigger Or;;
              Tau (compose' bfi bfo (k b) app)
          end kn
        end in
    match va with
    | (ae|) =>
      match ae in appE _ Y return (Y -> _) -> _ with
      | App__Recv st =>
        fun k =>
          match pick packet_from_client bfi with
          | None => step__net st None
          | Some (pkt, bi') =>
            let 'Packet s _ p := pkt in
            match s, p with
            | Some (inl c), inl r => Tau (compose' bi' bfo net (k (c, r)))
            | _, _ => Tau (compose' bi' bfo net app) (* drop the packet *)
            end
          end
      | App__Send c r =>
        fun k =>
          Tau (compose' bfi (bfo ++ [Packet None (Some (inl c)) (inr r)])
                        net (k tt))
      | App__Forward h r =>
        fun k => Tau (compose' bfi (bfo ++ [Packet None (Some (inr h)) (inl r)])
                            net (k tt))
      | App__Backward st h =>
        fun k =>
          match pick packet_from_origin bfi with
          | None => step__net st (Some h)
          | Some (pkt, bi') =>
            let 'Packet s _ p := pkt in
            match s, p with
            | Some (inr h), inr r =>
              Tau (compose' bi' bfo net (k (unwrap_response r)))
            | _, _ => Tau (compose' bi' bfo net app) (* drop the packet *)
            end
          end
      end ka
    | (|ne|) =>
      match ne in nondetE Y return (Y -> _) -> _ with
      | Or =>
        fun k =>
          b <- trigger Or;;
          Tau (compose' bfi bfo net (k b))
      end ka
    | (||le|) =>
      match le in logE Y return (Y -> _) -> _ with
      | Log str =>
        fun k =>
          embed Log ("App: " ++ str)%string;;
          Tau (compose' bfi bfo net (k tt))
      end ka
    | (|||se) =>
      match se in symE _ Y return (Y -> _) -> _ with
      | Sym__New =>
        fun k =>
          x <- trigger Sym__New;;
          Tau (compose' bfi bfo net (k x))
      end ka
    end
  end.

Definition compose_switch {E T} `{Is__nE E} :
  itree (switchE +' nondetE) T -> itree smE T -> itree E T :=
  compose' [] [].
