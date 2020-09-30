From Coq Require Export
     Nat.
From HTTP Require Export
     Semantics.
Export SumNotations.
Open Scope nat_scope.
Open Scope sum_scope.

Definition payloadT exp_ : Type := http_request + http_response exp_.

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
                             if (packet__src pkt' =? packet__src pkt) &&&
                                (packet__dst pkt' =? packet__dst pkt)
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

Class Is__sE E `{switchE -< E} `{nondetE -< E} `{symE exp -< E}.
Notation sE := (switchE +' nondetE +' symE exp).
Instance sE_Is__sE : Is__sE sE. Defined.

Definition conn_is_app : connT -> bool := Nat.eqb 0.

CoFixpoint compose' {E R} `{Is__sE E}
           (bfi bfo : list (@packetT exp))
           (net : itree (switchE +' nondetE) R)
           (app : itree smE R) : itree E R :=
  match observe net, observe app with
  | RetF r, _
  | _, RetF r => Ret r
  | TauF net', _ => Tau (compose' bfi bfo net' app)
  | _, TauF app' => Tau (compose' bfi bfo net  app')
  | VisF vn kn, VisF va ka =>
    let step__net :=
        match vn with
        | (se|) =>
          match se in switchE Y return (Y -> _) -> _ with
          | Switch__In =>
            fun k =>
              match bfo with
              | [] =>
                pkt <- trigger Switch__In;;
                Tau (compose' bfi []  (k pkt) app)
              | pkt :: bo' =>
                Tau (compose' bfi bo' (k pkt) app)
              end
          | Switch__Out pkt =>
            fun k =>
              if conn_is_app (packet__dst pkt)
              then Tau (compose' (bfi ++ [pkt]) bfo (k tt) app)
              else embed Switch__Out pkt;;
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
      | App__Recv =>
        fun k =>
          match bfi with
          | [] => step__net
          | pkt :: bi' =>
            let 'Packet s _ p := pkt in
            match p with
            | inl r => Tau (compose' bi' bfo net (k (s, r)))
            | inr _ => Tau (compose' bi' bfo net app) (* drop the packet *)
            end
          end
      | App__Send c r =>
        fun k => Tau (compose' bfi (bfo ++ [Packet 0 c (inr r)]) net (k tt))
      end ka
    | (|ne|) =>
      match ne in nondetE Y return (Y -> _) -> _ with
      | Or =>
        fun k =>
          b <- trigger Or;;
          Tau (compose' bfi bfo net (k b))
      end ka
    | (||se) =>
      match se in symE _ Y return (Y -> _) -> _ with
      | Sym__New =>
        fun k =>
          x <- trigger Sym__New;;
          Tau (compose' bfi bfo net (k x))
      end ka
    end
  end.

Definition compose_switch {E T} `{Is__sE E} :
  itree (switchE +' nondetE) T -> itree smE T -> itree E T :=
  compose' [] [].
