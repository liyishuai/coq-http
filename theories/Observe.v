From ITree Require Export
     Exception.
From HTTP Require Export
     Tcp.

Variant observeE : Type -> Type :=
  Observe__ToServer : server_state exp -> observeE (packetT id)
| Observe__ToClient : observeE (packetT id).

Definition wrap_field (f : field_line id) : field_line exp :=
  let 'Field n v := f in Field n (Exp__Const v).

Definition wrap_response (r : http_response id) : http_response exp :=
  let 'Response l f ob := r in
  Response l (map wrap_field f) (Exp__Const <$> (ob : option message_body)).

Definition wrap_payload : payloadT id -> payloadT exp :=
  fmap wrap_response.

Definition wrap_packet (pkt : packetT id) : packetT exp :=
  let 'Packet s d p := pkt in
  Packet s d (wrap_payload p).

Variant decideE : Type -> Set :=
  Decide : decideE bool.

Variant unifyE : Type -> Type :=
  Unify__FreshBody : unifyE (exp message_body)
| Unify__FreshETag : unifyE (exp field_value)
| Unify__Match     : exp bool -> bool -> unifyE unit
| Unify__Response  : http_response exp -> http_response id -> unifyE unit.

Notation failureE := (exceptE string).

Class Is__oE E `{failureE -< E} `{nondetE -< E}
      `{decideE -< E} `{unifyE -< E} `{logE -< E} `{observeE -< E}.
Notation oE := (failureE +' nondetE +' decideE +' unifyE +' logE +' observeE).
Instance oE_Is__oE : Is__oE oE. Defined.

Definition dualize {E R} `{Is__oE E} (e : netE R) : itree E R :=
  match e in netE R return _ R with
  | Net__In st => wrap_packet <$> embed Observe__ToServer st
  | Net__Out (Packet s0 d0 p0) =>
    '(Packet s d p) <- trigger Observe__ToClient;;
    if (s =? s0) &&& (d =? d0)
    then match p0, p with
         | inl _, _
         | _, inl _ => throw "Expect response but observed request"
         | inr r0, inr r => embed Unify__Response r0 r
         end
    else throw "Unexpected payload observed to client"
  end.

Definition observer {E R} `{Is__oE E} (m : itree nE R) : itree E R :=
  interp
    (fun _ e =>
       match e with
       | (se|) => dualize se
       | (|ne|) =>
         match ne in nondetE R return _ R with
         | Or => trigger Decide
         end
       | (||le|) =>
         match le in logE R return _ R with
         | Log str => embed Log ("SMI: " ++ str)%string
         end
       | (|||se) =>
         match se in symE _ R return _ R with
         | Sym__NewBody => trigger Unify__FreshBody
         | Sym__NewETag => trigger Unify__FreshETag
         | Sym__Decide x => b <- trigger Decide;;
                         embed Unify__Match x b;;
                         ret b
         end
       end) m.
