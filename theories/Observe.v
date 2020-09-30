From ITree Require Export
     Exception.
From HTTP Require Export
     Tcp.

Variant observeE : Type -> Set :=
  Observe__ToServer : observeE (packetT exp)
| Observe__ToClient : observeE (packetT id).

Variant decideE : Type -> Set :=
  Decide : decideE bool.

Variant unifyE : Type -> Type :=
  Unify__Fresh   : unifyE (exp message_body)
| Unify__Payload : payloadT exp -> payloadT id -> unifyE unit.

Notation failureE := (exceptE string).

Class Is__oE E `{failureE -< E} `{nondetE -< E}
      `{decideE -< E} `{unifyE -< E} `{observeE -< E}.
Notation oE := (failureE +' nondetE +' decideE +' unifyE +' observeE).
Instance oE_Is__oE : Is__oE oE. Defined.

Definition dualize {E R} `{Is__oE E} (e : switchE R) : itree E R :=
  match e in switchE R return _ R with
  | Switch__In => trigger Observe__ToServer
  | Switch__Out (Packet s0 d0 p0) =>
    '(Packet s d p) <- trigger Observe__ToClient;;
    if (s =? s0) &&& (d =? d0)
    then embed Unify__Payload p0 p
    else throw "Unexpected payload observed to client"
  end.

Definition observer {E R} `{Is__oE E} (m : itree sE R) : itree E R :=
  interp
    (fun _ e =>
       match e with
       | (se|) => dualize se
       | (|ne|) =>
         match ne in nondetE R return _ R with
         | Or => trigger Decide
         end
       | (||se) =>
         match se in symE _ R return _ R with
         | Sym__New => trigger Unify__Fresh
         end
       end) m.
