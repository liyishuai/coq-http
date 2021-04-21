From HTTP Require Import
     Observe.
From App Require Export
     Tcp.

Variant observeE {q r s} : Type -> Type :=
  Observe__ToServer : s -> observeE (packetT q r)
| Observe__FromServer :   observeE (packetT q r).
Arguments observeE : clear implicits.

Variant unifyE {r : (Set -> Type) -> _} : Type -> Type :=
  Unify__Fresh : unifyE (exp N)
| Unify__Eval  : exp nat -> unifyE nat
| Unify__Match : r exp -> r id -> unifyE unit.
Arguments unifyE : clear implicits.
Arguments unifyE _%type_scope.

Class Is__oE q r s E `{unifyE r -< E} `{failureE -< E} `{decideE -< E}
      `{observeE q (r id) s -< E}.
Notation oE q r s := (unifyE r +' failureE +' decideE +' observeE q (r id) s).
Instance oE_Is__oE q r s : Is__oE q r s (oE q r s). Defined.

Open Scope string_scope.

Definition dualize {q r s T E} `{Is__oE q r s E}
           (e : netE q (r exp) s T) : itree E T :=
  match e in netE _ _ _ T return _ T with
  | Net__Recv ss => '(Packet s d l) <- embed Observe__ToServer ss;;
                 match l with
                 | inl q => ret (Packet s d (inl q))
                 | inr _ => throw "Should not happen: dualize recv"
                 end
  | Net__Send (Packet sx dx px) =>
    '(Packet s d p) <- trigger Observe__FromServer;;
    if (sx, dx) = (s, d)?
    then if (px, p) is (inr rx, inr r)
         then embed Unify__Match rx r
         else throw "Should not happen: dualize send"
    else throw $ "Expect route " ++ to_string (sx, dx)
             ++ " but observed " ++ to_string (s,  d)
  end.

Definition observer {q r s E} `{Is__oE q r s E}
           (m : itree (nE q (r exp) s symE) void) : itree E void :=
  interp (fun _ e =>
            match e with
            | (e|) => dualize e
            | (|ne|) => match ne in nondetE Y return _ Y with
                       | Or => trigger Decide
                       end
            | (||se) =>
              match se in symE Y return _ Y with
              | Sym__Fresh   => trigger Unify__Fresh
              | Sym__Eval nx => embed   Unify__Eval nx
              end
            end) m.

Definition observe_swap := observer ∘ tcp_swap.
