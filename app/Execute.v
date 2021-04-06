From HTTP Require Import
     Execute.
From App Require Import
     Tester.

Variant texp : Type -> Set :=
  Texp__Const   : N -> texp N
| Texp__Order   : labelT -> texp N
| Texp__Account : labelT -> nat -> texp N
| Texp__Amount  : labelT -> nat -> N -> texp N.

Instance Serialize__texp : Serialize (texp N) :=
  fun tx => match tx with
         | Texp__Const    n   => Atom n
         | Texp__Order    x   => [Atom "Order"; Atom x]
         | Texp__Account  x n => [Atom "Account"; Atom x; Atom n]
         | Texp__Amount x n p => [Atom "Amount" ; Atom x; Atom n; Atom p]
         end%sexp.

Instance Serialize__request {exp_} `{Serialize (exp_ N)}
  : Serialize (swap_request exp_) :=
  fun req => match req with
          | Request__ListOrders        =>  Atom "listOrders"
          | Request__ListAccount uid   => [Atom "listAccount"; Atom uid]
          | Request__TakeOrder uid oid => [Atom "takeOrder"; Atom uid; to_sexp oid]
          | Request__MakeOrder uid bt ba st sa =>
            [Atom "makeOrder"; Atom uid; Atom bt; Atom ba; Atom st; to_sexp sa]
          | Request__Deposit uid t a => [Atom "deposit"; Atom uid; Atom t; Atom a]
          | Request__Withdraw uid t a =>
            [Atom "withdraw"; Atom uid; Atom t; to_sexp a]
          end%sexp.

Instance Serialize__symreq : Serialize (swap_request texp) := Serialize__request.

Instance Shrink__request : Shrink (swap_request texp) := { shrink _ := [] }.

Notation packetT := (packetT (swap_request id) (swap_response id)).
Notation traceT  := (@traceT packetT).

Fixpoint fallback {A B} (f : A -> option B) (l : list A) : B -> B :=
  if l is a::l'
  then if f a is Some b then const b else fallback f l'
  else id.
