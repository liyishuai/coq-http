From QuickChick Require Export
     QuickChick.
From ExtLib Require Export
     Functor
     Option.
From Coq Require Export
     Basics
     List.
Export
  IfNotations
  ListNotations.

Definition get' {K V} (eqb : K -> K -> bool) (k : K)
  : list (K * V) -> option V :=
  fmap snd ∘ find (eqb k ∘ fst).

Definition get {K V} `{Dec_Eq K}
  : K -> list (K * V) -> option V :=
  get' (fun k k' => k = k'?).

Definition delete' {K V} (eqb : K -> K -> bool) (k : K)
  : list (K * V) -> list (K * V) :=
  filter (negb ∘ eqb k ∘ fst).

Definition delete {K V} `{Dec_Eq K}
  : K -> list (K * V) -> list (K * V) :=
  delete' (fun k k' => k = k'?).

Definition put {K V} : K -> V -> list (K * V) -> list (K * V) :=
  compose cons ∘ pair.

Definition update' {K V} (eqb : K -> K -> bool) (k : K) (v : V)
  : list (K * V) -> list (K * V) :=
  put k v ∘ delete' eqb k.

Definition update {K V} `{Dec_Eq K} : K -> V -> list (K * V) -> list (K * V) :=
  update' (fun k k' => k = k'?).

Fixpoint pick {A} (f : A -> bool) (l : list A) : option (A * list A) :=
  if l is a :: tl
  then if f a
       then Some (a, tl)
       else if pick f tl is Some (x, l')
            then Some (x, a::l')
            else None
  else None.
