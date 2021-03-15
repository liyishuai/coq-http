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

Definition get {K V} `{Dec_Eq K} (k : K) :
  list (K * V) -> option V :=
  fmap snd ∘ find ((fun kv => k = fst kv?)).

Definition delete {K V} `{Dec_Eq K} (k : K) :
  list (K * V) -> list (K * V) :=
  filter (fun kv => (k <> fst kv?)).

Definition put {K V} : K -> V -> list (K * V) -> list (K * V) :=
  compose cons ∘ pair.

Definition update {K V} `{Dec_Eq K} (k : K) (v : V)
  : list (K * V) -> list (K * V) :=
  put k v ∘ delete k.

Fixpoint pick {A} (f : A -> bool) (l : list A) : option (A * list A) :=
  if l is a :: tl
  then if f a
       then Some (a, tl)
       else if pick f tl is Some (x, l')
            then Some (x, a::l')
            else None
  else None.
