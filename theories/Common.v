From Coq Require Export
     Basics
     Bool
     DecidableClass
     String
     List
     BinNat.
From ExtLib Require Export
     Functor
     Option.
Export
  ListNotations.
Open Scope lazy_bool_scope.
Open Scope program_scope.

Notation "P '?'" := (decide P) (at level 100).

Program Instance Decidable_not {P} `{Decidable P} : Decidable (~ P) := {
  Decidable_witness := negb (P?)
}.
Next Obligation.
  split; intro.
  - apply negb_true_iff in H0.
    eapply Decidable_complete_alt; intuition.
  - erewrite Decidable_sound_alt; intuition.
Qed.

Instance Decidable_eq_N (x y : N) : Decidable (x = y) :=
  { Decidable_witness := N.eqb    x y;
    Decidable_spec    := N.eqb_eq x y }.

Program Instance Decidable_eq_list {A} `{forall x y : A, Decidable (x = y)}
        (x y : list A) : Decidable (x = y) := {
  Decidable_witness :=
    (fix eqb (x y : list A) :=
       match x, y with
       | [], [] => true
       | a::x', b::y' => (a = b?) &&& eqb x' y'
       | _, _ => false
       end) x y }.
Solve Obligations with split; intros; intro; intuition; discriminate.
Next Obligation.
  generalize dependent y.
  induction x; destruct y; intuition; try discriminate.
  - apply andb_true_iff in H0.
    destruct H0.
    f_equal.
    + apply Decidable_spec. assumption.
    + apply IHx. assumption.
  - apply andb_true_iff.
    inversion H0; subst.
    split.
    + apply Decidable_spec. reflexivity.
    + apply IHx. reflexivity.
Qed.

Instance Decidable_eq_string (s1 s2 : string) : Decidable (s1 = s2) :=
  { Decidable_witness := String.eqb    s1 s2;
    Decidable_spec    := String.eqb_eq s1 s2 }.

Program Instance Decidable_eq_option {A} `{forall x y : A, Decidable (x = y)}
        (ox oy : option A) : Decidable (ox = oy) := {
  Decidable_witness :=
    match ox, oy with
    | Some x, Some y => x = y?
    | None  , None   => true
    | _     , _      => false
    end }.
Solve Obligations with split; intuition; discriminate.
Next Obligation.
  destruct ox, oy; intuition; try discriminate;
    f_equal; apply Decidable_spec; intuition.
  inversion H0; reflexivity.
Qed.

Definition get {K V} `{forall x y : K, Decidable (x = y)} (k : K) :
  list (K * V) -> option V :=
  fmap snd ∘ find ((fun kv => k = fst kv?)).

Definition delete {K V} `{forall x y : K, Decidable (x <> y)} (k : K) :
  list (K * V) -> list (K * V) :=
  filter (fun kv => (k <> fst kv?)).

Definition put {K V} : K -> V -> list (K * V) -> list (K * V) :=
  compose cons ∘ pair.

Definition update {K V} `{forall x y : K, Decidable (x <> y)} (k : K) (v : V)
  : list (K * V) -> list (K * V) :=
  put k v ∘ delete k.
