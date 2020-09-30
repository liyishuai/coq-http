From Coq Require Export
     Basics
     Bool
     DecidableClass.
From Ceres Require Export
     Ceres.
From ExtLib Require Export
     Functor
     Monad
     Option.
From ITree Require Export
     Nondeterminism
     ITree.
From HTTP Require Export
     Message.
Export
  FunctorNotation
  MonadNotation.
Open Scope lazy_bool_scope.
Open Scope list_scope.
Open Scope monad_scope.
Open Scope program_scope.

Program Instance Decidable_not {P} `{Decidable P} : Decidable (~ P) := {
  Decidable_witness := negb Decidable_witness
}.
Next Obligation.
  split; intro.
  - apply negb_true_iff in H0.
    eapply Decidable_complete_alt; intuition.
  - erewrite Decidable_sound_alt; intuition.
Qed.

Program Instance Decidable_eq_list {A} `{forall x y : A, Decidable (x = y)}
        (x y : list A) : Decidable (x = y) := {
  Decidable_witness :=
    (fix eqb (x y : list A) :=
       match x, y with
       | [], [] => true
       | a::x', b::y' => @Decidable_witness (a = b) _ &&& eqb x' y'
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

Definition status_line_of_code (c : status_code) : status_line :=
  Status (Version 1 1) c (snd <$> find (N.eqb c ∘ fst) statusCodes).

Definition server_state {exp_} := list (path * option (exp_ message_body)).

Definition get {exp_} (p : path) : @server_state exp_ -> option (option (exp_ message_body)) :=
  fmap snd ∘ find ((fun pq => decide (p = fst pq))).

Definition put {exp_} : path -> option (exp_ message_body) -> server_state -> server_state
  := compose cons ∘ pair.

Definition delete {exp_} (p : path) : @server_state exp_ -> server_state :=
  filter (fun pq => (decide (p <> fst pq))).

Inductive exp : Type -> Set :=
  Exp__Const : message_body -> exp message_body
| Exp__Var   : exp message_body.

Notation connT := nat.

Variant appE {exp_} : Type -> Type :=
  App__Recv : appE (connT * http_request)
| App__Send : connT -> @http_response exp_ -> appE unit.
Arguments appE : clear implicits.

Variant symE {exp_} : Type -> Set :=
  Sym__New : symE (exp_ message_body).
Arguments symE : clear implicits.

Class Is__smE E `{appE exp -< E} `{nondetE -< E} `{symE exp -< E}.
Notation smE := (appE exp +' nondetE +' symE exp).
Instance smE_Is__smE : Is__smE smE. Defined.

Definition http_smi {E R} `{Is__smE E} : itree E R :=
  rec
    (fun st : @server_state exp =>
       '(c, Request (RequestLine methd t _) hs om) <- trigger App__Recv;;
       let bad_request :=
           trigger (App__Send c (Response (status_line_of_code 400) [] None));;
           call st in
       match t with
       | RequestTarget__Origin p _
       | RequestTarget__Absolute _ _ p _ =>
         match methd with
         | Method__GET =>
           let not_found :=
               trigger (App__Send c (Response (status_line_of_code 404) [] None))
           in
           let ok m :=
               trigger (App__Send c (@Response exp (status_line_of_code 200)
                                             [] (Some m))) in
           match get p st with
           | Some (Some m) => ok m;; call st
           | Some None => not_found;; call st
           | None =>
             or (not_found;; call ((p, None)::st))
                (m <- trigger (@Sym__New exp);; ok m;; call ((p, Some m)::st))
           end
         | Method__PUT =>
           match om with
           | Some m =>
             trigger (App__Send c (Response (status_line_of_code 204) [] None));;
             call ((p, Some (Exp__Const m))::delete p st)
           | None => bad_request
           end
         | _ =>
           trigger (App__Send c (Response (status_line_of_code 405) [] None));;
           call st
         end
       | _ => bad_request
       end) [].
