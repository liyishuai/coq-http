From HTTP Require Export
     Tester.
From App Require Export
     Observe.

Definition solver_state := list (var * option N).

Definition unifyN (nx : exp N) (n : N) (s : solver_state)
  : option solver_state :=
  match nx with
  | Exp__Var x =>
    if get x s is Some (Some n0)
    then if n0 =? n then Some s else None
    else Some $ update x (Some n) s
  | Exp__Const n0 => if n0 =? n then Some s else None
  | Exp__Nth _ _  => None
  end.

Definition unifyOrder (s : solver_state) (ox : orderT exp) (o : orderT id)
  : option solver_state :=
  let '((oidx, (bix, bax, six, sax)), (oid, (bi, ba, si, sa))) := (ox, o) in
  if (bax, sax) = (ba, sa)?
  then unifyN oidx oid s >>= unifyN bix bi >>= unifyN six si
  else None.

Definition unifyAccount (s : solver_state) (ax : accountT exp) (a : accountT id)
  : option solver_state :=
  let '((aidx, vx), (aid, v)) := (ax, a) in
  if vx = v? then unifyN aidx aid s else None.

Definition unifyList {A : (Type -> Type) -> Type}
           (unifier : solver_state -> A exp -> A id -> option solver_state)
           (lx : list (A exp)) (l : list (A id)) (s : solver_state)
  : option solver_state :=
  if length lx =? length l
  then fold_left (fun os ab => os >>= (fun s => uncurry (unifier s) ab))
                 (zip lx l) (pure s)
  else None.

Definition get_value (s : solver_state) (x : exp N) : option N :=
  match x with
  | Exp__Var   x => join $ get x s
  | Exp__Const n => Some n
  | Exp__Nth _ _ => None
  end.

Fixpoint find_nth {A} (f : A -> bool) (l : list A) : nat :=
  match l with
  | [] => O
  | a :: l' => if f a then O else S (find_nth f l')
  end.

Definition eval_nth (n : N) (l : list (exp N)) (s : solver_state) : nat :=
  let l' : list (option N) := map (get_value s) l in
  find_nth (fun on => on = Some n?) l'.

Instance Serialize__idVar : Serialize (id var) := Atom.

Instance Serialize__IdResponse : Serialize (swap_response id) :=
  Serialize__Response.

Definition instantiate_unify {E A} `{failureE -< E} (e : unifyE swap_response A)
  : Monads.stateT solver_state (itree E) A :=
  fun s : solver_state =>
    match e with
    | Unify__Fresh =>
      let x : var := fresh_var s in
      ret (put x None s, Exp__Var x)
    | Unify__Eval v =>
      if v is Exp__Nth x l
      then if get_value s x is Some n
           then ret (s, eval_nth n l s)
           else ret (s, length l)
      else throw "Should not happen"
    | Unify__Match rx r =>
      let mismatch := throw $ "Expect " ++ to_string rx
                            ++ " but observed " ++ to_string r in
      let handle os' := if os' is Some s' then ret (s', tt) else mismatch in
      match rx, r with
      | Response__InsufficientFund, Response__InsufficientFund
      | Response__NotFound        , Response__NotFound => ret (s, tt)
      | Response__ListAccount lx  , Response__ListAccount l =>
        handle $ unifyList (A:=accountT) unifyAccount lx l s
      | Response__ListOrders  lx  , Response__ListOrders  l =>
        handle $ unifyList (A:=orderT) unifyOrder lx l s
      | Response__ListAccount [], Response__ListOrders  []
      | Response__ListOrders  [], Response__ListAccount [] => ret (s, tt)
      | Response__Account ax, Response__Account a => handle $ unifyAccount s ax a
      | Response__Order   ox, Response__Order   o => handle $ unifyOrder   s ox o
      | _, _ => mismatch
      end
    end.

Definition solver' {E F} `{failureE -< E} `{F -< E}
           (m : itree (unifyE swap_response +' F) void)
  : Monads.stateT solver_state (itree E) void :=
  interp
    (fun _ e =>
       match e with
       | (ue|) => instantiate_unify ue
       | (|ee)  => liftState (F:=itree _) (trigger ee)
       end) m.

Definition solver {E F} `{failureE -< E} `{F -< E}
           (m : itree (unifyE swap_response +' F) void) : itree E void :=
  snd <$> solver' m [].

Class Is__stE q r s E `{failureE -< E} `{decideE -< E} `{observeE q r s -< E}.
Notation stE q r s := (failureE +' decideE +' observeE q r s).
Instance stE_Is__stE q r s : Is__stE q r s (stE q r s). Defined.

Definition solve_swap {E}
           `{Is__stE (swap_request id) (swap_response id) (swap_state exp) E}
           : swap_state exp -> itree E void
  := solver ∘ observe_swap.
