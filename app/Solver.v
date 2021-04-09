From HTTP Require Export
     Tester.
From App Require Export
     Observe.

Definition solver_state := list (var * (N + list N)).

Definition assertN (nx : exp N) (n : N) (s : solver_state)
  : option solver_state :=
  match nx with
  | Exp__Var x =>
    match get x s with
    | Some (inl n0) => if n0 =? n then Some s else None
    | Some (inr ns) => if existsb (N.eqb n) ns
                      then None
                      else Some $ update x (inr (n::ns)) s
    | None => Some $ put x (inl n) s
    end
  | Exp__Const n0 => if n0 =? n then Some s else None
  | Exp__Nth _ _  => None
  end.

Definition assertNotN (nx : exp N) (n : N) (s : solver_state)
  : option solver_state :=
  match nx with
  | Exp__Var x =>
    match get x s with
    | Some (inl n0) => if n0 =? n then None else Some s
    | Some (inr ns) => Some $ update x (inr (n::ns)) s
    | None => Some $ put x (inr [n]) s
    end
  | Exp__Const n0 => if n0 =? n then None else Some s
  | Exp__Nth _ _ => None
  end.

Definition unifyOrder (s : solver_state) (ox : orderT exp) (o : orderT id)
  : option solver_state :=
  let '((oidx, (bix, bax, six, sax)), (oid, (bi, ba, si, sa))) := (ox, o) in
  if (bax, sax) = (ba, sa)?
  then assertN oidx oid s >>= assertN bix bi >>= assertN six si
  else None.

Definition unifyAccount (s : solver_state) (ax : accountT exp) (a : accountT id)
  : option solver_state :=
  let '((aidx, vx), (aid, v)) := (ax, a) in
  if vx = v? then assertN aidx aid s else None.

Definition unifyList {A : (Type -> Type) -> Type}
           (unifier : solver_state -> A exp -> A id -> option solver_state)
           (lx : list (A exp)) (l : list (A id)) (s : solver_state)
  : option solver_state :=
  if length lx =? length l
  then fold_left (fun os ab => os >>= (fun s => uncurry (unifier s) ab))
                 (zip lx l) (pure s)
  else None.

Fixpoint eval_nth {E} `{decideE -< E} `{failureE -< E}
           (n : N) (l : list (exp N))
  : Monads.stateT solver_state (itree E) nat :=
  fun s =>
    let assertSome (ost : option solver_state) : itree E solver_state :=
        if ost is Some st then ret st else throw "Unsatisfiable" in
    match l with
    | [] => ret (s, O)
    | x::l' => b <- trigger Decide;;
             if b : bool
             then s1 <- assertSome (assertN    x n s);; ret (s1, O)
             else s1 <- assertSome (assertNotN x n s);;
                  '(s2, n') <- eval_nth n l' s1;;
                  ret (s2, S n')
    end.

Definition instantiate_unify {E A} `{failureE -< E} `{decideE -< E}
           (e : unifyE swap_response A)
  : Monads.stateT solver_state (itree E) A :=
  fun s : solver_state =>
    match e with
    | Unify__Fresh =>
      let x : var := fresh_var s in
      ret (put x (inr []) s, Exp__Var x)
    | Unify__Eval v =>
      if v is Exp__Nth (Exp__Const n) l
      then eval_nth n l s
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

Definition solver' {E F} `{failureE -< E} `{decideE -< E} `{F -< E}
           (m : itree (unifyE swap_response +' F) void)
  : Monads.stateT solver_state (itree E) void :=
  interp
    (fun _ e =>
       match e with
       | (ue|) => instantiate_unify ue
       | (|ee)  => liftState (F:=itree _) (trigger ee)
       end) m.

Definition solver {E F} `{failureE -< E} `{decideE -< E} `{F -< E}
           (m : itree (unifyE swap_response +' F) void) : itree E void :=
  snd <$> solver' m [].

Class Is__stE q r s E `{failureE -< E} `{decideE -< E} `{observeE q r s -< E}.
Notation stE q r s := (failureE +' decideE +' observeE q r s).
Instance stE_Is__stE q r s : Is__stE q r s (stE q r s). Defined.

Definition solve_swap {E}
           `{Is__stE (swap_request id) (swap_response id) (swap_state exp) E}
           : swap_state exp -> itree E void
  := solver ∘ observe_swap.
