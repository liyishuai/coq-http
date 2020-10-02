From ExtLib Require Export
     OptionMonad.
From HTTP Require Export
     Printer
     Observe.
Open Scope N_scope.
Open Scope string_scope.

Definition exp_state : Set := list (var * option message_body) *
                              list (var * (field_value + list field_value)).

Definition fresh_var {T} (vs : list (var * T)) : var :=
  1 + fold_left N.max (map fst vs) 0.

Definition fresh_body (s : exp_state) : exp_state * var :=
  let (bs, es) := s in
  let x := fresh_var bs in
  ((x, None) :: bs, es, x).

Definition fresh_etag (s : exp_state) : exp_state * var :=
  let (bs, es) := s in
  let x := fresh_var es in
  (bs, (x, inr []) :: es, x).

Definition assert (x : var) (v : field_value) (s : exp_state)
  : option exp_state :=
  let (bs, es) := s in
  match get x es with
  | Some (inl e)  => if e =? v then Some s else None
  | Some (inr ts) => if existsb (String.eqb v) ts
                    then None
                    else Some (bs, put x (inl v) es)
  | None => Some (bs, put x (inl v) es)
  end.

Definition assert_not (x : var) (v : field_value) (s : exp_state)
  : option exp_state :=
  let (bs, es) := s in
  match get x es with
  | Some (inl e) => if e =? v then None else Some s
  | Some (inr ts) => Some (bs, put x (inr (v :: ts)) es)
  | None          => Some (bs, put x (inr [v]) es)
  end.

Definition unify {T} (e : exp T) (v : T) (s : exp_state) : option exp_state :=
  match e in exp T return T -> exp_state -> option exp_state with
  | Exp__Const m => fun v s => if m =? v then Some s else None
  | Exp__Body x =>
    fun v s =>
      let (bs, es) := s in
      match get x bs with
      | Some (Some b) => if b =? v then Some s else None
      | Some None     => None
      | None          => Some (put x (Some v) bs, es)
      end
  | Exp__ETag x => assert x
  | Exp__Match f (Exp__ETag x) =>
    fun v => if v then assert x f else assert_not x f
  | Exp__Match _ _ => fun _ _ => None
  end v s.

Variant genE : Type -> Type :=
  Gen : server_state exp -> exp_state -> genE (packetT id).

Variant clientE : Type -> Type :=
  Client__Recv : clientE (packetT id)
| Client__Send : packetT id -> clientE unit.

Class Is__tE E `{failureE -< E} `{nondetE -< E} `{genE -< E} `{clientE -< E}.
Notation tE := (failureE +' nondetE +' genE +' clientE).
Instance tE_Is__tE : Is__tE tE. Defined.

CoFixpoint match_event {T R} (e0 : observeE R) (r : R) (m : itree oE T)
  : itree oE T :=
  match observe m with
  | RetF x  => Ret x
  | TauF m' => Tau (match_event e0 r m')
  | VisF e k =>
    match e with
    | (||||oe) =>
      match oe in observeE Y, e0 in observeE R return (Y -> _) -> R -> _ with
      | Observe__ToServer _, Observe__ToServer _
      | Observe__ToClient, Observe__ToClient => id
      | _, _ => fun _ _ => throw "Unexpected event"
      end k r
    | _ => vis e (match_event e0 r ∘ k)
    end
  end.

Definition match_observe {T R} (e : observeE T) (r : T) (l : list (itree oE R))
  : list (itree oE R) := map (match_event e r) l.

CoFixpoint tester' {E R} `{Is__tE E} (s : exp_state) (others : list (itree oE R))
           (m : itree oE R) : itree E R :=
  match observe m with
  | RetF r => Ret r
  | TauF m' => Tau (tester' s others m')
  | VisF e k =>
    let catch (err : string) : itree E R :=
        match others with
        | [] => throw err
        | other :: others' => Tau (tester' s others' other)
        end in
    match e with
    | (Throw err|) => catch err
    | (|ne|) =>
      match ne in nondetE Y return (Y -> _) -> _ with
      | Or => fun k => b <- trigger Or;; Tau (tester' s others (k b))
      end k
    | (||de|) =>
      match de in decideE Y return (Y -> _) -> _ with
      | Decide => fun k => b <- trigger Or;;
                       Tau (tester' s (k (negb b) :: others) (k b))
      end k
    | (|||ue|) =>
      match ue in unifyE Y return (Y -> _) -> _ with
      | Unify__FreshBody => fun k => let (s', x) := fresh_body s in
                               Tau (tester' s' others (k (Exp__Body x)))
      | Unify__FreshETag => fun k => let (s', x) := fresh_etag s in
                               Tau (tester' s' others (k (Exp__ETag x)))
      | Unify__Response rx r =>
        fun k =>
          let 'Response (Status _ cx _ as stx) fx obx := rx in
          let 'Response (Status _ c  _ as st ) fs ob  := r  in
          if cx = c?
          then
            let unify_field (os : option exp_state) (f : field_line exp)
                : option exp_state :=
                match os with
                | Some s =>
                  let 'Field n vx := f in
                  match field__value <$> find (String.eqb n ∘ field__name) fs with
                  | Some v => unify vx (v : id field_value) s
                  | None   => None
                  end
                | None => None
                end in
            let os1 : option exp_state := fold_left unify_field fx (Some s) in
            match os1 with
            | Some s1 =>
              match obx, ob with
              | Some bx, Some b =>
                match unify bx b s1 with
                | Some s2 => Tau (tester' s2 others (k tt))
                | None    => catch "Message body unsatisfying."
                end
              | Some _, None => catch "Expect message body, but not found."
              | None, Some _ => catch "Expect no message body, but observed it."
              | None, None => Tau (tester' s1 others (k tt))
              end
            | None => catch "Field lines unsatisfying."
            end
          else catch $ "Expect status " ++ status_to_string stx
                    ++ " but observed " ++ status_to_string st
      end k
    | (||||oe) =>
      match oe in observeE Y return (Y -> _) -> _ with
      | Observe__ToServer st =>
        fun k => pkt <- embed Gen st s;;
              embed Client__Send pkt;;
              Tau (tester' s (match_observe (Observe__ToServer st) pkt others) (k pkt))
      | Observe__ToClient =>
        fun k => pkt <- trigger Client__Recv;;
              Tau (tester' s (match_observe Observe__ToClient pkt others) (k pkt))
      end k
    end
  end.

Definition tester {E R} `{Is__tE E} : itree oE R -> itree E R :=
  tester' ([], []) [].
