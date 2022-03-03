From AsyncTest Require Export
     AsyncTest.
From ExtLib Require Export
     OptionMonad.
From HTTP Require Export
     Decode
     Printer
     Observe.
Open Scope N_scope.
Open Scope string_scope.

#[global]
Instance Serialize__field {exp_} `{Serialize (exp_ field_value)}
  : Serialize (field_line exp_) :=
  fun f => let 'Field n v := f in
        [Atom n; to_sexp v]%sexp.

Definition exp_state : Set := N * list (var * option message_body) *
                              list (var * (field_value + list field_value)).

Definition fresh_var {T} (vs : list (var * T)) : var :=
  1 + fold_left N.max (map fst vs) 0.

Definition fresh_body (s : exp_state) : exp_state :=
  let '(n, bs, es) := s in
  (1 + n, bs, es).

Definition fresh_etag (s : exp_state) : exp_state * var :=
  let (bs, es) := s in
  let x := fresh_var es in
  (bs, (x, inr []) :: es, x).

Definition assert (w : bool) (x : var) (v : field_value)(s : exp_state)
  : string + exp_state :=
  let '(n, bs, es) := s in
  let fx  := get x es in
  let err := inl $ "Expect " ++ to_string fx
                 ++ ", but observed " ++ to_string v
                 ++ ", under " ++ (if w then "weak" else "strong")
                 ++ " comparison" in
  match fx with
  | Some (inl e)  => if etag_match w e v then inr s else err
  | Some (inr ts) => if existsb (String.eqb v) ts
                    then err
                    else inr (n, bs, put x (inl v) es)
  | None => inr (n, bs, put x (inl v) es)
  end.

Definition assert_not (w : bool) (x : var) (v : field_value) (s : exp_state)
  : string + exp_state :=
  let '(n, bs, es) := s in
  let '(n, bs, es) := s in
  let fx  := get x es in
  let err := inl $ "Expect not " ++ to_string fx
                 ++ ", but observed " ++ to_string v in
  match fx with
  | Some (inl e) => if etag_match w e v then err else inr s
  | Some (inr ts) => if existsb (String.eqb v) ts
                    then inr s
                    else inr (n, bs, put x (inr (v :: ts)) es)
  | None          => inr (n, bs, put x (inr [v]) es)
  end.

Definition unify {T} (e : exp T) (v : T) (s : exp_state) : string + exp_state :=
  let err {T} `{Serialize T} (v' : T) :=
      inl $ "Expect " ++ to_string e ++ ", but observed " ++ to_string v' in
  match e in exp T return T -> exp_state -> string + exp_state with
  | Exp__Const m => fun v s => if m =? v then inr s else err v
  | Exp__Body x =>
    fun v s =>
      let '(n, bs, es) := s in
      match get x bs with
      | Some (Some b) => if b =? v then inr s else err v
      | Some None     => err v
      | None          => inr (n, put x (Some v) bs, es)
      end
  | Exp__ETag x => assert true x
  | Exp__Match f (Exp__ETag x) w =>
    fun v => if v then assert w x f else assert_not w x f
  | Exp__Match _ _ _ => fun v _ => err v
  end v s.

Definition unify_state : Set := exp_state * list (clientT * clientT).

Variant testerE : Type -> Type :=
  Tester__Recv : testerE (packetT id)
| Tester__Send : server_state exp ->
               testerE (packetT id).

Class Is__stE E `{failureE -< E}
      `{decideE -< E} `{logE -< E} `{testerE -< E}.
Notation stE := (failureE +' decideE +' logE +' testerE).
#[global]
Instance stE_Is__stE : Is__stE stE. Defined.

Definition instantiate_unify {E A} `{Is__stE E} (e : unifyE A)
  : Monads.stateT unify_state (itree E) A :=
  fun s =>
    let (xs, ps) := s in
    match e with
    | Unify__FreshBody =>
      let '(x, bs, fs) := fresh_body xs in
      Ret ((x, bs, fs, ps), Exp__Body x)
    | Unify__FreshETag =>
      let (s', x) := fresh_etag xs in
      Ret (s', ps, Exp__ETag x)
    | Unify__Response rx r =>
      let 'Response (Status _ cx _ as stx) fx obx := rx in
      let 'Response (Status _ c  _ as st ) fs ob  := r  in
      if cx = c?
      then
        let unify_field (os : string + exp_state) (f : field_line exp)
            : string + exp_state :=
            match os with
            | inr s =>
              let 'Field n vx := f in
              match field__value <$> find (String.eqb n ∘ field__name) fs with
              | Some v => unify vx (v : id field_value) s
              | None   => inl $ to_string f ++ " not found in "
                             ++ fields_to_string fs
              end
            | inl err => inl err
            end in
        let os1 : string + exp_state := fold_left unify_field fx (inr xs) in
        match os1 with
        | inr s1 =>
          match obx, ob with
          | Some bx, Some b =>
            match unify bx b s1 with
            | inr s2  => Ret (s2, ps, tt)
            | inl err => throw $ "Unify message failed: " ++ err
            end
          | Some _, None => throw "Expect message body, but not found."
          | None, Some _ => throw "Expect no message body, but observed it."
          | None, None   => Ret (s1, ps, tt)
          end
        | inl err => throw $ "Unify field failed: " ++ err
        end
      else throw $ "Expect status " ++ status_to_string stx
                 ++ " but observed " ++ status_to_string st
                 (* ++ ", under state " ++ to_string s *)
    | Unify__Match bx b =>
      (* embed Log ("Unifying " ++ to_string bx ++ " against " ++ to_string b *)
      (*                        ++ ", under state " ++ to_string xs);; *)
      match unify bx b xs with
      | inr s1  =>
        (* embed Log ("Unification successful: " ++ to_string s1);; *)
        Ret (s1, ps, tt)
      | inl err => throw $ "Unify ETag failed: " ++ err
      end
    end.

Definition instantiate_observe {E A} `{Is__stE E} (e : observeE A)
  : Monads.stateT unify_state (itree E) A :=
  fun s =>
    let (xs, ps) := s in
    match e with
    | Observe__ToServer st =>
      pkt <- embed Tester__Send st;;
      Ret (s, pkt)
    | Observe__FromServer =>
      pkt <- embed Tester__Recv;;
      Ret (s, pkt)
    end.

Definition unifier' {E R} `{Is__stE E} (m : itree oE R)
  : Monads.stateT unify_state (itree E) R :=
  interp (fun _ e =>
            match e with
            | (||ue|)  => instantiate_unify   ue
            | (||||oe) => instantiate_observe oe
            | (Throw err|) =>
              fun s =>
                (* embed Log ("Failing state: " ++ to_string s);; *)
                throw err
            | (|e|)
            | (|||e|) => @liftState unify_state _ (itree _) _ (trigger e)
            end) m.

Definition unifier {E R} `{Is__stE E} (m : itree oE R) : itree E R :=
  (* snd <$> logger__st (snd <$> unifier' m (0, [], [], [])) []. *)
  snd <$> unifier' m (0, [], [], []).

CoFixpoint match_event {T R} (e0 : testerE R) (r : R) (m : itree stE T)
  : itree stE T :=
  match observe m with
  | RetF x  => Ret x
  | TauF m' => Tau (match_event e0 r m')
  | VisF e k =>
    match e with
    | (|||oe) =>
      match oe in testerE Y, e0 in testerE R return (Y -> _) -> R -> _ with
      | Tester__Send _, Tester__Send _
      | Tester__Recv      , Tester__Recv => id
      | _, _ => fun _ _ => throw "Unexpected event"
      end k r
    | _ => vis e (match_event e0 r ∘ k)
    end
  end.

Definition match_observe {T R} (e : testerE T) (r : T) (l : list (itree stE R))
  : list (itree stE R) := map (match_event e r) l.

Definition packet_req (p : Trace.packetT) : packetT id :=
  let 'Trace.Packet s d j := p in
  Packet s d (inl $ request_of_IR j).

Definition packet_res (p : Trace.packetT) : packetT id :=
  let 'Trace.Packet s d j := p in
  Packet s d (inr $ response_of_IR j).

Class Is__tE E`{failureE -< E} `{@clientE (server_state exp) -< E}
      `{nondetE -< E} `{logE -< E}.
Notation tE := (failureE +' @clientE (server_state exp) +' nondetE +' logE).
#[global]
Instance tE_Is__tE : Is__tE tE. Defined.

CoFixpoint backtrack' {E R} `{Is__tE E} (others : list (itree stE R))
           (m : itree stE R) : itree E R :=
  match observe m with
  | RetF r => Ret r
  | TauF m' => Tau (backtrack' others m')
  | VisF e k =>
    let catch (err : string) : itree E R :=
        match others with
        | [] => throw err
        | other :: others' =>
          (* embed Log ("Retry upon " ++ err);; *)
          Tau (backtrack' others' other)
        end in
    match e with
    | (Throw err|) => catch err
    | (|de|) =>
      match de in decideE Y return (Y -> _) -> _ with
      | Decide => fun k => b <- trigger Or;;
                        (* embed Log (to_string b);; *)
                       Tau (backtrack' (k (negb b) :: others) (k b))
      end k
    | (||le|) =>
      match le in logE Y return (Y -> _) -> _ with
      | Log str =>
        fun k => embed Log ("Observer: " ++ str);;
              Tau (backtrack' others (k tt))
      end k
    | (|||te) =>
      match te in testerE Y return (Y -> _) -> _ with
      | Tester__Send st =>
        fun k => op1 <- trigger Client__Recv;;
              match op1 with
              | Some p1 =>
                match match_observe Tester__Recv (packet_res p1) others with
                | [] => catch "Unexpected receive from server"
                | other :: others' =>
                  Tau (backtrack' others' other)
                end
              | None =>
                opkt <- embed Client__Send st;;
                match opkt with
                | Some pkt =>
                  let p : packetT id := packet_req pkt in
                  Tau (backtrack' (match_observe (Tester__Send st)
                                                 p others) (k p))
                | None =>
                  match others with
                  | [] =>
                    Tau (backtrack' [] m)
                  | other::others' =>
                    Tau (backtrack' (others' ++ [m]) other)
                  end
                end
              end
      | Tester__Recv =>
        fun k => opkt <- embed Client__Recv;;
              match opkt with
              | Some pkt =>
                let p : packetT id := packet_res pkt in
                Tau (backtrack' (match_observe Tester__Recv p others) (k p))
              | None =>
                match others with
                | [] =>
                  (* embed Log ("No more choices, retry receiving from " *)
                  (*              ++ to_string src);; *)
                  Tau (backtrack' [] m)
                | other :: others' =>
                  (* embed Log ("Postpone receiving from " ++ to_string src);; *)
                  Tau (backtrack' (others' ++ [m]) other)
                end
              end
      end k
    end
  end.

Definition backtrack {E R} `{Is__tE E} : itree stE R -> itree E R :=
  backtrack' [].

Definition tester {E R} `{Is__tE E} : itree oE R -> itree E R :=
  backtrack ∘ unifier.
