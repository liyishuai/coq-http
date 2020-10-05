From ExtLib Require Export
     OptionMonad.
From HTTP Require Export
     Printer
     Observe.
Open Scope N_scope.
Open Scope string_scope.

Instance Serialize__payloadT : Serialize (payloadT id) :=
  fun p =>
    match p with
    | inl r => Atom $ request_to_string  r
    | inr r => Atom $ response_to_string r
    end.

Instance Serialize__packetT : Serialize (packetT id) :=
  fun pkt =>
    let 'Packet s d p := pkt in
    [[Atom "Src"; to_sexp s];
    [Atom "Dst"; to_sexp d];
    [Atom "Msg"; to_sexp p]]%sexp.

Instance Serialize__field : Serialize (field_line exp) :=
  fun f => let 'Field n v := f in
        [to_sexp n; to_sexp v]%sexp.

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

(** https://httpwg.org/http-core/draft-ietf-httpbis-semantics-latest.html#rfc.section.7.9.3.2 *)

Definition etag_eqb (x y : field_value) : bool :=
  match x, y with
  | String "W" (String "/" _), _
  | _, String "W" (String "/" _) => false
  | _, _ => x =? y
  end.

Definition assert (x : var) (v : field_value) (s : exp_state)
  : string + exp_state :=
  let '(n, bs, es) := s in
  let fx  := get x es in
  let err := inl $ "Expect " ++ to_string fx
                 ++ ", but observed " ++ to_string v in
  match fx with
  | Some (inl e)  => if etag_eqb e v then inr s else err
  | Some (inr ts) => if existsb (String.eqb v) ts
                    then err
                    else inr (n, bs, put x (inl v) es)
  | None => inr (n, bs, put x (inl v) es)
  end.

Definition assert_not (x : var) (v : field_value) (s : exp_state)
  : string + exp_state :=
  let '(n, bs, es) := s in
  let '(n, bs, es) := s in
  let fx  := get x es in
  let err := inl $ "Expect not " ++ to_string fx
                 ++ ", but observed " ++ to_string v in
  match fx with
  | Some (inl e) => if etag_eqb e v then err else inr s
  | Some (inr ts) => inr (n, bs, put x (inr (v :: ts)) es)
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
  | Exp__ETag x => assert x
  | Exp__Match f (Exp__ETag x) =>
    fun v => if v then assert x f else assert_not x f
  | Exp__Match _ _ => fun v _ => err v
  end v s.

Variant testerE : Type -> Type :=
  Tester__Recv : testerE (packetT id)
| Tester__Send : server_state exp -> exp_state -> testerE (packetT id).

Class Is__stE E `{failureE -< E} `{nondetE -< E}
      `{decideE -< E} `{logE -< E} `{testerE -< E}.
Notation stE := (failureE +' nondetE +' decideE +' logE +' testerE).
Instance stE_Is__stE : Is__stE stE. Defined.

Definition instantiate_unify {E A} `{Is__stE E} (e : unifyE A)
  : Monads.stateT exp_state (itree E) A :=
  fun s =>
    match e with
    | Unify__FreshBody =>
      let '(x, bs, fs) := fresh_body s in
      Ret ((x, bs, fs), Exp__Body x)
    | Unify__FreshETag =>
      let (s', x) := fresh_etag s in
      Ret (s', Exp__ETag x)
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
        let os1 : string + exp_state := fold_left unify_field fx (inr s) in
        match os1 with
        | inr s1 =>
          match obx, ob with
          | Some bx, Some b =>
            match unify bx b s1 with
            | inr s2  => Ret (s2, tt)
            | inl err => throw $ "Unify message failed: " ++ err
            end
          | Some _, None => throw "Expect message body, but not found."
          | None, Some _ => throw "Expect no message body, but observed it."
          | None, None   => Ret (s1, tt)
          end
        | inl err => throw $ "Unify field failed: " ++ err
        end
      else throw $ "Expect status " ++ status_to_string stx
                 ++ " but observed " ++ status_to_string st
                 ++ ", under state " ++ to_string s
    | Unify__Match bx b =>
      (* embed Log ("Unifying " ++ to_string bx ++ " against " ++ to_string b);; *)
      match unify bx b s with
      | inr s1  => Ret (s1, tt)
      | inl err => throw $ "Unify If-Match failed: " ++ err
      end
    end.

Definition instantiate_observe {E A} `{Is__stE E} (e : observeE A)
  : Monads.stateT exp_state (itree E) A :=
  fun s =>
    match e with
    | Observe__ToServer st => pkt <- embed Tester__Send st s;; Ret (s, pkt)
    | Observe__ToClient => pkt <- trigger Tester__Recv;; Ret (s, pkt)
    end.

Definition liftState {S A} {F : Type -> Type} `{Functor F} (aF : F A)
  : Monads.stateT S F A :=
  fun s : S => pair s <$> aF.

Definition unifier {E R} `{Is__stE E} (m : itree oE R)
  : Monads.stateT exp_state (itree E) R :=
  interp (fun _ e =>
            match e with
            | (|||ue|)  => instantiate_unify   ue
            | (|||||oe) => instantiate_observe oe
            | (e|)
            | (|e|)
            | (||e|)
            | (||||e|) => @liftState exp_state _ (itree _) _ (trigger e)
            end) m.

CoFixpoint match_event {T R} (e0 : testerE R) (r : R) (m : itree stE T)
  : itree stE T :=
  match observe m with
  | RetF x  => Ret x
  | TauF m' => Tau (match_event e0 r m')
  | VisF e k =>
    match e with
    | (||||oe) =>
      match oe in testerE Y, e0 in testerE R return (Y -> _) -> R -> _ with
      | Tester__Send _ _, Tester__Send _ _
      | Tester__Recv    , Tester__Recv => id
      | _, _ => fun _ _ => throw "Unexpected event"
      end k r
    | _ => vis e (match_event e0 r ∘ k)
    end
  end.

Definition match_observe {T R} (e : testerE T) (r : T) (l : list (itree stE R))
  : list (itree stE R) := map (match_event e r) l.

Variant genE : Type -> Type :=
  Gen : server_state exp -> exp_state -> genE (packetT id).

Variant clientE : Type -> Type :=
| Client__Recv : clientE (option (packetT id))
| Client__Send : packetT id -> clientE unit.

Class Is__tE E `{failureE -< E} `{nondetE -< E}
      `{genE -< E} `{logE -< E} `{clientE -< E}.
Notation tE := (failureE +' nondetE +' genE +' logE +' clientE).
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
    | (|ne|) =>
      match ne in nondetE Y return (Y -> _) -> _ with
      | Or => fun k => b <- trigger Or;; Tau (backtrack' others (k b))
      end k
    | (||de|) =>
      match de in decideE Y return (Y -> _) -> _ with
      | Decide => fun k => b <- trigger Or;;
                       Tau (backtrack' (k (negb b) :: others) (k b))
      end k
    | (|||le|) =>
      match le in logE Y return (Y -> _) -> _ with
      | Log str =>
        fun k => embed Log ("Observer: " ++ str);;
              Tau (backtrack' others (k tt))
      end k
    | (||||te) =>
      match te in testerE Y return (Y -> _) -> _ with
      | Tester__Send st es =>
        fun k => pkt <- embed Gen st es;;
              embed Client__Send pkt;;
              Tau (backtrack' (match_observe (Tester__Send st es) pkt others)
                              (k pkt))
      | Tester__Recv =>
        fun k => opkt <- trigger Client__Recv;;
              match opkt with
              | Some pkt =>
                Tau (backtrack' (match_observe Tester__Recv pkt others) (k pkt))
              | None =>
                match others with
                | []              => Tau (backtrack' [] m)
                | other :: others' => Tau (backtrack' (others' ++ [m]) other)
                end
              end
      end k
    end
  end.

Definition backtrack {E R} `{Is__tE E} : itree stE R -> itree E R :=
  backtrack' [].

Definition tester {E R} `{Is__tE E} (mo : itree oE R) :=
  backtrack $ snd <$> unifier mo (0, [], []).
