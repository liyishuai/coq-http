From Ceres Require Export
     Ceres.
From ExtLib Require Export
     Extras
     Monad.
From ITree Require Export
     Nondeterminism
     ITree.
From HTTP Require Export
     Printer
     Parser.
Export
  FunNotation
  FunctorNotation
  MonadNotation.
Open Scope lazy_bool_scope.
Open Scope list_scope.
Open Scope monad_scope.
Open Scope program_scope.

Definition status_line_of_code (c : status_code) : status_line :=
  Status (Version 1 1) c (snd <$> find (N.eqb c ∘ fst) statusCodes).

Record resource_state {exp_} :=
  ResourceState {
      resource__body : exp_ message_body;
      resource__etag : option (exp_ field_value)
    }.
Arguments resource_state : clear implicits.
Arguments ResourceState {_}.

Definition server_state exp_ :=
  list (path * option (resource_state exp_)).

(** https://httpwg.org/http-core/draft-ietf-httpbis-semantics-latest.html#rfc.section.7.9.3.2 *)

Definition etag_match (weak : bool) (x y : field_value) : bool :=
  match x, y with
  | String "W" (String "/" s1), String "W" (String "/" s2)
  | String """" _ as s1       , String "W" (String "/" s2)
  | String "W" (String "/" s1), String """" _ as s2 =>
    weak &&& (s1 =? s2)
  | _, _ => x =? y
  end.

Notation var := N.

Inductive exp : Type -> Set :=
  Exp__Const : message_body -> exp message_body
| Exp__Body  : var -> exp message_body
| Exp__ETag  : var -> exp field_value
| Exp__Match : field_value -> exp field_value -> bool -> exp bool.

Fixpoint unwrap {T} (e : exp T) : T :=
  match e in exp T return T with
  | Exp__Const b => b
  | Exp__Body _
  | Exp__ETag _ => ""
  | Exp__Match f fx w => etag_match w f (unwrap fx)
  end.

Fixpoint exp_to_sexp {T} (e : exp T) : sexp :=
    match e with
    | Exp__Const s    => [Atom "Constant string"; to_sexp s]
    | Exp__Body  v    => [Atom "Message body"   ; to_sexp v]
    | Exp__ETag  v    => [Atom "Entity tag"     ; to_sexp v]
    | Exp__Match f fx w => [Atom "Match tag"; to_sexp f; exp_to_sexp fx; to_sexp w]
    end%sexp.

Instance Serialize__exp {T} : Serialize (exp T) :=
  exp_to_sexp.

Instance Serialize__resource : Serialize (resource_state exp) :=
  fun r =>
    let 'ResourceState b e := r in
    [Atom "Resource"; to_sexp b; to_sexp e]%sexp.

Notation clientT := nat.

Variant appE {exp_} : Type -> Type :=
  App__Recv : server_state exp_ -> appE (clientT * http_request id)
| App__Send : clientT -> http_response exp_ -> appE unit
| App__Forward  : authority -> http_request id -> appE clientT
| App__Backward : server_state exp_ -> clientT -> appE (http_response id).
Arguments appE : clear implicits.

Variant logE : Type -> Set :=
  Log : string -> logE unit.

Variant symE {exp_} : Type -> Type :=
  Sym__NewBody : symE (exp_ message_body)
| Sym__NewETag : symE (exp_ field_value)
| Sym__Decide  : exp_ bool -> symE bool.
Arguments symE : clear implicits.

Class Is__smE E `{appE exp -< E} `{nondetE -< E} `{logE -< E} `{symE exp -< E}.
Notation smE := (appE exp +' nondetE +' logE +' symE exp).
Instance smE_Is__smE : Is__smE smE. Defined.

Definition iter_forever {E : Type -> Type} {A : Type} (f : A -> itree E A)
  : A -> itree E void :=
  ITree.iter (fun a => inl <$> f a).

Section HTTP_SMI.

Context {E} `{Is__smE E}.

Section AfterConn.

Context (c : clientT).

Definition send_code (sc : status_code) (fs : list (field_line exp))
                     (b : option (exp message_body)) : itree E unit :=
  trigger (App__Send c (Response (status_line_of_code sc) fs b)).


Definition ok (ot : option (exp field_value)) (m : exp message_body) :=
     (t <- match ot with
          | Some t => ret t
          | None => embed (@Sym__NewETag exp)
          end;;
      send_code 200 [Field "ETag" t] (Some m);;
      ret (Some t)).

Definition created' (mx : option (exp message_body)) : itree E unit :=
  send_code 201 [] mx.

Definition created : itree E unit :=
  or (created' None)
     (mx <- embed (@Sym__NewBody exp);;
      created' (Some mx)).

Definition no_content : itree E unit :=
  send_code 204 [] None.

Definition not_modified : itree E unit :=
  send_code 304 [] None.

Definition bad_request : itree E unit := send_code 400 [] None.
Definition not_found : itree E unit :=
  or (send_code 404 [] None)
     (mx <- embed (@Sym__NewBody exp);;
      send_code 404 [] (Some mx)).

Definition precondition_failed : itree E unit :=
  or (send_code 412 [] None)
     (mx <- embed (@Sym__NewBody exp);;
      send_code 412 [] (Some mx)).

Section LoopBody.

Context (st : server_state exp) (methd : request_method) (t : request_target)
   (hs : list (field_line id)) (om : option message_body).

Section Localhost.

Context (p : path).

Definition http_smi_get_body'
  : Monads.stateT (server_state exp) (itree E) unit :=
  fun st =>
  (* embed Log ("State before GET: " ++ to_string st);; *)
  match get p st with
  | Some (Some (ResourceState m ot)) =>
    ot' <- ok ot m;;
    ret (update p (Some (ResourceState m ot')) st, tt)
  | Some None =>
    (* embed Log (p ++ " is known as not found");; *)
    not_found;; ret (st, tt)
  | None =>
    (* embed Log (p ++ " is unknown");; *)
    or (not_found;; ret (update p None st, tt))
       (mx <- embed (@Sym__NewBody exp);;
        ot <- ok None mx;;
        ret (update p (Some (ResourceState mx ot)) st, tt))
  end.

(* PUT or POST *)
Definition http_smi_put_body'
  : Monads.stateT (server_state exp) (itree E) unit :=
  fun st =>
  match om with
  | Some m =>
    match get p st with
    | Some (Some _) => no_content
    | Some None     => created
    | None          => or created no_content
    end;;
    ot <- Some <$> embed (@Sym__NewETag exp);;
    ret (update p (Some (ResourceState (Exp__Const m) ot)) st, tt)
  | None => bad_request;; ret (st, tt)
  end.

Definition getResource
  : Monads.stateT (server_state exp) (itree E) (option (resource_state exp)) :=
  fun st =>
    match get p st with
    | Some r => ret (st, r)
    | None =>
      r <- or (ret None)
             (Some <$>
                   liftA2 ResourceState (embed (@Sym__NewBody exp))
                       (Some <$> embed (@Sym__NewETag exp)));;
      ret (update p r st, r)
    end.

Section Precondition.

Context (m : Monads.stateT (server_state exp) (itree E) unit).

(** https://httpwg.org/http-core/draft-ietf-httpbis-semantics-latest.html#rfc.section.12.1.1 *)
Definition if_match : Monads.stateT (server_state exp) (itree E) unit :=
  let accept s := m s in
  let reject s := precondition_failed;; ret (s, tt) in
  fun st =>
  match findField "If-Match" hs with
  | Some v =>
    if v =? "*"
    then
      '(st', r) <- getResource st;;
      match r with
      | Some _ => accept st'
      | None   => reject st'
      end
    else
      match parse (parseCSV parseEntityTag) v with
      | inl _ => bad_request;; ret (st, tt)
      | inr (ts, _) =>
        '(st', r) <- getResource st;;
        (* embed Log ("Evaluating If-Match " *)
        (*              ++ to_string ts ++ " against state " *)
        (*              ++ to_string st')%string;; *)
        match resource__etag <$> r with
        | Some (Some tx) =>
          b <- fold_left
                (fun mb t =>
                   b <- mb;;
                   if b : bool
                   then ret true
                   else embed (@Sym__Decide exp) (Exp__Match t tx false))
                ts (ret false);;
          if b
          then accept st'
          else reject st'
        | Some None | None => reject st'
        end
      end
  | None => accept st
  end.

(** https://httpwg.org/http-core/draft-ietf-httpbis-semantics-latest.html#rfc.section.12.1.2 *)
Definition if_none_match : Monads.stateT (server_state exp) (itree E) unit :=
  let accept s := m s in
  let reject s :=
      match methd with
      | Method__GET | Method__HEAD => not_modified
      | _                      => precondition_failed
      end;; ret (s, tt) in
  fun st =>
    match findField "If-None-Match" hs with
    | Some v =>
      if v =? "*"
      then
        '(st', r) <- getResource st;;
        match r with
        | Some _ => reject st'
        | None   => accept st'
        end
      else
        match parse (parseCSV parseEntityTag) v with
        | inl _ => bad_request;; ret (st, tt)
        | inr (ts, _) =>
          '(st', r) <- getResource st;;
          match resource__etag <$> r with
          | Some (Some tx) =>
            b <- fold_left
                  (fun mb t =>
                     b <- mb;;
                     if b : bool
                     then ret true
                     else embed (@Sym__Decide exp) (Exp__Match t tx true))
                  ts (ret false);;
          if b
          then reject st'
          else accept st'
          | Some None | None => accept st'
          end
        end
    | None => accept st
    end.

End Precondition.

Definition http_smi_get_body : Monads.stateT (server_state exp) (itree E) unit
  := if_match $ if_none_match http_smi_get_body'.

Definition http_smi_put_body : Monads.stateT (server_state exp) (itree E) unit
  := if_match $ if_none_match http_smi_put_body'.

End Localhost.

Section Proxy.

Context (u : absolute_uri).

Definition removeField (n : field_name) : list (field_line id) :=
  filter (fun f => negb $ fold (String ∘ tolower) "" (field__name f) =?
                fold (String ∘ tolower) "" n) hs.

Definition updateField (n : field_name) (v : field_value) : list (field_line id)
  := Field n v :: removeField n.

Definition forward_request : itree E (http_response id) :=
  let 'URI s (Authority ou h op as a) p oq := u in
  let req : http_request id :=
      Request (RequestLine methd
                           (RequestTarget__Origin p oq)
                           (Version 1 1))
              (updateField "Host" $ to_string a) om in
  embed App__Forward a req >>= embed App__Backward st.

End Proxy.

Definition target_uri : option absolute_uri :=
  let mh : option authority :=
      match findField "Host" hs with
      | Some a =>
        match parse parseAuthority a with
        | inl _      => None
        | inr (Authority ou h op, _) =>
          let h' := if h =? "localhost" then "127.0.0.1" else h in
          let op' := Some $ match op with
                            | Some p' => p'
                            | None    => 80
                            end in
          Some (Authority ou h' op')
        end%string
      | None   => Some $ Authority None "127.0.0.1" (Some 80)
      end in
  match t with
  | RequestTarget__Absolute u =>
    let 'URI s (Authority ou h op) p oq := u in
    let h' := if h =? "localhost" then "127.0.0.1" else h in
    let op' := Some $ match op with
                      | Some p' => p'
                      | None    => 80
                      end in
    ret $ URI s (Authority ou h' op') p oq
  | RequestTarget__Authority a => ret $ URI Scheme__HTTP a "" None
  | RequestTarget__Origin  p q => h <- mh;; ret (URI Scheme__HTTP h p q)
  | RequestTarget__Asterisk    => h <- mh;; ret (URI Scheme__HTTP h "" None)
  end.

Definition wrap_field (f : field_line id) : field_line exp :=
  let 'Field n v := f in Field n (Exp__Const v).

Definition unwrap_field (f : field_line exp) : field_line id :=
  let 'Field n v := f in Field n (unwrap v).

Definition wrap_response (r : http_response id) : http_response exp :=
  let 'Response l f ob := r in
  Response l (map wrap_field f) (Exp__Const <$> (ob : option message_body)).

Definition unwrap_response (r : http_response exp) : http_response id :=
  let 'Response l f ob := r in
  Response l (map unwrap_field f) (unwrap <$> ob : option message_body).

Definition server_port : N := 80.

Definition http_smi_body : itree E (server_state exp) :=
  match target_uri with
  | Some u =>
    let 'URI s (Authority ou h op as a) p oq := u in
    if (h =? "127.0.0.1") &&& (op = Some server_port?)
    then
      match methd with
      | Method__GET =>
        fst <$> http_smi_get_body p st
      | Method__PUT
      | Method__POST =>
        fst <$> http_smi_put_body p st
      | _ =>
        send_code 405 [] None;; ret st
      end
    else
      forward_request u >>= embed App__Send c ∘ wrap_response;;
      ret st
  | None => bad_request;; ret st
  end.

End LoopBody.
End AfterConn.

Definition http_smi : itree E void :=
  iter_forever (fun st : server_state exp =>
    '(c, Request (RequestLine methd t _) hs om) <- embed App__Recv st;;
    http_smi_body c st methd t hs om) [].

End HTTP_SMI.
