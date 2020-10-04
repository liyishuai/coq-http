From Ceres Require Export
     Ceres.
From ExtLib Require Export
     Extras
     Monad.
From ITree Require Export
     Nondeterminism
     ITree.
From HTTP Require Export
     Message
     Common.
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

Record resource_state exp_ :=
  ResourceState {
      resource__body : exp_ message_body;
      resource__etag : option (exp_ field_value)
    }.
Arguments ResourceState {_}.

Definition server_state exp_ := list (path * option (resource_state exp_)).

Notation var := N.

Inductive exp : Type -> Set :=
  Exp__Const : message_body -> exp message_body
| Exp__Body  : var -> exp message_body
| Exp__ETag  : var -> exp field_value
| Exp__Match : field_value -> exp field_value -> exp bool.

Fixpoint exp_to_sexp {T} (e : exp T) : sexp :=
    match e with
    | Exp__Const s    => [Atom "Constant string"; to_sexp s]
    | Exp__Body  v    => [Atom "Message body"   ; to_sexp v]
    | Exp__ETag  v    => [Atom "Entity tag"     ; to_sexp v]
    | Exp__Match f fx => [Atom "Match tag"; to_sexp f; exp_to_sexp fx]
    end%sexp.

Instance Serialize__exp {T} : Serialize (exp T) :=
  exp_to_sexp.

Instance Serialize__resource : Serialize (resource_state exp) :=
  fun r =>
    let 'ResourceState b e := r in
    [Atom "Resource"; to_sexp b; to_sexp e]%sexp.

Notation connT := nat.

Variant appE {exp_} : Type -> Type :=
  App__Recv : server_state exp_ -> appE (connT * http_request)
| App__Send : connT -> http_response exp_ -> appE unit.
Arguments appE : clear implicits.

Variant logE : Type -> Set :=
  Log : string -> logE unit.

Variant symE {exp_} : Type -> Set :=
  Sym__NewBody : symE (exp_ message_body)
| Sym__NewETag : symE (exp_ field_value).
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

Context (c : connT).

Definition send_code (sc : status_code) (fs : list (field_line exp))
                     (b : option (exp message_body)) : itree E unit :=
  trigger (App__Send c (Response (status_line_of_code sc) [] b)).


Definition ok (ot : option (exp field_value)) (m : exp message_body) :=
  or (send_code 200 [] (Some m);; ret None)
     (t <- match ot with
          | Some t => ret t
          | None => embed (@Sym__NewETag exp)
          end;;
      send_code 200 [Field "ETag" t] (Some m);;
      ret (Some t)).

Definition created' (mx : option (exp message_body)) : itree E (option (exp field_value)) :=
(* or (t <- watvalue <$> embed (@Sym__NewETag exp);; *)
(*     send_code 201 [Field "ETag" t] None;; *)
(*     ret (Some t)) *)
  (send_code 201 [] None;; ret None).

Definition created : itree E (option (exp field_value)) :=
(* or (created' None) *)
  (mx <- embed (@Sym__NewBody exp);;
   created' (Some mx)).

Definition no_content : itree E (option (exp field_value)) :=
  or (send_code 204 [] None;; ret None)
     (t <- trigger (@Sym__NewETag exp);;
      send_code 204 [Field "ETag" t] None;;
      ret (Some t)).

Definition bad_request : itree E unit := send_code 400 [] None.
Definition not_found : itree E unit :=
  or (send_code 404 [] None)
     (mx <- embed (@Sym__NewBody exp);;
      send_code 404 [] (Some mx)).

Section LoopBody.

Context (st : server_state exp) (methd : request_method) (t : request_target)
   (om : option message_body).

Section TargetAbsolute.

Context (p : path).

Definition http_smi_get_body : itree E (server_state exp) :=
  (* embed Log ("State before GET: " ++ to_string st);; *)
  match get p st with
  | Some (Some (ResourceState m ot)) =>
    ot' <- ok ot m;;
    ret (update p (Some (ResourceState m ot')) st)
  | Some None =>
    (* embed Log (p ++ " is known as not found");; *)
    not_found;; ret st
  | None =>
    (* embed Log (p ++ " is unknown");; *)
    or (not_found;; ret (update p None st))
       (mx <- embed (@Sym__NewBody exp);;
        ot <- ok None mx;;
        ret (update p (Some (ResourceState mx ot)) st))
  end.

(* PUT or POST *)
Definition http_smi_put_body : itree E (server_state exp) :=
  match om with
  | Some m =>
    (* embed Log ("State before PUT: " ++ to_string st);; *)
    ot <-
    match get p st with
    | Some (Some _) => no_content
    | Some None     => created
    | None          => or created no_content
    end;;
    ret (update p (Some (ResourceState (Exp__Const m) ot)) st)
  | None => bad_request;; ret st
  end.

End TargetAbsolute.

Definition http_smi_body : itree E (server_state exp) :=
  match t with
  | RequestTarget__Origin p _
  | RequestTarget__Absolute _ _ p _ =>
    match methd with
    | Method__GET => http_smi_get_body p
    | Method__PUT
    | Method__POST => http_smi_put_body p
    | _ =>
      send_code 405 [] None;; ret st
    end
  | _ => bad_request;; ret st
  end.

End LoopBody.
End AfterConn.

Definition http_smi : itree E void :=
  iter_forever (fun st : server_state exp =>
    '(c, Request (RequestLine methd t _) hs om) <- embed App__Recv st;;
    http_smi_body c st methd t om) [].

End HTTP_SMI.
