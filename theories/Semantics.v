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

Notation connT := nat.

Variant appE {exp_} : Type -> Type :=
  App__Recv : server_state exp_ -> appE (connT * http_request)
| App__Send : connT -> http_response exp_ -> appE unit.
Arguments appE : clear implicits.

Variant symE {exp_} : Type -> Set :=
  Sym__NewBody : symE (exp_ message_body)
| Sym__NewETag : symE (exp_ field_value).
Arguments symE : clear implicits.

Class Is__smE E `{appE exp -< E} `{nondetE -< E} `{symE exp -< E}.
Notation smE := (appE exp +' nondetE +' symE exp).
Instance smE_Is__smE : Is__smE smE. Defined.

Definition http_smi {E R} `{Is__smE E} : itree E R :=
  rec
    (fun st : server_state exp =>
       '(c, Request (RequestLine methd t _) hs om) <- embed App__Recv st;;
       let send_code (sc : status_code) (b : option (exp message_body)) :=
           trigger (App__Send c (Response (status_line_of_code sc) [] b)) in
       let ok (m : exp message_body)        := send_code 200 $ Some m in
       let created     := send_code 201 None     in
       let no_content  := send_code 204 None     in
       let bad_request := send_code 400 None     in
       let not_found   := send_code 404 None     in
       match t with
       | RequestTarget__Origin p _
       | RequestTarget__Absolute _ _ p _ =>
         match methd with
         | Method__GET =>
           match get p st with
           | Some (Some (ResourceState m _)) => ok m;; call st
           | Some None => not_found;; call st
           | None =>
             or (not_found;; call (update p None st))
                (mx <- embed (@Sym__NewBody exp);;
                 let mx' : exp message_body :=
                     match mx in exp message_body with
                     | Exp__Const b => Exp__Const b
                     | Exp__Body  v => Exp__Body v
                     | Exp__ETag  _
                     | Exp__Match _ _ => Exp__Const ""
                     end in     (* WAT *)
                 ok mx';;
                 call (update p (Some (ResourceState mx' None)) st))
           end
         | Method__PUT
         | Method__POST =>
           match om with
           | Some m =>
             match get p st with
             | Some (Some _) => no_content
             | Some None     => created
             | None          => or created no_content
             end;;
             call (update p (Some (ResourceState (Exp__Const m) None)) st)
           | None => bad_request;; call st
           end
         | _ =>
           send_code 405 None;; call st
         end
       | _ => bad_request;; call st
       end) [].
