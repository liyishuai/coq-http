From IShrink Require Export
     Common.
From SimpleIO Require Export
     SimpleIO.
From ITree Require Export
     Exception
     Nondeterminism
     ITree.
From Ceres Require Export
     Ceres.
From ExtLib Require Export
     Extras.
Export
  FunNotation
  FunctorNotation
  MonadNotation
  SumNotations.
Open Scope sum_scope.
Open Scope string_scope.
Open Scope list_scope.

Section IShrink.

(** ** Scripting Language *)
Variable expT               : Type -> Type.
Variable requestT responseT : (Set -> Type) -> Type.
Context `{Shrink (requestT expT)}.
Context `{Serialize (requestT expT)} `{Serialize (responseT id)}.

Definition payloadT exp_ : Type := requestT id + responseT exp_.

Variable connT      : Type.
Variable Conn__Server : connT.
Context `{Serialize connT}.
Context `{Dec_Eq    connT}.

Record packetT {exp_} :=
  Packet {
      packet__src : connT;
      packet__dst : connT;
      packet__payload : payloadT exp_
    }.
Arguments Packet {_}.

Notation pktT := (@packetT id).
Context `{Serialize pktT}.

Definition labelT := nat.

Definition scriptT := list (labelT * requestT expT).
Definition traceT  := list (labelT * pktT).

Fixpoint repeat_list {A} (n : nat) (l : list A) : list A :=
  match n with
  | O    => []
  | S n' => l ++ repeat_list n' l
  end.

Definition shrink_execute' (exec : scriptT -> IO (bool * traceT))
           (init : scriptT) : IO (option scriptT) :=
  prerr_endline "<<<<< initial script >>>>>";;
  prerr_endline (to_string init);;
  IO.fix_io
    (fun shrink_rec ss =>
       match ss with
       | [] => prerr_endline "<<<<< shrink exhausted >>>>";; ret None
       | sc :: ss' =>
         '(b, tr) <- exec sc;;
         if b : bool
         then prerr_endline "<<<<< accepting trace >>>>>";;
              prerr_endline (to_string tr);;
              shrink_rec ss'
         else prerr_endline "<<<<< rejecting trace >>>>>";;
              prerr_endline (to_string tr);;
              prerr_endline "<<<<< shrink ended >>>>>>>>";;
              ret (Some sc)
       end) (repeat_list 20 $ shrink init).

Definition shrink_execute (first_exec : IO (bool * (scriptT * traceT)))
           (then_exec : scriptT -> IO (bool * traceT)) : IO bool :=
  '(b, (sc, _)) <- first_exec;;
  if b : bool
  then ret true
  else IO.while_loop (shrink_execute' then_exec) sc;;
       ret false.

(** ** Testing Language *)

Variable gen_state : Type.

Variant clientE : Type -> Type :=
  Client__Recv : clientE (option pktT)
| Client__Send : gen_state -> clientE (option pktT).

Variable otherE : Type -> Type.
Variable other_handler : otherE ~> IO.
Arguments other_handler {_}.

Definition failureE := (exceptE string).
Notation tE := (failureE +' clientE +' otherE).

Variable instantiate_request : traceT -> requestT expT -> requestT id.
Variable gen_request   : gen_state -> traceT -> IO (requestT expT).
Variable conn_state    : Type.
Variable init_state    : conn_state.
Variable recv_response : Monads.stateT conn_state IO (option pktT).
Variable send_request  :
  requestT id -> Monads.stateT conn_state IO (option connT).

Fixpoint execute' {R} (fuel : nat) (s : conn_state)
         (oscript : option scriptT) (acc : scriptT * traceT) (m : itree tE R)
  : IO (bool * conn_state * (scriptT * traceT)) :=
  let (script0, trace0) := acc in
  match fuel with
  | O => ret (true, s, acc)
  | S fuel =>
    match observe m with
    | RetF _ => ret (true, s, acc)
    | TauF m' => execute' fuel s oscript acc m'
    | VisF e k =>
      match e with
      | (Throw err|) => ret (false, s, acc)
      | (|ce|) =>
        match ce in clientE Y return (Y -> _) -> _ with
        | Client__Recv =>
          fun k => '(s', op) <- recv_response s;;
                let acc' :=
                    match op with
                    | Some p =>
                      let dst : connT := packet__dst p in
                      let lreqs :=
                          filter (fun lpkt => packet__src (snd lpkt) = dst?)
                                 trace0 in
                      let prevs :=
                          length (filter (fun lpkt => packet__dst (snd lpkt) = dst?)
                                         trace0) in
                      let label := nth prevs (map fst lreqs) O in
                      (script0, trace0 ++ [(label, p)])
                    | None => acc
                    end in
                execute' fuel s' oscript acc' (k op)
        | Client__Send gs =>
          fun k => '(ostep, osc') <-
                match oscript with
                | Some [] => ret (None, Some [])
                | Some (sc :: script') =>
                  ret (Some sc, Some script')
                | None =>
                  let freshVar : nat :=
                      S $ fold_left Nat.max (map fst script0) O in
                  step <- pair freshVar <$> gen_request gs trace0;;
                         ret (Some step, None)
                end;;
                match ostep with
                | Some ((n, rx) as step) =>
                  let req : requestT id := instantiate_request trace0 rx in
                  '(s', oc) <- send_request req s;;
                  if oc is Some c
                  then let pkt : pktT := Packet c Conn__Server (inl req) in
                       execute' fuel s' osc'
                                (script0 ++ [step], trace0 ++ [(n, pkt)])
                                (k (Some pkt))
                  else execute' fuel s' osc' acc (k None)
                | None => execute' fuel s osc' acc (k None)
                end
        end k
      | (||oe) => other_handler oe >>= execute' fuel s oscript acc ∘ k
      end
    end
  end.

Variable cleanup : conn_state -> IO unit.

Definition execute {R} (m : itree tE R) (oscript : option scriptT)
  : IO (bool * (scriptT * traceT)) :=
  '(b, s, t') <- execute' 5000 init_state oscript ([], []) m;;
  cleanup s;;
  ret (b, t').

Definition test {R} (m : itree tE R) : IO bool :=
  shrink_execute (execute m None)
                 (fmap (fun '(b, (_, t)) => (b, t)) ∘ execute m ∘ Some).

End IShrink.

Arguments packetT : clear implicits.
Arguments Packet        {_ _ _ _}.
Arguments packet__src     {_ _ _ _}.
Arguments packet__dst     {_ _ _ _}.
Arguments packet__payload {_ _ _ _}.