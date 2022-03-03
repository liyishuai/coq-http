From HTTP Require Export
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

Variant clientE {packetT gen_state : Type} : Type -> Type :=
  Client__Recv : clientE (option packetT)
| Client__Send : gen_state -> clientE (option packetT).

Definition labelT := nat.
Definition scriptT {symreqT : Type} := list (labelT * symreqT).
Definition traceT   packetT         := list (labelT * packetT).

Module Type IShrinkSIG.

Parameters requestT responseT : Type.
Notation payloadT := (requestT + responseT)%type.

Parameter connT      : Type.
Parameter Conn__Server : connT.
#[global]
Declare Instance Serialize__connT : Serialize connT.
#[global]
Declare Instance Dec_Eq__connT : Dec_Eq connT.

Parameter packetT : Type.
Parameter Packet : connT -> connT -> payloadT -> packetT.
Parameter packet__payload       : packetT -> payloadT.
Parameter packet__src packet__dst : packetT -> connT.
#[global]
Declare Instance Serialize__packetT : Serialize packetT.

(** Model state exposed for request generation purposes. *)
Parameter gen_state : Type.

Notation failureE := (exceptE string).

(** Events other than [clientE] and [failureE]. *)
Parameter otherE : Type -> Type.
Parameter other_handler : otherE ~> IO.
Arguments other_handler {_}.
Notation tE := (failureE +' @clientE packetT gen_state +' otherE).

Parameter conn_state    : Type.
Parameter init_state    : conn_state.
Parameter recv_response : Monads.stateT conn_state IO (option packetT).
Parameter send_request  : requestT -> Monads.stateT conn_state IO (option connT).
Parameter cleanup : conn_state -> IO unit.

(** Symbolic request type, for scripting purposes. *)
Parameter symreqT : Type.
#[global]
Declare Instance Shrink__symreqT    : Shrink symreqT.
#[global]
Declare Instance Serialize__symreqT : Serialize symreqT.

Parameter instantiate_request : traceT packetT -> symreqT -> requestT.
Parameter gen_request : gen_state -> traceT packetT -> IO symreqT.

Parameter tester_state : Type.
Parameter tester_init  : IO tester_state.
Parameter tester : tester_state -> itree tE void.

End IShrinkSIG.

Module IShrink (M : IShrinkSIG).
Include M.

Fixpoint repeat_list {A} (n : nat) (l : list A) : list A :=
  match n with
  | O    => []
  | S n' => l ++ repeat_list n' l
  end.

Definition shrink_execute' (exec : scriptT -> IO (bool * traceT packetT))
           (init : scriptT) : IO (option scriptT) :=
  prerr_endline "===== initial script =====";;
  prerr_endline (to_string init);;
  IO.fix_io
    (fun shrink_rec ss =>
       match ss with
       | [] => prerr_endline "<<<<< shrink exhausted >>>>";; ret None
       | sc :: ss' =>
         prerr_endline "<<<<< current script >>>>>>";;
         prerr_endline (to_string sc);;
         '(b, tr) <- exec sc;;
         if b : bool
         then prerr_endline "===== accepting trace =====";;
              prerr_endline (to_string tr);;
              shrink_rec ss'
         else prerr_endline "===== rejecting trace =====";;
              prerr_endline (to_string tr);;
              prerr_endline "<<<<< shrink ended >>>>>>>>";;
              ret (Some sc)
       end) (repeat_list 20 $ shrink init).

Definition shrink_execute (first_exec : IO (bool * (scriptT * traceT packetT)))
           (then_exec : scriptT -> IO (bool * traceT packetT)) : IO bool :=
  '(b, (sc, tr)) <- first_exec;;
  if b : bool
  then ret true
  else prerr_endline "<<<<< rejecting trace >>>>>";;
       prerr_endline (to_string tr);;
       IO.while_loop (shrink_execute' then_exec) sc;;
       ret false.

Fixpoint execute' {R} (fuel : nat) (s : conn_state)
         (oscript : option scriptT) (acc : scriptT * traceT packetT) (m : itree tE R)
  : IO (bool * conn_state * (scriptT * traceT packetT)) :=
  let (script0, trace0) := acc in
  match fuel with
  | O => ret (true, s, acc)
  | S fuel =>
    match observe m with
    | RetF _ => ret (true, s, acc)
    | TauF m' => execute' fuel s oscript acc m'
    | VisF e k =>
      match e with
      | (Throw err|) =>
        prerr_endline err;;
        ret (false, s, acc)
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
                  let req : requestT := instantiate_request trace0 rx in
                  '(s', oc) <- send_request req s;;
                  if oc is Some c
                  then let pkt : packetT := Packet c Conn__Server (inl req) in
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

Set Warnings "-abstract-large-number".
Definition execute {R} (m : tester_state -> itree tE R) (oscript : option scriptT)
  : IO (bool * (scriptT * traceT packetT)) :=
  tester_init_state <- tester_init;;
  '(b, s, t') <- execute' 1000000 init_state oscript ([], []) (m tester_init_state);;
  cleanup s;;
  ret (b, t').
(* end hide *)

(** ** From client ITree to shrink-testing program *)

Definition test : IO bool :=
  shrink_execute (execute tester None)
                 (fmap (fun '(b, (_, t)) => (b, t)) ∘ execute tester ∘ Some).

End IShrink.
