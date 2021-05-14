From SimpleIO Require Export
     IO_Float
     IO_Random.
From HTTP Require Export
     Gen
     NetUnix
     Parser
     Tester.
From AsyncTest Require Export
     AsyncTest.
Open Scope string_scope.

Fixpoint findResponse (s : conn_state)
  : IO (conn_state * option packetT) :=
  match s with
  | [] => ret ([], None)
  | cfs :: t =>
    let '(c, (f, str)) := cfs in
    match parse parseJres str with
    | inl (Some err) =>
      failwith $ "Bad response " ++ to_string str ++ " received on connection "
               ++ to_string c ++ ", error message: " ++ err
    | inl None =>
      (* prerr_endline ("Incomplete response: " ++ str);; *)
      '(t', op) <- findResponse t;;
      ret (cfs :: t', op)
    | inr (r, str') =>
      (* curr <- OFloat.to_string <$> OUnix.gettimeofday;; *)
      (* prerr_endline curr;; *)
      (* prerr_endline ("==============RECEIVED==============" *)
      (*                  ++ to_string c ++ CRLF ++ response_to_string r);; *)
      ret ((c, (f, str')) :: t, Some (Packet Conn__Server (Conn__Client c) r))
    end
  end.

Definition recv_http_response : Monads.stateT conn_state IO (option Trace.packetT) :=
  recv_bytes;; findResponse.

Definition new_conn (tr : traceT) : clientT :=
  S $ fold_left (fun n p =>
                   let 'Packet src dst _ := p in
                   max n $
                       match src, dst with
                       | Conn__Client s, Conn__Client d => max s d
                       | Conn__Client x, _
                       | _, Conn__Client x => x
                       | _, _ => O
                       end) (map snd tr) O.

Definition gen_step (ss : server_state exp) (tr : traceT)
  : IO (clientT * jexp) :=
  pair (new_conn tr) <$> gen_request ss tr.

Definition http_tester {E} `{Is__tE E} : itree E void :=
  tester $ observer $ compose_switch tcp http_smi.

Definition or_handler : nondetE ~> IO :=
  fun _ e => let 'Or := e in ORandom.bool tt.

Definition other_handler : nondetE +' logE ~> IO :=
  fun _ e => match e with
          | (ne|) => or_handler _ ne
          | (|le) => let 'Log str := le in
                    prerr_endline str
          end.

Definition cleanup (s : conn_state) : IO unit :=
  fold_left (fun m fd => OUnix.close fd;; m)
            (map (fst ∘ snd) s) (ret tt).

Module HttpTypes : AsyncTestSIG.

Definition gen_state           := server_state exp.
Definition gen_step            := gen_step.

Definition otherE              := nondetE +' logE.
Definition other_handler       := other_handler.

Definition conn_state          := conn_state.
Definition init_state          := [] : conn_state.
Definition recv_response       := recv_http_response.
Definition send_request        := send_request.
Definition cleanup             := cleanup.

Definition tester_state        := unit.
Definition tester_init         := ret tt : IO tester_state.
Definition tester              := fun (_ : tester_state) => http_tester.

End HttpTypes.

Module TestHTTP := AsyncTest HttpTypes.

Definition test_http : IO bool :=
  TestHTTP.test.
