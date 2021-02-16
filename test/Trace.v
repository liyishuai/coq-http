From HTTP Require Import
     TesterSpec.

Definition tester_send {E} `{testerE -< E} : itree E (packetT id) :=
  embed Tester__Send [] Conn__Server (0, [], []).

Definition tester_recv {E} `{testerE -< E} : itree E (packetT id) :=
  trigger Tester__Recv.

Definition same_status_code (p0 p1 : payloadT id) : bool :=
  match p0, p1 with
  | inr (Response (Status _ c0 _) _ _), inr (Response (Status _ c1 _) _ _) =>
    c0 =? c1
  | _, _ => false
  end%N.

Definition echo0 : itree stE void :=
  ITree.forever
    ('(Packet s0 d0 p0) <- tester_send;;
     '(Packet s1 d1 p1) <- tester_recv;;
     if (d1 = s0?) &&& (s1 = d0?) &&& same_status_code p0 p1
     then ret tt
     else throw "Message mismatch").

Definition payload (sc : status_code) : payloadT id :=
  inr $ Response (status_line_of_code sc) [] None.

Definition trace0 : list traceT :=
  [Trace__Out $ Packet (Conn__User 0) Conn__Server $ payload 0;
   Trace__In  $ Packet Conn__Server (Conn__User 0) $ payload 0].

Goal is_trace echo0 trace0 = true.
Proof. reflexivity. Qed.

Goal accepts (backtrack echo0) trace0 = true.
Proof. reflexivity. Qed.

Definition trace1 : list traceT :=
  [Trace__Out $ Packet (Conn__User 0) Conn__Server $ payload 0;
   Trace__Out $ Packet (Conn__User 1) Conn__Server $ payload 1;
   Trace__In  $ Packet Conn__Server (Conn__User 0) $ payload 0;
   Trace__In  $ Packet Conn__Server (Conn__User 1) $ payload 1].

Goal is_trace echo0 trace1 = false.
Proof. reflexivity. Qed.

Definition echo1 : itree stE void :=
  (rec-fix loop l :=
     b <- trigger Decide;;
     if b : bool
     then
       pkt <- tester_send;;
       call (pkt :: l)
     else
       pkt <- tester_recv;;
       let '(Packet s1 d1 p1) := pkt in
       match pick (fun pkt0 =>
                     let 'Packet s0 d0 p0 := pkt0 in
                     (d1 = s0?)
                       &&& (s1 = d0?)
                       &&& same_status_code p0 p1) l with
       | Some (_, l') => call l'
       | None => throw $ to_string pkt ++ " not found in:" ++ CRLF ++ list_to_string l
       end) [].

Goal is_trace echo1 trace0 = true.
Proof. reflexivity. Qed.

Goal accepts (backtrack echo1) trace0 = true.
Proof. reflexivity. Qed.

Goal is_trace echo1 trace1 = true.
Proof. reflexivity. Qed.

Goal accepts (backtrack echo1) trace1 = true.
Proof. reflexivity. Qed.

Definition trace2 : list traceT :=
  [Trace__Out $ Packet (Conn__User 0) Conn__Server $ payload 0;
   Trace__Out $ Packet (Conn__User 1) Conn__Server $ payload 1;
   Trace__In  $ Packet Conn__Server (Conn__User 0) $ payload 1;
   Trace__In  $ Packet Conn__Server (Conn__User 1) $ payload 0].

Goal is_trace echo1 trace2 = false.
Proof. reflexivity. Qed.

Goal accepts (backtrack echo1) trace2 = false.
Proof. reflexivity. Qed.
