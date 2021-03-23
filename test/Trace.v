From HTTP Require Import
     Execute.

Import HttpTypes.

Definition getline (p : path) : request_line :=
  RequestLine Method__GET (RequestTarget__Origin p None) (Version 1 1).
Definition okline : status_line :=
  Status (Version 1 1) 200 (Some "OK").

Definition not_modified {exp_} : http_response exp_ :=
  Response (Status (Version 1 1) 304 (Some "Not Modified"))
           [] None.

Open Scope nat_scope.

Fail Example request0 : symreqT :=
  Request (getline "index.html") [] None.

Example request1 : symreqT :=
  Request (getline "index.html")
          [Field "If-None-Match" (Texp__Var O)] None.

(** An initial execution might produce [init_script] and [init_trace]: *)
Example init_script : scriptT :=
  [(0, request0);
   (1, request0);
   (2, request1)].
Example init_trace : traceT :=
  [(0, Packet (Conn__User 0) Conn__Server $ inl $
              Request (getline "index.html") [] None);
   (0, Packet Conn__Server (Conn__User 0) $ inr $
              Response okline
              [Field "ETag" """tag-foo""";
               Field "Content-Length" "12"]
              (Some "hello, world"));
   (1, Packet (Conn__User 1) Conn__Server $ inl $
              Request (getline "index.html") [] None);
   (1, Packet Conn__Server (Conn__User 1) $ inr $
              Response okline
              [Field "ETag" """tag-foo""";
               Field "Content-Length" "12"]
              (Some "hello, world"));
   (2, Packet (Conn__User 2) Conn__Server $ inl $
              Request (getline "index.html")
              [Field "If-None-Match" """tag-foo"""] None);
   (2, Packet Conn__Server (Conn__User 2) $ inr not_modified)].

(** A script shrunk from [init_script]: *)
Example shrunk_script : scriptT :=
  [(0, request0);
   (2, request1)].

(** Trace before executing the second request in the shrunk script: *)
Example runtime_trace : traceT :=
  [(0, Packet (Conn__User 0) Conn__Server $ inl $
              Request (getline "index.html") [] None);
   (0, Packet Conn__Server (Conn__User 0) $ inr $
              Response okline
              [Field "ETag" """tag-bar""";
               Field "Content-Length" "5"]
              (Some "world"))].

(** Based on this runtime trace, we can instantiate the next request to be sent
    to the server: *)
Goal instantiate_request runtime_trace request1 =
     Request (getline "index.html")
             [Field "If-None-Match" """tag-bar"""] None.
Proof. reflexivity. Qed.
