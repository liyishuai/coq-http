From HTTP Require Import
     Codec
     Gen
     Semantics.

Goal parse parseRequest ("GET /pub/WWW/TheProject.html HTTP/1.8"
                           ++ CRLF ++ "Host: www.google.com"
                           ++ CRLF ++ "User-agent: Coq"
                           ++ CRLF ++ CRLF ++ "message")
     = inr (Request
              (RequestLine Method__GET
                    (RequestTarget__Origin "pub/WWW/TheProject.html" None)
                    (Version 1 8))
              [Field "Host" "www.google.com";
              Field "User-agent" "Coq"]
              None,
            "message").
Proof. reflexivity. Qed.

Goal parse parseRequest ("HEAD http://www.example.org/ HTTP/1.7"
                              ++ CRLF ++ "Content-Length: 2"
                              ++ CRLF ++ CRLF ++ "message")
     = inr (Request
              (RequestLine Method__HEAD
                  (RequestTarget__Absolute $ URI Scheme__HTTP
                                         (Authority None "www.example.org" None)
                                         "" None)
                  (Version 1 7))
              [Field "Content-Length" "2"]
              (Some "me"), "ssage").
Proof. reflexivity. Qed.

Goal parse parseResponse ("HTTP/1.1 404 Not Found"
                            ++ CRLF ++ CRLF)
     = inr (Response (Status (Version 1 1) 404 (Some "Not Found")) [] None, "").
Proof. reflexivity. Qed.

Definition parse_print_response
  : http_response id -> option string + http_response id * string :=
  parse parseResponse ∘ response_to_string.

Definition parse_print_response_spec (r : http_response id) : Prop :=
  parse_print_response r = inr (r, "").

Example response1 : http_response id :=
  Response (status_line_of_code 405)
           [Field "foo" "bar"] None.

Goal parse_print_response_spec response1.
Proof. reflexivity. Qed.

Example line1 : request_line :=
  RequestLine Method__GET (RequestTarget__Origin "index.html" None) (Version 1 1).

Open Scope jexp_scope.

Example xreq1 : jexp := xencode line1 + jkv "fields" host_localhost.
(* Compute xreq1. *)

Definition jreq1 : IR := jexp_to_IR_weak [] xreq1.
(* Compute jreq1. *)

(* Compute decode jreq1 : string + http_request id. *)
