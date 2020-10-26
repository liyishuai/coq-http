From HTTP Require Import
     Parser
     Printer.

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
