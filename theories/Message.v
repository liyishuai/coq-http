From Coq Require Export
     BinNat
     List
     String.
Export ListNotations.
Open Scope N_scope.
Open Scope string_scope.

(** https://httpwg.org/http-core/draft-ietf-httpbis-messaging-latest.html#request.method *)
(** https://httpwg.org/http-core/draft-ietf-httpbis-semantics-latest.html#methods *)
Variant request_method :=
  Method__GET
| Method__HEAD
| Method__POST
| Method__PUT
| Method__DELETE
| Method__CONNECT
| Method__OPTIONS
| Method__TRACE
| Method : string -> request_method.

(** https://www.rfc-editor.org/rfc/rfc3986.html#section-3.1 *)
(** https://httpwg.org/http-core/draft-ietf-httpbis-semantics-latest.html#resources *)
Variant http_scheme := Scheme__HTTP | Scheme__HTTPS.

(** https://www.rfc-editor.org/rfc/rfc3986.html#section-3.2 *)
Record authority :=
  Authority {
      authority__userinfo : option string;
      authority__host     : string;
      authority__port     : option N
    }.

(** https://www.rfc-editor.org/rfc/rfc3986.html#section-3.3 *)
Definition segment := string.

(** https://httpwg.org/http-core/draft-ietf-httpbis-semantics-latest.html#uri *)
Definition path := list segment.

(** https://www.rfc-editor.org/rfc/rfc3986.html#section-3.4 *)
Definition query := string.

(** https://httpwg.org/http-core/draft-ietf-httpbis-messaging-latest.html#request.target *)
Variant request_target :=
  RequestTarget__Origin    : path -> option query -> request_target
| RequestTarget__Absolute  : http_scheme -> authority ->
                           path -> option query -> request_target
| RequestTarget__Authority : authority -> request_target
| RequestTarget__Asterisk.

(** https://httpwg.org/http-core/draft-ietf-httpbis-messaging-latest.html#http.version *)
Record http_version :=
  Version {
      version__major : N;
      version__minor : N
    }.

(** https://httpwg.org/http-core/draft-ietf-httpbis-messaging-latest.html#request.line *)
Record request_line :=
  RequestLine {
      request__method  : request_method;
      request__target  : request_target;
      request__version : http_version
    }.

(** https://httpwg.org/http-core/draft-ietf-httpbis-semantics-latest.html#status.codes *)
Definition status_code := N.
Definition reason_phrase := string.
Definition statusCodes : list (status_code * reason_phrase) :=
  [(100, "Continue");
   (101, "Switching Protocols");
   (200, "OK");
   (201, "Created");
   (202, "Accepted");
   (203, "Non-Authoritative Information");
   (204, "No Content");
   (205, "Reset Content");
   (206, "Partial Content");
   (300, "Multiple Choices");
   (301, "Moved Permanently");
   (302, "Found");
   (303, "See Other");
   (304, "Not Modified");
   (305, "Use Proxy");
   (307, "Temporary Redirect");
   (400, "Bad Request");
   (401, "Unauthorized");
   (402, "Payment Required");
   (403, "Forbidden");
   (404, "Not Found");
   (405, "Method Not Allowed");
   (406, "Not Acceptable");
   (407, "Proxy Authentication Required");
   (408, "Request Time-out");
   (409, "Conflict");
   (410, "Gone");
   (411, "Length Required");
   (412, "Precondition Failed");
   (413, "Request Entity Too Large");
   (414, "Request-URI Too Large");
   (415, "Unsupported Media Type");
   (416, "Requested range not satisfiable");
   (417, "Expectation Failed");
   (500, "Internal Server Error");
   (501, "Not Implemented");
   (502, "Bad Gateway");
   (503, "Service Unavailable");
   (504, "Gateway Time-out");
   (505, "HTTP Version not supported")].

(** https://httpwg.org/http-core/draft-ietf-httpbis-messaging-latest.html#status.line *)
Record status_line :=
  Status {
      status__version : http_version;
      status__code    : status_code;
      status__phrase  : option reason_phrase
    }.

(** https://httpwg.org/http-core/draft-ietf-httpbis-semantics-latest.html#field.names *)
Definition field_name := string.

(** https://httpwg.org/http-core/draft-ietf-httpbis-semantics-latest.html#field.values *)
Definition field_value := string.

(** https://httpwg.org/http-core/draft-ietf-httpbis-messaging-latest.html#header.field.syntax *)
Record field_line exp_ :=
  Field {
      field__name  : field_name;
      field__value : exp_ field_value
    }.
Arguments Field      {_}.
Arguments field__name  {_}.
Arguments field__value {_}.

(** https://httpwg.org/http-core/draft-ietf-httpbis-messaging-latest.html#message.body *)
Definition message_body := string.

(** https://httpwg.org/http-core/draft-ietf-httpbis-messaging-latest.html#message.format *)
Record http_request :=
  Request {
      request__line   : request_line;
      request__fields : list (field_line id);
      request__body   : option message_body
    }.

Record http_response {exp_} :=
  Response {
      response__line   : status_line;
      response__fields : list (field_line exp_);
      response__body   : option (exp_ message_body)
    }.
Arguments http_response : clear implicits.
Arguments Response {exp_}.
