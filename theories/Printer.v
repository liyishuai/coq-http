From Coq Require Import
     Ascii
     NArith
     String
     DecimalString.
From ExtLib Require Export
     Extras.
From HTTP Require Export
     Message.
Export FunNotation.

Definition N_to_string (n : N) : string :=
  NilZero.string_of_uint (N.to_uint n).

Definition method_to_string (m : request_method) : string :=
  match m with
  | Method__GET     => "GET"
  | Method__HEAD    => "HEAD"
  | Method__POST    => "POST"
  | Method__PUT     => "PUT"
  | Method__DELETE  => "DELETE"
  | Method__CONNECT => "CONNECT"
  | Method__OPTIONS => "OPTIONS"
  | Method__TRACE   => "TRACE"
  | Method s      => s
  end.

Definition scheme_to_string (s : http_scheme) : string :=
  match s with
  | Scheme__HTTP  => "http://"
  | Scheme__HTTPS => "https://"
  end.

(* ["user"] to ["user@"] *)
Definition userinfo_to_string (ou : option string) : string :=
  match ou with
  | Some u => u ++ "@"
  | None   => ""
  end.

(* ["80"] to [":80"] *)
Definition port_to_string (p : option N) : string :=
  match p with
  | Some p => String ":" (N_to_string p)
  | None => ""
  end.

Definition authority_to_string (s : authority) : string :=
  userinfo_to_string (authority__userinfo s) ++
  authority__host s ++
  port_to_string (authority__port s).

Definition path_to_string : path -> string :=
  String "/".

Definition oquery_to_string (oq : option query) : string :=
  match oq with
  | Some q => String "?" q
  | None   => ""
  end.

Definition target_to_string (t : request_target) : string :=
  match t with
  | RequestTarget__Origin p oq => path_to_string p ++ oquery_to_string oq
  | RequestTarget__Absolute s a p oq =>
    scheme_to_string s ++ authority_to_string a ++ path_to_string p ++ oquery_to_string oq
  | RequestTarget__Authority a => authority_to_string a
  | RequestTarget__Asterisk => "*"
  end.

Definition version_to_string (v : http_version) : string :=
  "HTTP/" ++ N_to_string (version__major v) ++ String "." (N_to_string (version__minor v)).

Definition line_to_string (l : request_line) : string :=
  method_to_string (request__method l) ++ String " " (
  target_to_string (request__target l) ++ String " " (
  version_to_string (request__version l))).

Definition status_to_string (l : status_line) : string :=
  version_to_string (status__version l) ++ String " " (
  N_to_string (status__code l) ++ String " " (
  match status__phrase l with
  | Some p => p
  | None   => ""
  end)).

Definition field_to_string (f : field_line id) : string :=
  let 'Field n v := f in n ++ ": " ++ v.

Definition CRLF : string := String "013" (String "010" "").

Definition fields_to_string (l : list (field_line id)) : string :=
  String.concat CRLF (map field_to_string l).

Definition body_to_string (ob : option message_body) : string :=
  match ob with
  | Some b => b
  | None   => ""
  end.

Definition request_to_string (r : http_request) : string :=
  let 'Request l fs ob := r in
  line_to_string (request__line r) ++ CRLF ++
  fields_to_string (request__fields r) ++ CRLF ++
  CRLF ++
  body_to_string (request__body r).

Definition response_to_string (r : http_response id) : string :=
  status_to_string (response__line r) ++ CRLF ++
  fields_to_string (response__fields r) ++ CRLF ++
  CRLF ++
  body_to_string (response__body r).
