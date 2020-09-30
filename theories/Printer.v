From Coq Require Export
     Ascii.
From Ceres Require Export
     Ceres.
From ExtLib Require Export
     Extras.
From HTTP Require Export
     Message.
Export FunNotation.

Instance Serialize__method : Serialize request_method :=
  fun m => Atom (match m with
              | Method__GET     => "GET"
              | Method__HEAD    => "HEAD"
              | Method__POST    => "POST"
              | Method__PUT     => "PUT"
              | Method__DELETE  => "DELETE"
              | Method__CONNECT => "CONNECT"
              | Method__OPTIONS => "OPTIONS"
              | Method__TRACE   => "TRACE"
              | Method s      => s
              end).

Instance Serialize__scheme : Serialize http_scheme :=
  fun s => Atom (match s with
              | Scheme__HTTP  => "http://"
              | Scheme__HTTPS => "https://"
              end).

Instance Serialize__authority : Serialize authority :=
  fun s =>
    let 'Authority ou h op := s in
    Atom ((match ou with
           | Some u => u ++ "@"
           | None   => ""
           end) ++ h ++
          (match op with
           | Some p => String ":" $ to_string p
           | None   => ""
           end)).

Instance Serialize__path : Serialize path :=
  fun p => Atom (String "/" $ concat "/" p).

Instance Serialize__oquery : Serialize (option query) :=
  fun oq => Atom (match oq with
               | Some q => String "?" q
               | None   => ""
               end).

Instance Serialize__target : Serialize request_target :=
  fun t => Atom (match t with
              | RequestTarget__Origin p oq => to_string p ++ to_string oq
              | RequestTarget__Absolute s a p oq =>
                to_string s ++ to_string a ++ to_string p ++ to_string oq
              | RequestTarget__Authority a => to_string a
              | RequestTarget__Asterisk => "*"
              end).

Instance Serialize__version : Serialize http_version :=
  fun v =>
    let 'Version m n := v in
    Atom ("HTTP/" ++ to_string m ++ String "." (to_string n)).

Instance Serialize__line : Serialize request_line :=
  fun l =>
    let 'RequestLine m t v := l in
    Atom (to_string m ++ String " " (to_string t) ++ String " " (to_string v)).

Instance Serialize__status : Serialize status_line :=
  fun l =>
    let 'Status v c op := l in
    Atom (to_string v ++ String " " (to_string c) ++ String " " (match op with
                                                                 | Some p => p
                                                                 | None   => ""
                                                                 end)).

Instance Serialize__field : Serialize (field_line id) :=
  fun f => let 'Field n v := f in Atom (n ++ ": " ++ v).

Definition CRLF : string := String "013" (String "010" "").

Instance Serialize__fields : Serialize (list (field_line id)) :=
  fun l => Atom (concat CRLF (map to_string l)).

Instance Serialize__body : Serialize (option message_body) :=
  fun ob => Atom (match ob with
               | Some b => b
               | None   => ""
               end).

Instance Serialize__request : Serialize http_request :=
  fun r =>
    let 'Request l fs ob := r in
    Atom (to_string l ++ CRLF ++ to_string fs ++ CRLF ++ CRLF ++ to_string ob).

Instance Serialize__response : Serialize (http_response id) :=
  fun r =>
    let 'Response l fs ob' := r in
    let ob : option message_body := ob' in
    Atom (to_string l ++ CRLF ++ to_string fs ++ CRLF ++ CRLF ++ to_string ob).
