From AsyncTest Require Export
     Classes
     Operator.
From HTTP Require Export
     Message
     Printer.
Import
  XNotations.
Open Scope jexp_scope.

Instance XEncode__Method : XEncode request_method :=
  jobj' (JSON__String ∘ method_to_string) "method".

Definition encode__path   : XEncode path           := jobj "path".
Definition encode__oquery : XEncode (option query) := jobj "query".

Instance XEncode__Scheme : XEncode http_scheme :=
  jobj' (JSON__String ∘ scheme_to_string) "scheme".

Instance XEncode__Authority : XEncode authority :=
  fun a => let 'Authority u h p := a in
        jobj "userinfo" u + jobj "host" h + jobj "port" p.

Instance XEncode__RequestTarget : XEncode request_target :=
  fun t =>
    match t with
    | RequestTarget__Origin p oq =>
      jkv "origin" $ encode__path p + encode__oquery oq
    | RequestTarget__Absolute (URI s a p oq) =>
      jkv "absolute" $ xencode s + xencode a + encode__path p + encode__oquery oq
    | RequestTarget__Authority a => jkv "authority" $ xencode a
    | RequestTarget__Asterisk => Jexp__Const JSON__Null
    end.

Instance XEncode__Version : XEncode http_version :=
  fun v => let 'Version maj min := v in
        jkv "version" $ jobj "major" maj + jobj "minor" min.

Instance XEncode__RequestLine : XEncode request_line :=
  fun l => let 'RequestLine m t v := l in
        xencode m + jkv "target" (xencode t) + xencode v.
