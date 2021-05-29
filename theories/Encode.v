From AsyncTest Require Export
     Classes
     Operator.
From JSON Require Export
     Operator.
From HTTP Require Export
     Message
     Printer.
Export
  JNotations
  XNotations.

Open Scope jexp_scope.

Instance XEncode__Method : XEncode request_method :=
  jobj' (JSON__String ∘ method_to_string) "method".

Definition xencode__path   : XEncode path           := jobj "path".
Definition xencode__oquery : XEncode (option query) := jobj "query".

Instance XEncode__Scheme : XEncode http_scheme :=
  jobj' (JSON__String ∘ scheme_to_string) "scheme".

Instance XEncode__Authority : XEncode authority :=
  fun a => let 'Authority u h p := a in
         jobj "userinfo" u + jobj "host" h + jobj "port" p.

Instance XEncode__RequestTarget : XEncode request_target :=
  fun t =>
    match t with
    | RequestTarget__Origin p oq =>
      jkv "origin" $ xencode__path p + xencode__oquery oq
    | RequestTarget__Absolute (URI s a p oq) =>
      jkv "absolute" $ xencode s + xencode a + xencode__path p + xencode__oquery oq
    | RequestTarget__Authority a => jkv "authority" $ xencode a
    | RequestTarget__Asterisk => Jexp__Object []
    end.

Instance XEncode__Version : XEncode http_version :=
  fun v => let 'Version maj min := v in
        jkv "version" $ jobj "major" maj + jobj "minor" min.

Instance XEncode__RequestLine : XEncode request_line :=
  fun l => let 'RequestLine m t v := l in
        xencode m + jkv "target" (xencode t) + xencode v.

Instance XEncode__Field : XEncode (field_line id) :=
  fun f => let 'Field k v := f in
         jobj k v.

Close Scope jexp_scope.

Open Scope json_scope.

Instance Encode__Status : JEncode status_line :=
  fun s => let 'Status v c op := s in
         encode__xencode v + Encode.jobj "code" c + Encode.jobj "reason" op.

Instance XEncode__Fields : JEncode (list (field_line id)) :=
    Encode.jkv "fields" ∘ fold_right (or_json ∘ encode__xencode) (JSON__Object []).

Instance Encode__Response : JEncode (http_response id) :=
  fun r => let 'Response l f ob := r in
         encode l + encode f + Encode.jobj "body" ob.

Close Scope json_scope.
