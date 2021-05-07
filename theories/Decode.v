From JSON Require Export
     Decode.
From Coq Require Export
     ssr.ssrfun.
From HTTP Require Export
     Parser.
Export
  JpathNotations.
Open Scope json_scope.

Definition dparse {T} (pr : parser T) (s : string) : string + T :=
  match parse pr s with
  | inl os     => inl (odflt "Parser out of fuel" os)
  | inr (t, _) => inr t
  end.

Definition dpath' {T} (d : JDecode T) (s : string) (j : json) : string + T :=
  decode__jpath (s -> this) j >>= d.

Definition dpath {T} `{JDecode T} : string -> json -> string + T :=
  dpath' decode.

Instance JDecode__Method : JDecode request_method :=
  fun j => dpath "method" j >>= dparse parseMethod.

Definition decode__path : JDecode path :=
  fun j => dpath "path" j.

Definition decode__oquery : JDecode (option query) :=
  fun j => dpath "query" j.

Definition decode__origin : JDecode request_target :=
  fun j => liftA2 RequestTarget__Origin (decode__path j) (decode__oquery j).

Instance JDecode__Scheme : JDecode http_scheme :=
  fun j => dpath "scheme" j >>= dparse parseScheme.

Instance JDecode__Authority : JDecode authority :=
  fun j => liftA2 Authority (dpath "userinfo" j) (dpath "host" j) <*>
               (dpath "port" j).

Instance JDecode__URI : JDecode absolute_uri :=
  fun j => liftA2 URI (decode j) (dpath "authroity" j) <*>
               (decode__path j) <*> (decode__oquery j).

Instance JDecode__RequestTarget : JDecode request_target :=
  fun j => dpath' decode__origin "origin" j <|>
        RequestTarget__Absolute  <$> dpath "absolute"  j <|>
        RequestTarget__Authority <$> dpath "authority" j <|>
        inr RequestTarget__Asterisk.

Instance JDecode__Version : JDecode http_version :=
  fun j => liftA2 Version (dpath "major" j) (dpath "minor" j).

Instance JDecode__RequestLine : JDecode request_line :=
  fun j => liftA2 RequestLine (decode j) (dpath "target" j) <*>
               (dpath "version" j).
