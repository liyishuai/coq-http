From AsyncTest Require Export
     Common.
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

Definition dpath {T} `{JDecode T} : string -> JDecode T := dpath' decode.

Instance JDecode__Method : JDecode request_method :=
  fun j => dpath "method" j >>= dparse parseMethod.

Definition decode__path : JDecode path := dpath "path".

Definition decode__oquery : JDecode (option query) := dpath "query".

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

Definition decode__version : JDecode http_version :=
  fun j => liftA2 Version (dpath "major" j) (dpath "minor" j).

Instance JDecode__version : JDecode http_version :=
  fun j => (dpath' decode__version "version" j) <|> inr (Version 1 1).

Instance JDecode__RequestLine : JDecode request_line :=
  fun j => liftA2 RequestLine (decode j) (dpath "target" j) <*> (decode j).

Instance JDecode__Fields : JDecode (list (field_line id)) :=
  fun j => if j is JSON__Object l
         then inr $ map_ifr (fun kv => let (k, v) := kv : string * json in
                                     Field k <$> decode v) l
         else inl $ "Not an object: " ++ Printer.to_string j.

Instance JDecode__Request : JDecode (http_request id) :=
  fun j => liftA2 Request (decode j) (dpath "fields" j) <*> (dpath "body" j).

Instance JDecode__Status : JDecode status_line :=
  fun j => liftA2 Status (decode j) (dpath "code" j) <*> (dpath "reason" j).

Instance JDecode__Response : JDecode (http_response id) :=
  fun j => liftA2 Response (decode j) (dpath "fields" j) <*> (dpath "body" j).

Definition request_of_IR (j : json) : http_request id :=
  if decode j is inr req then req
  else Request (RequestLine (Method "BREW") RequestTarget__Asterisk (Version 1 0))
               [] None.

Definition response_of_IR (j : json) : http_response id :=
  if decode j is inr res then res
  else Response (Status (Version 1 0) 418 None) [] None.
