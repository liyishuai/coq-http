From AsyncTest Require Export
     Common.
From JSON Require Export
     Decode.
From HTTP Require Export
     Parser.

#[global]
Instance JDecode__Method : JDecode request_method :=
  fun j => dpath "method" j >>= dparse parseMethod.

Definition decode__path : JDecode path := dpath "path".

Definition decode__oquery : JDecode (option query) := dpath' decode__option "query".
Definition decode__obody  : JDecode (option message_body) := dpath' decode__option "body".

Definition decode__origin : JDecode request_target :=
  fun j => liftA2 RequestTarget__Origin (decode__path j) (decode__oquery j).

#[global]
Instance JDecode__Scheme : JDecode http_scheme :=
  fun j => dpath "scheme" j >>= dparse parseScheme.

#[global]
Instance JDecode__Authority : JDecode authority :=
  fun j => liftA2 Authority (dpath' decode__option "userinfo" j) (dpath "host" j)
                <*> (dpath' decode__option "port" j).

#[global]
Instance JDecode__URI : JDecode absolute_uri :=
  fun j => liftA2 URI (decode j) (dpath "authroity" j) <*>
               (decode__path j) <*> (decode__oquery j).

#[global]
Instance JDecode__RequestTarget : JDecode request_target :=
  fun j => dpath' decode__origin "origin" j <|>
        RequestTarget__Absolute  <$> dpath "absolute"  j <|>
        RequestTarget__Authority <$> dpath "authority" j <|>
        inr RequestTarget__Asterisk.

Definition decode__version : JDecode http_version :=
  fun j => liftA2 Version (dpath "major" j) (dpath "minor" j).

#[global]
Instance JDecode__version : JDecode http_version :=
  fun j => (dpath' decode__version "version" j) <|> inr (Version 1 1).

#[global]
Instance JDecode__RequestLine : JDecode request_line :=
  fun j => liftA2 RequestLine (decode j) (dpath "target" j) <*> (decode j).

#[global]
Instance JDecode__Fields : JDecode (list (field_line id)) :=
  fun j => if j is JSON__Object l
         then inr $ map_ifr (fun kv => let (k, v) := kv : string * json in
                                     Field k <$> decode v) l
         else inl $ "Not an object: " ++ Printer.to_string j.

#[global]
Instance JDecode__Request : JDecode (http_request id) :=
  fun j => liftA2 Request (decode j) (dpath "fields" j) <*> decode__obody j.

#[global]
Instance JDecode__Status : JDecode status_line :=
  fun j => liftA2 Status (decode j) (dpath "code" j) <*>
                (dpath' decode__option "reason" j).

#[global]
Instance JDecode__Response : JDecode (http_response id) :=
  fun j => liftA2 Response (decode j) (dpath "fields" j) <*> decode__obody j.

Definition request_of_IR (j : json) : http_request id :=
  if decode j is inr req then req
  else Request (RequestLine (Method "BREW") RequestTarget__Asterisk (Version 1 0))
               [] None.

Definition response_of_IR (j : json) : http_response id :=
  if decode j is inr res then res
  else Response (Status (Version 1 0) 418 None) [] None.
