From SimpleIO Require Export
     IO_Random
     SimpleIO.
From Coq Require Export
     ExtrOcamlIntConv.
From HTTP Require Export
     Encode
     Semantics.
Export
  JpathNotations.
Open Scope json_scope.

Definition io_choose_ {A} (default : IO A) (l : list A) : IO A :=
  match l with
  | [] => default
  | a :: _ =>
    i <- nat_of_int <$> ORandom.int (int_of_nat (length l));;
    ret (nth i l a)
  end.

Definition io_choose' {A} (l : list A) : IO (nat * A) :=
  match l with
  | [] => failwith "Cannot choose from empty list"
  | a :: _ =>
    i <- nat_of_int <$> ORandom.int (int_of_nat (length l));;
    ret (i, nth i l a)
  end.

Definition io_choose {A} : list A -> IO A :=
  fmap snd ∘ io_choose'.

Definition io_or {A} (x y : IO A) : IO A :=
  b <- ORandom.bool tt;;
  if b : bool then x else y.

Definition gen_string' : IO string :=
  io_choose ["Hello"; "World"].

Fixpoint gen_many {A} (n : nat) (ma : IO A) : IO (list A) :=
  match n with
  | O => ret []
  | S n' => liftA2 cons ma $ io_or (ret []) (gen_many n' ma)
  end.

Definition gen_string : IO string :=
  String "~" ∘ String.concat "" <$> gen_many 3 gen_string'.

Definition gen_path : server_state exp -> IO path :=
  io_choose_ gen_string ∘ map fst.

Definition gen_line (ss : server_state exp) : IO request_line :=
  p <- gen_path ss;;
  m <- io_choose [Method__GET; Method__PUT];;
  ret (RequestLine m (RequestTarget__Origin p None) (Version 1 1)).

Definition find_etag (tr : traceT) : IO jexp :=
  io_choose_ (ret $ Jexp__Object []) $
             findpath (this@"fields"@"ETag") id tr.

Definition gen_condition (tr : traceT) : IO jexp :=
  condition <- io_choose ["If-Match"; "If-None-Match"];;
  etag <- find_etag tr;;
  ret (jkv condition etag).

Definition host_localhost : jexp := xencode $ Field "Host" "localhost".
Definition content_length (content : string) : jexp :=
  xencode $ Field "Content-Length" $ to_string $ String.length content.

Open Scope jexp_scope.

Definition gen_request (ss : server_state exp) (tr : traceT) : IO jexp :=
  l <- gen_line ss;;
  f <- gen_condition tr;;
  match request__method l with
  | Method__PUT =>
    content <- gen_string;;
    ret (xencode l +
         jkv "fields" (host_localhost + f + content_length content) +
         jobj "body" content)
  | _ => ret $ xencode l + jkv "fields" (host_localhost + f)
  end.
