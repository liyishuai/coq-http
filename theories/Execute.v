From SimpleIO Require Export
     IO_Random.
From HTTP Require Export
     NetUnix
     Parser
     Tester.

Fixpoint findResponse (s : conn_state)
  : IO (option (packetT id) * conn_state) :=
  match s with
  | [] => ret (None, [])
  | cfs :: t =>
    let '(c, (f, str)) := cfs in
    match parse parseResponse str with
    | inl (Some err) =>
      failwith $ "Bad response " ++ to_string str ++ " received on connection "
               ++ to_string c ++ ", error message: " ++ err
    | inl None => '(op, t') <- findResponse t;;
                 ret (op, cfs :: t')
    | inr (r, str') =>
      prerr_endline ("recv: " ++ response_to_string r);;
      ret (Some (Packet 0 c (inr r)), (c, (f, str')) :: t)
    end
  end.

Definition client_io : clientE ~> stateT conn_state IO :=
  fun _ ce =>
    match ce with
    | Client__Recv   => mkStateT (fun s0 => execStateT recv_bytes s0 >>= findResponse)
    | Client__Send p => mkStateT (fun s0 => s1 <- execStateT (send_request p) s0;;
                                      ret (tt, s1))
    end.

Definition io_choose {A} (default : A) (l : list A) : IO A :=
  match l with
  | [] => ret default
  | _ :: _ =>
    i <- nat_of_int <$> ORandom.int (int_of_nat (length l));;
    ret (nth i l default)
  end.

Definition io_or {A} (x y : IO A) : IO A :=
  b <- ORandom.bool tt;;
  if b : bool then x else y.

Definition gen_string' : IO string :=
  io_choose "" ["Hello"; "World"; "Foo"; "Bar"].

Fixpoint dup {A} (n : nat) (a : A) : list A :=
  match n with
  | O => []
  | S n' => a :: dup n' a
  end.

Definition gen_string : IO string :=
  n <- nat_of_int <$> ORandom.int 4;;
  let gens : list (IO string) := dup (S n) gen_string' in
  fold_left (liftA2 append) gens (ret "").

Definition gen_path (s : server_state exp) : IO path :=
  let paths : list path := map fst s in
  p <- gen_string;;
  io_choose p (p::paths).

Definition gen_etag (p : path) (s : server_state exp) (es : exp_state)
  : IO field_value :=
  let tags : list field_value :=
      concat (map (fun st =>
                     match snd st with
                     | inl t => [t]
                     | inr n => n
                     end) (snd es)) in
  (* prerr_endline ("Generating ETag for " *)
  (*                  ++ to_string p ++ " under state " *)
  (*                  ++ to_string (s, es));; *)
  let random_tag := io_choose """12-5b0dffb40b3bb""" tags in
  match get p s with
  | None
  | Some None
  | Some (Some (ResourceState _ None)) => random_tag
  | Some (Some (ResourceState _ (Some tx))) =>
    match tx with
    | Exp__Const t => io_or (ret t) (io_choose t tags)
    | Exp__ETag  x =>
      match get x (snd es) with
      | Some (inl t)  => ret t
      | Some (inr ts) => io_choose """a-5b0dffb40d6e3""" ts
      | None => random_tag
      end
    | _ => random_tag
    end
  end.

Definition random_request (s : server_state exp) (es : exp_state)
  : IO http_request :=
  m <- io_or (ret Method__GET) (ret Method__PUT);;
  p <- gen_path s;;
  let l : request_line :=
      RequestLine m (RequestTarget__Origin p None) (Version 1 1) in
  match m with
  | Method__PUT =>
    str0 <- gen_string;;
    let str1 : string := p ++ ": " ++ str0 in
    tag_field <- io_or (t <- gen_etag p s es;;
                       ret [@Field id "If-Match" (t : field_value)])
                      (ret []);;
    ret (Request
           l (tag_field
                ++ [Field "Host" "localhost:8000";
                   Field "Content-Length" (to_string $ String.length str1)])
           (Some str1))
  | _ => ret $ Request l [Field "Host" "localhost:8000"] None
  end.

Definition gen_request' (p : path) (s : server_state exp)
           (es : exp_state) : IO http_request :=
  match get p s with
  | Some _ =>
    str0 <- gen_string;;
    t <- gen_etag p s es;;
    let l : request_line :=
        RequestLine Method__PUT (RequestTarget__Origin p None) (Version 1 1) in
    let str1 : string := p ++ ": " ++ str0 in
    ret (Request
           l [Field "Host" "localhost:8000";
             Field "Content-Length" (to_string $ String.length str1);
             Field "If-Match" (t : field_value)]
           (Some str1) : http_request)
  | None =>
    io_or (let l : request_line :=
               RequestLine Method__PUT (RequestTarget__Origin p None) (Version 1 1) in
           str0 <- gen_string;;
           let str1 : string := p ++ ": " ++ str0 in
           ret $ Request
               l [Field "Host" "localhost:8000";
                 Field "Content-Length" (to_string $ String.length str1)]
               (Some str1))
          (let l : request_line :=
               RequestLine Method__GET (RequestTarget__Origin p None) (Version 1 1) in
           ret (Request l [Field "Host" "localhost:8000"] None : http_request))
  end.

Definition gen_request (s : server_state exp) (es : exp_state) : IO http_request :=
  p <- gen_path s;;
  io_or (gen_request' p s es) (random_request s es).

Fixpoint execute' {R} (fuel : nat) (s : conn_state) (m : itree tE R)
  : IO (bool * conn_state) :=
  match fuel with
  | O => ret (true, s)
  | S fuel =>
    match observe m with
    | RetF _  => ret (true, s)
    | TauF m' => execute' fuel s m'
    | VisF e k =>
      match e with
      | (Throw err|) => prerr_endline err;; ret (false, s)
      | (|ne|) =>
        match ne in nondetE Y return (Y -> _) -> _ with
        | Or =>
          fun k =>
            b <- ORandom.bool tt;;
            execute' fuel s (k b)
        end k
      | (||ge|) =>
        match ge in genE Y return (Y -> _) -> _ with
        | Gen ss es =>
          fun k =>
            c <- io_or (ret $ S $ length s) (io_choose 1%nat (map fst s));;
            p <- Packet c 0 ∘ inl <$> gen_request ss es;;
            execute' fuel s (k p)
        end k
      | (|||le|) =>
        match le in logE Y return (Y -> _) -> _ with
        | Log str =>
          fun k => prerr_endline ("Tester: " ++ str);;
                execute' fuel s (k tt)
        end k
      | (||||ce) => '(r, s') <- runStateT (client_io _ ce) s;;
                  execute' fuel s' (k r)
      end
    end
  end.

Definition execute {R} (m : itree tE R) : IO bool :=
  '(b, s) <- execute' bigNumber [] m;;
  fold_left (fun m fd => OUnix.close fd;; m) (map (fst ∘ snd) s) (ret tt);;
  ret b.

Definition test {R} : itree smE R -> IO bool :=
  execute ∘ tester ∘ observer ∘ compose_switch tcp.
