From SimpleIO Require Export
     IO_Float
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
      prerr_endline ("==============RECEIVED=============="
                       ++ to_string c ++ CRLF ++ response_to_string r);;
      ret (Some (Packet Conn__Server (Conn__User c) (inr r)), (c, (f, str')) :: t)
    end
  end.

Fixpoint findRequest'
         (conns : list (clientT *
                        (OUnix.file_descr * string * option http_request)))
  : IO (option (clientT * http_request) *
        list (clientT * (OUnix.file_descr * string * option http_request)))
  :=
    match conns with
    | [] => ret (None, [])
    | conn :: t =>
      let '(c, (fd, str, _)) := conn in
      match parse parseRequest str with
      | inl (Some err) =>
        failwith $ "Bad request " ++ to_string str ++
                 ", error message: " ++ err
      | inl None => '(or, t') <- findRequest' t;;
                   ret (or, conn :: t')
      | inr (r, str') =>
        prerr_endline ("===========PROXY RECEIVED==========="
                         ++ to_string c
                         ++ CRLF ++ request_to_string r);;
        ret (Some (c, r), (c, (fd, str', Some r)) :: t)
      end
    end.

Definition findRequest (s : origin_state) :
  IO (option (clientT * http_request) * origin_state) :=
  let '(sfd, port, conns, ss) := s in
  '(or, conns') <- findRequest' conns;;
  ret (or, (sfd, port, conns', ss)).

Definition tester_state : Type := conn_state * origin_state.

Definition originAuthority (port : N) : authority :=
  Authority None "host.docker.internal" (Some port).

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
  io_choose "" ["Hello"; "World"].

Fixpoint gen_many {A} (n : nat) (ma : IO A) : IO (list A) :=
  match n with
  | O => ret []
  | S n' => liftA2 cons ma $ io_or (ret []) (gen_many n' ma)
  end.

Definition gen_string : IO string :=
  String "~" ∘ String.concat "" <$> gen_many 1 gen_string'.

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
  let random_tag := io_choose """Random""" tags in
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
      | Some (inr ts) => io_choose """Unknown""" ts
      | None => random_tag
      end
    | _ => random_tag
    end
  end.

Definition random_request (origin_port : N) (s : server_state exp) (es : exp_state)
  : IO http_request :=
  m <- io_or (ret Method__GET) (ret Method__PUT);;
  p <- gen_path s;;
  a <- io_or (ret $ Authority None "localhost" (Some server_port))
            (ret $ Authority None "host.docker.internal" (Some origin_port));;
  let uri : absolute_uri :=
      URI Scheme__HTTP a p None in
  let l : request_line :=
      RequestLine m (RequestTarget__Absolute uri) (Version 1 1) in
  match m with
  | Method__PUT =>
    str0 <- gen_string;;
    let str1 : string := p ++ ": " ++ str0 in
    tag_field <- io_or (t <- gen_etag p s es;;
                       match m with
                       | Method__GET | Method__HEAD => io_or
                         (ret [@Field id "If-Match" (t : field_value)])
                         (ret [@Field id "If-None-Match" (t : field_value)])
                       | _ => ret [@Field id "If-Match" (t : field_value)]
                       end)
                      (ret []);;
    ret (Request
           l (tag_field
                ++ [Field "Host" $ authority_to_string a;
                   Field "Content-Length" (to_string $ String.length str1)])
           (Some str1))
  | _ => ret $ Request l [Field "Host" $ authority_to_string a] None
  end%string.

Definition gen_request' (p : path) (s : server_state exp)
           (es : exp_state) : IO http_request :=
  let port : string := to_string server_port in
  match get p s with
  | Some (Some _) =>
    str0 <- gen_string;;
    t <- gen_etag p s es;;
    io_or (
    let l : request_line :=
        RequestLine Method__PUT (RequestTarget__Origin p None) (Version 1 1) in
    let str1 : string := p ++ ": " ++ str0 in
    ret (Request
           l [Field "Host" $ "localhost:" ++ port;
             Field "Content-Length" (to_string $ String.length str1);
             Field "If-Match" (t : field_value)]
           (Some str1) : http_request)
      ) (let l : request_line :=
             RequestLine Method__GET (RequestTarget__Origin p None) (Version 1 1) in
         ret (Request
                l [Field "Host" $ "localhost:" ++ port;
                  Field "If-None-Match" (t : field_value)] None : http_request))
  | Some None
  | None =>
    io_or (let l : request_line :=
               RequestLine Method__PUT (RequestTarget__Origin p None) (Version 1 1) in
           str0 <- gen_string;;
           let str1 : string := p ++ ": " ++ str0 in
           ret $ Request
               l [Field "Host" $ "localhost:" ++ port;
                 Field "Content-Length" (to_string $ String.length str1)]
               (Some str1))
          (let l : request_line :=
               RequestLine Method__GET (RequestTarget__Origin p None) (Version 1 1) in
           ret (Request l [Field "Host" $ "localhost:" ++ port] None : http_request))
  end.

Definition gen_request (port : N) (s : server_state exp) (es : exp_state)
  : IO http_request :=
  p <- gen_path s;;
  io_or (gen_request' p s es) (random_request port s es).

Definition ok (s : string) : state (server_state id) (http_response id) :=
  ret (Response (status_line_of_code 200)
                [@Field id "Content-Length" $ to_string $ String.length s]
                (Some s)).

Definition not_modified
  : state (server_state id) (http_response id) :=
  ret (Response (status_line_of_code 304) [] None).

Definition bad_request
  : state (server_state id) (http_response id) :=
  ret (Response (status_line_of_code 400)
                [@Field id "Content-Length" "0"] $ Some "").

Definition forbidden
  : state (server_state id) (http_response id) :=
  ret (Response (status_line_of_code 403)
                [@Field id "Content-Length" "0"] $ Some "").

Definition not_found
  : state (server_state id) (http_response id) :=
  ret (Response (status_line_of_code 404)
                [@Field id "Content-Length" "0"] $ Some "").

Definition method_not_allowed
  : state (server_state id) (http_response id) :=
  ret (Response (status_line_of_code 405)
                [@Field id "Content-Length" "0"] $ Some "").

Definition precondition_failed
  : state (server_state id) (http_response id) :=
  ret (Response (status_line_of_code 412)
                [@Field id "Content-Length" "0"] $ Some "").

Definition if_match (p : path) (hs : list (field_line id))
           (m : state (server_state id) (http_response id))
  : state (server_state id) (http_response id) :=
  mkState
    (fun ss =>
       let reject := runState precondition_failed ss in
       let accept := runState m ss in
       match findField "If-Match" hs with
       | Some v =>
         match get p ss with
         | Some (Some (ResourceState _ oetag)) =>
           match v, oetag with
           | "*", _  => accept
           | _, None => reject
           | v, Some t =>
             match parse (parseCSV parseEntityTag) v with
             | inl _ => runState bad_request ss
             | inr (ts, _) =>
               if existsb (etag_match false t) ts
               then accept
               else reject
             end
           end
         | _ => reject
         end
       | None => accept
       end).

Definition if_none_match (methd : request_method) (p : path)
           (hs : list (field_line id))
           (m : state (server_state id) (http_response id))
  : state (server_state id) (http_response id) :=
  mkState
    (fun ss =>
       let reject :=
           match methd with
           | Method__GET | Method__HEAD => runState not_modified ss
           | _ => runState precondition_failed ss
           end in
       let accept := runState m ss in
       match findField "If-None-Match" hs with
       | Some "*" =>
         match get p ss with
         | Some (Some _) => reject
         | _ => accept
         end
       | Some v =>
         match get p ss with
         | Some (Some (ResourceState _ (Some t))) =>
           match parse (parseCSV parseEntityTag) v with
           | inl _ => runState bad_request ss
           | inr (ts, _) =>
             if existsb (etag_match true t) ts
             then reject
             else accept
           end
         | _ => accept
         end
       | None => accept
       end).

Definition execute_request (req : http_request)
  : state (server_state id) (http_response id) :=
  mkState
    (fun ss =>
       let '(Request (RequestLine methd tgt ver) fields obody) := req in
       match target_uri tgt fields with
       | Some u =>
         let 'URI s a p oq := u in
         match methd with
         | Method__GET =>
           runState (ok "It works!") ss
         | Method__PUT
         | _ => runState method_not_allowed ss
         end
       | None => runState bad_request ss
       end).

Definition gen_response (ss : server_state exp) (es : exp_state)
           (c : clientT) : state origin_state (http_response id) :=
  mkState
    (fun os =>
       let '(sfd, port, conns, ss) := os in
       match get c conns with
       | Some (fd, str, Some req) =>
         let (res, ss') := runState (execute_request req) ss in
         (res, (sfd, port, conns, ss'))
       | _ => (Response (status_line_of_code 403) [] None, os)
       end).

Definition client_io (port : N) : clientE ~> stateT tester_state IO :=
  fun _ ce =>
    match ce with
    | Client__Recv src =>
      mkStateT
        (fun s0 =>
           let '(cs, os0) := s0 in
           let recv_client os :=
               '(op, cs') <- execStateT recv_bytes cs >>= findResponse;;
               (* prerr_endline ("Client received " ++ to_string op);; *)
               ret (op, (cs', os)) in
           match src with
           | Conn__Proxy _ =>
             '(ocr, os1) <- execStateT recv_bytes_origin os0 >>= findRequest;;
             match ocr with
             | Some (c, r) =>
               (* prerr_endline ("Proxy received " ++ to_string p);; *)
               ret (Some (Packet (Conn__Proxy c)
                                 (Conn__Authority $ originAuthority port)
                                 (inl r)), (cs, os1))
             | None => recv_client os1
             end
           | _ => recv_client os0
           end)
    | Client__Send ss dst es =>
      mkStateT
        $ fun s0 =>
            let '(cs, os) := s0 in
            match dst with
            | Conn__Proxy c =>
              let (res, os1) := runState (gen_response ss es c) os in
              '(b, os2) <- runStateT (send_response c res) os1;;
              ret (if b : bool
                   then Some $ Packet (Conn__Authority $ originAuthority port)
                             dst $ inr res
                   else None, (cs, os2))
            | Conn__Server =>
              req <- gen_request port ss es;;
              let cids : list clientT := map fst cs in
              c <- io_choose 1%nat (S (length cs) :: cids ++ cids ++ cids ++ cids);;
              '(b, cs1) <- runStateT (send_request c req) cs;;
              ret (if b : bool
                   then Some $ Packet (Conn__User c) Conn__Server $ inl req
                   else None, (cs1, os))
            | _ => failwith ""
            end
    end.

Fixpoint execute' {R} (fuel : nat) (port : N) (s : tester_state) (m : itree tE R)
  : IO (bool * tester_state) :=
  match fuel with
  | O => ret (true, s)
  | S fuel =>
    match observe m with
    | RetF _  => ret (true, s)
    | TauF m' => execute' fuel port s m'
    | VisF e k =>
      match e with
      | (Throw err|) => prerr_endline err;; ret (false, s)
      | (|ne|) =>
        match ne in nondetE Y return (Y -> _) -> _ with
        | Or =>
          fun k =>
            b <- ORandom.bool tt;;
            execute' fuel port s (k b)
        end k
      | (||le|) =>
        match le in logE Y return (Y -> _) -> _ with
        | Log str =>
          fun k =>
            curr <- OFloat.to_string <$> OUnix.gettimeofday tt;;
            prerr_endline (ostring_app curr (String "009" "Tester: " ++ str));;
            execute' fuel port s (k tt)
        end k
      | (|||ce) => '(r, s') <- runStateT (client_io port _ ce) s;;
                  execute' fuel port s' (k r)
      end
    end
  end.

Definition execute {R} (m : itree tE R) : IO bool :=
  prerr_endline "<<<<< begin test >>>>>>>";;
  '(port, sfd) <- create_sock;;
  '(b, s) <- execute' 5000 port ([], (sfd, port, [], [])) m;;
  let '(cs, (sfd, _, conns, _)) := s in
  fold_left (fun m fd => OUnix.close fd;; m)
            (map (fst ∘ snd) cs ++ map (fst ∘ fst ∘ snd) conns)
            (OUnix.close sfd);;
  prerr_endline "<<<<<<< end test >>>>>>>";;
  ret b.

Definition test {R} : itree smE R -> IO bool :=
  execute ∘ tester ∘ observer ∘ compose_switch tcp.
