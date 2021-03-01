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
      (* curr <- OFloat.to_string <$> OUnix.gettimeofday;; *)
      (* prerr_endline curr;; *)
      prerr_endline ("==============RECEIVED=============="
                       ++ to_string c ++ CRLF ++ response_to_string r);;
      ret (Some (Packet Conn__Server (Conn__User c) (inr r)), (c, (f, str')) :: t)
    end
  end.

Fixpoint findRequest'
         (conns : list (clientT *
                        (OUnix.file_descr * string * option (http_request id))))
  : IO (option (clientT * http_request id) *
        list (clientT * (OUnix.file_descr * string * option (http_request id))))
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
  IO (option (clientT * http_request id) * origin_state) :=
  let '(sfd, port, conns, ss) := s in
  '(or, conns') <- findRequest' conns;;
  ret (or, (sfd, port, conns', ss)).

Definition tester_state : Type := conn_state * origin_state.

Definition originAuthority (port : N) : authority :=
  Authority None "host.docker.internal" (Some port).

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

Definition gen_path (s : server_state exp) : IO path :=
  io_choose_ gen_string (map fst s).

Fixpoint pick_some {A} (l : list (option A)) : list A :=
  match l with
  | [] => []
  | Some a :: l' => a :: pick_some l'
  | None   :: l' =>     pick_some l'
  end.

Definition gen_etag (s : server_state exp) : IO (exp field_value) :=
  let rs : list (resource_state exp) := pick_some $ map snd           s in
  let ts : list (exp field_value)    := pick_some $ map resource__etag rs in
  io_choose_ (ret $ Exp__Const """Random""") ts.

Definition gen_request (origin_port : N) (s : server_state exp)
  : IO (http_request exp) :=
  m <- io_or (ret Method__GET) (ret Method__PUT);;
  p <- gen_path s;;
  (* let a := Authority None "localhost" (Some server_port) in *)
  a <- io_or (ret $ Authority None "localhost" (Some server_port))
            (ret $ Authority None "host.docker.internal" (Some origin_port));;
  m <- io_or (ret Method__GET) (ret Method__PUT);;
  p <- gen_path s;;
  let uri : absolute_uri :=
      URI Scheme__HTTP a p None in
  let l : request_line :=
      RequestLine m (RequestTarget__Absolute uri) (Version 1 1) in
  match m with
  | Method__PUT =>
    str0 <- gen_string;;
    let str1 : string := p ++ ": " ++ str0 in
    tag_field <- (t <- gen_etag s;;
                 io_choose [[Field "If-Match" t];
                            [Field "If-None-Match" t];
                            []]);;
    ret (Request
           l (tag_field
                ++ [Field "Host" $ Exp__Const $ authority_to_string a;
                    @Field exp "Content-Length" $
                           Exp__Const $ to_string $ String.length str1])
           (Some str1))
  | _ => ret $ Request l [Field "Host" $ Exp__Const $ authority_to_string a] None
  end%string.

Definition fill_tag (es : exp_state) (tx : exp field_value)
  : IO (id field_value) :=
  let gen_tag :=
      io_choose_ gen_string $ @concat _ $
                 map (fun s => match snd s with
                            | inl t => [t]
                            | inr ts => ts
                            end) $ snd es in
  match tx with
  | Exp__Const t => io_or (ret t) gen_tag
  | Exp__Body x =>
    match get x $ snd es with
    | Some (inl t)  => io_or (ret t) gen_tag
    | Some (inr ts) => io_or (io_choose_ gen_tag ts) gen_tag
    | None          => gen_tag
    end
  | _ => gen_tag
  end.

Definition fill_request (es : exp_state) (rx : http_request exp)
  : IO (http_request id) :=
  let 'Request l fx b := rx in
  let fill_field (f : field_line exp) : IO (field_line id) :=
      let 'Field n vx := f in @Field id n <$> fill_tag es vx in
  fs <- sequence (map fill_field fx);;
  ret (Request l fs b).

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

Definition execute_request (req : http_request id)
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

Definition client_io (port : N) : clientE ~> stateT (tester_state * nat) IO :=
  fun _ ce =>
    match ce with
    | Client__Recv =>
      mkStateT
        (fun s0 =>
           let '(cs, os0, n) := s0 in
           let recv_client os :=
               '(op, cs') <- execStateT recv_bytes cs >>= findResponse;;
               (* prerr_endline ("Client received " ++ to_string op);; *)
               let n' : nat :=
                   match op with
                   | Some _ => S n
                   | None   => n
                   end in
               ret (op, (cs', os, n')) in
             '(ocr, os1) <- execStateT recv_bytes_origin os0 >>= findRequest;;
             match ocr with
             | Some (c, r) =>
               (* prerr_endline ("Proxy received " ++ to_string p);; *)
               ret (Some (Packet (Conn__Proxy c)
                                 (Conn__Authority $ originAuthority port)
                                 (inl r)), (cs, os1, S n))
             | None => recv_client os1
             end)
    | Client__Send ss dst es =>
      mkStateT
        $ fun s0 =>
            let '(cs, os, n) := s0 in
            match dst with
            | Conn__Proxy c =>
              let (res, os1) := runState (gen_response ss es c) os in
              '(b, os2) <- runStateT (send_response c res) os1;;
              ret (if b : bool
                   then (Some $ Packet (Conn__Authority $ originAuthority port)
                             dst $ inr res, (cs, os2, S n))
                   else (None, (cs, os2, n)))
            | Conn__Server =>
              rx <- gen_request port ss;;
              req <- fill_request es rx;;
              let cids : list clientT := map fst cs in
              c <- io_choose (S (length cs) :: cids ++ cids ++ cids ++ cids);;
              '(b, cs1) <- runStateT (send_request c req) cs;;
              ret (if b : bool
                   then (Some $ Packet (Conn__User c) Conn__Server $ inl req, (cs1, os, S n))
                   else (None, (cs1, os, n)))
            | _ => failwith ""
            end
    end.

Fixpoint execute' {R} (fuel : nat) (port : N) (s : tester_state) (n : nat) (m : itree tE R)
  : IO (bool * tester_state * nat) :=
  match fuel with
  | O => ret (true, s, n)
  | S fuel =>
    match observe m with
    | RetF _  => ret (true, s, n)
    | TauF m' => execute' fuel port s n m'
    | VisF e k =>
      match e with
      | (Throw err|) => prerr_endline err;; ret (false, s, n)
      | (|ne|) =>
        match ne in nondetE Y return (Y -> _) -> _ with
        | Or =>
          fun k =>
            b <- ORandom.bool tt;;
            execute' fuel port s n (k b)
        end k
      | (||le|) =>
        match le in logE Y return (Y -> _) -> _ with
        | Log str =>
          fun k =>
            (* curr <- OFloat.to_string <$> OUnix.gettimeofday;; *)
            (* prerr_endline (ostring_app curr (String "009" "Tester: " ++ str));; *)
            execute' fuel port s n (k tt)
        end k
      | (|||ce) => '(r, (s', n')) <- runStateT (client_io port _ ce) (s, n);;
                  execute' fuel port s' n' (k r)
      end
    end
  end.

Definition execute {R} (m : itree tE R) : IO (bool * nat) :=
  prerr_endline "<<<<< begin test >>>>>>>";;
  '(port, sfd) <- create_sock;;
  '(b, s, n) <- execute' 5000 port ([], (sfd, port, [], [])) O m;;
  let '(cs, (sfd, _, conns, _)) := s in
  fold_left (fun m fd => OUnix.close fd;; m)
            (map (fst ∘ snd) cs ++ map (fst ∘ fst ∘ snd) conns)
            (OUnix.close sfd);;
  prerr_endline (if b : bool
                 then "<<<<< pass  test >>>>>>>"
                 else "<<<<< fail  test >>>>>>>");;
  ret (b, n).

Definition test {R} : itree smE R -> IO (bool * nat) :=
  execute ∘ tester ∘ observer ∘ compose_switch tcp.
