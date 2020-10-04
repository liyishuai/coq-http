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
      failwith $ "Bad response " ++ str ++ " received on connection "
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
  io_choose "" ["hello";
               "world";
               "foobar";
               "abcde";
               "LEFTOVER"].

Fixpoint dup {A} (n : nat) (a : A) : list A :=
  match n with
  | O => []
  | S n' => a :: dup n' a
  end.

Definition gen_string : IO string :=
  n <- nat_of_int <$> ORandom.int 2;;
  let gens : list (IO string) := dup (S n) gen_string' in
  fold_left (liftA2 append) gens (ret "").

Definition gen_request : IO http_request :=
  m <- io_or (ret Method__GET) (ret Method__PUT);;
  p <- gen_string;;
  let l : request_line :=
      RequestLine m (RequestTarget__Origin p None) (Version 1 1) in
  match m with
  | Method__PUT =>
    str <- gen_string;;
    ret (Request l [Field "Host" "localhost:8000";
                   Field "Content-Length" (to_string $ String.length str)]
                 (Some str))
  | _ => ret $ Request l [Field "Host" "localhost:8000"] None
  end.

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
        | Gen _ _ =>
          fun k =>
            c <- io_choose 1%nat (map fst s);;
            p <- Packet c 0 ∘ inl <$> gen_request;;
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
