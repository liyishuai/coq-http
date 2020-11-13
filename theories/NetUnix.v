From Coq Require Export
     ExtrOcamlIntConv
     String.
From ExtLib Require Export
     Functor
     Monad
     StateMonad.
From SimpleIO Require Export
     IO_Bytes
     IO_Float
     IO_Random
     IO_Sys
     IO_Unix
     SimpleIO.
From HTTP Require Export
     Printer
     Tcp.
Export
  FunctorNotation
  MonadNotation.
Open Scope string_scope.
Open Scope monad_scope.
Open Scope N_scope.

Import
  OSys
  OUnix.

Coercion int_of_n : N >-> int.

Definition getport : IO N :=
  N.add 8000 ∘ n_of_int <$> ORandom.int 5000.

Definition try {a b} (f : IO a) (g : IO b) : IO (option a) :=
  catch_error
    (Some <$> f) $
    fun e m _ =>
      g;;
      (* prerr_endline (ostring_app m $ *)
      (*                            ostring_app " throws an exception: " $ *)
      (*                            error_message e);; *)
      ret None.

Definition create_sock' (port : N) : IO (option file_descr) :=
  let iaddr : inet_addr := inet_addr_any in
  ofd <- try (socket PF_INET SOCK_STREAM int_zero) (ret tt);;
  match ofd with
  | Some fd =>
    let f :=
        bind fd (ADDR_INET iaddr $ int_of_n port);;
        listen fd 128;;
        ret fd in
    try f $
        (* prerr_endline ("Binding and listening to port " *)
        (*                  ++ to_string port);; *)
    close fd
  | None => ret None
  end.

Definition create_sock : IO (N * file_descr) :=
  getport >>=
          IO.fix_io
          (fun next p =>
             ofd <- create_sock' p;;
             match ofd with
             | Some fd => ret (p, fd)
             | None    => getport >>= next
             end).

Definition accept_conn (sfd : file_descr) : IO file_descr :=
  fst <$> accept sfd.

Definition conn_state := list (clientT * (file_descr * string)).

Definition conn_of_fd (fd : file_descr)
  : conn_state -> option (clientT * (file_descr * string)) :=
  find (file_descr_eqb fd ∘ fst ∘ snd).

Definition create_conn (c : clientT) : stateT conn_state IO (option file_descr) :=
  mkStateT
    (fun s =>
       let iaddr : inet_addr := inet_addr_loopback in
       ofd <- try (fd <- socket PF_INET SOCK_STREAM int_zero;;
                  connect fd (ADDR_INET iaddr server_port);;
                  ret fd) (ret tt);;
       ret (ofd, match ofd with
                 | Some fd => (c, (fd, ""))::s
                 | None    => s
                 end)).

Notation BUFFER_SIZE := 1024.
Definition SELECT_TIMEOUT := OFloat.Unsafe.of_string "1e-3".

Definition recv_bytes' : stateT conn_state IO bool :=
  mkStateT
    (fun s =>
       '(fds, _, _) <- select (map (fst ∘ snd) s) [] [] SELECT_TIMEOUT;;
       fold_left
         (fun _bs0 fd =>
            '(b, s0) <- _bs0;;
            match conn_of_fd fd s0 with
            | Some (c, (fd, str0)) =>
              buf <- OBytes.create BUFFER_SIZE;;
              len <- recv fd buf int_zero BUFFER_SIZE [];;
              if len <? int_zero
              then close fd;; _bs0
              else if len =? int_zero
                   then _bs0
                   else str <- from_ostring <$> OBytes.to_string buf;;
                        let str1 : string := substring 0 (nat_of_int len) str in
                        ret (true, update c (fd, str0 ++ str1) s0)
            | None => _bs0
            end)%int fds (ret (false, s))).

Definition recv_bytes : stateT conn_state IO unit :=
  mkStateT
    (IO.fix_io
       (fun recv_rec s =>
          '(b, s') <- runStateT recv_bytes' s;;
          if b : bool then recv_rec s' else ret (tt, s'))).

Instance Serialize__conn : Serialize (file_descr * string) :=
  to_sexp ∘ snd.

Definition origin_state : Type :=
  file_descr * N *
  list (clientT *
        (file_descr * string * option http_request)) *
  server_state id.

Definition origin_host (port : N) : authority :=
  Authority None "host.docker.internal" (Some port).

Definition proxy_of_fd (fd : file_descr)
  : list (clientT * (file_descr * string * option http_request)) ->
    option (clientT * (file_descr * string * option http_request)) :=
  find (file_descr_eqb fd ∘ fst ∘ fst ∘ snd).

Definition recv_bytes_origin : stateT origin_state IO unit :=
  mkStateT
    $ fun s =>
        let '(sfd, port, conns, ss) := s in
        '(fds, _, _) <- select (map (fst ∘ fst ∘ snd) conns) [] [] SELECT_TIMEOUT;;
        conns' <-
        fold_left
          (fun _s0 fd =>
             s0 <- _s0;;
             match proxy_of_fd fd s0 with
             | Some (c, (fd, str0, or)) =>
               buf <- OBytes.create BUFFER_SIZE;;
               len <- recv fd buf int_zero BUFFER_SIZE [];;
               if len <? int_zero
               then close fd;; ret s0
               else if len =? int_zero
                    then _s0
                    else str <- from_ostring <$> OBytes.to_string buf;;
                         let str1 : string := substring 0 (nat_of_int len) str in
                         ret $ update c (fd, str0 ++ str1, or) s0
             | None => ret s0
             end)%int fds
          ('(fds, _, _) <- select [sfd] [] [] SELECT_TIMEOUT;;
           match fds with
           | [] => ret conns
           | sfd :: _ => fd <- accept_conn sfd;;
                       ret (put (length conns) (fd, "", None) conns)
           end);;
        ret (tt, (sfd, port, conns', ss)).

Definition send_request (c : clientT) (req : http_request) : stateT conn_state IO bool :=
  let send_bytes fd s :=
        let str : string := request_to_string req in
        buf <- OBytes.of_string str;;
        let len : int := OBytes.length buf in
        b <- IO.fix_io
          (fun send_rec o =>
             sent <- send fd buf o (len - o)%int [];;
             if sent <? int_zero
             then close fd;;
                  prerr_endline "Send byte failed";;
                  ret false
             else
               if o + sent =? len
               then prerr_endline ("================SENT================"
                                     ++ to_string c ++ CRLF ++ str);;
                    ret true
               else send_rec (o + sent))%int int_zero;;
        ret (b, s)
  in
  mkStateT
    (fun s =>
         match get c s with
         | Some (fd, _) => send_bytes fd s
         | None => '(ofd, s') <- runStateT (create_conn c) s;;
                  match ofd with
                  | Some fd => send_bytes fd s'
                  | None    => ret (false, s')
                  end
         end).

Definition send_response (c : clientT) (res : http_response id) : stateT origin_state IO bool :=
  mkStateT
    (fun s =>
       let '(sfd, port, conns, ss) := s in
       match get c conns with
       | Some (fd, _, _) =>
         let str : string := response_to_string res in
         buf <- OBytes.of_string str;;
         let len : int := OBytes.length buf in
         b <- IO.fix_io
               (fun send_rec o =>
                  sent <- send fd buf o (len - o)%int [];;
                  if sent <? int_zero
                  then ret false
                  else
                    if o + sent =? len
                    then prerr_endline ("=============PROXY SENT============="
                                          ++ to_string c
                                          ++ CRLF ++ str);;
                         ret true
                    else send_rec (o + sent))%int int_zero;;
         ret (b, s)
       | None => ret (false, s)
       end).
