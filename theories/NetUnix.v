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
  let default : N := 1080 in
  oport <- getenv_opt "PORT";;
  ret (match oport with
       | Some ostr => match int_of_ostring_opt ostr with
                     | Some port => n_of_int port
                     | None => default
                     end
       | None => default
       end).

Definition create_sock (port : N) : IO file_descr :=
  let iaddr : inet_addr := inet_addr_any in
  fd <- socket PF_INET SOCK_STREAM int_zero;;
  bind fd (ADDR_INET iaddr $ int_of_n port);;
  listen fd 128;;
  ret fd.

Definition accept_conn (sfd : file_descr) : IO file_descr :=
  fst <$> accept sfd.

Definition conn_state := list (clientT * (file_descr * string)).

Definition conn_of_fd (fd : file_descr)
  : conn_state -> option (clientT * (file_descr * string)) :=
  find (file_descr_eqb fd ∘ fst ∘ snd).

Definition create_conn (c : clientT) : stateT conn_state IO file_descr :=
  mkStateT
    (fun s =>
       let iaddr : inet_addr := inet_addr_loopback in
       fd <- socket PF_INET SOCK_STREAM int_zero;;
       (ADDR_INET iaddr ∘ int_of_n <$> getport) >>= connect fd;;
       ret (fd, (c, (fd, "")) :: s)).

Notation BUFFER_SIZE := 1024.

Definition recv_bytes : stateT conn_state IO unit :=
  mkStateT
    (fun s =>
       '(fds, _, _) <- select (map (fst ∘ snd) s) [] [] (OFloat.of_int 1);;
       s' <- fold_left
              (fun _s0 fd =>
                 s0 <- _s0;;
                 match conn_of_fd fd s0 with
                 | Some (c, (fd, str0)) =>
                   buf <- OBytes.create BUFFER_SIZE;;
                   len <- recv fd buf int_zero BUFFER_SIZE [];;
                   if len <? int_zero
                   then close fd;; _s0
                   else if len =? int_zero
                     then _s0
                     else str <- from_ostring <$> OBytes.to_string buf;;
                          let str1 : string := substring 0 (nat_of_int len) str in
                          ret $ update c (fd, str0 ++ str1) s0
                 | None => _s0
                 end)%int fds (ret s);;
       ret (tt, s')).

Instance Serialize__conn : Serialize (file_descr * string) :=
  to_sexp ∘ snd.

Definition origin_state : Type :=
  file_descr * option file_descr * string * option (http_request) * server_state id.

Definition origin_host : authority :=
  Authority None "host.docker.internal" (Some 80).

Definition recv_bytes_origin (a : authority) : stateT origin_state IO unit :=
  mkStateT
    $ fun s =>
        let '(sfd, ofd, str, or, ss) := s in
        fd <- match ofd with
             | Some fd => ret fd
             | None => accept_conn sfd
             end;;
        buf <- OBytes.create BUFFER_SIZE;;
        len <- recv fd buf int_zero BUFFER_SIZE [];;
        if (len <? int_zero)%int
        then close fd;; ret (tt, s)
        else if (len =? int_zero)%int
             then ret (tt, s)
             else str0 <- from_ostring <$> OBytes.to_string buf;;
                  let str1 : string := substring 0 (nat_of_int len) str0 in
                  ret (tt, (sfd, Some fd, str ++ str1, None, ss)).

Definition send_request (c : clientT) (req : http_request) : stateT conn_state IO unit :=
  let send_bytes fd :=
        let str : string := request_to_string req in
        buf <- OBytes.of_string str;;
        let len : int := OBytes.length buf in
        IO.fix_io
          (fun send_rec o =>
             sent <- send fd buf o (len - o)%int [];;
             if sent <? int_zero
             then close fd;; failwith "Send byte failed"
             else
               if o + sent =? len
               then ret tt
               else send_rec (o + sent))%int int_zero;;
        prerr_endline ("================SENT================"
                         ++ to_string c ++ CRLF ++ str)
  in
  mkStateT
    (fun s =>
         match get c s with
         | Some (fd, _) => send_bytes fd;;
                          ret (tt, s)
         | None => '(fd, s') <- runStateT (create_conn c) s;;
                  send_bytes fd;;
                  ret (tt, s')
         end).

Definition send_response (fd : file_descr) (res : http_response id) : IO bool :=
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
         then prerr_endline ("================SENT================"
                               ++ to_string origin_host ++ CRLF ++ str);;
              ret true
         else send_rec (o + sent))%int int_zero;;
  close fd;;
  ret b.
