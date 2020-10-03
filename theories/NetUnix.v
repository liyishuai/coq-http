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

Definition getport : IO int :=
  let default : int := 8000 in
  oport <- getenv_opt "PORT";;
  ret (match oport with
       | Some ostr => match int_of_ostring_opt ostr with
                     | Some port => port
                     | None => default
                     end
       | None => default
       end).

Definition create_sock : IO file_descr :=
  let iaddr : inet_addr := inet_addr_any in
  fd <- socket PF_INET SOCK_STREAM int_zero;;
  (ADDR_INET iaddr <$> getport) >>= bind fd;;
  listen fd 128;;
  ret fd.

Definition accept_conn (sfd : file_descr) : IO file_descr :=
  fst <$> accept sfd.

Definition conn_state := list (connT * (file_descr * string)).

Definition conn_of_fd (fd : file_descr)
  : conn_state -> option (connT * (file_descr * string)) :=
  find (file_descr_eqb fd ∘ fst ∘ snd).

Definition create_conn : stateT conn_state IO file_descr :=
  mkStateT
    (fun s =>
       let iaddr : inet_addr := inet_addr_loopback in
       fd <- socket PF_INET SOCK_STREAM int_zero;;
       (ADDR_INET iaddr <$> getport) >>= connect fd;;
       ret (fd, (S (length s), (fd, "")) :: s)).

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

Definition send_request (pkt : packetT id) (s : conn_state) : IO unit :=
  let 'Packet c _ p := pkt in
  match get c s with
  | Some (fd, _) =>
    match p with
    | inl req =>
      buf <- OBytes.of_string (request_to_string req);;
      let len : int := OBytes.length buf in
      IO.fix_io
        (fun send_rec o =>
           sent <- send fd buf o (len - o)%int [];;
           if sent <? int_zero
           then close fd;; failwith "Send byte failed"
           else
             if o + sent =? len
             then ret tt
             else send_rec (o + sent))%int int_zero
    | inr _ => failwith "Unexpected send response"
    end
  | None => failwith "Connection not found"
  end.
