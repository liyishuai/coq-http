From Coq Require Export
     ExtrOcamlIntConv
     String.
From ExtLib Require Export
     Functor
     Monad.
From SimpleIO Require Export
     IO_Bytes
     IO_Float
     IO_Random
     IO_Sys
     IO_Unix
     SimpleIO.
From HTTP Require Export
     Codec
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

Definition try {a b} (f : IO a) (g : IO b) : IO (option a) :=
  catch_error
    (Some <$> f) $
    fun e m _ =>
      g;;
      (* prerr_endline (ostring_app m $ *)
      (*                            ostring_app " throws an exception: " $ *)
      (*                            error_message e);; *)
      ret None.

Definition conn_state := list (clientT * (file_descr * string)).

Definition conn_of_fd (fd : file_descr)
  : conn_state -> option (clientT * (file_descr * string)) :=
  find (file_descr_eqb fd ∘ fst ∘ snd).

Definition create_conn (c : clientT) : Monads.stateT conn_state IO file_descr :=
  fun s =>
    let iaddr : inet_addr := inet_addr_loopback in
    fd <- socket PF_INET SOCK_STREAM int_zero;;
    connect fd (ADDR_INET iaddr server_port);;
    ret ((c, (fd, ""))::s, fd).

Notation BUFFER_SIZE := 2048.
Definition SELECT_TIMEOUT := OFloat.Unsafe.of_string ".01".

Definition recv_bytes' : Monads.stateT conn_state IO bool :=
    (fun s =>
       '(fds, _, _) <- select (map (fst ∘ snd) s) [] [] SELECT_TIMEOUT;;
       fold_left
         (fun _bs0 fd =>
            '(s0, b) <- _bs0;;
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
                        ret (update c (fd, str0 ++ str1) s0, true)
            | None => _bs0
            end)%int fds (ret (s, false))).

Definition recv_bytes : Monads.stateT conn_state IO unit :=
    (IO.fix_io
       (fun recv_rec s =>
          '(s', b) <- recv_bytes' s;;
          if b : bool then recv_rec s' else ret (s', tt))).

Instance Serialize__conn : Serialize (file_descr * string) :=
  to_sexp ∘ snd.

Definition send_request (c : clientT) (req : IR)
  : Monads.stateT conn_state IO unit :=
  fun s =>
    '(s', fd) <- match get c s with
                 | Some (fd, _) => ret (s, fd)
                 | _            => create_conn c s
                 end;;
    let str : string := jreq_to_string req in
    buf <- OBytes.of_string str;;
    let len : int := OBytes.length buf in
    IO.fix_io
      (fun send_rec o =>
         sent <- send fd buf o (len - o)%int [];;
         if sent <? int_zero
         then close fd;; failwith "Send byte failed"
         else
           if o + sent =? len
           then
             (* prerr_endline ("================SENT================" *)
             (*                     ++ to_string c ++ CRLF ++ str);; *)
             ret (s', tt)
           else send_rec (o + sent))%int int_zero.
