From ITree Require Export
     Exception.
From HTTP Require Export
     Printer
     Instances
     Tcp.

Definition wrap_payload : payloadT id -> payloadT exp :=
  fmap wrap_response.

Definition wrap_packet (pkt : packetT id) : packetT exp :=
  let 'Packet s d p := pkt in
  Packet s d (wrap_payload p).

Variant observeE : Type -> Type :=
  Observe__ToServer   : server_state exp -> connT -> observeE (packetT id)
| Observe__FromServer : connT -> observeE (packetT id).

Variant decideE : Type -> Set :=
  Decide : decideE bool.

Variant unifyE : Type -> Type :=
  Unify__FreshBody : unifyE (exp message_body)
| Unify__FreshETag : unifyE (exp field_value)
| Unify__Match     : exp bool -> bool -> unifyE unit
| Unify__Response  : http_response exp -> http_response id -> unifyE unit.

Notation failureE := (exceptE string).

Class Is__oE E `{failureE -< E} `{nondetE -< E}
      `{decideE -< E} `{unifyE -< E} `{logE -< E} `{observeE -< E}.
Notation oE := (failureE +' nondetE +' decideE +' unifyE +' logE +' observeE).
Instance oE_Is__oE : Is__oE oE. Defined.

Instance Serialize__payloadT : Serialize (payloadT id) :=
  fun p =>
    match p with
    | inl r => Atom $ request_to_string  r
    | inr r => Atom $ response_to_string r
    end.

Instance Serialize__connT : Serialize connT :=
  fun c =>
    match c with
    | Conn__User      c => [Atom "User"; to_sexp c]
    | Conn__Server      => [Atom "Server"]
    | Conn__Proxy     c => [Atom "Proxy"; to_sexp c]
    | Conn__Authority a => [Atom "Authority"; to_sexp a]
    end%sexp.

Instance Serialize__packetT : Serialize (packetT id) :=
  fun pkt =>
    let 'Packet s d p := pkt in
    [[Atom "Src"; to_sexp s];
    [Atom "Dst"; to_sexp d];
    [Atom "Msg"; to_sexp p]]%sexp.

(* TODO: distinguish proxy from clients *)
Definition dualize {E R} `{Is__oE E} (e : netE R) : itree E R :=
  match e in netE R return _ R with
  | Net__In st oh => wrap_packet <$> embed Observe__ToServer st oh
  | Net__Out (Packet s0 d0 p0) =>
    pkt <- embed Observe__FromServer s0;;
    let '(Packet s d p) := pkt in
    if (s = s0?) &&& (d = d0?)
    then match p0, p with
         | inl _, inr _ => throw "Expect request but observed response"
         | inr _, inl _ => throw "Expect response but observed request"
         | inl r0, inl r =>
           let 'Request (RequestLine m0 t0 _) hs0 ob0 := r0 in
           let 'Request (RequestLine m  t  _) hs  ob  := r  in
           match target_uri t0 hs0, target_uri t hs with
           | None, _ => throw "Model sent bad request"
           | _, None => throw "Cannot construct URI from observed request"
           | Some u0, Some u =>
             if u0 = u?
             then
               if m0 = m?
               then
                 match ob0, ob with
                 | Some _, None =>
                   throw "Expect message body but didn't observe it"
                 | None, Some _ =>
                   throw "Expect no message body but observed it"
                 | None, None => ret tt
                 | Some b0, Some b =>
                   if b0 =? b
                   then ret tt
                   else throw $ "Expect message body " ++ to_string b0
                              ++ ", but observed " ++ to_string b
                 end
               else throw $ "Expect method " ++ method_to_string m0
                        ++ ", but observed " ++ method_to_string m
             else throw $ "Expect target URI " ++ absolute_uri_to_string u0
                          ++ ", but observed " ++ absolute_uri_to_string u
           end
         | inr r0, inr r => embed Unify__Response r0 r
         end
    else throw "Unexpected payload observed to client"
  end%string.

Definition observer {E R} `{Is__oE E} (m : itree nE R) : itree E R :=
  interp
    (fun _ e =>
       match e with
       | (se|) => dualize se
       | (|ne|) =>
         match ne in nondetE R return _ R with
         | Or => trigger Decide
         end
       | (||le|) =>
         match le in logE R return _ R with
         | Log str => embed Log ("SMI: " ++ str)%string
         end
       | (|||se) =>
         match se in symE _ R return _ R with
         | Sym__NewBody => trigger Unify__FreshBody
         | Sym__NewETag => trigger Unify__FreshETag
         | Sym__Decide x => b <- trigger Decide;;
                         embed Unify__Match x b;;
                         ret b
         end
       end) m.
