From HTTP Require Export
     Tester.

Fixpoint is_trace' {R} (fuel : nat) (m : itree stE R) (l : list traceT)
  : option (string + option R) :=
  match fuel with
  | O => None
  | S fuel =>
    match observe m with
    | RetF r => Some (inr $ Some r)
    | TauF m' => is_trace' fuel m' l
    | VisF e k =>
      match e with
      | (Throw err|) => Some (inl err)
      | (|ne|) =>
        match ne in nondetE Y return (Y -> _) -> _ with
        | Or =>
          fun k =>
            let rl := is_trace' fuel (k true)  l in
            let rr := is_trace' fuel (k false) l in
            match rl, rr with
            | Some (inl el), Some (inl er) =>
              Some (inl $ "IF   branch failed with: "
                        ++ el ++ CRLF ++ "ELSE branch failed with: " ++ er)
            | _, Some (inl _)
            | Some (inr _), _ => rl
            | _, _ => rr
            end
        end k
      | (||de|) =>
        match de in decideE Y return (Y -> _) -> _ with
        | Decide =>
          fun k =>
            let rl := is_trace' fuel (k true)  l in
            let rr := is_trace' fuel (k false) l in
            match rl, rr with
            | Some (inl el), Some (inl er) =>
              Some (inl $ "TRUE  branch failed with: "
                        ++ el ++ CRLF ++ "FALSE branch failed with: " ++ er)
            | _, Some (inl _)
            | Some (inr _), _ => rl
            | _, _ => rr
            end
        end k
      | (|||le|) =>
        match le in logE Y return (Y -> _) -> _ with
        | Log str =>
          fun k =>
            match is_trace' fuel (k tt) l with
            | Some (inl err) =>
              Some (inl $ "Failing log: " ++ str ++ CRLF ++ err)
            | r => r
            end
        end k
      | (||||te) =>
        match l with
        | [] => Some (inr None)
        | h::l =>
          match te in testerE Y return (Y -> _) -> _ with
          | Tester__Recv _ =>
            fun k =>
              match h with
              | Trace__In pkt => is_trace' fuel (k pkt) l
              | Trace__Out _ => Some (inl "Expect recv but observed send")
              end
          | Tester__Send _ _ _ =>
            fun k =>
              match h with
              | Trace__Out pkt => is_trace' fuel (k pkt) l
              | Trace__In _ => Some (inl "Expect send but observed recv")
              end
          end k
        end
      end
    end
  end.

Definition is_trace {R} (m : itree stE R) (l : list traceT) : bool :=
  match is_trace' bigNumber m l with
  | Some (inl _) => false
  | _            => true
  end.

Fixpoint accepts' {R} (fuel : nat) (m : itree tE R) (l : list traceT)
  : option (string + option R) :=
  match fuel with
  | O => None
  | S fuel =>
    match observe m with
    | RetF r => (Some (inr $ Some r))
    | TauF m' => accepts' fuel m' l
    | VisF e k =>
      match e with
      | (Throw err|) => Some (inl err)
      | (|ne|) =>
        match ne in nondetE Y return (Y -> _) -> _ with
        | Or =>
          fun k =>
            let rl := accepts' fuel (k true)  l in
            let rr := accepts' fuel (k false) l in
            match rl, rr with
            | Some (inl el), _ =>
              Some (inl $ "TRUE  branch failed with: " ++ el)
            | _, Some (inl er) =>
              Some (inl $ "FALSE branch failed with: " ++ er)
            | _, None => rl
            | _, _ => rr
            end
        end k
      | (||le|) =>
        match le in logE Y return (Y -> _) -> _ with
        | Log str =>
          fun k =>
            match accepts' fuel (k tt) l with
            | Some (inl err) =>
              Some (inl $ "Failing log: " ++ str ++ CRLF ++ err)
            | r => r
            end
        end k
      | (|||ce) =>
        match l with
        | [] => Some (inr None)
        | h::l =>
          match ce in clientE Y return (Y -> _) -> _ with
          | Client__Recv _ =>
            fun k =>
              match h with
              | Trace__In pkt => accepts' fuel (k $ Some pkt) l
              | Trace__Out _  => accepts' fuel (k   None)     l
              end
          | Client__Send _ _ _ =>
            fun k =>
              match h with
              | Trace__Out pkt => accepts' fuel (k $ Some pkt) l
              | Trace__In  _   => accepts' fuel (k   None)     l
              end
          end k
        end
      end
    end
  end.

Definition accepts {R} (m : itree tE R) (l : list traceT) : bool :=
  match accepts' bigNumber m l with
  | Some (inl _) => false
  | _            => true
  end.

Notation "x ==> y" := (negb x ||| y) (at level 55).

Definition backtrack_false_spec {R} (backtrack : itree stE R -> itree tE R)
           (m : itree stE R) (l : list traceT) : bool :=
  is_trace m l ==> accepts (backtrack m) l.

Definition backtrack_true_spec  {R} (backtrack : itree stE R -> itree tE R)
           (m : itree stE R) (l : list traceT) : bool :=
  accepts (backtrack m) l ==> is_trace m l.
