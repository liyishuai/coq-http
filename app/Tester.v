From App Require Export
     Solver.
From IShrink Require Export
     IShrink.

Notation clientE := (@clientE (packetT (swap_request id) (swap_response id))
                              (swap_state exp)).

Notation tE := (failureE +' clientE +' nondetE +' logE).

Notation swap_stE :=
  (stE (swap_request id) (swap_response id) (swap_state exp)).

CoFixpoint match_event {q r s T} (e0 : observeE q r s T) (v : T)
           (m : itree (stE q r s) void) : itree (stE q r s) void :=
  match observe m with
  | RetF vd => match vd in void with end
  | TauF m' => Tau (match_event e0 v m')
  | VisF e k =>
    match e with
    | (||oe) =>
      match oe in observeE _ _ _ Y, e0 in observeE _ _ _ Z
            return (Y -> _) -> Z -> _ with
      | Observe__FromServer, Observe__FromServer
      | Observe__ToServer _, Observe__ToServer _ => id
      | _, _ => fun _ _ => throw "Unexpected event"
      end k v
    | _ => vis e (match_event e0 v ∘ k)
    end
  end.

Definition match_observe {q r s T} (e : observeE q r s T) (v : T)
  : list (itree (stE q r s) void) -> list (itree (stE q r s) void) :=
  map (match_event e v).

CoFixpoint tester' (others : list (itree swap_stE void))
           (m : itree swap_stE void) : itree tE void :=
  match observe m with
  | RetF vd => match vd in void with end
  | TauF m' => Tau (tester' others m')
  | VisF e k =>
    let catch (err : string) : itree tE void :=
        embed Log err;;
        if others is other::others'
        then Tau (tester' others' other)
        else throw err in
    match e with
    | (Throw err|) => catch err
    | (|de|) =>
      match de in decideE Y return (Y -> _) -> _ with
      | Decide => fun k => b <- trigger Or;;
                       Tau (tester' (k (negb b)::others) (k b))
      end k
    | (||oe) =>
      match oe in observeE _ _ _ Y return (Y -> _) -> _ with
      | Observe__ToServer st =>
        fun k =>
          op1 <- trigger Client__Recv;;
          if op1 is Some p1
          then if match_observe Observe__FromServer p1 others is other::others'
               then Tau (tester' others' other)
               else catch "Unexpected receive from server"
          else op <- embed Client__Send st;;
               if op is Some p
               then Tau (tester' (match_observe (Observe__ToServer st) p others)
                                 (k p))
               else if others is other::others'
                    then Tau (tester' (others' ++ [m]) other)
                    else Tau (tester' [] m)
      | Observe__FromServer =>
        fun k =>
          op <- trigger Client__Recv;;
          if op is Some p
          then Tau (tester' (match_observe Observe__FromServer p others) (k p))
          else if others is other::others'
               then Tau (tester' (others' ++ [m]) other)
               else Tau (tester' [] m)
      end k
    end
  end.

Definition tester : itree swap_stE void -> itree tE void := tester' [].

Definition swap_tester : swap_state exp -> itree tE void := tester ∘ solve_swap.
