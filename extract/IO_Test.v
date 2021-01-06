From Coq Require Export
     Ascii
     ExtrOcamlIntConv
     String.
From ExtLib Require Export
     Extras
     Functor
     Monad.
From Ceres Require Export
     Ceres.
From SimpleIO Require Export
     IO_Float
     IO_Unix
     SimpleIO.
Export
  FloatNotations
  FunNotation
  FunctorNotation
  MonadNotation.
Open Scope monad_scope.
Open Scope string_scope.

Definition run_time {A} `{Serialize A} (x : IO A) : IO A :=
  start_time <- OUnix.gettimeofday;;
  a <- x;;
  end_time <- OUnix.gettimeofday;;
  prerr_endline (ostring_app (OFloat.to_string (end_time - start_time))
                             (String "," (to_string a)));;
  ret a.

(** Repeat [n0 + 1] times. *)
Fixpoint repeat1 {A} (n1 : nat) (x : IO A) : IO A :=
  match n1 with
  | O => x
  | S n => x;; repeat1 n x
  end.

Definition upon_success (handler test : IO bool) : IO bool :=
  b <- test;;
  if b : bool
  then handler
  else ret false.

Fixpoint multi_test' (fuel : nat) (test : IO (bool * nat)) : IO nat :=
  match fuel with
  | O => ret 5000
  | S fuel =>
    '(b, n) <- test;;
    if b : bool
    then Nat.add n <$> multi_test' fuel test
    else ret n
  end.

Definition multi_test : IO (bool * nat) -> IO nat := multi_test' 5000.
