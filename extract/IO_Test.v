From Coq Require Export
     ExtrOcamlIntConv
     String.
From ExtLib Require Export
     Monad.
From Ceres Require Export
     Ceres.
From SimpleIO Require Export
     IO_Unix
     SimpleIO.
Export MonadNotation.
Open Scope monad_scope.
Open Scope string_scope.

Definition upon_success (handler test : IO bool) : IO bool :=
  b <- test;;
  if b : bool
  then handler
  else ret false.

Fixpoint multi_test' (fuel : nat) (test : IO bool) : IO bool :=
  match fuel with
  | O => ret true
  | S fuel =>
    upon_success (prerr_endline (to_string fuel);;
                  multi_test' fuel test) test
  end.

Definition multi_test : IO bool -> IO bool := multi_test' 5000.

Definition run_test (test : IO bool) : IO unit :=
  b <- test;;
  if b : bool
  then print_endline "Success"
  else print_endline "Failure";;
       exit (int_of_nat 1).
