From Extract Require Import
     IO_Test.
From App Require Import
     Execute.
Extraction Blacklist Char.

Definition run_test : io_unit :=
  IO.unsafe_run
    (ORandom.self_init tt;; multi_test test_swap).

Separate Extraction run_test.
