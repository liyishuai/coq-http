From Extract Require Import
     IO_Test.
From HTTP Require Import
     Execute.

Parameter command : ocaml_string -> IO int.

Definition run_test : io_unit :=
  IO.unsafe_run
    (ORandom.self_init tt;; multi_test (@test void http_smi)).

Extract Constant command => "fun s k -> k (Sys.command s)".

Separate Extraction run_test.
