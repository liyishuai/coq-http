From HTTP Require Import
     Tester.

(** https://httpwg.org/http-core/draft-ietf-httpbis-semantics-latest.html#rfc.section.7.9.3.2 *)
Goal etag_match false "W/""1""" "W/""1""" = false.
Proof. reflexivity. Qed.

Goal etag_match true "W/""1""" "W/""1""" = true.
Proof. reflexivity. Qed.

Goal forall b : bool, etag_match b "W/""1""" "W/""2""" = false.
Proof. intros []; reflexivity. Qed.

Goal etag_match false "W/""1""" """1""" = false.
Proof. reflexivity. Qed.

Goal etag_match true "W/""1""" """1""" = true.
Proof. reflexivity. Qed.

Goal forall b : bool, etag_match b """1""" """1""" = true.
Proof. intros []; reflexivity. Qed.
