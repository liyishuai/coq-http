From HTTP Require Import
     Common
     Message.

Program Instance Decidable_eq_method (x y : request_method) : Decidable (x = y) := {
  Decidable_witness :=
    match x, y with
    | Method__GET    , Method__GET
    | Method__HEAD   , Method__HEAD
    | Method__POST   , Method__POST
    | Method__PUT    , Method__PUT
    | Method__DELETE , Method__DELETE
    | Method__CONNECT, Method__CONNECT
    | Method__OPTIONS, Method__OPTIONS
    | Method__TRACE  , Method__TRACE => true
    | Method sx    , Method sy => sx = sy?
    | _, _ => false
    end }.
Solve Obligations with split; intuition; try discriminate.
Next Obligation.
  intuition.
  - destruct x, y; try discriminate; intuition.
    f_equal.
    apply eqb_eq.
    assumption.
  - subst.
    destruct y; intuition.
    apply eqb_eq.
    reflexivity.
Qed.

Program Instance Decidable_eq_scheme (x y : http_scheme) : Decidable (x = y) :=
  { Decidable_witness :=
      match x, y with
      | Scheme__HTTP , Scheme__HTTP
      | Scheme__HTTPS, Scheme__HTTPS => true
      | Scheme s1  , Scheme s2 => s1 = s2?
      | _, _ => false
      end }.
Solve Obligations with split; intuition; discriminate.
Next Obligation.
  destruct x, y; intuition; try discriminate; f_equal; apply eqb_eq; intuition.
  inversion H; reflexivity.
Qed.

Program Instance Decidable_eq_authority (x y : authority) : Decidable (x = y) :=
  { Decidable_witness :=
      let 'Authority u1 h1 p1 := x in
      let 'Authority u2 h2 p2 := y in
      (u1 = u2?) &&& (h1 =? h2) &&& (p1 = p2?) }.
Next Obligation.
  intuition.
  - destruct x, y.
    do 2 (apply andb_true_iff in H; destruct H).
    f_equal; apply Decidable_spec; intuition.
  - subst.
    destruct y.
    destruct authority__userinfo, authority__port;
      repeat (apply andb_true_iff; intuition);
        try apply eqb_eq; try apply N.eqb_eq; reflexivity.
Qed.

Program Instance Decidable_eq_uri (x y : absolute_uri) : Decidable (x = y) :=
  { Decidable_witness :=
      let 'URI s1 a1 p1 oq1 := x in
      let 'URI s2 a2 p2 oq2 := y in
      (s1 = s2)? &&& (a1 = a2?) &&& (p1 =? p2) &&& (oq1 = oq2?) }.
Next Obligation.
  intuition.
  - destruct x, y.
    do 3 (apply andb_true_iff in H; destruct H).
    f_equal; apply Decidable_spec; intuition.
  - subst.
    destruct y.
    destruct uri__scheme, uri__authority, uri__query, authority__userinfo, authority__port;
      repeat (apply andb_true_iff; intuition);
      try apply eqb_eq; try apply N.eqb_eq; reflexivity.
Qed.
