From QuickChick Require Import
     QuickChick.
From HTTP Require Import
     Message.

Instance Dec_Eq__method : Dec_Eq request_method.
Proof. dec_eq. Defined.

Instance Dec_Eq__scheme : Dec_Eq http_scheme.
Proof. dec_eq. Defined.

Instance Dec_Eq__authority : Dec_Eq authority.
Proof. dec_eq. Defined.

Instance Dec_Eq__uri : Dec_Eq absolute_uri.
Proof. dec_eq. Defined.

Instance Shrink__Version : Shrink http_version :=
  { shrink _ := [] }.
