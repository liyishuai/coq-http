From Coq Require Export
     Ascii
     Basics
     List
     String.
Open Scope program_scope.
Open Scope string_scope.

Notation key   := string.
Notation value := string.
Notation form  := (list (key * value)).

Definition form_to_string : form -> string :=
  let entry_to_string (k : key) (v : value) : string :=
      k ++ String "="%char v in
  concat "&" ∘ map (uncurry entry_to_string).
