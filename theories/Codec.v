From HTTP Require Export
     Decode
     Encode
     Parser
     Printer.

Definition jreq_to_string : IR -> string :=
  request_to_string ∘ request_of_json.

Definition jres_to_string : IR -> string :=
  response_to_string ∘ response_of_json.

Definition parseJres : parser IR :=
  encode <$> parseResponse.
