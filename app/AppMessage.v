From App Require Export
     Form.
From HTTP Require Export
     Message.
From Coq Require Export
     DecimalString
     NArith.
Export IfNotations.

Notation user_id  := N.
Notation order_id := N.
Notation amountT  := N.
Notation assetT   := string.

Coercion string_of_N :=
  NilZero.string_of_uint ∘ N.to_uint : N -> string.

Coercion string_of_nat :=
  NilZero.string_of_uint ∘ Nat.to_uint : nat -> string.

Variant swap_request :=
  Swap__ListOrders
| Swap__ListAccount (uid : user_id)
| Swap__TakeOrder (uid : user_id) (oid : order_id)
| Swap__MakeOrder (uid : user_id)
                (buyTicker  : assetT) (buyAmount  : amountT)
                (sellTicker : assetT) (sellAmount : amountT)
| Swap__Deposit  (uid : user_id) (ticker : assetT) (amount : amountT)
| Swap__Withdraw (uid : user_id) (ticker : assetT) (amount : amountT).

Definition swap_method (req : swap_request) : request_method :=
  match req with
  | Swap__ListOrders    | Swap__ListAccount _   => Method__GET
  | Swap__TakeOrder _ _ | Swap__MakeOrder _ _ _ _ _
  | Swap__Deposit _ _ _ | Swap__Withdraw  _ _ _ => Method__POST
  end.

Definition swap_form (req : swap_request) : form :=
  match req with
  | Swap__ListOrders => []
  | Swap__ListAccount uid => [("user", string_of_N uid)]
  | Swap__TakeOrder uid oid =>
    [("user", string_of_N uid);
    ("order", string_of_N oid)]
  | Swap__MakeOrder uid buyTicker buyAmount sellTicker sellAmount =>
    [("user"     , string_of_N uid);
    ("buyTicker" ,             buyTicker);
    ("buyAmount" , string_of_N buyAmount);
    ("sellTicker",             sellTicker);
    ("sellAmount", string_of_N sellAmount)]
  | Swap__Deposit  uid ticker amount
  | Swap__Withdraw uid ticker amount =>
    [("user" , string_of_N uid);
    ("ticker", ticker);
    ("amount", string_of_N amount)]
  end.

Definition swap_target (req : swap_request) : request_target :=
  let q : query := form_to_string (swap_form req) in
  match req with
  | Swap__ListAccount _       => RequestTarget__Origin "/listAccount" (Some q)
  | Swap__ListOrders          => RequestTarget__Origin "/listOrders" None
  | Swap__TakeOrder _ _       => RequestTarget__Origin "/takeOrder"  None
  | Swap__MakeOrder _ _ _ _ _ => RequestTarget__Origin "/makeOrder"  None
  | Swap__Deposit   _ _ _     => RequestTarget__Origin "/deposit"    None
  | Swap__Withdraw  _ _ _     => RequestTarget__Origin "/withdraw"   None
  end.

Definition swap_body (req : swap_request) : option message_body :=
  match req with
  | Swap__ListAccount _ | Swap__ListOrders => None
  | Swap__TakeOrder _ _ | Swap__MakeOrder _ _ _ _ _
  | Swap__Deposit _ _ _ | Swap__Withdraw  _ _ _ =>
                        Some (form_to_string (swap_form req))
  end.

Definition encode_request (req : swap_request) : http_request id :=
  let method : request_method := swap_method req in
  let target : request_target := swap_target req in
  let line   : request_line   := RequestLine method target (Version 1 1) in
  let obody  : option message_body := swap_body req in
  let headers : list (field_line id) :=
      Field "Host" "gswap.herokuapp.com"::
            if obody is Some body
            then [Field "Content-Length" (string_of_nat (length body));
                  Field "Content-Type" "application/x-www-form-urlencoded"]
            else []
  in
  Request line headers obody.
