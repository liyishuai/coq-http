From App Require Export
     Form.
From HTTP Require Export
     Message.
From Parsec Require Export
     Parser.
From JSON Require Export
     Lexer
     JSON.
From ExtLib Require Export
     Monad
     OptionMonad.
From Coq Require Export
     DecimalString
     NArith.
Export
  IfNotations
  MonadNotation.
Open Scope parser_scope.
Open Scope monad_scope.

Definition user_id  := N.
Definition order_id := N.
Definition amountT  := N.
Definition assetT   := string.

Coercion string_of_N :=
  NilZero.string_of_uint ∘ N.to_uint : N -> string.

Coercion string_of_nat :=
  NilZero.string_of_uint ∘ Nat.to_uint : nat -> string.

Variant swap_request {exp_} :=
  Request__ListOrders
| Request__ListAccount (uid : user_id)
| Request__TakeOrder (uid : user_id) (oid : exp_ order_id)
| Request__MakeOrder (uid : user_id)
                   (buyTicker  : assetT) (buyAmount  :      amountT)
                   (sellTicker : assetT) (sellAmount : exp_ amountT)
| Request__Deposit   (uid : user_id) (ticker : assetT) (amount :      amountT)
| Request__Withdraw  (uid : user_id) (ticker : assetT) (amount : exp_ amountT).
Arguments swap_request : clear implicits.

Definition swap_method (req : swap_request id) : request_method :=
  match req with
  | Request__ListOrders    | Request__ListAccount _   => Method__GET
  | Request__TakeOrder _ _ | Request__MakeOrder _ _ _ _ _
  | Request__Deposit _ _ _ | Request__Withdraw  _ _ _ => Method__POST
  end.

Definition swap_form (req : swap_request id) : form :=
  match req with
  | Request__ListOrders => []
  | Request__ListAccount uid => [("user", string_of_N uid)]
  | Request__TakeOrder uid oid =>
    [("user", string_of_N uid);
    ("order", string_of_N oid)]
  | Request__MakeOrder uid buyTicker buyAmount sellTicker sellAmount =>
    [("user"     , string_of_N uid);
    ("buyTicker" ,             buyTicker);
    ("buyAmount" , string_of_N buyAmount);
    ("sellTicker",             sellTicker);
    ("sellAmount", string_of_N sellAmount)]
  | Request__Deposit  uid ticker amount
  | Request__Withdraw uid ticker amount =>
    [("user" , string_of_N uid);
    ("ticker", ticker);
    ("amount", string_of_N amount)]
  end.

Definition swap_target (req : swap_request id) : request_target :=
  match req with
  | Request__ListOrders          => RequestTarget__Origin "/listOrders" None
  | Request__TakeOrder _ _       => RequestTarget__Origin "/takeOrder"  None
  | Request__MakeOrder _ _ _ _ _ => RequestTarget__Origin "/makeOrder"  None
  | Request__Deposit   _ _ _     => RequestTarget__Origin "/deposit"    None
  | Request__Withdraw  _ _ _     => RequestTarget__Origin "/withdraw"   None
  | Request__ListAccount _       => RequestTarget__Origin "/listAccount"
                             (Some (form_to_string (swap_form req)))
  end.

Definition swap_body (req : swap_request id) : option message_body :=
  match req with
  | Request__ListAccount _ | Request__ListOrders => None
  | Request__TakeOrder _ _ | Request__MakeOrder _ _ _ _ _
  | Request__Deposit _ _ _ | Request__Withdraw  _ _ _ =>
                        Some (form_to_string (swap_form req))
  end.

Definition encode_request (req : swap_request id) : http_request id :=
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

Definition account_id := N.
Definition accountT exp_ : Type :=
  exp_ account_id * (user_id * assetT * exp_ amountT).
Definition orderT exp_ : Type :=
  exp_ order_id * (exp_ account_id * amountT * exp_ account_id * amountT).

Variant swap_response {exp_} :=
  Response__InsufficientFund
| Response__NotFound
| Response__ListAccount (l : list (accountT exp_))
| Response__ListOrders  (l : list (orderT exp_))
| Response__Account     (a : accountT exp_)
| Response__Order       (o : orderT exp_).
Arguments swap_response : clear implicits.

Definition getAccount (j : json) : option (accountT id) :=
  aid <- (get_N "ID"     j : option (id N));;
  amt <- (get_N "Amount" j : option (id N));;
  uid <-  get_N "UserID" j;;
  tcr <-  get_string "AssetTicker" j;;
  Some (aid, (uid, tcr, amt)).

Definition getOrder (j : json) : option (orderT id) :=
  oid <- (get_N "ID"         j : option (id N));;
  bid <- (get_N "BuyerID"    j : option (id N));;
  sid <- (get_N "SellerID"   j : option (id N));;
  bam <-  get_N "BuyAmount"  j;;
  sam <-  get_N "SellAmount" j;;
  Some (oid, (bid, bam, sid, sam)).

Instance Exception__option : MonadExc unit option := {|
  raise _ _   := None;
  catch _ _ f := f tt |}.

Definition decode_response (res : http_response id)
  : option (swap_response id) :=
  let 'Response (Status _ c _) _ ob := res in
  match c with
  | 402 => Some Response__InsufficientFund
  | 404 => Some Response__NotFound
  | 200 =>
    body <- (ob : option string);;
    if from_string body is inr j
    then Response__Account     <$> getAccount          j
     <|> Response__Order       <$> getOrder            j
     <|> Response__ListAccount <$> get_list getAccount j
     <|> Response__ListOrders  <$> get_list getOrder   j
    else None
  | _ => None
  end.
