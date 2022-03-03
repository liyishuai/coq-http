From JSON Require Export
     Operator.
From AsyncTest Require Export
     Classes
     Operator.
From App Require Export
     AppMessage.
Import
  XNotations.
Open Scope jexp_scope.

#[global]
Instance XEncode__Request : XEncode (swap_request id) :=
  fun r =>
    jobj "method" (swap_path r) +
    match r with
    | Request__ListAccount uid =>
      jobj "user" uid
    | Request__TakeOrder uid oid =>
      jobj "user" uid + jobj "order" oid
    | Request__MakeOrder uid bt ba st sa =>
      jobj "user" uid + jobj "buyTicker" bt + jobj "buyAmount" ba +
      jobj "sellTicker" st + jobj "sellAmount" sa
    | Request__Deposit  uid t a
    | Request__Withdraw uid t a =>
      jobj "user" uid + jobj "ticker" t + jobj "amount" a
    | Request__Clean
    | Request__ListOrders => Jexp__Object []
    end.

Close Scope jexp_scope.

Import
  Encode
  JNotations.
Open Scope json_scope.

#[global]
Instance JEncode__Account : JEncode (accountT id) :=
  fun a => let '(aid, (uid, tkr, amt)) := a in
         jobj "ID"          aid +
         jobj "UserID"      uid +
         jobj "AssetTicker" tkr +
         jobj "Amount"      amt.

#[global]
Instance JEncode__Order : JEncode (orderT id) :=
  fun o => let '(oid, (bid, bam, sid, sam)) := o in
         jobj "ID"         oid +
         jobj "BuyerID"    bid +
         jobj "BuyAmount"  bam +
         jobj "SellerID"   sid +
         jobj "SellAmount" sam.

#[global]
Instance JEncode__Response : JEncode (swap_response id) :=
  fun r =>
    jobj "code" (swap_code r) +
    match r with
    | Response__ListAccount l => jobj "accounts" l
    | Response__ListOrders  l => jobj "orders"   l
    | Response__Account x
    | Response__Order   x     => encode x
    | _ => JSON__Object []
    end.

Close Scope json_scope.
