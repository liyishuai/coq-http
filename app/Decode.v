From ExtLib Require Export
     Applicative.
From JSON Require Export
     Decode.
From App Require Export
     AppMessage.
Export
  ApplicativeNotation.

Instance JDecode__Request : JDecode (swap_request id) :=
  fun j =>
    m <- dpath "method" j;;
    match m with
    | "clean"       => ret Request__Clean
    | "listAccount" => Request__ListAccount <$> dpath "user" j
    | "takeOrder"   => liftA2 Request__TakeOrder (dpath "user" j) (dpath "order" j)
    | "makeOrder"   => liftA2 Request__MakeOrder (dpath "user" j)
                             (dpath "buyTicker" j) <*> (dpath "buyAmount" j) <*>
                             (dpath "sellTicker" j) <*> (dpath "sellAmount" j)
    | "deposit"     => liftA2 Request__Deposit (dpath "user" j) (dpath "ticker" j)
                             <*> (dpath "amount" j)
    | "withdraw"    => liftA2 Request__Withdraw (dpath "user" j) (dpath "ticker" j)
                             <*> (dpath "amount" j)
    | _             => ret Request__ListOrders
    end.

Instance JDecode__Account : JDecode (accountT id) :=
  fun j =>
    aid <- dpath "ID"          j;;
    uid <- dpath "UserID"      j;;
    tcr <- dpath "AssetTicker" j;;
    amt <- dpath "Amount"      j;;
    ret (aid, (uid, tcr, amt)).

Instance JDecode__Order : JDecode (orderT id) :=
  fun j =>
    oid <- dpath "ID"         j;;
    bid <- dpath "BuyerID"    j;;
    bam <- dpath "BuyAmount"  j;;
    sid <- dpath "BuyerID"    j;;
    sam <- dpath "SellAmount" j;;
    ret (oid, (bid, bam, sid, sam)).

Instance JDecode__Response : JDecode (swap_response id) :=
  fun j =>
    c <- dpath "code" j;;
    match c with
    | 200 =>
      Response__ListAccount <$> dpath' decode__list "accounts" j <|>
      Response__ListOrders  <$> dpath' decode__list "orders"   j <|>
      Response__Account     <$> decode j                       <|>
      Response__Order       <$> decode j
    | 204 => ret Response__NoContent
    | 400 => ret Response__BadRequest
    | 402 => ret Response__InsufficientFund
    | 404 => ret Response__NotFound
    | _   => ret Response__InternalServerError
    end.
