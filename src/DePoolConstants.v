
Require Export Coq.Program.Basics.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Program.Combinators.
Require Export ZArith.
Require Export Lists.List.
Require Export Ascii.
Require Export Strings.String. 
Require Import Coq.Strings.Byte.

Require Import depoolContract.Lib.HexNotations.
Import HexNotations.

Module DePoolConsts.

Local Open Scope solidity_scope_hex.
Local Open Scope solidity_scope_dec.

Local Notation "a 'e' b" := ( (a * 10^b)%Z )(at level 60, right associativity) . 
Local Notation "'0.09' '*' 'ton'" := (90000000%Z). 
Local Notation "'0.5' '*' 'ton'" := (500000000%Z). 

Definition ton := 1000000000%Z . 
Definition milliton := 1000%Z . 
Definition minutes := 60%Z . 
 
Definition Errors_ι_IS_NOT_OWNER := 101%Z . 
Definition Errors_ι_IS_NOT_PROXY := 107%Z . 
Definition Errors_ι_IS_EXT_MSG := 108%Z . 
Definition Errors_ι_IS_NOT_VALIDATOR := 113%Z . 
Definition Errors_ι_DEPOOL_IS_CLOSED := 114%Z . 
Definition Errors_ι_NO_SUCH_PARTICIPANT := 116%Z . 
Definition Errors_ι_IS_NOT_DEPOOL := 120%Z . 
Definition Errors_ι_INVALID_ROUND_STEP := 125%Z . 
Definition Errors_ι_INVALID_QUERY_ID := 126%Z . 
Definition Errors_ι_IS_NOT_ELECTOR := 127%Z . 
Definition Errors_ι_BAD_STAKES := 129%Z . 
Definition Errors_ι_CONSTRUCTOR_NO_PUBKEY := 130%Z . 
Definition Errors_ι_VALIDATOR_IS_NOT_STD := 133%Z . 
Definition Errors_ι_BAD_PART_REWARD := 138%Z . 
Definition Errors_ι_BAD_PROXY_CODE := 141%Z . 
Definition Errors_ι_NOT_WORKCHAIN0 := 142%Z . 
Definition Errors_ι_NEW_VALIDATOR_FRACTION_MUST_BE_GREATER_THAN_OLD := 143%Z . 
Definition Errors_ι_FRACTION_MUST_NOT_BE_ZERO := 144%Z . 
Definition Errors_ι_BAD_BALANCE_THRESHOLD := 145%Z . 
Definition Errors_ι_BAD_ACCOUNT_BALANCE := 146%Z . 
Definition InternalErrors_ι_ERROR507 := 507%Z . 
Definition InternalErrors_ι_ERROR508 := 508%Z . 
Definition InternalErrors_ι_ERROR509 := 509%Z . 
Definition InternalErrors_ι_ERROR511 := 511%Z . 
Definition InternalErrors_ι_ERROR513 := 513%Z . 
Definition InternalErrors_ι_ERROR516 := 516%Z . 
Definition InternalErrors_ι_ERROR517 := 517%Z . 
Definition InternalErrors_ι_ERROR518 := 518%Z . 
Definition InternalErrors_ι_ERROR519 := 519%Z . 
Definition InternalErrors_ι_ERROR521 := 521%Z . 
Definition InternalErrors_ι_ERROR522 := 522%Z . 
Definition InternalErrors_ι_ERROR523 := 523%Z . 
Definition InternalErrors_ι_ERROR524 := 524%Z . 
Definition InternalErrors_ι_ERROR525 := 525%Z . 
Definition InternalErrors_ι_ERROR526 := 526%Z . 
Definition InternalErrors_ι_ERROR527 := 527%Z . 
Definition InternalErrors_ι_ERROR528 := 528%Z . 
Definition DePoolLib_ι_PROXY_FEE := (0.09 * ton )%Z . 
Definition DePoolLib_ι_MIN_PROXY_BALANCE := (1 * ton )%Z . 
Definition DePoolLib_ι_PROXY_CONSTRUCTOR_FEE := (1 * ton )%Z . 
Definition DePoolLib_ι_DEPOOL_CONSTRUCTOR_FEE := (1 * ton )%Z . 
Definition DePoolLib_ι_ELECTOR_FEE := (1 * ton )%Z . 
Definition DePoolLib_ι_MAX_UINT64 := "FFFFFFFFFFFFFFFF" . 
Definition DePoolLib_ι_MAX_TIME := "FFFFFFFF" . 
Definition DePoolLib_ι_ELECTOR_UNFREEZE_LAG := (1 * minutes )%Z . 
Definition DePool_ι_STAKE_FEE := (0.5 * ton )%Z . 
Definition DePool_ι_RET_OR_REINV_FEE := (50 * milliton )%Z . 
Definition DePool_ι_MAX_MSGS_PER_TR := 25%Z . 
Definition DePool_ι_MAX_QTY_OF_OUT_ACTIONS := 250%Z . 
Definition DePool_ι_VALUE_FOR_SELF_CALL := (1 * ton )%Z . 
Definition DePool_ι_PROXY_CODE_HASH := "481d7f583b458a1672ee602f66e8aa8d2f99d3cd9ece2eaa20e25c7ddf4c7f4a". 
Definition DePool_ι_STATUS_SUCCESS := 0%Z . 
Definition DePool_ι_STATUS_STAKE_TOO_SMALL := 1%Z . 
Definition DePool_ι_STATUS_DEPOOL_CLOSED := 3%Z . 
Definition DePool_ι_STATUS_NO_PARTICIPANT := 6%Z . 
Definition DePool_ι_STATUS_PARTICIPANT_ALREADY_HAS_VESTING := 9%Z . 
Definition DePool_ι_STATUS_WITHDRAWAL_PERIOD_GREATER_TOTAL_PERIOD := 10%Z . 
Definition DePool_ι_STATUS_TOTAL_PERIOD_MORE_18YEARS := 11%Z . 
Definition DePool_ι_STATUS_WITHDRAWAL_PERIOD_IS_ZERO := 12%Z . 
Definition DePool_ι_STATUS_TOTAL_PERIOD_IS_NOT_DIVISIBLE_BY_WITHDRAWAL_PERIOD := 13%Z . 
Definition DePool_ι_STATUS_REMAINING_STAKE_LESS_THAN_MINIMAL := 16%Z . 
Definition DePool_ι_STATUS_PARTICIPANT_ALREADY_HAS_LOCK := 17%Z . 
Definition DePool_ι_STATUS_TRANSFER_AMOUNT_IS_TOO_BIG := 18%Z . 
Definition DePool_ι_STATUS_TRANSFER_SELF := 19%Z . 
Definition DePool_ι_STATUS_TRANSFER_TO_OR_FROM_VALIDATOR := 20%Z . 
Definition DePool_ι_STATUS_FEE_TOO_SMALL := 21%Z . 
Definition DePool_ι_STATUS_INVALID_ADDRESS := 22%Z . 
Definition DePool_ι_STATUS_INVALID_BENEFICIARY := 23%Z . 
Definition DePool_ι_STATUS_NO_ELECTION_ROUND := 24%Z . 
Definition DePool_ι_STATUS_INVALID_ELECTION_ID := 25%Z . 
Definition DePool_ι_CRITICAL_THRESHOLD := (10 * ton )%Z . 
Definition DePoolHelper_ι_TICKTOCK_FEE := 1 e 9 . 
Definition DePoolHelper_ι__timerRate := 400000%Z . 
Definition DePoolHelper_ι__fwdFee := 1000000%Z . 
Definition DePoolHelper_ι__epsilon := 1 e 9 . 
Definition DePoolProxyContract_ι_ERROR_IS_NOT_DEPOOL := 102%Z . 
Definition DePoolProxyContract_ι_ERROR_BAD_BALANCE := 103%Z . 

End DePoolConsts.