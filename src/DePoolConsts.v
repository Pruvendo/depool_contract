
 Require Import depoolContract.SolidityNotations. 
(*  Require Import depoolContract.ProofEnvironment. *) 
 (* Require Import depoolContract.DePoolClass.  *)
 
 
 Module Type DePoolConstsTypesSig (xt: XTypesSig) (sm: StateMonadSig). 
 Module SolidityNotations := SolidityNotations xt sm .  
 Import SolidityNotations. 
 
 Import xt. (* Import sm.  *)
 
Parameter Errors_ι_IS_NOT_OWNER : XInteger . 
Parameter Errors_ι_IS_NOT_PROXY : XInteger . 
Parameter Errors_ι_IS_EXT_MSG : XInteger . 
Parameter Errors_ι_IS_NOT_VALIDATOR : XInteger . 
Parameter Errors_ι_DEPOOL_IS_CLOSED : XInteger . 
Parameter Errors_ι_NO_SUCH_PARTICIPANT : XInteger . 
Parameter Errors_ι_IS_NOT_DEPOOL : XInteger . 
Parameter Errors_ι_INVALID_ROUND_STEP : XInteger . 
Parameter Errors_ι_INVALID_QUERY_ID : XInteger . 
Parameter Errors_ι_IS_NOT_ELECTOR : XInteger . 
Parameter Errors_ι_BAD_STAKES : XInteger8 . 
Parameter Errors_ι_CONSTRUCTOR_NO_PUBKEY : XInteger8 . 
Parameter Errors_ι_VALIDATOR_IS_NOT_STD : XInteger8 . 
Parameter Errors_ι_BAD_PART_REWARD : XInteger8 . 
Parameter Errors_ι_BAD_PROXY_CODE : XInteger8 . 
Parameter Errors_ι_NOT_WORKCHAIN0 : XInteger8 . 
Parameter Errors_ι_NEW_VALIDATOR_FRACTION_MUST_BE_GREATER_THAN_OLD : XInteger8 . 
Parameter Errors_ι_FRACTION_MUST_NOT_BE_ZERO : XInteger8 . 
Parameter Errors_ι_BAD_ACCOUNT_BALANCE : XInteger8 . 
Parameter InternalErrors_ι_ERROR507 : XInteger . 
Parameter InternalErrors_ι_ERROR508 : XInteger . 
Parameter InternalErrors_ι_ERROR509 : XInteger . 
Parameter InternalErrors_ι_ERROR511 : XInteger . 
Parameter InternalErrors_ι_ERROR513 : XInteger . 
Parameter InternalErrors_ι_ERROR516 : XInteger . 
Parameter InternalErrors_ι_ERROR517 : XInteger . 
Parameter InternalErrors_ι_ERROR518 : XInteger . 
Parameter InternalErrors_ι_ERROR519 : XInteger . 
Parameter InternalErrors_ι_ERROR521 : XInteger . 
Parameter InternalErrors_ι_ERROR522 : XInteger . 
Parameter InternalErrors_ι_ERROR523 : XInteger . 
Parameter InternalErrors_ι_ERROR524 : XInteger . 
Parameter InternalErrors_ι_ERROR525 : XInteger . 
Parameter InternalErrors_ι_ERROR526 : XInteger . 
Parameter InternalErrors_ι_ERROR527 : XInteger . 
Parameter InternalErrors_ι_ERROR528 : XInteger . 
Parameter DePoolLib_ι_PROXY_FEE : XInteger64 . 
Parameter DePoolLib_ι_MIN_PROXY_BALANCE : XInteger64 . 
Parameter DePoolLib_ι_PROXY_CONSTRUCTOR_FEE : XInteger64 . 
Parameter DePoolLib_ι_DEPOOL_CONSTRUCTOR_FEE : XInteger64 . 
Parameter DePoolLib_ι_ELECTOR_FEE : XInteger64 . 
Parameter DePoolLib_ι_MAX_UINT64 : XInteger64 . 
Parameter DePoolLib_ι_MAX_TIME : XInteger32 . 
Parameter DePoolLib_ι_ELECTOR_UNFREEZE_LAG : XInteger64 . 
Parameter DePool_ι_STAKE_FEE : XInteger64 . 
Parameter DePool_ι_RET_OR_REINV_FEE : XInteger64 . 
Parameter DePool_ι_MAX_MSGS_PER_TR : XInteger8 . 
Parameter DePool_ι_MAX_QTY_OF_OUT_ACTIONS : XInteger16 . 
Parameter DePool_ι_VALUE_FOR_SELF_CALL : XInteger64 . 
Parameter DePool_ι_PROXY_CODE_HASH : XInteger256 . 
Parameter DePool_ι_STATUS_SUCCESS : XInteger8 . 
Parameter DePool_ι_STATUS_STAKE_TOO_SMALL : XInteger8 . 
Parameter DePool_ι_STATUS_DEPOOL_CLOSED : XInteger8 . 
Parameter DePool_ι_STATUS_NO_PARTICIPANT : XInteger8 . 
Parameter DePool_ι_STATUS_PARTICIPANT_ALREADY_HAS_VESTING : XInteger8 . 
Parameter DePool_ι_STATUS_WITHDRAWAL_PERIOD_GREATER_TOTAL_PERIOD : XInteger8 . 
Parameter DePool_ι_STATUS_TOTAL_PERIOD_MORE_18YEARS : XInteger8 . 
Parameter DePool_ι_STATUS_WITHDRAWAL_PERIOD_IS_ZERO : XInteger8 . 
Parameter DePool_ι_STATUS_TOTAL_PERIOD_IS_NOT_DIVISIBLE_BY_WITHDRAWAL_PERIOD : XInteger8 . 
Parameter DePool_ι_STATUS_REMAINING_STAKE_LESS_THAN_MINIMAL : XInteger8 . 
Parameter DePool_ι_STATUS_PARTICIPANT_ALREADY_HAS_LOCK : XInteger8 . 
Parameter DePool_ι_STATUS_TRANSFER_AMOUNT_IS_TOO_BIG : XInteger8 . 
Parameter DePool_ι_STATUS_TRANSFER_SELF : XInteger8 . 
Parameter DePool_ι_STATUS_TRANSFER_TO_OR_FROM_VALIDATOR : XInteger8 . 
Parameter DePool_ι_STATUS_FEE_TOO_SMALL : XInteger8 . 
Parameter DePool_ι_STATUS_INVALID_ADDRESS : XInteger8 . 
Parameter DePool_ι_STATUS_INVALID_BENEFICIARY : XInteger8 . 
Parameter DePool_ι_STATUS_NO_ELECTION_ROUND : XInteger8 . 
Parameter DePool_ι_STATUS_INVALID_ELECTION_ID : XInteger8 . 
Parameter DePool_ι_CRITICAL_THRESHOLD : XInteger64 . 
Parameter DePoolProxyContract_ι_ERROR_IS_NOT_DEPOOL : XInteger . 
Parameter DePoolProxyContract_ι_ERROR_BAD_BALANCE : XInteger . 

End DePoolConstsTypesSig.
