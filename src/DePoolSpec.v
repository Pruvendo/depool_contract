
Require Import depoolContract.SolidityNotations.
Require Import depoolContract.ProofEnvironment. 
Require Import depoolContract.DePoolClass.


Module DePoolSpec (xt: XTypesSig) (sm: StateMonadSig).
Module LedgerClass := LedgerClass xt sm .
Import LedgerClass.
Import SolidityNotations.

Module Type DePoolSpecSig.
Import xt. Import sm.

Parameter ProxyBase_Ф__recoverStake : XAddress -> XInteger64 -> XAddress -> LedgerT True .
Parameter ProxyBase_Ф__sendElectionRequest : XAddress -> XInteger64 -> XInteger64 -> DePoolLib_ι_Request -> XAddress -> LedgerT True .
Parameter ConfigParamsBase_Ф_getCurValidatorData : LedgerT ( XErrorValue ( XInteger256 # XInteger32 # XInteger32 )%sol XInteger ) .
Parameter ConfigParamsBase_Ф_getPrevValidatorHash : LedgerT ( XErrorValue XInteger XInteger ) .
Parameter ConfigParamsBase_Ф_roundTimeParams : LedgerT ( XErrorValue ( XInteger32 # XInteger32 # XInteger32 # XInteger32 )%sol XInteger ) .
Parameter ConfigParamsBase_Ф_getMaxStakeFactor : LedgerT ( XErrorValue XInteger32 XInteger ) .
Parameter ConfigParamsBase_Ф_getElector : LedgerT ( XErrorValue XAddress XInteger ) .
Parameter ParticipantBase_Ф__setOrDeleteParticipant : XAddress -> DePoolLib_ι_Participant -> LedgerT True .
Parameter ParticipantBase_Ф_getOrCreateParticipant  : XAddress -> LedgerT DePoolLib_ι_Participant .
Parameter DePoolProxyContract_Ф_constructor5 : LedgerT ( XErrorValue True XInteger ) .
Parameter DePoolProxyContract_Ф_process_new_stake : XInteger64 -> XInteger256 -> XInteger32 -> XInteger32 -> XInteger256 -> XList XInteger8 -> XAddress -> LedgerT ( XErrorValue True XInteger ) .
Parameter DePoolProxyContract_Ф_onStakeAccept : XInteger64 -> XInteger32 -> LedgerT True .
Parameter DePoolProxyContract_Ф_onStakeReject : XInteger64 -> XInteger32 -> LedgerT True .
Parameter DePoolProxyContract_Ф_recover_stake : XInteger64 -> XAddress -> LedgerT ( XErrorValue True XInteger ) .
Parameter DePoolProxyContract_Ф_onSuccessToRecoverStake : XInteger64 -> LedgerT True .
Parameter DePoolProxyContract_Ф_getProxyInfo : LedgerT ( XAddress # XInteger64 )%sol .
Parameter RoundsBase_Ф__addStakes : RoundsBase_ι_Round -> DePoolLib_ι_Participant -> XAddress -> XInteger64 -> XMaybe RoundsBase_ι_InvestParams -> XMaybe RoundsBase_ι_InvestParams -> LedgerT ( RoundsBase_ι_Round # DePoolLib_ι_Participant )%sol .
Parameter RoundsBase_Ф_stakeSum : RoundsBase_ι_StakeValue -> LedgerT XInteger64 .
Parameter RoundsBase_Ф_transferStakeInOneRound : RoundsBase_ι_Round -> DePoolLib_ι_Participant -> DePoolLib_ι_Participant -> XAddress -> XAddress -> XInteger64 -> XInteger64 -> LedgerT ( RoundsBase_ι_Round # XInteger64 # XInteger64 # DePoolLib_ι_Participant # DePoolLib_ι_Participant )%sol .
Parameter RoundsBase_Ф_isRoundPre0 : XInteger64 -> LedgerT XBool .
Parameter RoundsBase_Ф_isRound0 : XInteger64 -> LedgerT XBool .
Parameter RoundsBase_Ф_isRound1 : XInteger64 -> LedgerT XBool .
Parameter RoundsBase_Ф_isRound2 : XInteger64 -> LedgerT XBool .
Parameter RoundsBase_Ф_roundAt : XInteger64 -> LedgerT RoundsBase_ι_Round .
Parameter RoundsBase_Ф_getRoundPre0 : LedgerT RoundsBase_ι_Round .
Parameter RoundsBase_Ф_getRound0 : LedgerT RoundsBase_ι_Round .
Parameter RoundsBase_Ф_getRound1 : LedgerT RoundsBase_ι_Round .
Parameter RoundsBase_Ф_getRound2 : LedgerT RoundsBase_ι_Round .
Parameter RoundsBase_Ф_setRound : XInteger -> RoundsBase_ι_Round -> LedgerT True .
Parameter RoundsBase_Ф_setRoundPre0 : RoundsBase_ι_Round -> LedgerT True .
Parameter RoundsBase_Ф_setRound0 : RoundsBase_ι_Round -> LedgerT True .
Parameter RoundsBase_Ф_setRound1 : RoundsBase_ι_Round -> LedgerT True .
Parameter RoundsBase_Ф_setRound2 : RoundsBase_ι_Round -> LedgerT True .
Parameter RoundsBase_Ф_fetchRound : XInteger64 -> LedgerT (XMaybe RoundsBase_ι_Round)  .
Parameter ParticipantBase_Ф_fetchParticipant : XAddress -> LedgerT (XMaybe ( DePoolLib_ι_Participant) ) .
Parameter RoundsBase_Ф_minRound : LedgerT (XMaybe (XInteger64 # RoundsBase_ι_Round)%sol) .
Parameter RoundsBase_Ф_nextRound : XInteger64 -> LedgerT (XMaybe (XInteger64 # RoundsBase_ι_Round)%sol) .
Parameter RoundsBase_Ф_withdrawStakeInPoolingRound : DePoolLib_ι_Participant -> XAddress -> XInteger64 -> XInteger64 -> LedgerT ( XInteger64 # DePoolLib_ι_Participant )%sol .
Parameter RoundsBase_Ф_toTruncatedRound : RoundsBase_ι_Round -> LedgerT RoundsBase_ι_TruncatedRound .
Parameter RoundsBase_Ф_getRounds : LedgerT (XHMap XInteger64 RoundsBase_ι_TruncatedRound) .
Parameter DePoolContract_Ф_generateRound : LedgerT RoundsBase_ι_Round .
Parameter DePoolContract_Ф_Constructor6 : XInteger64 -> XInteger64 -> TvmCell -> XAddress -> XInteger8 -> LedgerT ( XErrorValue True XInteger ) .
Parameter DePoolContract_Ф_setLastRoundInfo : RoundsBase_ι_Round -> LedgerT True .
Parameter DePoolContract_Ф__returnChange : LedgerT True .
Parameter DePoolContract_Ф__sendError : XInteger32 -> XInteger64 -> LedgerT True .
Parameter DePoolContract_Ф_startRoundCompleting : RoundsBase_ι_Round -> RoundsBase_ι_CompletionReason -> LedgerT RoundsBase_ι_Round .
Parameter DePoolContract_Ф_cutWithdrawalValue : RoundsBase_ι_InvestParams -> XBool -> XInteger32 -> LedgerT ( (XMaybe RoundsBase_ι_InvestParams) # XInteger64 # XInteger64 )%sol .
Parameter DePoolContract_Ф__returnOrReinvestForParticipant : RoundsBase_ι_Round -> RoundsBase_ι_Round -> XAddress -> RoundsBase_ι_StakeValue -> XBool -> XInteger32 -> LedgerT ( XErrorValue ( RoundsBase_ι_Round # RoundsBase_ι_Round )%sol XInteger ) .
Parameter DePoolContract_Ф__returnOrReinvest : RoundsBase_ι_Round -> XInteger8 -> LedgerT ( XErrorValue RoundsBase_ι_Round XInteger ) .
Parameter DePoolContract_Ф_sendAcceptAndReturnChange128 : XInteger64 -> LedgerT True .
Parameter DePoolContract_Ф_sendAcceptAndReturnChange : LedgerT True .
Parameter DePoolContract_Ф_addOrdinaryStake : XInteger64 -> LedgerT ( XErrorValue  True XInteger ) .
Parameter DePoolContract_Ф_addVestingOrLock : XInteger64 -> XAddress -> XInteger32 -> XInteger32 -> XBool -> LedgerT True .
Parameter DePoolContract_Ф_addVestingStake : XInteger64 -> XAddress -> XInteger32 -> XInteger32 -> LedgerT True .
Parameter DePoolContract_Ф_addLockStake : XInteger64 -> XAddress -> XInteger32 -> XInteger32 -> LedgerT True .
Parameter DePoolContract_Ф_withdrawPart : XInteger64 -> LedgerT (XErrorValue True XInteger) .
Parameter DePoolContract_Ф_withdrawAll : LedgerT (XErrorValue True XInteger) .
Parameter DePoolContract_Ф_cancelWithdrawal : LedgerT (XErrorValue True XInteger) .
Parameter DePoolContract_Ф_transferStake : XAddress -> XInteger64 -> LedgerT ( XErrorValue  True XInteger ) .
Parameter DePoolContract_Ф_totalParticipantFunds : XInteger64 -> LedgerT XInteger64 .
Parameter DePoolContract_Ф_checkPureDePoolBalance : LedgerT XBool .
Parameter DePoolContract_Ф_participateInElections : XInteger64 -> XInteger256 -> XInteger32 -> XInteger32 -> XInteger256 -> XList XInteger8 -> LedgerT ( XErrorValue True XInteger ) .
Parameter DePoolContract_Ф_updateRound2 : RoundsBase_ι_Round -> XInteger256 -> XInteger256 -> XInteger32 -> LedgerT RoundsBase_ι_Round .
Parameter DePoolContract_Ф_isEmptyRound : RoundsBase_ι_Round -> LedgerT XBool .
Parameter DePoolContract_Ф_updateRounds : LedgerT (XErrorValue (XValueValue True) XInteger) .
Parameter DePoolContract_Ф_ticktock : LedgerT ( XErrorValue True XInteger ) .
Parameter DePoolContract_Ф_acceptRewardAndStartRoundCompleting : RoundsBase_ι_Round -> XInteger64 -> LedgerT RoundsBase_ι_Round .
Parameter DePoolContract_Ф_onSuccessToRecoverStake : XInteger64 -> XAddress -> LedgerT ( XErrorValue True XInteger ) .
Parameter DePoolContract_Ф_onFailToRecoverStake : XInteger64 -> XAddress -> LedgerT ( XErrorValue True XInteger ) .
Parameter DePoolContract_Ф_terminator : LedgerT ( XErrorValue True XInteger ) .
Parameter DePoolContract_Ф_onBounce : TvmSlice -> LedgerT (XErrorValue True XInteger) .
Parameter DePoolContract_Ф_completeRoundWithChunk : XInteger64 -> XInteger8 -> LedgerT (XErrorValue ( XValueValue True ) XInteger ) .
Parameter DePoolContract_Ф_completeRound : XInteger64 -> XInteger32 -> LedgerT ( XErrorValue True XInteger ) .
Parameter DePoolContract_Ф_onStakeAccept : XInteger64 -> XInteger32 -> XAddress -> LedgerT ( XErrorValue True XInteger ) .
Parameter DePoolContract_Ф_onStakeReject : XInteger64 -> XInteger32 -> XAddress -> LedgerT ( XErrorValue True XInteger ) .
Parameter DePoolContract_Ф_receiveFunds : LedgerT True .
Parameter DePool_Ф_getParticipantInfo : XAddress -> LedgerT (XErrorValue ( XInteger64 # XInteger64 # XBool # XInteger64 # (XHMap XInteger64 XInteger64) # (XHMap XInteger64 RoundsBase_ι_InvestParams) # (XHMap XInteger64 RoundsBase_ι_InvestParams) ) XInteger)%sol.
Parameter DePoolContract_Ф_setValidatorRewardFraction :  XInteger8 -> LedgerT ( XErrorValue True XInteger ) .
Parameter DePool_Ф_getParticipants : LedgerT (XArray XAddress) .
Parameter DePoolContract_Ф_withdrawFromPoolingRound : XInteger64 -> LedgerT (XErrorValue True XInteger) .

End DePoolSpecSig.

End DePoolSpec.
