Require Import DePoolClass. 
Require Import depoolContract.SolidityNotations.
Require Import depoolContract.ProofEnvironment.

Module DePoolSpec (xt: XTypesSig) (sm: StateMonadSig).


Module StakingProxyContractClass := StakingProxyContractClass xt sm .
Import StakingProxyContractClass.
Import SolidityNotations.

Module Type DePoolSpecSig.
Import xt. Import sm.

Parameter StakingProxyContract_Ф_process_new_stake : XInteger64 -> StakingProxyContractT True .
Parameter StakingProxyContract_Ф_recover_stake : XInteger64 -> StakingProxyContractT True .

Module StakingContractClass := StakingContractClass xt sm .
Import StakingContractClass.
Import SolidityNotations.

Module Type DePoolSpecSig.
Import xt. Import sm.

Parameter StakingContract_Ф_receiveConfirmation : XInteger64 -> StakingContractT True .
Parameter StakingContract_Ф_receiveReturnedStake : XInteger64 -> StakingContractT True .
Parameter StakingContract_Ф_acceptRecoveredStake : XInteger64 -> StakingContractT True .
Parameter StakingContract_Ф_ticktock : StakingContractT True .

Parameter StakingContract_Ф__returnGrams : StakingContractT True .
Parameter StakingContract_Ф__calcLastRoundInterest : XInteger64 -> StakingContractT XInteger64 .
Parameter StakingContract_Ф__addRequest : XInteger32 -> StakingContractT True .
Parameter StakingContract_Ф_Constructor7 : XAddress -> StakingContractT True .

Parameter Stakeholder_Ф_sendTransaction : XAddress -> True . (* StakeholderT True . *)

Parameter AcceptBase_Ф_Constructor1 : (* AcceptBaseT *) True .

Module OwnerBaseClass := OwnerBaseClass xt sm .
Import OwnerBaseClass.
Import SolidityNotations.

Module Type DePoolSpecSig.
Import xt. Import sm.

Parameter OwnerBase_Ф_Constructor2 : XAddress -> OwnerBaseT True .
Parameter OwnerBase_Ф_withdrawOwnerReward : XInteger64 -> OwnerBaseT True .
Parameter OwnerBase_Ф__increaseOwnerReward : XInteger64 -> OwnerBaseT True .

Module ElectorBaseClass := ElectorBaseClass xt sm .
Import ElectorBaseClass.
Import SolidityNotations.

Module Type DePoolSpecSig.
Import xt. Import sm.

Parameter ElectorBase_Ф_Constructor3 : XAddress -> ElectorBaseT True .
Parameter ElectorBase_Ф__recoverStakeRewards : ElectorBaseT True .
Parameter ElectorBase_Ф__recoverPendingRoundStakes : XInteger32 -> ElectorBaseT True .
Parameter ElectorBase_Ф__sendRequestToElector : ElectorBase_ι_Request -> ElectorBaseT True .

Module ElectionParamsClass := ElectionParamsClass xt sm .
Import ElectionParamsClass.
Import SolidityNotations.

Module Type DePoolSpecSig.
Import xt. Import sm.

Parameter ElectionParams_Ф__getFreezingPeriod : ElectionParamsT XInteger32 .
Parameter ElectionParams_Ф__getNextElectionId : ElectionParamsT XInteger32 .
Parameter ElectionParams_Ф__getElectionsStart : ElectionParamsT XInteger32 .
Parameter ElectionParams_Ф__getElectAt : ElectionParamsT XInteger32 .
Parameter ElectionParams_Ф__isElectionOver : XInteger32 -> ElectionParamsT XBool .

Module StakeholderBaseClass := StakeholderBaseClass xt sm .
Import StakeholderBaseClass.
Import SolidityNotations.

Module Type DePoolSpecSig.
Import xt. Import sm.

Parameter StakeholderBase_Ф__haveVesting : StakeholderBase_ι_Stakeholder -> StakeholderBaseT XBool .
Parameter StakeholderBase_Ф__stakeholderSetVesting : StakeholderBase_ι_Stakeholder -> StakeholderBaseT StakeholderBase_ι_Stakeholder .
Parameter StakeholderBase_Ф__getStakeholder : XAddress -> StakeholderBaseT StakeholderBase_ι_Stakeholder .
Parameter StakeholderBase_Ф__stakeholderFetch : XAddress -> StakeholderBaseT ( (XBool # StakeholderBase_ι_Stakeholder)%sol ) .
Parameter StakeholderBase_Ф__setOrDeleteStakeholder : XAddress -> StakeholderBaseT True .
Parameter StakeholderBase_Ф__stakeholderAddStakeAndSetReinvest : StakeholderBase_ι_Stakeholder -> StakeholderBaseT StakeholderBase_ι_Stakeholder .
Parameter StakeholderBase_Ф__stakeholderRemoveStake : XAddress -> StakeholderBaseT True .
Parameter StakeholderBase_Ф__stakeholderIncreaseStakeAndUnused : StakeholderBase_ι_Stakeholder -> StakeholderBaseT StakeholderBase_ι_Stakeholder .
Parameter StakeholderBase_Ф_stakeholderDecreaseStakeAndUnused : StakeholderBase_ι_Stakeholder -> StakeholderBaseT StakeholderBase_ι_Stakeholder .
Parameter StakeholderBase_Ф__stakeholderSetReinvest : StakeholderBase_ι_Stakeholder -> StakeholderBaseT StakeholderBase_ι_Stakeholder .
Parameter StakeholderBase_Ф__stakeholderUpdateTotalStake : StakeholderBase_ι_Stakeholder -> StakeholderBaseT StakeholderBase_ι_Stakeholder .
Parameter StakeholderBase_Ф__stakeholderIncreaseUnusedStake : StakeholderBase_ι_Stakeholder -> StakeholderBaseT StakeholderBase_ι_Stakeholder .
Parameter StakeholderBase_Ф__stakeholderDecreaseUnusedStake : StakeholderBase_ι_Stakeholder -> StakeholderBaseT StakeholderBase_ι_Stakeholder .
Parameter StakeholderBase_Ф__stakeholderResetVesting : StakeholderBase_ι_Stakeholder -> StakeholderBaseT StakeholderBase_ι_Stakeholder .
Parameter StakeholderBase_Ф__stakeholderUpdateLastPaymentTime : StakeholderBase_ι_Stakeholder -> StakeholderBaseT StakeholderBase_ι_Stakeholder .

Module StakingOwnerClass := StakingOwnerClass xt sm .
Import StakingOwnerClass.
Import SolidityNotations.

Module Type DePoolSpecSig.
Import xt. Import sm.

Parameter StakingOwner_Ф_Constructor5 : XAddress -> StakingOwnerT True .
Parameter StakingOwner_Ф_updateStakingPoolAddress : XAddress -> StakingOwnerT True .
Parameter StakingOwner_Ф_getStakingPoolAddress : StakingOwnerT XAddress .
Parameter StakingOwner_Ф_getHistory : StakingOwnerT XAddress .
Parameter StakingOwner_Ф_onCodeUpgrade : StakingOwnerT True .
 
Module StakingProxyContractClass := StakingProxyContractClass xt sm .
Import StakingProxyContractClass.
Import SolidityNotations.

Module Type DePoolSpecSig.
Import xt. Import sm.

Parameter StakingProxyContract_Ф_Constructor6 : XAddress -> StakingProxyContractT True .

Module RoundsBaseClass := RoundsBaseClass xt sm .
Import RoundsBaseClass.
Import SolidityNotations.

Module Type DePoolSpecSig.
Import xt. Import sm.

Parameter RoundsBase_Ф__getLastRoundIdx : RoundsBaseT XInteger64 .
Parameter RoundsBase_Ф__addNewPoolingRound : XInteger32 -> RoundsBaseT True .
Parameter RoundsBase_Ф__getRoundsCount : RoundsBaseT XInteger8 .
Parameter RoundsBase_Ф__removeOldestRound : RoundsBaseT RoundsBase_ι_Round .
Parameter RoundsBase_Ф__getOldestRound : RoundsBaseT RoundsBase_ι_Round .
Parameter RoundsBase_Ф__setOldestRound : RoundsBase_ι_Round -> RoundsBaseT True .
Parameter RoundsBase_Ф__roundAddStakeAndVesting : RoundsBase_ι_Round -> RoundsBaseT RoundsBase_ι_Round .
Parameter RoundsBase_Ф__roundMoveStake : RoundsBase_ι_Round -> RoundsBaseT ( ( RoundsBase_ι_Round # XInteger64 )%sol ) .
Parameter RoundsBase_Ф__addPendingRound : RoundsBase_ι_Round -> RoundsBaseT True .
Parameter RoundsBase_Ф__removePendingRound : XInteger32 -> RoundsBaseT ( ( XBool # RoundsBase_ι_Round )%sol ) .
Parameter RoundsBase_Ф__roundFetchPendingRound : XInteger32 -> RoundsBaseT ( ( XBool # RoundsBase_ι_Round  )%sol ) .
Parameter RoundsBase_Ф__setOrDeletePendingRound : RoundsBase_ι_Round -> RoundsBaseT True .
Parameter RoundsBase_Ф__deletePendingRound : XInteger32 -> RoundsBaseT True .
Parameter RoundsBase_Ф_sumOfStakes : RoundsBase_ι_StakeValue -> RoundsBaseT XInteger64 .
Parameter RoundsBase_Ф_arePendingRoundsEmpty : RoundsBaseT XBool .
Parameter RoundsBase_Ф__fetchOldestPendingRound : RoundsBaseT ( ( XInteger32 # RoundsBase_ι_Round # XBool )%sol ) .
Parameter RoundsBase_Ф__getRoundsInfo : RoundsBaseT RoundsBase_ι_RoundInfo .
Parameter RoundsBase_Ф__getPendingRoundsInfo : RoundsBaseT RoundsBase_ι_RoundInfo .

(* 
contract DePool hasn't strust ... I don't know what to do...

Module DePoolClass := DePoolClass xt sm .
Import DePoolClass.
Import SolidityNotations.

Module Type DePoolSpecSig.
Import xt. Import sm.

Parameter DePool_Ф_Constructor8 : XAddress -> DePoolT True .
Parameter DePool_Ф_getOwnerReward : DePoolT XInteger64 .
Parameter DePool_Ф_getMinStake : DePoolT XInteger64 .
Parameter DePool_Ф_getValidator : DePoolT XAddress . 
Parameter DePool_Ф_getRounds : DePoolT ( ( XInteger32 # XInteger32 # RoundsBase_ι_RoundInfo )%sol ) .
Parameter DePool_Ф_getStakeholderInfo : XAddress -> DePoolT ( ( XInteger64 # XInteger64 # XInteger64 # XBool # ι_int64 # ι_М_StakeInfo )%sol ) .
Parameter DePool_Ф_getStakingInfo : DePoolT ( ( XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger32 # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 )%sol ) .
Parameter DePool_Ф_getPendingRounds : DePoolT RoundsBase_ι_RoundInfo . 

*)

Module TestElectorClass := TestElectorClass xt sm .
Import TestElectorClass.
Import SolidityNotations.

Module Type DePoolSpecSig.
Import xt. Import sm.

Parameter TestElector_Ф_Constructor9 : XInteger32 -> TestElectorT True .
Parameter TestElector_Ф_getElectionId : TestElectorT XInteger32 .
Parameter ElectorBase_Ф__recoverStakes : ElectorBaseT True .






Parameter ElectionParams_Ф__getStakingPeriod : ElectionParamsT XInteger32 .
Parameter ElectionParams_Ф__isRoundUnfrozen : XInteger32 -> ElectionParamsT XBool .
Parameter ElectionParams_Ф__setAndGetNextElectAt : ElectionParamsT XInteger32 .
Parameter StakingOwner_Ф__settimer : XAddress -> StakingOwnerT True .
Parameter StakingOwner_Ф_onTimer : StakingOwnerT True .
Parameter StakingProxyContract_Ф_process_new_stake : XInteger64 -> StakingProxyContractT True .
Parameter StakingProxyContract_Ф_recover_stake : XInteger64 -> StakingProxyContractT True .
Parameter StakingProxyContract_Ф_receive_confirmation : XInteger64 -> StakingProxyContractT True .
Parameter StakingProxyContract_Ф_receive_returned_stake : XInteger64 -> StakingProxyContractT True .
Parameter StakingProxyContract_Ф_accept_recovered_stake : XInteger64 -> StakingProxyContractT True .
Parameter RoundsBase_Ф__getLastRound : RoundsBaseT RoundsBase_ι_Round .
Parameter RoundsBase_Ф__setLastRound : RoundsBase_ι_Round -> RoundsBaseT True .
Parameter RoundsBase_Ф__getPenultimateRound : RoundsBaseT RoundsBase_ι_Round .
Parameter RoundsBase_Ф__setPenultimateRound : RoundsBase_ι_Round -> RoundsBaseT True .
Parameter RoundsBase_Ф__roundRemoveStakeInLastRound : XAddress -> RoundsBaseT ( ( XInteger64 # XInteger64 )%sol ) .
Parameter StakingContract_Ф__addNewRoundAndUpdateRounds : StakingContractT True .
Parameter StakingContract_Ф__checkPenultimateRound : StakingContractT XBool .
Parameter StakingContract_Ф__checkOldestRound : StakingContractT True .
Parameter StakingContract_Ф__sendError : XInteger32 -> StakingContractT True .
Parameter StakingContract_Ф__sendAccept : XInteger64 -> StakingContractT True .
Parameter StakingContract_Ф__requestStakesSigning : RoundsBase_ι_Round -> StakingContractT RoundsBase_ι_Round .
Parameter StakingContract_Ф__acceptPendingRoundStake : XInteger32 -> StakingContractT True .
Parameter StakingContract_Ф__acceptUnusedStake : StakingContractT True .
Parameter StakingContract_Ф__acceptRewardStake : StakingContractT True .
Parameter StakingContract_Ф__completeRoundWithSpecialChunkSize : RoundsBase_ι_Round -> StakingContractT RoundsBase_ι_Round .
Parameter StakingContract_Ф__completeRound : RoundsBase_ι_Round -> StakingContractT RoundsBase_ι_Round .
Parameter StakingContract_Ф__returnOrReinvestForStakeholder : RoundsBase_ι_Round -> StakingContractT RoundsBase_ι_Round .
Parameter StakingContract_Ф__returnOrReinvest : RoundsBase_ι_Round -> StakingContractT RoundsBase_ι_Round .
Parameter StakingContract_Ф__getMsgValueAndSendErrorIfNeeded : XInteger64 -> StakingContractT ( ( XInteger64 # XBool )%sol ) .
Parameter StakingContract_Ф_investStake : XInteger64 -> StakingContractT True .
Parameter StakingContract_Ф_addVesting : XAddress -> StakingContractT True .
Parameter StakingContract_Ф_removeStake : XBool -> StakingContractT True .
Parameter StakingContract_Ф_setReinvest : XBool -> StakingContractT True .
Parameter StakingContract_Ф_transferStake : XAddress -> StakingContractT True .
Parameter StakingContract_Ф_processNewStake : XInteger64 -> StakingContractT True .
Parameter ElectorBase_Ф__sendRequestToElector : ElectorBase_ι_Request -> ElectorBaseT True .
Parameter StakingContract_Ф_ticktock : StakingContractT True .
Parameter StakingContract_Ф_forceCompletePendingRound : XBool -> StakingContractT True .
Parameter StakingContract_Ф_completePendingRoundChunk : XInteger32 -> StakingContractT True .
Parameter StakingContract_Ф_receiveReturnedStake : XInteger64 -> StakingContractT True .
Parameter StakingContract_Ф_acceptRecoveredStake : XInteger64 -> StakingContractT True .
Parameter StakingContract_Ф_terminator : XInteger8 -> StakingContractT True . 
Parameter ElectionParams_Ф_Constructor4 : XInteger32 -> ElectionParamsT True .
Parameter StakingOwner_Ф_initTimer : XAddress -> StakingOwnerT True .
Parameter StakingOwner_Ф_upgrade : TvmCell -> StakingOwnerT True .
Parameter RoundsBase_Ф__roundMoveStakes : XAddress -> RoundsBaseT XInteger64 .
Parameter StakingContract_Ф__completePendingRound : RoundsBase_ι_Round -> StakingContractT RoundsBase_ι_Round .



(* Parameter Participant_Ф_receiveRewardStake : XInteger32 -> ParticipantT True .
Parameter Participant_Ф_receiveAnswer : XInteger32 -> ParticipantT True .
Parameter Participant_Ф_receiveRewardStake : XInteger32 -> ParticipantT True .
Parameter Participant_Ф_receiveAnswer : XInteger32 -> ParticipantT True .
 *)