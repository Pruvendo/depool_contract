Require Import depoolContract.depoolClass. 
Require Import depoolContract.SolidityNotations.
Require Import depoolContract.ProofEnvironment.

Module StakingSpec (xt: XTypesSig) (sm: StateMonadSig).
Module StakingContractClass := StakingContractClass xt sm .
Import StakingContractClass.
Import SolidityNotations.

Module Type StakingSpecSig.
Import xt. Import sm.

Parameter Participant_Ф_receiveRewardStake : XInteger32 -> ParticipantT True .
Parameter Participant_Ф_receiveAnswer : XInteger32 -> ParticipantT True .
Parameter Participant_Ф_receiveRewardStake : XInteger32 -> ParticipantT True .
Parameter Participant_Ф_receiveAnswer : XInteger32 -> ParticipantT True .
Parameter StakingProxyContract_Ф_process_new_stake : XInteger64 -> StakingProxyContractT True .
Parameter StakingProxyContract_Ф_recover_stake : XInteger64 -> StakingProxyContractT True .
Parameter StakingContract_Ф_receiveConfirmation : XInteger64 -> StakingContractT True .
Parameter StakingContract_Ф_receiveReturnedStake : XInteger64 -> StakingContractT ( XInteger64 # XInteger32 ) .
Parameter StakingContract_Ф_acceptRecoveredStake : XInteger64 -> StakingContractT True .
Parameter StakingContract_Ф_ticktock : StakingContractT True .
Parameter Stakeholder_Ф_sendTransaction : XAddress -> StakeholderT True .
Parameter AcceptBase_Ф_Constructor1 : AcceptBaseT True .
Parameter OwnerBase_Ф_Constructor2 : XAddress -> OwnerBaseT True .
Parameter OwnerBase_Ф_withdrawOwnerReward : XInteger64 -> OwnerBaseT True .
Parameter OwnerBase_Ф__increaseOwnerReward : XInteger64 -> OwnerBaseT True .
Parameter ElectorBase_Ф_Constructor3 : XAddress -> ElectorBaseT True .
Parameter ElectionParams_Ф__getFreezingPeriod : ElectionParamsT XInteger32 .
Parameter ElectionParams_Ф__getNextElectionId : ElectionParamsT XInteger32 .
Parameter ElectionParams_Ф__getElectionsStart : ElectionParamsT XInteger32 .
Parameter ElectionParams_Ф__getElectAt : ElectionParamsT XInteger32 .
Parameter ElectionParams_Ф__isElectionOver : XInteger32 -> ElectionParamsT XBool .
Parameter StakeholderBase_Ф__haveVesting : ι_Stakeholder -> StakeholderBaseT XBool .
Parameter StakeholderBase_Ф__stakeholderSetVesting : ι_Stakeholder -> StakeholderBaseT ι_Stakeholder .
Parameter StakeholderBase_Ф__stakeholderExists : XAddress -> StakeholderBaseT XBool .
Parameter StakeholderBase_Ф__getStakeholder : XAddress -> StakeholderBaseT ι_Stakeholder .
Parameter StakeholderBase_Ф__stakeholderFetch : XAddress -> StakeholderBaseT ( XBool # ι_Stakeholder ) .
Parameter StakeholderBase_Ф__setOrDeleteStakeholder : XAddress -> StakeholderBaseT True .
Parameter StakeholderBase_Ф__stakeholderUpdateStake : XAddress -> StakeholderBaseT True .
Parameter StakeholderBase_Ф__stakeholderUpdateStake2 : ι_Stakeholder -> StakeholderBaseT ι_Stakeholder .
Parameter StakeholderBase_Ф__stakeholderRemoveStake : XAddress -> StakeholderBaseT True .
Parameter StakeholderBase_Ф__stakeholderIncreaseTotalAndUnused : ι_Stakeholder -> StakeholderBaseT ι_Stakeholder .
Parameter StakeholderBase_Ф__stakeholderDecreaseTotalAndUnused : ι_Stakeholder -> StakeholderBaseT ι_Stakeholder .
Parameter StakeholderBase_Ф__stakeholderSetReinvest : XAddress -> StakeholderBaseT True .
Parameter StakeholderBase_Ф__stakeholderSetReinvest2 : ι_Stakeholder -> StakeholderBaseT ι_Stakeholder .
Parameter StakeholderBase_Ф__stakeholderUpdateGrossReward : ι_Stakeholder -> StakeholderBaseT ι_Stakeholder .
Parameter StakeholderBase_Ф__stakeholderUpdateTotalStake : ι_Stakeholder -> StakeholderBaseT ι_Stakeholder .
Parameter StakeholderBase_Ф__stakeholderUpdateUnusedStake : XAddress -> StakeholderBaseT True .
Parameter StakeholderBase_Ф__stakeholderIncreaseUnusedStake : ι_Stakeholder -> StakeholderBaseT ι_Stakeholder .
Parameter StakeholderBase_Ф__stakeholderDecreaseUnusedStake : ι_Stakeholder -> StakeholderBaseT ι_Stakeholder .
Parameter StakeholderBase_Ф__stakeholderResetVesting : ι_Stakeholder -> StakeholderBaseT ι_Stakeholder .
Parameter StakeholderBase_Ф__stakeholderUpdateLastPaymentTime : ι_Stakeholder -> StakeholderBaseT ι_Stakeholder .
Parameter StakingOwner_Ф_Constructor5 : XAddress -> StakingOwnerT True .
Parameter StakingOwner_Ф_updateStakingPoolAddress : XAddress -> StakingOwnerT True .
Parameter StakingOwner_Ф_getStakingPoolAddress : StakingOwnerT XAddress .
Parameter StakingOwner_Ф_getHistory : StakingOwnerT ι_М_Address .
Parameter StakingOwner_Ф_onCodeUpgrade : StakingOwnerT True .
Parameter StakingProxyContract_Ф_Constructor6 : XAddress -> StakingProxyContractT True .
Parameter RoundsBase_Ф__getRoundsInfo : RoundsBaseT ι_М_RoundInfo .
Parameter RoundsBase_Ф__getPendingRoundsInfo : RoundsBaseT ι_М_RoundInfo .
Parameter RoundsBase_Ф__getLastRoundIdx : RoundsBaseT XInteger64 .
Parameter RoundsBase_Ф__addNewPoolingRound : XInteger32 -> RoundsBaseT True .
Parameter RoundsBase_Ф__getRoundsCount : RoundsBaseT XInteger8 .
Parameter RoundsBase_Ф__removeOldestRound : RoundsBaseT ι_Round .
Parameter RoundsBase_Ф__getOldestRound : RoundsBaseT ι_Round .
Parameter RoundsBase_Ф__setOldestRound : ι_Round -> RoundsBaseT True .
Parameter RoundsBase_Ф__roundAddStakeAndVesting : ι_Round -> RoundsBaseT ι_Round .
Parameter RoundsBase_Ф__roundMoveStake : ι_Round -> RoundsBaseT ( ι_Round # XInteger64 ) .
Parameter RoundsBase_Ф__addPendingRound : ι_Round -> RoundsBaseT True .
Parameter RoundsBase_Ф__removePendingRound : XInteger32 -> RoundsBaseT ( XBool # ι_Round ) .
Parameter RoundsBase_Ф__roundFetchPendingRound : XInteger32 -> RoundsBaseT ( XBool # ι_Round ) .
Parameter RoundsBase_Ф__setOrDeletePendingRound : ι_Round -> RoundsBaseT True .
Parameter RoundsBase_Ф__deletePendingRound : XInteger32 -> RoundsBaseT True .
Parameter RoundsBase_Ф_getTotalStake : ι_StakeValue -> RoundsBaseT XInteger64 .
Parameter RoundsBase_Ф_arePendingRoundsEmpty : RoundsBaseT XBool .
Parameter RoundsBase_Ф__fetchOldestPendingRound : RoundsBaseT ( XInteger32 # ι_Round # XBool ) .
Parameter StakingContract_Ф__returnGrams : StakingContractT True .
Parameter StakingContract_Ф__calcLastRoundInterest : XInteger64 -> StakingContractT XInteger64 .
Parameter StakingContract_Ф__addRequest : XInteger32 -> StakingContractT True .
Parameter StakingContract_Ф__getStakeAndFeeAndUpdateMinStakeIfNeeded : XInteger64 -> StakingContractT ( XInteger64 # XInteger64 ) .
Parameter StakingContract_Ф_Constructor7 : XAddress -> StakingContractT True .
Parameter StakingContract_Ф_receiveConfirmation : XInteger64 -> StakingContractT True .
Parameter DePool_Ф_Constructor8 : XAddress -> DePoolT True .
Parameter DePool_Ф_getOwnerReward : DePoolT XInteger64 .
Parameter DePool_Ф_getMinStake : DePoolT XInteger64 .
Parameter DePool_Ф_getValidator : DePoolT ι_Node .
Parameter StakingContract_Ф_receiveConfirmation : XInteger64 -> StakingContractT True .
Parameter StakingContract_Ф_acceptRecoveredStake : XInteger64 -> StakingContractT True .
Parameter TestElector_Ф_Constructor9 : XInteger32 -> TestElectorT True .
Parameter TestElector_Ф_getElectionId : TestElectorT XInteger32 .
Parameter ElectorBase_Ф__recoverStakes : ElectorBaseT True .
Parameter ElectorBase_Ф__recoverStakeRewards : ElectorBaseT True .
Parameter ElectorBase_Ф__recoverPendingRoundStakes : XInteger32 -> ElectorBaseT True .
Parameter ElectorBase_Ф__runForElection : ι_Request -> ElectorBaseT True .
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
Parameter RoundsBase_Ф__getLastRound : RoundsBaseT ι_Round .
Parameter RoundsBase_Ф__setLastRound : ι_Round -> RoundsBaseT True .
Parameter RoundsBase_Ф__getPenultimateRound : RoundsBaseT ι_Round .
Parameter RoundsBase_Ф__setPenultimateRound : ι_Round -> RoundsBaseT True .
Parameter StakingContract_Ф__addNewRoundAndUpdateRounds : StakingContractT True .
Parameter StakingContract_Ф__checkPenultimateRound : StakingContractT XBool .
Parameter StakingContract_Ф__checkOldestRound : StakingContractT XBool .
Parameter StakingContract_Ф__returnAnswer : XInteger32 -> StakingContractT True .
Parameter StakingContract_Ф__returnError : XInteger32 -> StakingContractT True .
Parameter StakingContract_Ф__returnConfirmation : XInteger64 -> StakingContractT True .
Parameter StakingContract_Ф__investStake : XAddress -> StakingContractT XBool .
Parameter StakingContract_Ф__requestStakesSigning : ι_Round -> StakingContractT ι_Round .
Parameter StakingContract_Ф__acceptPendingRoundStake : XInteger32 -> StakingContractT True .
Parameter StakingContract_Ф__acceptUnusedStake : StakingContractT True .
Parameter StakingContract_Ф__acceptRewardStake : StakingContractT True .
Parameter StakingContract_Ф__completeRound : ι_Round -> StakingContractT ι_Round .
Parameter StakingContract_Ф__completeRoundAndSetCompletionStatus : ι_Round -> StakingContractT ι_Round .
Parameter StakingContract_Ф_getNewStakeAndFees : XInteger64 -> StakingContractT ( XInteger64 # XInteger64 # XInteger64 ) .
Parameter StakingContract_Ф__returnOrReinvestForStakeholder : ι_Round -> StakingContractT ι_Round .
Parameter StakingContract_Ф__returnOrReinvest : ι_Round -> StakingContractT ι_Round .
Parameter StakingContract_Ф__getStakeAndSendErrorIfNeeded : StakingContractT ( XInteger64 # XBool ) .
Parameter StakingContract_Ф_addStake : XBool -> StakingContractT True .
Parameter StakingContract_Ф_addVesting : XAddress -> StakingContractT True .
Parameter StakingContract_Ф_removeStake : XInteger64 -> StakingContractT True .
Parameter StakingContract_Ф_continueStake : XInteger64 -> StakingContractT True .
Parameter StakingContract_Ф_setReinvest : XBool -> StakingContractT True .
Parameter StakingContract_Ф_transferStake : XAddress -> StakingContractT True .
Parameter StakingContract_Ф_processNewStake : XInteger64 -> StakingContractT True .
Parameter StakingContract_Ф_ticktock : StakingContractT True .
Parameter StakingContract_Ф_forceCompletePendingRound : XBool -> StakingContractT True .
Parameter StakingContract_Ф_completePendingRoundChunk : XInteger32 -> StakingContractT True .
Parameter StakingContract_Ф_receiveReturnedStake : XInteger64 -> StakingContractT ( XInteger64 # XInteger32 ) .
Parameter StakingContract_Ф_acceptRecoveredStake : XInteger64 -> StakingContractT True .
Parameter StakingContract_Ф_terminator : XInteger8 -> StakingContractT True .
Parameter DePool_Ф_getRounds : DePoolT ( XInteger32 # XInteger32 # ι_М_RoundInfo ) .
Parameter DePool_Ф_getStakeholderInfo : XAddress -> DePoolT ( XInteger64 # XInteger64 # XInteger64 # XBool # XInteger64 # ι_М_StakeInfo ) .
Parameter DePool_Ф_getStakingInfo : DePoolT ( XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger32 # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 ) .
Parameter DePool_Ф_getPendingRounds : DePoolT ι_М_RoundInfo .
Parameter StakingProxyContract_Ф_process_new_stake : XInteger64 -> StakingProxyContractT True .
Parameter ElectionParams_Ф_Constructor4 : XInteger32 -> ElectionParamsT True .
Parameter StakingOwner_Ф_initTimer : XAddress -> StakingOwnerT True .
Parameter StakingOwner_Ф_upgrade : TvmCell -> StakingOwnerT True .
Parameter RoundsBase_Ф__roundMoveStakes : XAddress -> RoundsBaseT XInteger64 .
Parameter StakingContract_Ф__completePendingRound : ι_Round -> StakingContractT ι_Round .
