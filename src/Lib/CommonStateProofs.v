
 Require Import Coq.Program.Basics. 
 Require Import Coq.Logic.FunctionalExtensionality. 
 Require Import Coq.Program.Combinators. 
 Require Import omega.Omega. 
 Require Import Setoid. 
 
 Require Import FinProof.Common. 
 Require Import FinProof.CommonInstances. 
 Require Import FinProof.StateMonad2. 
 Require Import FinProof.StateMonadInstances. 
 Require Import FinProof.ProgrammingWith. 
 
 Require Import FinProof.CommonProofs. 
 Require Import depoolContract.ProofEnvironment. 
 Require Import depoolContract.DePoolClass. 
 Require Import depoolContract.SolidityNotations. 
 
 Require Import depoolContract.Lib.CommonModelProofs. 
 Module CommonModelProofs := CommonModelProofs StateMonadSig. 
 Import CommonModelProofs. 
 
 Import DePoolSpec. 
 Import LedgerClass. 
 Import SolidityNotations. 
 Set Typeclasses Iterative Deepening. 
 Set Typeclasses Depth 10. 
 
 Require Import depoolContract.Lib.Tactics. 
 
 Local Open Scope struct_scope. 
 Local Open Scope Z_scope. 
 Local Open Scope solidity_scope. 
 
 Require Import Lists.List. 
 Import ListNotations. 
 Local Open Scope list_scope. 
 
 Existing Instance monadStateT. 
 Existing Instance monadStateStateT. 
 

Lemma ledgerEq: forall (l l': Ledger) ,
(*  A l = A l' -> 
 C l = C l' ->  *)
 Ledger_ι_ValidatorBase l = Ledger_ι_ValidatorBase l' -> 
 Ledger_ι_ProxyBase l = Ledger_ι_ProxyBase l' -> 
 Ledger_ι_ParticipantBase l = Ledger_ι_ParticipantBase l' -> 
 Ledger_ι_DePoolProxyContract l = Ledger_ι_DePoolProxyContract l' -> 
 Ledger_ι_RoundsBase l = Ledger_ι_RoundsBase l' -> 
 Ledger_ι_DePoolContract l = Ledger_ι_DePoolContract l' -> 
 Ledger_ι_VMState l = Ledger_ι_VMState l' -> 
 Ledger_ι_LocalState l = Ledger_ι_LocalState l' -> l = l' . 
Proof.
 intros. destruct l. destruct l'.
 simpl in H. simpl in * |-. 
 subst. auto.
Qed.


Lemma ParticipantEq : forall (l l': DePoolLib_ι_Participant) , 
 DePoolLib_ι_Participant_ι_roundQty l = DePoolLib_ι_Participant_ι_roundQty l' -> 
 DePoolLib_ι_Participant_ι_reward l = DePoolLib_ι_Participant_ι_reward l' -> 
 DePoolLib_ι_Participant_ι_haveVesting l = DePoolLib_ι_Participant_ι_haveVesting l' -> 
 DePoolLib_ι_Participant_ι_haveLock l = DePoolLib_ι_Participant_ι_haveLock l' -> 
 DePoolLib_ι_Participant_ι_reinvest l = DePoolLib_ι_Participant_ι_reinvest l' -> 
 DePoolLib_ι_Participant_ι_withdrawValue l = DePoolLib_ι_Participant_ι_withdrawValue l' -> l = l' . 
 
 Proof. 
 intros. destruct l. destruct l'. 
 simpl in H. simpl in * |-. 
 subst. auto. 
 Qed. 
 
 
 Lemma RequestEq : forall (l l': DePoolLib_ι_Request) , 
 DePoolLib_ι_Request_ι_queryId l = DePoolLib_ι_Request_ι_queryId l' -> 
 DePoolLib_ι_Request_ι_validatorKey l = DePoolLib_ι_Request_ι_validatorKey l' -> 
 DePoolLib_ι_Request_ι_stakeAt l = DePoolLib_ι_Request_ι_stakeAt l' -> 
 DePoolLib_ι_Request_ι_maxFactor l = DePoolLib_ι_Request_ι_maxFactor l' -> 
 DePoolLib_ι_Request_ι_adnlAddr l = DePoolLib_ι_Request_ι_adnlAddr l' -> 
 DePoolLib_ι_Request_ι_signature l = DePoolLib_ι_Request_ι_signature l' -> l = l' . 
 
 Proof. 
 intros. destruct l. destruct l'. 
 simpl in H. simpl in * |-. 
 subst. auto. 
 Qed. 
 
Lemma DePoolContractEq : forall (l l': DePoolContract) , 
 DePoolContract_ι_m_poolClosed l = DePoolContract_ι_m_poolClosed l' -> 
 DePoolContract_ι_m_minStake l = DePoolContract_ι_m_minStake l' -> 
 DePoolContract_ι_m_validatorAssurance l = DePoolContract_ι_m_validatorAssurance l' -> 
 DePoolContract_ι_m_participantRewardFraction l = DePoolContract_ι_m_participantRewardFraction l' -> 
 DePoolContract_ι_m_validatorRewardFraction l = DePoolContract_ι_m_validatorRewardFraction l' -> 
 DePoolContract_ι_m_balanceThreshold l = DePoolContract_ι_m_balanceThreshold l' -> 
 l = l' .
 Proof. 
 intros. destruct l. destruct l'. 
 simpl in H. simpl in * |-. 
 subst. auto. 
 Qed. 
 
 
 Lemma ValidatorBaseEq : forall (l l': ValidatorBase) , 
 ValidatorBase_ι_m_validatorWallet l = ValidatorBase_ι_m_validatorWallet l' -> l = l' . 
 
 Proof. 
 intros. destruct l. destruct l'. 
 simpl in H. simpl in * |-. 
 subst. auto. 
 Qed. 
 
 
 Lemma ProxyBaseEq : forall (l l': ProxyBase) , 
 ProxyBase_ι_m_proxies l = ProxyBase_ι_m_proxies l' -> l = l' . 
 
 Proof. 
 intros. destruct l. destruct l'. 
 simpl in H. simpl in * |-. 
 subst. auto. 
 Qed. 
 
 
 Lemma ParticipantBaseEq : forall (l l': ParticipantBase) , 
 ParticipantBase_ι_m_participants l = ParticipantBase_ι_m_participants l' -> l = l' . 
 
 Proof. 
 intros. destruct l. destruct l'. 
 simpl in H. simpl in * |-. 
 subst. auto. 
 Qed. 
 
 Lemma DePoolProxyContractEq : forall (l l': DePoolProxyContract) , 
 DePoolProxyContract_ι_m_dePool l = DePoolProxyContract_ι_m_dePool l' -> l = l' . 
 
 Proof. 
 intros. destruct l. destruct l'. 
 simpl in H. simpl in * |-. 
 subst. auto. 
 Qed. 
 
Lemma InvestParamsEq : forall (l l': RoundsBase_ι_InvestParams) , 
 RoundsBase_ι_InvestParams_ι_remainingAmount l = RoundsBase_ι_InvestParams_ι_remainingAmount l' -> 
 RoundsBase_ι_InvestParams_ι_lastWithdrawalTime l = RoundsBase_ι_InvestParams_ι_lastWithdrawalTime l' -> 
 RoundsBase_ι_InvestParams_ι_withdrawalPeriod l = RoundsBase_ι_InvestParams_ι_withdrawalPeriod l' -> 
 RoundsBase_ι_InvestParams_ι_withdrawalValue l = RoundsBase_ι_InvestParams_ι_withdrawalValue l' -> 
 RoundsBase_ι_InvestParams_ι_owner l = RoundsBase_ι_InvestParams_ι_owner l' -> l = l' . 
 
Proof. 
 intros. destruct l. destruct l'. 
 simpl in H. simpl in * |-. 
 subst. auto. 
 Qed. 
 
 
 Lemma StakeValueEq : forall (l l': RoundsBase_ι_StakeValue) , 
 RoundsBase_ι_StakeValue_ι_ordinary l = RoundsBase_ι_StakeValue_ι_ordinary l' -> 
 RoundsBase_ι_StakeValue_ι_vesting l = RoundsBase_ι_StakeValue_ι_vesting l' -> 
 RoundsBase_ι_StakeValue_ι_lock l = RoundsBase_ι_StakeValue_ι_lock l' -> l = l' . 
 
 Proof. 
 intros. destruct l. destruct l'. 
 simpl in H. simpl in * |-. 
 subst. auto. 
 Qed. 
 
 
 Lemma RoundEq : forall (l l': RoundsBase_ι_Round) , 
 RoundsBase_ι_Round_ι_id l = RoundsBase_ι_Round_ι_id l' -> 
 RoundsBase_ι_Round_ι_supposedElectedAt l = RoundsBase_ι_Round_ι_supposedElectedAt l' -> 
 RoundsBase_ι_Round_ι_unfreeze l = RoundsBase_ι_Round_ι_unfreeze l' -> 
 RoundsBase_ι_Round_ι_stakeHeldFor l = RoundsBase_ι_Round_ι_stakeHeldFor l' -> 
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase l = RoundsBase_ι_Round_ι_vsetHashInElectionPhase l' -> 
 RoundsBase_ι_Round_ι_step l = RoundsBase_ι_Round_ι_step l' -> 
 RoundsBase_ι_Round_ι_completionReason l = RoundsBase_ι_Round_ι_completionReason l' -> 
 RoundsBase_ι_Round_ι_stake l = RoundsBase_ι_Round_ι_stake l' -> 
 RoundsBase_ι_Round_ι_recoveredStake l = RoundsBase_ι_Round_ι_recoveredStake l' -> 
 RoundsBase_ι_Round_ι_unused l = RoundsBase_ι_Round_ι_unused l' -> 
 RoundsBase_ι_Round_ι_isValidatorStakeCompleted l = RoundsBase_ι_Round_ι_isValidatorStakeCompleted l' -> 
 RoundsBase_ι_Round_ι_grossReward l = RoundsBase_ι_Round_ι_grossReward l' -> 
 RoundsBase_ι_Round_ι_rewards l = RoundsBase_ι_Round_ι_rewards l' -> 
 RoundsBase_ι_Round_ι_participantQty l = RoundsBase_ι_Round_ι_participantQty l' -> 
 RoundsBase_ι_Round_ι_stakes l = RoundsBase_ι_Round_ι_stakes l' -> 
 RoundsBase_ι_Round_ι_validatorStake l = RoundsBase_ι_Round_ι_validatorStake l' -> 
 RoundsBase_ι_Round_ι_validatorRemainingStake l = RoundsBase_ι_Round_ι_validatorRemainingStake l' -> 
 RoundsBase_ι_Round_ι_handledStakesAndRewards l = RoundsBase_ι_Round_ι_handledStakesAndRewards l' -> 
 RoundsBase_ι_Round_ι_validatorRequest l = RoundsBase_ι_Round_ι_validatorRequest l' -> 
 RoundsBase_ι_Round_ι_elector l = RoundsBase_ι_Round_ι_elector l' -> 
 RoundsBase_ι_Round_ι_proxy l = RoundsBase_ι_Round_ι_proxy l' -> 
 RoundsBase_ι_Round_ι_validatorsElectedFor l = RoundsBase_ι_Round_ι_validatorsElectedFor l' ->
 l = l' . 
 
 Proof. 
 intros. destruct l. destruct l'. 
 simpl in H. simpl in * |-. 
 subst. auto. 
 Qed. 
 
 
 Lemma LastRoundInfoEq : forall (l l': DePool_ι_LastRoundInfo) , 
 DePool_ι_LastRoundInfo_ι_supposedElectedAt l = DePool_ι_LastRoundInfo_ι_supposedElectedAt l' -> 
 DePool_ι_LastRoundInfo_ι_participantRewardFraction l = DePool_ι_LastRoundInfo_ι_participantRewardFraction l' -> 
 DePool_ι_LastRoundInfo_ι_validatorRewardFraction l = DePool_ι_LastRoundInfo_ι_validatorRewardFraction l' -> 
 DePool_ι_LastRoundInfo_ι_participantQty l = DePool_ι_LastRoundInfo_ι_participantQty l' -> 
 DePool_ι_LastRoundInfo_ι_roundStake l = DePool_ι_LastRoundInfo_ι_roundStake l' -> 
 DePool_ι_LastRoundInfo_ι_validatorWallet l = DePool_ι_LastRoundInfo_ι_validatorWallet l' -> 
 DePool_ι_LastRoundInfo_ι_validatorPubkey l = DePool_ι_LastRoundInfo_ι_validatorPubkey l' -> 
 DePool_ι_LastRoundInfo_ι_validatorAssurance l = DePool_ι_LastRoundInfo_ι_validatorAssurance l' -> 
 DePool_ι_LastRoundInfo_ι_reward l = DePool_ι_LastRoundInfo_ι_reward l' -> 
 DePool_ι_LastRoundInfo_ι_reason l = DePool_ι_LastRoundInfo_ι_reason l' -> 
 DePool_ι_LastRoundInfo_ι_isDePoolClosed l = DePool_ι_LastRoundInfo_ι_isDePoolClosed l' -> l = l' . 
 
 Proof. 
 intros. destruct l. destruct l'. 
 simpl in H. simpl in * |-. 
 subst. auto. 
 Qed. 
 
 
 Lemma RoundsBaseEq : forall (l l': RoundsBase) , 
 RoundsBase_ι_m_rounds l = RoundsBase_ι_m_rounds l' -> 
 RoundsBase_ι_m_roundQty l = RoundsBase_ι_m_roundQty l' -> 
 RoundsBase_ι_lastRoundInfo l = RoundsBase_ι_lastRoundInfo l' -> l = l' . 
 
 Proof. 
 intros. destruct l. destruct l'. 
 simpl in H. simpl in * |-. 
 subst. auto. 
 Qed. 
 
 
 Lemma TruncatedRoundEq : forall (l l': RoundsBase_ι_TruncatedRound) , 
 RoundsBase_ι_TruncatedRound_ι_id l = RoundsBase_ι_TruncatedRound_ι_id l' -> 
 RoundsBase_ι_TruncatedRound_ι_supposedElectedAt l = RoundsBase_ι_TruncatedRound_ι_supposedElectedAt l' -> 
 RoundsBase_ι_TruncatedRound_ι_unfreeze l = RoundsBase_ι_TruncatedRound_ι_unfreeze l' -> 
 RoundsBase_ι_TruncatedRound_ι_stakeHeldFor l = RoundsBase_ι_TruncatedRound_ι_stakeHeldFor l' -> 
 RoundsBase_ι_TruncatedRound_ι_vsetHashInElectionPhase l = RoundsBase_ι_TruncatedRound_ι_vsetHashInElectionPhase l' -> 
 RoundsBase_ι_TruncatedRound_ι_step l = RoundsBase_ι_TruncatedRound_ι_step l' -> 
 RoundsBase_ι_TruncatedRound_ι_completionReason l = RoundsBase_ι_TruncatedRound_ι_completionReason l' -> 
 RoundsBase_ι_TruncatedRound_ι_stake l = RoundsBase_ι_TruncatedRound_ι_stake l' -> 
 RoundsBase_ι_TruncatedRound_ι_recoveredStake l = RoundsBase_ι_TruncatedRound_ι_recoveredStake l' -> 
 RoundsBase_ι_TruncatedRound_ι_unused l = RoundsBase_ι_TruncatedRound_ι_unused l' -> 
 RoundsBase_ι_TruncatedRound_ι_isValidatorStakeCompleted l = RoundsBase_ι_TruncatedRound_ι_isValidatorStakeCompleted l' -> 
 RoundsBase_ι_TruncatedRound_ι_rewards l = RoundsBase_ι_TruncatedRound_ι_rewards l' -> 
 RoundsBase_ι_TruncatedRound_ι_participantQty l = RoundsBase_ι_TruncatedRound_ι_participantQty l' -> 
 RoundsBase_ι_TruncatedRound_ι_validatorStake l = RoundsBase_ι_TruncatedRound_ι_validatorStake l' -> 
 RoundsBase_ι_TruncatedRound_ι_validatorRemainingStake l = RoundsBase_ι_TruncatedRound_ι_validatorRemainingStake l' -> 
 RoundsBase_ι_TruncatedRound_ι_handledStakesAndRewards l = RoundsBase_ι_TruncatedRound_ι_handledStakesAndRewards l' -> l = l' . 
 
 Proof. 
 intros. destruct l. destruct l'. 
 simpl in H. simpl in * |-. 
 subst. auto. 
 Qed. 
 

 Lemma VMStateEq : forall (l l': VMState ) , 
 
 VMState_ι_pubkey l = 
 VMState_ι_pubkey l' -> 
 
 VMState_ι_msg_pubkey l = 
 VMState_ι_msg_pubkey l' -> 
 
 VMState_ι_now l = 
 VMState_ι_now l' -> 
 
 VMState_ι_logstr l = 
 VMState_ι_logstr l' -> 
 
 VMState_ι_balance l = 
 VMState_ι_balance l' -> 
 
 VMState_ι_address l = 
 VMState_ι_address l' -> 
 
 VMState_ι_ltime l = 
 VMState_ι_ltime l' -> 
 
 VMState_ι_code l = 
 VMState_ι_code l' -> 
 VMState_ι_events l = VMState_ι_events l' -> 
 VMState_ι_savedDePoolContracts l = VMState_ι_savedDePoolContracts l' -> 
 VMState_ι_msg_sender l = VMState_ι_msg_sender l' -> 
 VMState_ι_msg_value l = VMState_ι_msg_value l' -> 
 VMState_ι_messages l = VMState_ι_messages l' -> 
 VMState_ι_msg_data l = VMState_ι_msg_data l' -> 
 VMState_ι_transactions l = VMState_ι_transactions l' -> 

 VMState_ι_accepted l = VMState_ι_accepted l' ->
 VMState_ι_reserved l = VMState_ι_reserved l' ->
 VMState_ι_currentCode l = VMState_ι_currentCode l' ->

 VMState_ι_validatorsElectedFor l = VMState_ι_validatorsElectedFor l' ->
 VMState_ι_electionsStartBefore l = VMState_ι_electionsStartBefore l' ->
 VMState_ι_electionsEndBefore l = VMState_ι_electionsEndBefore l' ->
 VMState_ι_stakeHeldFor l = VMState_ι_stakeHeldFor l' ->

 VMState_ι_curValidatorData l = VMState_ι_curValidatorData l' ->
 VMState_ι_unknown34 l = VMState_ι_unknown34 l' ->
 VMState_ι_utime_since l = VMState_ι_utime_since l' ->
 VMState_ι_utime_until l = VMState_ι_utime_until l' ->

 VMState_ι_prevValidatorData l = VMState_ι_prevValidatorData l' ->

 VMState_ι_rawConfigParam_17 l = VMState_ι_rawConfigParam_17 l' ->
 VMState_ι_unknown17_1 l = VMState_ι_unknown17_1 l' ->
 VMState_ι_unknown17_2 l = VMState_ι_unknown17_2 l' ->
 VMState_ι_unknown17_3 l = VMState_ι_unknown17_3 l' ->
 VMState_ι_maxStakeFactor l = VMState_ι_maxStakeFactor l' ->

 VMState_ι_rawConfigParam_1 l = VMState_ι_rawConfigParam_1 l' ->
 VMState_ι_electorRawAddress l = VMState_ι_electorRawAddress l' ->
 VMState_ι_deployed l = VMState_ι_deployed l' ->

 l = l' . 
 Proof. 
 intros. destruct l. destruct l'. 
 simpl in H. simpl in * |-. 
 subst. auto. 
 Qed. 
 

