Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.
Require Import omega.Omega.
Require Import Setoid.
Require Import ZArith.
Require Import FinProof.Common.
Require Import FinProof.CommonInstances.
Require Import FinProof.StateMonad2.
Require Import FinProof.StateMonadInstances.
Require Import FinProof.ProgrammingWith. 
Local Open Scope struct_scope.
Require Import FinProof.CommonProofs.
Require Import depoolContract.ProofEnvironment.
Require Import depoolContract.DePoolClass.
Require Import depoolContract.SolidityNotations.
Require Import depoolContract.DePoolFunc.
Require Import depoolContract.DePoolConsts.
Require Import depoolContract.Lib.CommonModelProofs.
Module CommonModelProofs := CommonModelProofs StateMonadSig.
Import CommonModelProofs. 
Require Import depoolContract.Lib.Tactics.
Require Import depoolContract.Lib.ErrorValueProofs.
Require Import depoolContract.Scenarios.ScenarioCommon.
Import DePoolSpec.LedgerClass.SolidityNotations. 
Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope solidity_scope.
Require Import Lists.List.
Import ListNotations.
Local Open Scope list_scope.
Set Typeclasses Iterative Deepening.
Set Typeclasses Depth 100.
Module Scenario1  (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Import dc.
Module ScenarioCommon := ScenarioCommon dc.
Import ScenarioCommon.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.

Lemma Scenario_OrdinaryStakeWin_byValidator: forall 
                        (minStake validatorAssurance proxyCode validatorWallet   participantRewardFraction : Z)
                        (proxyCode : TvmCell)
                        (now_constructor msg_pubkey_constructor : Z)
                        (NetParams_init : NetParams)
                        (stake :Z )
                        (NetParams_addOrdinaryStake :  NetParams)
                        (now_addOrdinaryStake msg_value_addOrdinaryStake msg_sender_addOrdinaryStake : Z)
                        (now_round1  msg_value_round1 msg_sender_round1 : Z)
                        (NetParams_round1 :  NetParams)
                        (queryId0 validatorKey stakeAt maxFactor adnlAddr : Z)
                        ( signature : XList XInteger8 )
                        (now_participateInElections  msg_value_participateInElections msg_sender_participateInElections : Z)
                        (NetParams_participateInElections :  NetParams)                        
                        (queryId comment elector : Z)
                        (now_onStakeAccept  msg_value_onStakeAccept msg_sender_onStakeAccept : Z)
                        (NetParams_onStakeAccept :  NetParams)
                        (now_toWaitingIfValidatorWinElections  msg_value_toWaitingIfValidatorWinElections msg_sender_toWaitingIfValidatorWinElections : Z)
                        (NetParams_toWaitingIfValidatorWinElections :  NetParams)
                        (now_onFailToRecoverStake  msg_value_onFailToRecoverStake msg_sender_onFailToRecoverStake : Z)
                        (NetParams_onFailToRecoverStake :  NetParams)
                        (now_toWaitingReward  msg_value_toWaitingReward msg_sender_toWaitingReward : Z)
                        (NetParams_toWaitingReward :  NetParams)
                        (now_onSuccessToRecoverStake  msg_value_onSuccessToRecoverStake msg_sender_onSuccessToRecoverStake : Z)
                        (NetParams_onSuccessToRecoverStake :  NetParams),
let l_init_NetParams := withNetParams default NetParams_init in
let l_init := {$ l_init_NetParams With (VMState_ι_now,   now_constructor); 
                                       (VMState_ι_msg_pubkey,   msg_pubkey_constructor)$} in 
let l_constructor:= exec_state (DePoolContract_Ф_Constructor6 minStake validatorAssurance proxyCode validatorWallet   participantRewardFraction  ) l_init in 
let (r, l_fin) := run  (modify (fun l => withNetParams l NetParams_addOrdinaryStake) >>
                        modify (fun l => {$ l With (VMState_ι_now,   now_addOrdinaryStake);
                                                   (VMState_ι_msg_value , msg_value_addOrdinaryStake);
                                                   (VMState_ι_msg_sender , msg_sender_addOrdinaryStake) $}) >>
                        do _ ← DePoolContract_Ф_addOrdinaryStake'' stake ??;
                        modify (fun l => withNetParams l NetParams_round1) >>
                        modify (fun l => {$ l With (VMState_ι_now,          now_round1);
                                                   (VMState_ι_msg_value ,   msg_value_round1);
                                                   (VMState_ι_msg_sender ,  msg_sender_round1) $}) >>
                        do _ ← DePoolContract_Ф_ticktock ??;
                        modify (fun l => withNetParams l NetParams_participateInElections) >>
                        modify (fun l => {$ l With (VMState_ι_now,          now_participateInElections);
                                                   (VMState_ι_msg_value ,   msg_value_participateInElections);
                                                   (VMState_ι_msg_sender ,  msg_sender_participateInElections) $}) >>
                        do _ ← DePoolContract_Ф_participateInElections'' queryId0 validatorKey stakeAt maxFactor adnlAddr signature ??;
                        modify (fun l => withNetParams l NetParams_onStakeAccept) >>
                        modify (fun l => {$ l With (VMState_ι_now,          now_onStakeAccept);
                                                   (VMState_ι_msg_value ,   msg_value_onStakeAccept);
                                                   (VMState_ι_msg_sender ,  msg_sender_onStakeAccept) $}) >>
                        do _ ← DePoolContract_Ф_onStakeAccept queryId comment elector ??;
                        modify (fun l => withNetParams l NetParams_toWaitingIfValidatorWinElections) >>
                        modify (fun l => {$ l With (VMState_ι_now,          now_toWaitingIfValidatorWinElections);
                                                   (VMState_ι_msg_value ,   msg_value_toWaitingIfValidatorWinElections);
                                                   (VMState_ι_msg_sender ,  msg_sender_toWaitingIfValidatorWinElections) $}) >>
                        do _ ← DePoolContract_Ф_ticktock ??;
                        modify (fun l => withNetParams l NetParams_onFailToRecoverStake) >>
                        modify (fun l => {$ l With (VMState_ι_now,          now_onFailToRecoverStake);
                                                   (VMState_ι_msg_value ,   msg_value_onFailToRecoverStake);
                                                   (VMState_ι_msg_sender ,  msg_sender_onFailToRecoverStake) $}) >>
                        do _ ← DePoolContract_Ф_onFailToRecoverStake queryId elector ??;
                        modify (fun l => withNetParams l NetParams_toWaitingReward) >>
                        modify (fun l => {$ l With (VMState_ι_now,          now_toWaitingReward);
                                                   (VMState_ι_msg_value ,   msg_value_toWaitingReward);
                                                   (VMState_ι_msg_sender ,  msg_sender_toWaitingReward) $}) >>
                        do _ ← DePoolContract_Ф_ticktock ??;
                        modify (fun l => withNetParams l NetParams_onSuccessToRecoverStake) >>
                        modify (fun l => {$ l With (VMState_ι_now,          now_onSuccessToRecoverStake);
                                                   (VMState_ι_msg_value ,   msg_value_onSuccessToRecoverStake);
                                                   (VMState_ι_msg_sender ,  msg_sender_onSuccessToRecoverStake) $}) >>
                        do _ ← DePoolContract_Ф_onSuccessToRecoverStake queryId elector ?;
                        $ I )  l_constructor in errorValueIsValue r = true ->
msg_sender_addOrdinaryStake = validatorWallet ->  
(now_round1 >=? NetParams_round1 ->> NetParams_ι_utime_until - NetParams_round1 ->> NetParams_ι_electionsStartBefore) = true -> 
((negb (tvm_hash (NetParams_init ->> NetParams_ι_curValidatorData) =? tvm_hash (NetParams_round1 ->> NetParams_ι_curValidatorData))) &&
(negb (tvm_hash (NetParams_init ->> NetParams_ι_prevValidatorData) =? tvm_hash (NetParams_round1 ->> NetParams_ι_curValidatorData))))%bool= true ->     
(stake >=? validatorAssurance) = true -> 
( tvm_hash  (NetParams_round1 ->> NetParams_ι_curValidatorData)  =?  tvm_hash  (NetParams_toWaitingIfValidatorWinElections ->> NetParams_ι_prevValidatorData))  = true ->
(now_toWaitingIfValidatorWinElections >=? NetParams_toWaitingIfValidatorWinElections ->> NetParams_ι_utime_until - NetParams_toWaitingIfValidatorWinElections ->> NetParams_ι_electionsStartBefore) = true ->
(negb (0 =? tvm_hash ((NetParams_toWaitingIfValidatorWinElections ->> NetParams_ι_curValidatorData)))) = true ->
((negb (tvm_hash ((NetParams_toWaitingReward ->> NetParams_ι_curValidatorData)) =? tvm_hash ((NetParams_round1 ->> NetParams_ι_curValidatorData)))) &&
(negb (tvm_hash ((NetParams_toWaitingReward ->> NetParams_ι_prevValidatorData)) =? tvm_hash ((NetParams_round1 ->> NetParams_ι_curValidatorData)))))%bool= true ->   
(now_toWaitingReward >=? NetParams_toWaitingReward ->> NetParams_ι_utime_since + NetParams_round1 ->> NetParams_ι_stakeHeldFor + DePoolLib_ι_ELECTOR_UNFREEZE_LAG) = true ->
(msg_value_onSuccessToRecoverStake + DePoolLib_ι_PROXY_FEE >=? stake) = true ->
let reward_all := msg_value_onSuccessToRecoverStake + DePoolLib_ι_PROXY_FEE - stake  - (DePool_ι_RET_OR_REINV_FEE +  1 * DePool_ι_RET_OR_REINV_FEE) in
let rewards := reward_all * participantRewardFraction / 100  in
let stakeSum := stake in 
let reward := stakeSum * rewards / stake  in
let optRound := eval_state ( ↓ ( RoundsBase_Ф_fetchRound queryId ) ) l_fin in                  
let round := maybeGet optRound in 
let stakes :=  round ->> RoundsBase_ι_Round_ι_stakes in
let optStake := stakes ->fetch validatorWallet in
let current_stakes := maybeGet optStake in
round ->> RoundsBase_ι_Round_ι_stake = stake + reward
/\ current_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary  = stake + reward.
Proof.

Abort.
End Scenario1.