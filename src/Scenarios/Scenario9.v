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
Module Scenario9  (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Import dc.
Module ScenarioCommon := ScenarioCommon dc.
Import ScenarioCommon.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.

Lemma Scenario_OrdinaryStakeNotAccepted_byValidatorAndParticipant: forall 
                        (minStake validatorAssurance proxyCode validatorWallet   participantRewardFraction : Z)
                        (proxyCode : TvmCell)
                        (now_constructor msg_pubkey_constructor : Z)
                        (NetParams_init : NetParams)
                        (stakeV :Z )
                        (NetParams_addOrdinaryStake :  NetParams)
                        (now_addOrdinaryStakeV msg_value_addOrdinaryStakeV msg_sender_addOrdinaryStakeV : Z)
                        (stakeP :Z )
                        (now_addOrdinaryStakeP msg_value_addOrdinaryStakeP msg_sender_addOrdinaryStakeP : Z)
                        (now_round1  msg_value_round1 msg_sender_round1 : Z)
                        (NetParams_round1 :  NetParams)
                        (now_toWaitingUnfreeze  msg_value_toWaitingUnfreeze msg_sender_toWaitingUnfreeze : Z)
                        (NetParams_toWaitingUnfreeze :  NetParams)
                        (now_toComplete  msg_value_toComplete msg_sender_toComplete : Z)
                        (NetParams_toComplete :  NetParams),
let l_init_NetParams := withNetParams default NetParams_init in
let l_init := {$ l_init_NetParams With (VMState_ι_now,   now_constructor); 
                                       (VMState_ι_msg_pubkey,   msg_pubkey_constructor)$} in 
let l_constructor:= exec_state (DePoolContract_Ф_Constructor6 minStake validatorAssurance proxyCode validatorWallet   participantRewardFraction  ) l_init in 
let (r, l_fin) := run  (modify (fun l => withNetParams l NetParams_addOrdinaryStake) >>
                        modify (fun l => {$ l With (VMState_ι_now,   now_addOrdinaryStakeV);
                                                   (VMState_ι_msg_value , msg_value_addOrdinaryStakeV);
                                                   (VMState_ι_msg_sender , msg_sender_addOrdinaryStakeV) $}) >>
                        do _ ← DePoolContract_Ф_addOrdinaryStake'' stakeV ??;
                        modify (fun l => {$ l With (VMState_ι_now,   now_addOrdinaryStakeP);
                                                   (VMState_ι_msg_value , msg_value_addOrdinaryStakeP);
                                                   (VMState_ι_msg_sender , msg_sender_addOrdinaryStakeP) $}) >>
                        do _ ← DePoolContract_Ф_addOrdinaryStake'' stakeP ??;
                        modify (fun l => withNetParams l NetParams_round1) >>
                        modify (fun l => {$ l With (VMState_ι_now,          now_round1);
                                                   (VMState_ι_msg_value ,   msg_value_round1);
                                                   (VMState_ι_msg_sender ,  msg_sender_round1) $}) >>
                        do _ ← DePoolContract_Ф_ticktock ??;
                        modify (fun l => withNetParams l NetParams_toWaitingUnfreeze) >>
                        modify (fun l => {$ l With (VMState_ι_now,          now_toWaitingUnfreeze);
                                                   (VMState_ι_msg_value ,   msg_value_toWaitingUnfreeze);
                                                   (VMState_ι_msg_sender ,  msg_sender_toWaitingUnfreeze) $}) >>
                        do _ ← DePoolContract_Ф_ticktock ??;
                        modify (fun l => withNetParams l NetParams_toComplete) >>
                        modify (fun l => {$ l With (VMState_ι_now,          now_toComplete);
                                                   (VMState_ι_msg_value ,   msg_value_toComplete);
                                                   (VMState_ι_msg_sender ,  msg_sender_toComplete) $}) >>
                        do _ ← DePoolContract_Ф_ticktock ?;
                        $ I )  l_constructor in errorValueIsValue r = true ->
msg_sender_addOrdinaryStakeV = validatorWallet ->  
msg_sender_addOrdinaryStakeV <> validatorWallet ->  
(now_round1 >=? NetParams_round1 ->> NetParams_ι_utime_until - NetParams_round1 ->> NetParams_ι_electionsStartBefore) = true -> 
((negb (tvm_hash (NetParams_init ->> NetParams_ι_curValidatorData) =? tvm_hash (NetParams_round1 ->> NetParams_ι_curValidatorData))) &&
(negb (tvm_hash (NetParams_init ->> NetParams_ι_prevValidatorData) =? tvm_hash (NetParams_round1 ->> NetParams_ι_curValidatorData))))%bool= true ->     
(stakeV >=? validatorAssurance) = false -> 
( tvm_hash  (NetParams_round1 ->> NetParams_ι_curValidatorData)  =?  tvm_hash  (NetParams_toWaitingUnfreeze ->> NetParams_ι_prevValidatorData))  = true ->
(now_toWaitingUnfreeze >=? NetParams_toWaitingUnfreeze ->> NetParams_ι_utime_until - NetParams_toWaitingUnfreeze ->> NetParams_ι_electionsStartBefore) = true ->
(negb (0 =? tvm_hash ((NetParams_toWaitingUnfreeze ->> NetParams_ι_curValidatorData)))) = true ->
((negb (tvm_hash ((NetParams_toComplete ->> NetParams_ι_curValidatorData)) =? tvm_hash ((NetParams_round1 ->> NetParams_ι_curValidatorData)))) &&
(negb (tvm_hash ((NetParams_toComplete ->> NetParams_ι_prevValidatorData)) =? tvm_hash ((NetParams_round1 ->> NetParams_ι_curValidatorData)))))%bool= true ->     
(now_toComplete >=? NetParams_toComplete ->> NetParams_ι_utime_since + NetParams_round1 ->> NetParams_ι_stakeHeldFor + DePoolLib_ι_ELECTOR_UNFREEZE_LAG) = true ->
let reward := 0  in
let rewardV := 0  in
let optRound := eval_state ( ↓ ( RoundsBase_Ф_fetchRound 2 ) ) l_fin in                  
let round := maybeGet optRound in 
let stakes :=  round ->> RoundsBase_ι_Round_ι_stakes in
let optStake := stakes ->fetch msg_sender_addOrdinaryStakeP in
let optStakeV := stakes ->fetch validatorWallet in
let current_stakes := maybeGet optStake in
let current_stakesV := maybeGet optStakeV in 
round ->> RoundsBase_ι_Round_ι_stake = stakeP + stakeV + reward + rewardV
/\ current_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary  = stakeP + reward
/\ current_stakesV ->> RoundsBase_ι_StakeValue_ι_ordinary  = stakeV + rewardV.

Proof.

Abort.



End Scenario9.