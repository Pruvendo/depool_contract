
Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.
Require Import Setoid.
Require Import ZArith.
Require Import Psatz.


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

Require Import depoolContract.NewProofs.ProofHelpers.
Require Import depoolContract.DePoolFunc.

(* Set Typeclasses Iterative Deepening.
Set Typeclasses Depth 100. *)

Require Import depoolContract.Lib.CommonModelProofs.
Module CommonModelProofs := CommonModelProofs StateMonadSig.
Import CommonModelProofs. 
Require Import depoolContract.Lib.Tactics.
Require Import depoolContract.Lib.ErrorValueProofs.
Require Import depoolContract.Lib.CommonCommon.

(* Require Import MultiSigWallet.Proofs.tvmFunctionsProofs. *)

Import DePoolSpec.LedgerClass.SolidityNotations. 

Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope solidity_scope.
Require Import Lists.List.
Import ListNotations.
Local Open Scope list_scope.

Require Import depoolContract.DePoolConsts.
Module DePoolContract_Ф_acceptRewardAndStartRoundCompleting (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.

Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair intMin.
Opaque  DePoolContract_Ф_startRoundCompleting.    

Lemma DePoolContract_Ф_acceptRewardAndStartRoundCompleting_eval : forall ( Л_round2 : RoundsBase_ι_Round ) 
                                                                          ( Л_value : XInteger64 ) 
                                                                          (l: Ledger) , 
let round2 := Л_round2 in 
let effectiveStake := ( round2 ->> RoundsBase_ι_Round_ι_stake ) - ( round2 ->> RoundsBase_ι_Round_ι_unused ) in
let reward := Л_value - effectiveStake in
let round2 := {$ round2 with RoundsBase_ι_Round_ι_grossReward := reward $} in
let RET_OR_REINV_FEE := DePool_ι_RET_OR_REINV_FEE in 

let m_participantRewardFraction := eval_state ( ↑12 ε DePoolContract_ι_m_participantRewardFraction) l in
let m_validatorRewardFraction := eval_state ( ↑12 ε DePoolContract_ι_m_validatorRewardFraction) l in
let m_validatorWallet := eval_state ( ↑2 ε ValidatorBase_ι_m_validatorWallet) l in 

let newReward := reward - (intMin reward (RET_OR_REINV_FEE + (round2 ->> RoundsBase_ι_Round_ι_participantQty) * RET_OR_REINV_FEE)) in
let newReward' := newReward * m_participantRewardFraction / 100 in
let round2' := {$ round2 with RoundsBase_ι_Round_ι_rewards := newReward' $} in

let validatorReward := newReward * m_validatorRewardFraction / 100 in

let l1 :=  exec_state ( ↓ tvm_transfer m_validatorWallet validatorReward false 1 default ) l in

(* let associationReward := reward * ( eval_state ( ↑12 ε DePoolContract_ι_m_validatorRewardFraction ) l1 ) / 100  in
let if2 : bool := ( negb ( associationReward =? 0 ) ) in
let l2 := if if2 then exec_state (  tvm_transfer (  eval_state ( ↑2 ε ValidatorBase_ι_m_validatorWallet ) l1 )
                                                associationReward  
                                                false  
                                                1
                                                default ) l1 else l1 in
 *)
eval_state ( ↓ DePoolContract_Ф_acceptRewardAndStartRoundCompleting Л_round2 Л_value ) l = 
eval_state ( ↓ DePoolContract_Ф_startRoundCompleting round2' RoundsBase_ι_CompletionReasonP_ι_RewardIsReceived  ) l1.
 Proof. 

  intros.
  destructLedger l. 
  destruct Л_round2.
  compute.

  Time repeat destructIf_solve. idtac.
  destructFunction2 DePoolContract_Ф_startRoundCompleting; auto. 

 Qed.
 
 Lemma DePoolContract_Ф_acceptRewardAndStartRoundCompleting_exec : forall ( Л_round2 : RoundsBase_ι_Round ) 
                                                                          ( Л_value : XInteger64 ) 
                                                                          (l: Ledger) , 
let round2 := Л_round2 in 
let effectiveStake := ( round2 ->> RoundsBase_ι_Round_ι_stake ) - ( round2 ->> RoundsBase_ι_Round_ι_unused ) in
let reward := Л_value - effectiveStake in
let round2 := {$ round2 with RoundsBase_ι_Round_ι_grossReward := reward $} in
let RET_OR_REINV_FEE := DePool_ι_RET_OR_REINV_FEE in 

let m_participantRewardFraction := eval_state ( ↑12 ε DePoolContract_ι_m_participantRewardFraction) l in
let m_validatorRewardFraction := eval_state ( ↑12 ε DePoolContract_ι_m_validatorRewardFraction) l in
let m_validatorWallet := eval_state ( ↑2 ε ValidatorBase_ι_m_validatorWallet) l in 

let newReward := reward - (intMin reward (RET_OR_REINV_FEE + (round2 ->> RoundsBase_ι_Round_ι_participantQty) * RET_OR_REINV_FEE)) in
let newReward' := newReward * m_participantRewardFraction / 100 in
let round2' := {$ round2 with RoundsBase_ι_Round_ι_rewards := newReward' $} in

let validatorReward := newReward * m_validatorRewardFraction / 100 in

let l1 :=  exec_state ( ↓ tvm_transfer m_validatorWallet validatorReward false 1 default ) l in

(* let associationReward := reward * ( eval_state ( ↑12 ε DePoolContract_ι_m_validatorRewardFraction ) l1 ) / 100  in
let if2 : bool := ( negb ( associationReward =? 0 ) ) in
let l2 := if if2 then exec_state (  tvm_transfer (  eval_state ( ↑2 ε ValidatorBase_ι_m_validatorWallet ) l1 )
                                                associationReward  
                                                false  
                                                1
                                                default ) l1 else l1 in
 *)
exec_state ( ↓ DePoolContract_Ф_acceptRewardAndStartRoundCompleting Л_round2 Л_value ) l = 
exec_state ( ↓ DePoolContract_Ф_startRoundCompleting round2' RoundsBase_ι_CompletionReasonP_ι_RewardIsReceived  ) l1.
 Proof. 

  intros.
  destructLedger l. 
  destruct Л_round2.
  compute.

  Time repeat destructIf_solve. idtac.
  destructFunction2 DePoolContract_Ф_startRoundCompleting; auto. 

 Qed.

 End DePoolContract_Ф_acceptRewardAndStartRoundCompleting.