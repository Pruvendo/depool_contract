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
Module DePoolContract_Ф_withdrawFromPoolingRound (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.

Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair.

Opaque RoundsBase_Ф_withdrawStakeInPoolingRound DePoolFuncs.RoundsBase_Ф_withdrawStakeInPoolingRound.

Lemma DePoolContract_Ф_withdrawFromPoolingRound_exec: forall (Л_withdrawValue: Z) (l: Ledger),
 let sender := eval_state msg_sender l in 
 let isExtMsg : bool := negb (sender =? 0) in 
 let isPoolClosed : bool := eval_state (↑12 ε DePoolContract_ι_m_poolClosed) l in 
 let optParticipant := eval_state (↓ ParticipantBase_Ф_fetchParticipant sender) l in 
 let partHasValue : bool := xMaybeIsSome optParticipant in 
 let participant := maybeGet optParticipant  in 
 let minStake := eval_state (↑12 ε DePoolContract_ι_m_minStake) l in 
 let (rp', l_withdraw) := run (↓ RoundsBase_Ф_withdrawStakeInPoolingRound participant sender Л_withdrawValue minStake) l in
 let (removedPoolingStake, participant') := rp' in
 let sender' := eval_state msg_sender l_withdraw in 
 let l_set := exec_state (↓ ParticipantBase_Ф__setOrDeleteParticipant sender' participant') l_withdraw in
 let l_transfer := exec_state (tvm_transfer sender' removedPoolingStake false 64 default) l_set in 
 
 exec_state (↓ DePoolContract_Ф_withdrawFromPoolingRound Л_withdrawValue) l =
 if isExtMsg then
    if isPoolClosed then exec_state (DePoolContract_Ф__sendError DePool_ι_STATUS_DEPOOL_CLOSED 0 ) l
       else if (negb partHasValue) then exec_state (DePoolContract_Ф__sendError DePool_ι_STATUS_NO_PARTICIPANT 0 ) l 
                                   else l_transfer
 else l.      
 Proof.

  intros.
  destructLedger l. 
  compute.

  Time repeat destructIf_solve. idtac.
  all: try destructFunction4 RoundsBase_Ф_withdrawStakeInPoolingRound; auto. idtac. 
  all: try destruct x; auto. idtac.
  all: time repeat destructIf_solve. 

 Qed.
 

Lemma DePoolContract_Ф_withdrawFromPoolingRound'_eval: forall (Л_withdrawValue: Z) (l: Ledger),
let sender := eval_state msg_sender l in 
let isExtMsg : bool := negb ( sender =? 0) in 
let isPoolClosed : bool := eval_state (↑12 ε DePoolContract_ι_m_poolClosed) l in 
let optParticipant := eval_state (↓ ParticipantBase_Ф_fetchParticipant sender) l in 
let partHasValue : bool := xMaybeIsSome optParticipant in 

eval_state (↓ (DePoolContract_Ф_withdrawFromPoolingRound' Л_withdrawValue)) l = 
if isExtMsg then
   if isPoolClosed then Value (Error I) 
      else if (negb partHasValue) then Value (Error I) else Value (Value I)
else Error Errors_ι_IS_EXT_MSG .  
Proof.

  intros.
  destructLedger l. 
  compute.

  Time repeat destructIf_solve. idtac.
  all: try destructFunction4 RoundsBase_Ф_withdrawStakeInPoolingRound; auto. idtac. 
  all: try destruct x; auto. idtac.
  all: time repeat destructIf_solve. 

Qed.


Lemma DePoolContract_Ф_withdrawFromPoolingRound_eval: forall (Л_withdrawValue: Z) (l: Ledger),
let sender := eval_state msg_sender l in 
let isExtMsg : bool := negb ( sender =? 0) in 
let isPoolClosed : bool := eval_state (↑12 ε DePoolContract_ι_m_poolClosed) l in 
let optParticipant := eval_state (↓ ParticipantBase_Ф_fetchParticipant sender) l in 
let partHasValue : bool := xMaybeIsSome optParticipant in 

eval_state (↓ (DePoolContract_Ф_withdrawFromPoolingRound Л_withdrawValue)) l = 
if isExtMsg then
   if isPoolClosed then Value I 
      else if (negb partHasValue) then Value I else Value I
else Error Errors_ι_IS_EXT_MSG . 
Proof.

  intros.

  assert (eval_state (↓ DePoolContract_Ф_withdrawFromPoolingRound Л_withdrawValue) l = 
  xErrorMapDefaultF (xValue ∘ fromValueValue) (eval_state (↓ DePoolContract_Ф_withdrawFromPoolingRound' Л_withdrawValue) l) xError ).
  unfold DePoolContract_Ф_withdrawFromPoolingRound.
  unfold callEmbeddedStateAdj.
  remember (DePoolContract_Ф_withdrawFromPoolingRound' Л_withdrawValue).
  setoid_rewrite runbind.
  setoid_rewrite eval_bind2.
  rewrite eval_get.
  rewrite exec_get.
  remember (run l0 (injEmbed (T:=LocalState) DePoolFuncs.DePoolSpec.LedgerClass.local0 l)).
  setoid_rewrite <- Heqp.
  destruct p.
  destruct x.
  auto. auto.

  (**********************)
  rewrite H.
  rewrite DePoolContract_Ф_withdrawFromPoolingRound'_eval.
  compute.
  repeat destructIf; auto.
Qed.

  
End DePoolContract_Ф_withdrawFromPoolingRound.