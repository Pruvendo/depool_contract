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

Require Import depoolContract.Lib.CommonStateProofs.

Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope solidity_scope.
Require Import Lists.List.
Import ListNotations.
Local Open Scope list_scope.

Require Import depoolContract.DePoolConsts.
Module DePoolContract_Ф_setLastRoundInfo (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.



Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair.

(* function setLastRoundInfo(Round round) internal {
        LastRoundInfo info = LastRoundInfo({
            supposedElectedAt: round.supposedElectedAt,
            participantRewardFraction: m_participantRewardFraction,
            validatorRewardFraction: m_validatorRewardFraction,
            participantQty: round.participantQty,
            roundStake: round.stake,
            validatorWallet: m_validatorWallet,
            validatorPubkey: tvm.pubkey(),
            validatorAssurance: m_validatorAssurance,
            reward: round.grossReward,
            reason: uint8(round.completionReason),
            isDePoolClosed: m_poolClosed
        });
        lastRoundInfo[false] = info; } *) 


Lemma DePoolContract_Ф_setLastRoundInfo_exec : forall ( Л_round : RoundsBase_ι_Round )
                                                      (l: Ledger) ,
let info : DePool_ι_LastRoundInfo := {|
   DePool_ι_LastRoundInfo_ι_supposedElectedAt :=     Л_round ->> RoundsBase_ι_Round_ι_supposedElectedAt ; 
   DePool_ι_LastRoundInfo_ι_participantRewardFraction := eval_state ( ↑12 ε DePoolContract_ι_m_participantRewardFraction ) l ; 
   DePool_ι_LastRoundInfo_ι_validatorRewardFraction :=  eval_state ( ↑12 ε DePoolContract_ι_m_validatorRewardFraction ) l ; 
   DePool_ι_LastRoundInfo_ι_participantQty :=       Л_round ->> RoundsBase_ι_Round_ι_participantQty ; 
   DePool_ι_LastRoundInfo_ι_roundStake :=         Л_round ->> RoundsBase_ι_Round_ι_stake ; 
   DePool_ι_LastRoundInfo_ι_validatorWallet :=     eval_state ( ↑2 ε ValidatorBase_ι_m_validatorWallet ) l ; 
   DePool_ι_LastRoundInfo_ι_validatorPubkey :=      eval_state tvm_pubkey l; 
   DePool_ι_LastRoundInfo_ι_validatorAssurance :=   eval_state ( ↑12 ε DePoolContract_ι_m_validatorAssurance ) l ; 
   DePool_ι_LastRoundInfo_ι_reward :=           Л_round ->> RoundsBase_ι_Round_ι_grossReward ; 
   DePool_ι_LastRoundInfo_ι_reason :=            Л_round ->> RoundsBase_ι_Round_ι_completionReason ; 
   DePool_ι_LastRoundInfo_ι_isDePoolClosed :=    eval_state  ( ↑12 ε DePoolContract_ι_m_poolClosed ) l
|} in 
let lastRoundInfo := eval_state (↑11 ε RoundsBase_ι_lastRoundInfo ) l in
let l' := {$ l With ( RoundsBase_ι_lastRoundInfo , lastRoundInfo [false] ← info ) $} in
exec_state ( ↓ DePoolContract_Ф_setLastRoundInfo Л_round ) l = l' .
Proof.
  intros. destruct l. auto.  
Qed. 
 
Lemma DePoolContract_Ф_setLastRoundInfo_eval : forall ( Л_round : RoundsBase_ι_Round )
                                                      (l: Ledger) ,
eval_state ( ↓ DePoolContract_Ф_setLastRoundInfo Л_round ) l = I .
Proof.
  intros. destruct l. auto. 
Qed. 

End DePoolContract_Ф_setLastRoundInfo.