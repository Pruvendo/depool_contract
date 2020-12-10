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
Module RoundsBase_Ф_toTruncatedRound (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.


 Lemma RoundsBase_Ф_toTruncatedRound_exec : forall ( Л_round : RoundsBase_ι_Round ) (l: Ledger) , 
 	 exec_state (↓ RoundsBase_Ф_toTruncatedRound Л_round ) l = l .  
 Proof. 
   intros. destruct l. auto. 
 Qed. 
 
 Lemma RoundsBase_Ф_toTruncatedRound_eval : forall ( Л_round : RoundsBase_ι_Round ) (l: Ledger) , 
    eval_state (↓ RoundsBase_Ф_toTruncatedRound Л_round ) l = 
    RoundsBase_ι_TruncatedRoundC (Л_round ->> RoundsBase_ι_Round_ι_id)
                                 (Л_round ->> RoundsBase_ι_Round_ι_supposedElectedAt)
                                 (Л_round ->> RoundsBase_ι_Round_ι_unfreeze)
                                 (Л_round ->> RoundsBase_ι_Round_ι_stakeHeldFor)
                                 (Л_round ->> RoundsBase_ι_Round_ι_vsetHashInElectionPhase)
                                 (Л_round ->> RoundsBase_ι_Round_ι_step)
                                 (Л_round ->> RoundsBase_ι_Round_ι_completionReason)
                                 (Л_round ->> RoundsBase_ι_Round_ι_stake)
                                 (Л_round ->> RoundsBase_ι_Round_ι_recoveredStake)
                                 (Л_round ->> RoundsBase_ι_Round_ι_unused)
                                 (Л_round ->> RoundsBase_ι_Round_ι_isValidatorStakeCompleted)
                                 (Л_round ->> RoundsBase_ι_Round_ι_rewards)
                                 (Л_round ->> RoundsBase_ι_Round_ι_participantQty)
                                 (Л_round ->> RoundsBase_ι_Round_ι_validatorStake)
                                 (Л_round ->> RoundsBase_ι_Round_ι_validatorRemainingStake)
                                 (Л_round ->> RoundsBase_ι_Round_ι_handledStakesAndRewards).
 Proof. 
   intros. destruct l. auto. 
 Qed. 

 End RoundsBase_Ф_toTruncatedRound.