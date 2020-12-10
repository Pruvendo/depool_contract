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
Module DePoolContract_Ф_isEmptyRound (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.



Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair.

(* function isEmptyRound(Round round) private pure returns (bool) { 
  return round.step == RoundStep.Completed || round.stake == 0; 
} *) 


Lemma DePoolContract_Ф_isEmptyRound_exec : forall (Л_round: RoundsBase_ι_Round)
                                                           (l: Ledger) ,
exec_state ( ↓ DePoolContract_Ф_isEmptyRound Л_round ) l = l .
Proof.
  intros. destruct l. auto. 
Qed. 

Lemma DePoolContract_Ф_isEmptyRound_eval : forall ( Л_round: RoundsBase_ι_Round )
                                                  ( l: Ledger ) ,
eval_state ( ↓ DePoolContract_Ф_isEmptyRound Л_round ) l = 
       ( ( eqb ( Л_round ->> RoundsBase_ι_Round_ι_step ) RoundsBase_ι_RoundStepP_ι_Completed ) ||
         ( Л_round ->> RoundsBase_ι_Round_ι_stake =? 0 ) )%bool.
Proof.
  intros. auto.
Qed. 



End DePoolContract_Ф_isEmptyRound.