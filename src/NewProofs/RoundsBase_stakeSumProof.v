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
Module RoundsBase_Ф_stakeSum (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.


Lemma RoundsBase_Ф_stakeSum_exec : forall (stakes: RoundsBase_ι_StakeValue) 
                                          (l: Ledger) , 
    exec_state (↓ RoundsBase_Ф_stakeSum stakes) l = l .
Proof.
  intros.
  destruct l. compute. 
  repeat destructIf; auto.
Qed.

Lemma RoundsBase_Ф_stakeSum_eval : forall (stakes: RoundsBase_ι_StakeValue) 
                                          (l: Ledger) , 
let ordStake := RoundsBase_ι_StakeValue_ι_ordinary stakes in
let vestingStake := RoundsBase_ι_InvestParams_ι_remainingAmount (maybeGet (RoundsBase_ι_StakeValue_ι_vesting stakes)) in
let lockStake := RoundsBase_ι_InvestParams_ι_remainingAmount (maybeGet (RoundsBase_ι_StakeValue_ι_lock stakes)) in    

    eval_state (↓ RoundsBase_Ф_stakeSum stakes) l = ordStake + vestingStake + lockStake.
Proof.
  intros.
  destruct l. compute. 
  destruct stakes;
  destruct RoundsBase_ι_StakeValue_ι_vesting;
  destruct RoundsBase_ι_StakeValue_ι_lock; try lia.
Qed.

Lemma RoundsBase_Ф_stakeSum_run : forall (stakes: RoundsBase_ι_StakeValue) 
                                          (l: Ledger) , 
let ordStake := RoundsBase_ι_StakeValue_ι_ordinary stakes in
let vestingStake := RoundsBase_ι_InvestParams_ι_remainingAmount (maybeGet (RoundsBase_ι_StakeValue_ι_vesting stakes)) in
let lockStake := RoundsBase_ι_InvestParams_ι_remainingAmount (maybeGet (RoundsBase_ι_StakeValue_ι_lock stakes)) in        

    run (↓ RoundsBase_Ф_stakeSum stakes) l = (ordStake + vestingStake + lockStake, l).
Proof.
  intros.
  rewrite run_eval_exec.
  rewrite RoundsBase_Ф_stakeSum_eval ,  RoundsBase_Ф_stakeSum_exec.
  auto.
Qed.

End RoundsBase_Ф_stakeSum.

