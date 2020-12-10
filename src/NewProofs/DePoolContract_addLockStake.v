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
Module DePoolContract_Ф_addLockStake (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.


Opaque DePoolContract_Ф_addVestingOrLock.

Lemma DePoolContract_Ф_addLockStake_exec : forall ( Л_stake : XInteger64 )
                                                   (Л_beneficiary: XAddress)
										                               (Л_withdrawalPeriod: XInteger32)
										                               (Л_totalPeriod: XInteger32)
                                                   (l: Ledger) , 
exec_state ( ↓ DePoolContract_Ф_addLockStake Л_stake Л_beneficiary Л_withdrawalPeriod Л_totalPeriod ) l = 
exec_state ( ↓ DePoolContract_Ф_addVestingOrLock Л_stake Л_beneficiary Л_withdrawalPeriod Л_totalPeriod xBoolFalse ) l .  
 Proof. 
  intros.
  destructLedger l. 
  compute.

  destructFunction5 DePoolContract_Ф_addVestingOrLock; auto. 
 Qed. 
 
 Lemma DePoolContract_Ф_addLockStake_eval : forall ( Л_stake : XInteger64 )
                                                   (Л_beneficiary: XAddress)
										                               (Л_withdrawalPeriod: XInteger32)
										                               (Л_totalPeriod: XInteger32)
                                                   (l: Ledger) ,
eval_state ( ↓ DePoolContract_Ф_addLockStake Л_stake Л_beneficiary Л_withdrawalPeriod Л_totalPeriod )  l = 
eval_state ( ↓ DePoolContract_Ф_addVestingOrLock Л_stake Л_beneficiary Л_withdrawalPeriod Л_totalPeriod xBoolFalse )  l .  
 Proof. 
  intros.
  destructLedger l. 
  compute.

  destructFunction5 DePoolContract_Ф_addVestingOrLock; auto. 
Qed. 
 
Lemma DePoolContract_Ф_addVestingStake_exec : forall ( Л_stake : XInteger64 )
                                                   (Л_beneficiary: XAddress)
										                               (Л_withdrawalPeriod: XInteger32)
										                               (Л_totalPeriod: XInteger32)
                                                   (l: Ledger) , 
exec_state ( ↓ DePoolContract_Ф_addVestingStake Л_stake Л_beneficiary Л_withdrawalPeriod Л_totalPeriod ) l = 
exec_state ( ↓ DePoolContract_Ф_addVestingOrLock Л_stake Л_beneficiary Л_withdrawalPeriod Л_totalPeriod xBoolTrue ) l .  
 Proof. 
  intros.
  destructLedger l. 
  compute.

  destructFunction5 DePoolContract_Ф_addVestingOrLock; auto. 
 Qed. 
 
 Lemma DePoolContract_Ф_addVesingStake_eval : forall ( Л_stake : XInteger64 )
                                                   (Л_beneficiary: XAddress)
										                               (Л_withdrawalPeriod: XInteger32)
										                               (Л_totalPeriod: XInteger32)
                                                   (l: Ledger) ,
eval_state ( ↓ DePoolContract_Ф_addVestingStake Л_stake Л_beneficiary Л_withdrawalPeriod Л_totalPeriod )  l = 
eval_state ( ↓ DePoolContract_Ф_addVestingOrLock Л_stake Л_beneficiary Л_withdrawalPeriod Л_totalPeriod xBoolTrue )  l .  
 Proof. 
  intros.
  destructLedger l. 
  compute.

  destructFunction5 DePoolContract_Ф_addVestingOrLock; auto. 
Qed. 


End DePoolContract_Ф_addLockStake.