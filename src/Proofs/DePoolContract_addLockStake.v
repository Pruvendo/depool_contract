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
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.

(* Import SolidityNotations. *)
Set Typeclasses Iterative Deepening.
Set Typeclasses Depth 100.
(*Set Typeclasses Strict Resolution. *)
(* Set Typeclasses Debug.  *) 
(* Set Typeclasses Unique Instances. 
Unset Typeclasses Unique Solutions. *)

(* Existing Instance monadStateT.
Existing Instance monadStateStateT. *)
(* Module MultiSigWalletSpecSig := MultiSigWalletSpecSig XTypesSig StateMonadSig. *)

Require Import depoolContract.Lib.CommonModelProofs.
Module CommonModelProofs := CommonModelProofs StateMonadSig.
Import CommonModelProofs. 
Require Import depoolContract.Lib.Tactics.
Require Import depoolContract.Lib.ErrorValueProofs.
Require Import depoolContract.Lib.CommonCommon.

(* Require Import MultiSigWallet.Proofs.tvmFunctionsProofs. *)

Import DePoolSpec.LedgerClass.SolidityNotations. 

Local Open Scope solidity_scope.

(* Require Import MultiSigWallet.Specifications._validatelimit_inlineSpec.
Module _validatelimit_inlineSpec := _validatelimit_inlineSpec MultiSigWalletSpecSig.
Import _validatelimit_inlineSpec. *)

Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope solidity_scope.
Require Import Lists.List.
Import ListNotations.
Local Open Scope list_scope.

 (* function addLockStake(uint64 stake, address beneficiary, uint32 withdrawalPeriod, uint32 totalPeriod) public {
        addVestingOrLock(stake, beneficiary, withdrawalPeriod, totalPeriod, false);											
*) 

Opaque DePoolContract_Ф_addVestingOrLock.
Lemma DePoolContract_Ф_addLockStake_exec : forall ( Л_stake : XInteger64 )
                                                   (Л_beneficiary: XAddress)
										                               (Л_withdrawalPeriod: XInteger32)
										                               (Л_totalPeriod: XInteger32)
                                                   (l: Ledger) , 
exec_state ( ↓ ( DePoolContract_Ф_addLockStake Л_stake Л_beneficiary Л_withdrawalPeriod Л_totalPeriod ) ) l = 
exec_state ( ↓ 
          ( DePoolContract_Ф_addVestingOrLock Л_stake Л_beneficiary Л_withdrawalPeriod Л_totalPeriod xBoolFalse ) ) l .  
 Proof. 
   intros. destruct l. compute. idtac.
   remember (DePoolContract_Ф_addVestingOrLock
   Л_stake
   Л_beneficiary
   Л_withdrawalPeriod
   Л_totalPeriod
   false).
   destruct l; auto.
   destruct p; auto.
 Qed. 
 
 Lemma DePoolContract_Ф_addLockStake_eval : forall ( Л_stake : XInteger64 )
                                                   (Л_beneficiary: XAddress)
										                               (Л_withdrawalPeriod: XInteger32)
										                               (Л_totalPeriod: XInteger32)
                                                   (l: Ledger) ,
eval_state ( ↓ ( DePoolContract_Ф_addLockStake Л_stake Л_beneficiary Л_withdrawalPeriod Л_totalPeriod ) ) l = 
eval_state ( ↓ ( DePoolContract_Ф_addVestingOrLock Л_stake Л_beneficiary Л_withdrawalPeriod Л_totalPeriod xBoolFalse ) ) l .  
 Proof. 
  intros. destruct l. compute. idtac.
  remember (DePoolContract_Ф_addVestingOrLock
  Л_stake
  Л_beneficiary
  Л_withdrawalPeriod
  Л_totalPeriod
  false).
  destruct l; auto.
  destruct p; auto. 
Qed. 
 
