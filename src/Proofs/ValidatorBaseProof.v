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
(* Require Import depoolContract.Lib.CommonStateProofs. *)

(* Require Import MultiSigWallet.Proofs.tvmFunctionsProofs. *)

Import DePoolSpec.LedgerClass.SolidityNotations. 

Local Open Scope solidity_scope.


Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope solidity_scope.
Require Import Lists.List.
Import ListNotations.
Local Open Scope list_scope.

Existing Instance monadStateT.
Existing Instance monadStateStateT.


 (* function ValidatorBase.Constructor2 ( address validatorWallet )  internal  { 
        m_validatorWallet = validatorWallet ; 
     } 
Definition ValidatorBase_Ф_Constructor2 ( Л_validatorWallet : XAddress ) : LedgerT True := 
 ↑2 U1! ValidatorBase_ι_m_validatorWallet := $ Л_validatorWallet.
*) 

 Lemma ValidatorBase_Ф_Constructor2_exec : forall ( Л_validatorWallet : XAddress ) (l: Ledger) , 
    exec_state (  ValidatorBase_Ф_Constructor2 Л_validatorWallet ) l = 
    {$ l With ValidatorBase_ι_m_validatorWallet := Л_validatorWallet $} . 
 Proof. 
   intros. auto. 
 Qed. 
 
 Lemma ValidatorBase_Ф_Constructor2_eval : forall ( Л_validatorWallet : XAddress ) (l: Ledger) , 
 	 eval_state ( ValidatorBase_Ф_Constructor2 Л_validatorWallet ) l = I . 
 Proof. 
   intros. auto.
 Qed. 
 
