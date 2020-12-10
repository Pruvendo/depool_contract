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
Module DePoolContract_Ф_generateRound (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.


Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo.

Lemma DePoolContract_Ф_generateRound_exec : forall (l: Ledger) , 
let m_roundQty1 := ( eval_state ( ↑11 ε RoundsBase_ι_m_roundQty ) l ) + 1 in

    exec_state ( ↓ DePoolContract_Ф_generateRound ) l = 
    {$ l With ( RoundsBase_ι_m_roundQty , m_roundQty1 ) $} .  
 Proof. 
   intros. destruct l. auto. 
 Qed. 
 
Lemma DePoolContract_Ф_generateRound_eval : forall (l: Ledger) , 
let addr : XAddress := default in
let req (* : DePoolLib_ι_RequestP *) := default in
let n := eval_state (↑ε11 RoundsBase_ι_m_roundQty) l in 
let r : RoundsBase_ι_Round := RoundsBase_ι_RoundC n 0 DePoolLib_ι_MAX_TIME 
                0 0  RoundsBase_ι_RoundStepP_ι_PrePooling RoundsBase_ι_CompletionReasonP_ι_Undefined 
                0 0 0 false 0 0 0 xHMapEmpty 0 0 0 req 0 (eval_state (↓ ProxyBase_Ф_getProxy n ) l) 0 in
eval_state ( ↓ DePoolContract_Ф_generateRound ) l = r . 
 Proof.  
   intros. destruct l. auto. 
Qed. 

End DePoolContract_Ф_generateRound.