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
Module DePoolContract_Ф_checkPureDePoolBalance (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.



Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair.

(* function checkPureDePoolBalance() private returns (bool) { 
    uint stakes = totalParticipantFunds(0); 
    uint64 msgValue = uint64(msg.value); 
    uint sum = CRITICAL_THRESHOLD + stakes + msgValue; 
    if (address(this).balance < sum) { 
      uint replenishment = sum - address(this).balance; 
      emit TooLowDePoolBalance(replenishment); 
      return false; 
    } 
    return true; 
  } *) 


Opaque   DePoolContract_Ф_totalParticipantFunds.

Lemma DePoolContract_Ф_checkPureDePoolBalance'_exec : forall (l: Ledger) ,
let (stakes, l') := run ( ↓ DePoolContract_Ф_totalParticipantFunds 0 ) l in
let msgValue := eval_state msg_value l' in
let sum := DePool_ι_CRITICAL_THRESHOLD + stakes + msgValue in
let balance := eval_state tvm_balance l' in
let replenishment := sum - balance in
let oldEvents := eval_state (↑16 ε VMState_ι_events) l' in
let newEvent  := TooLowDePoolBalance replenishment in 
let l_emit := {$ l' With (VMState_ι_events ,  newEvent :: oldEvents ) $} in
let l' := if ( balance <? sum ) then l_emit
                                else l' in
 
exec_state ( ↓ DePoolContract_Ф_checkPureDePoolBalance' ) l = l' .
Proof.
  intros.
  destructLedger l. 
  compute. idtac.

  destructFunction1 DePoolContract_Ф_totalParticipantFunds; auto. idtac.
  repeat destructIf_solve2. 
Qed. 
 
Lemma DePoolContract_Ф_checkPureDePoolBalance'_eval : forall (l: Ledger) ,
let (stakes, l') := run ( ↓ DePoolContract_Ф_totalParticipantFunds 0 ) l in
let msgValue := eval_state msg_value l' in
let sum := DePool_ι_CRITICAL_THRESHOLD + stakes + msgValue in
let balance := eval_state tvm_balance l' in
let replenishment := sum - balance in
let oldEvents := eval_state (↑16 ε VMState_ι_events) l' in
let newEvent  := TooLowDePoolBalance replenishment in 
let l_emit := {$ l' With (VMState_ι_events ,  newEvent :: oldEvents ) $} in
let ret := if ( balance <? sum ) then Error false
                                 else Value true 
in
eval_state ( ↓ DePoolContract_Ф_checkPureDePoolBalance' ) l = ret .
Proof.
  intros.
  destructLedger l. 
  compute. idtac.

  destructFunction1 DePoolContract_Ф_totalParticipantFunds; auto. idtac.
  repeat destructIf_solve2. 
Qed. 

Opaque DePoolContract_Ф_checkPureDePoolBalance'.

Lemma DePoolContract_Ф_checkPureDePoolBalance_exec' : forall (l: Ledger) ,
exec_state ( ↓ DePoolContract_Ф_checkPureDePoolBalance ) l = 
exec_state ( ↓ DePoolContract_Ф_checkPureDePoolBalance' ) l .
Proof.
  intros.
  unfold DePoolContract_Ф_checkPureDePoolBalance.
  unfold callEmbeddedStateAdj.
  remember (DePoolContract_Ф_checkPureDePoolBalance' ).
  setoid_rewrite runbind.
  setoid_rewrite exec_bind.
  rewrite eval_get.
  rewrite exec_get.
  remember (run l0 (injEmbed (T:=LocalState) DePoolFuncs.DePoolSpec.LedgerClass.local0 l)).
  setoid_rewrite <- Heqp.
  destruct p.
  destruct x.
  auto. auto.
Qed.

Lemma DePoolContract_Ф_checkPureDePoolBalance_exec : forall (l: Ledger) ,
let (stakes, l') := run ( ↓ DePoolContract_Ф_totalParticipantFunds 0 ) l in
let msgValue := eval_state msg_value l' in
let sum := DePool_ι_CRITICAL_THRESHOLD + stakes + msgValue in
let balance := eval_state tvm_balance l' in
let replenishment := sum - balance in
let oldEvents := eval_state (↑16 ε VMState_ι_events) l' in
let newEvent  := TooLowDePoolBalance replenishment in 
let l_emit := {$ l' With (VMState_ι_events ,  newEvent :: oldEvents ) $} in
let l' := if ( balance <? sum ) then l_emit
                                else l' in
 
exec_state ( ↓ DePoolContract_Ф_checkPureDePoolBalance ) l = l' .
Proof.
  intros.
  rewrite DePoolContract_Ф_checkPureDePoolBalance_exec'.
  apply DePoolContract_Ф_checkPureDePoolBalance'_exec.
Qed. 

Lemma DePoolContract_Ф_checkPureDePoolBalance_eval' : forall (l: Ledger) ,
eval_state ( ↓ DePoolContract_Ф_checkPureDePoolBalance ) l = 
fromValueValue (eval_state ( ↓ DePoolContract_Ф_checkPureDePoolBalance' ) l) .
Proof.
  intros.
  unfold DePoolContract_Ф_checkPureDePoolBalance.
  unfold callEmbeddedStateAdj.
  remember (DePoolContract_Ф_checkPureDePoolBalance' ).
  setoid_rewrite runbind.
  setoid_rewrite eval_bind2.
  rewrite eval_get.
  rewrite exec_get.
  remember (run l0 (injEmbed (T:=LocalState) DePoolFuncs.DePoolSpec.LedgerClass.local0 l)).
  setoid_rewrite <- Heqp.
  destruct p.
  destruct x.
  auto. auto.
Qed.

Opaque fromValueValue exec_state eval_state run.

Lemma DePoolContract_Ф_checkPureDePoolBalance_eval : forall (l: Ledger) ,
let (stakes, l') := run ( ↓ DePoolContract_Ф_totalParticipantFunds 0 ) l in
let msgValue := eval_state msg_value l' in
let sum := DePool_ι_CRITICAL_THRESHOLD + stakes + msgValue in
let balance := eval_state tvm_balance l' in
let replenishment := sum - balance in
let oldEvents := eval_state (↑16 ε VMState_ι_events) l' in
let newEvent  := TooLowDePoolBalance replenishment in 
let l_emit := {$ l' With (VMState_ι_events ,  newEvent :: oldEvents ) $} in
let ret := if ( balance <? sum ) then  false
                                 else  true 
in
eval_state ( ↓ DePoolContract_Ф_checkPureDePoolBalance ) l = ret .
Proof.
  intros.
  rewrite DePoolContract_Ф_checkPureDePoolBalance_eval'.
  remember (run (↓ DePoolContract_Ф_totalParticipantFunds 0) l).
  case_eq p; intros.

  remember (DePoolContract_Ф_checkPureDePoolBalance'_eval l). clear Heqy.
  rewrite <- Heqp in y.
  rewrite H in y.

  setoid_rewrite y.
  rewrite if_fromValueValue.
  auto.
  
Qed.


End DePoolContract_Ф_checkPureDePoolBalance.