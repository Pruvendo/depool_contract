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
Module DePoolContract_Ф_sendAcceptAndReturnChange128 (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.



Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair.

(* function sendAcceptAndReturnChange128(uint64 fee) private { 
    tvm.rawReserve(address(this).balance - fee, 0); 
    IParticipant(msg.sender).receiveAnswer{value: 0, bounce: false, flag: 128}(STATUS_SUCCESS, 0); 
  } *) 

Lemma DePoolContract_Ф_sendAcceptAndReturnChange128_exec : forall (Л_fee: XInteger64) (l: Ledger) ,
let oldMessages := eval_state ( ↑16 ε VMState_ι_messages) l in
let newMessage  :=  {| contractAddress  := eval_state msg_sender l ;
                      contractFunction := IParticipant_И_receiveAnswerF DePool_ι_STATUS_SUCCESS 0 ;
                      contractMessage  := {$ default with (messageValue , 0) ;
                                                          (messageBounce ,false) ;
                                                          (messageFlag , 128) $} |}  in 
exec_state ( ↓ DePoolContract_Ф_sendAcceptAndReturnChange128 Л_fee ) l =  
{$ l With (VMState_ι_messages ,  newMessage :: oldMessages) ;
                 (VMState_ι_reserved ,  ( eval_state tvm_balance l ) - Л_fee)$} .  
Proof.
  intros. destruct l. auto. 
Qed. 

Lemma DePoolContract_Ф_sendAcceptAndReturnChange128_eval : forall (Л_fee: XInteger64)
                                                  ( l: Ledger ) ,
eval_state ( ↓ DePoolContract_Ф_sendAcceptAndReturnChange128 Л_fee ) l = I .
Proof.
  intros. destruct l. auto. 
Qed. 



End DePoolContract_Ф_sendAcceptAndReturnChange128.