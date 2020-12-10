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

Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair.

(* Opaque tvm_accept DePoolContract_Ф_checkPureDePoolBalance RoundsBase_Ф_getRound1. *)


Lemma ifSimpleState: forall X (b: bool) (f g: Ledger -> X * Ledger), 
(if b then SimpleState f else SimpleState g ) =
SimpleState (if b then f else  g).
Proof.
  intros. destruct b; auto.
Qed.  

Lemma ifFunApply: forall X (b: bool) (f g: Ledger -> X * Ledger) l, 
(if b then f else  g ) l =
(if b then f l else g l).
Proof.
  intros. destruct b; auto.
Qed. 



Lemma fstImplies : forall  X Y T (f: X*T) (g: X -> Y)  ,  (let (x, _) := f in g x) = g (fst f).
Proof.
  intros.
  destruct f; auto.
Qed.


Lemma sndImplies : forall  X Y T (f: X*T) (g: T -> Y)  ,  (let (_, t) := f in g t) = g (snd f).
Proof.
  intros.
  destruct f; auto.
Qed.

Lemma fstsndImplies : forall  X Y T (f: X*T) (g: X -> T -> Y)  ,  (let (x, t) := f in g x t) = g (fst f) (snd f).
Proof.
  intros.
  destruct f; auto.
Qed.


Ltac pr_numgoals := let n := numgoals in idtac "There are" n "goals".


(*
function withdrawPart(uint64 withdrawValue) public onlyInternalMessage {
        if (m_poolClosed) {
            return _sendError(STATUS_DEPOOL_CLOSED, 0);
        }

        optional(DePoolLib.Participant) optParticipant = fetchParticipant(msg.sender);
        if (!optParticipant.hasValue()) {
            return _sendError(STATUS_NO_PARTICIPANT, 0);
        }
        DePoolLib.Participant participant = optParticipant.get();

        participant.withdrawValue = withdrawValue;
        _setOrDeleteParticipant(msg.sender, participant);
        sendAcceptAndReturnChange();
    }
*)

Lemma DePoolContract_Ф_withdrawPart_exec : forall (l : Ledger)(Л_withdrawValue : XInteger64),
let sender := eval_state msg_sender l in
let isInternalMessage := negb (sender =? 0) in
let isPoolClosed : bool := eval_state (↑ε12 DePoolContract_ι_m_poolClosed) l in
let optParticipant := eval_state (↓ ParticipantBase_Ф_fetchParticipant sender) l in
let isEmptyParticipant : bool := negb (isSome optParticipant) in
let participant := maybeGet optParticipant in
let newParticipant := {$ participant with (DePoolLib_ι_Participant_ι_withdrawValue, Л_withdrawValue) $} in
let l_set := exec_state (↓ ParticipantBase_Ф__setOrDeleteParticipant sender newParticipant) l in
let l_send := exec_state (↓ DePoolContract_Ф_sendAcceptAndReturnChange) l_set in
let statusDepoolClosed := eval_state (↑12 ε DePoolContract_ι_STATUS_DEPOOL_CLOSED) l in
let statusNoParticipant := eval_state (↑12 ε DePoolContract_ι_STATUS_NO_PARTICIPANT) l in
exec_state (DePoolContract_Ф_withdrawPart' Л_withdrawValue) l =
if isInternalMessage then 
    if isPoolClosed then
        exec_state (↓ DePoolContract_Ф__sendError statusDepoolClosed 0) l else
        if isEmptyParticipant then
            exec_state (↓ DePoolContract_Ф__sendError statusNoParticipant 0) l
            else l_send
else l.
Proof.
    intros.
    destruct l. 
    destruct Ledger_ι_DebugDePool, Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ConfigParamsBase, Ledger_ι_ParticipantBase, 
    Ledger_ι_DePoolHelper, Ledger_ι_Errors, Ledger_ι_InternalErrors, Ledger_ι_DePoolLib, Ledger_ι_DePoolProxyContract, 
    Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_DePool, Ledger_ι_Participant, Ledger_ι_TestElector, 
    Ledger_ι_VMState, Ledger_ι_LocalState.
  
    compute. idtac.
  
  
    Time  repeat (
    
    time match goal with
  
      | |- ?x =>
        match x with
         
       
        | context [if ?b then _ else _] =>  idtac "if..." b; 
                                            repeat rewrite ifSimpleState ; 
                                            repeat rewrite ifFunApply ;
                                              (* compute ; *)
                                              (* let rem := fresh "rem" in  *)
                                              (* set (rem:= b) ;  *)
                                            case_eq b ; 
                                            simpl ; intros                                
         | context [let (x, t) := ?f in @?g x t] => idtac "let..." f g; 
                                                   replace (let (x, t) := f in g x t) with (g (fst f) (snd f)) 
                                                            by (symmetry; apply fstsndImplies) ;
                                                   destruct (snd f);          
                                                   simpl                                                                  
        | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
        end
  
   
    end) . 

    all: pr_numgoals.

Qed.

Lemma DePoolContract_Ф_withdrawPart_eval : forall (l : Ledger)(Л_withdrawValue : XInteger64),
let sender := eval_state msg_sender l in
let isInternalMessage := negb (sender =? 0) in
let isPoolClosed : bool := eval_state (↑ε12 DePoolContract_ι_m_poolClosed) l in
let optParticipant := eval_state (↓ ParticipantBase_Ф_fetchParticipant sender) l in
let isEmptyParticipant : bool := negb (isSome optParticipant) in
eval_state (DePoolContract_Ф_withdrawPart' Л_withdrawValue)  l =
if isInternalMessage then 
    if isPoolClosed then Value (Error I) else
        if isEmptyParticipant then Value (Error I)
    else Value (Value I)
else  Error (eval_state ( ↑7 ε Errors_ι_IS_EXT_MSG) l).
Proof.

    intros.
    destruct l. 
    destruct Ledger_ι_DebugDePool, Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ConfigParamsBase, Ledger_ι_ParticipantBase, 
    Ledger_ι_DePoolHelper, Ledger_ι_Errors, Ledger_ι_InternalErrors, Ledger_ι_DePoolLib, Ledger_ι_DePoolProxyContract, 
    Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_DePool, Ledger_ι_Participant, Ledger_ι_TestElector, 
    Ledger_ι_VMState, Ledger_ι_LocalState.
  
    compute. idtac.
  
  
    Time  repeat (
    
    time match goal with
  
      | |- ?x =>
        match x with
         
       
        | context [if ?b then _ else _] =>  idtac "if..." b; 
                                            repeat rewrite ifSimpleState ; 
                                            repeat rewrite ifFunApply ;
                                              (* compute ; *)
                                              (* let rem := fresh "rem" in  *)
                                              (* set (rem:= b) ;  *)
                                            case_eq b ; 
                                            simpl ; intros                                     
         | context [let (x, t) := ?f in @?g x t] => idtac "let..." f g; 
                                                   replace (let (x, t) := f in g x t) with (g (fst f) (snd f)) 
                                                            by (symmetry; apply fstsndImplies) ;
                                                   destruct (snd f);          
                                                   simpl                                                                  
        | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
        end
  
   
    end) . 

    all: pr_numgoals.

Qed.