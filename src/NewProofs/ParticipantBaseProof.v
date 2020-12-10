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
Module ParticipantBaseProofs (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.


Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair.


(* ParticipantBase_Ф__setOrDeleteParticipant *)

Lemma ParticipantBase_Ф__setOrDeleteParticipant_exec : forall Л_addr Л_participant (l: Ledger),
 let roundQty := Л_participant ->> DePoolLib_ι_Participant_ι_roundQty in
 let m_participants := eval_state ( ↑5 ε ParticipantBase_ι_m_participants ) l in
 let bNoRounds := ( roundQty =? 0 ) in

 exec_state (↓ ParticipantBase_Ф__setOrDeleteParticipant Л_addr Л_participant) l = 

 if bNoRounds 
 then {$ l With ParticipantBase_ι_m_participants := m_participants ->delete Л_addr $} 
 else {$ l With ParticipantBase_ι_m_participants := m_participants [ Л_addr ] ← Л_participant $}.

 Proof. 
   intros. destruct l. compute.
   destructIf; auto.
 Qed. 
 
 Lemma ParticipantBase_Ф__setOrDeleteParticipant_eval : forall ( Л_addr : XAddress ) 
                                                       ( Л_participant : DePoolLib_ι_Participant )
                                                       (l: Ledger) , 
 	 eval_state (↓  ParticipantBase_Ф__setOrDeleteParticipant Л_addr Л_participant ) l = I . 
 Proof.  
   intros. compute; destructIf; auto. 
 Qed. 
 
 
(* ParticipantBase_Ф_getOrCreateParticipant *) 

Lemma ParticipantBase_Ф_getOrCreateParticipant'_exec : forall ( Л_addr : XAddress ) 
                                                              (l: Ledger) ,
exec_state (↓ ParticipantBase_Ф_getOrCreateParticipant' Л_addr ) l = l.
Proof.
  intros. destruct l. compute; destructIf; auto.
Qed.

Lemma ParticipantBase_Ф_getOrCreateParticipant'_eval : forall ( Л_addr : XAddress ) 
                                                              (l: Ledger) ,
let m_participants := eval_state ( ↑5 ε ParticipantBase_ι_m_participants ) l in
let optParticipant := m_participants ->fetch Л_addr in
let bOld := isSome optParticipant in

eval_state (↓ ParticipantBase_Ф_getOrCreateParticipant' Л_addr ) l =

  if bOld then  Error ( maybeGet optParticipant )
 else  Value 
    {|
        DePoolLib_ι_Participant_ι_roundQty := 0 ;
        DePoolLib_ι_Participant_ι_reward := 0 ;
        DePoolLib_ι_Participant_ι_haveVesting := false ;
        DePoolLib_ι_Participant_ι_haveLock := false ;
        DePoolLib_ι_Participant_ι_reinvest := true ;
        DePoolLib_ι_Participant_ι_withdrawValue := 0 
    |}.
Proof. 
  intros.  destruct l. compute.
  destructIf ; auto.
Qed.

Opaque ParticipantBase_Ф_getOrCreateParticipant'.


Lemma ParticipantBase_Ф_getOrCreateParticipant_eval' : forall ( Л_addr : XAddress ) 
                                                              (l: Ledger) ,
eval_state (↓ ParticipantBase_Ф_getOrCreateParticipant Л_addr ) l = 

fromValueValue (eval_state (↓ ParticipantBase_Ф_getOrCreateParticipant' Л_addr ) l) .
Proof.
 intros.
 compute.
 destructFunction1 ParticipantBase_Ф_getOrCreateParticipant'.
 auto.
Qed.

Transparent ParticipantBase_Ф_getOrCreateParticipant'.

Lemma ParticipantBase_Ф_getOrCreateParticipant_eval : forall ( Л_addr : XAddress ) 
                                                              (l: Ledger) ,
let m_participants := eval_state ( ↑5 ε ParticipantBase_ι_m_participants ) l in
let optParticipant := m_participants ->fetch Л_addr in
let bOld := isSome optParticipant in

eval_state (↓ ParticipantBase_Ф_getOrCreateParticipant Л_addr ) l =

 if bOld then maybeGet optParticipant 
 else  
    {|
        DePoolLib_ι_Participant_ι_roundQty      := 0 ;
        DePoolLib_ι_Participant_ι_reward        := 0 ;
        DePoolLib_ι_Participant_ι_haveVesting   := false ;
        DePoolLib_ι_Participant_ι_haveLock      := false ;
        DePoolLib_ι_Participant_ι_reinvest      := true ;
        DePoolLib_ι_Participant_ι_withdrawValue := 0 
    |}.
Proof.
 intros.
 rewrite  ParticipantBase_Ф_getOrCreateParticipant_eval'.
 rewrite  ParticipantBase_Ф_getOrCreateParticipant'_eval.

 rewrite if_fromValueValue.
 auto.
Qed. 


Lemma ParticipantBase_Ф_getOrCreateParticipant_exec' : forall ( Л_addr : XAddress ) 
                                                              (l: Ledger) ,
exec_state (↓ ParticipantBase_Ф_getOrCreateParticipant Л_addr ) l = 
exec_state (↓ ParticipantBase_Ф_getOrCreateParticipant' Л_addr ) l.
Proof.
  intros. destruct l. compute; destructIf; auto.
Qed.


Lemma ParticipantBase_Ф_getOrCreateParticipant_exec : forall ( Л_addr : XAddress ) 
                                                              (l: Ledger) ,
exec_state (↓ ParticipantBase_Ф_getOrCreateParticipant Л_addr ) l = l.
Proof.
 intros. rewrite ParticipantBase_Ф_getOrCreateParticipant_exec'.
 rewrite ParticipantBase_Ф_getOrCreateParticipant'_exec.
 auto.
Qed.



End ParticipantBaseProofs.