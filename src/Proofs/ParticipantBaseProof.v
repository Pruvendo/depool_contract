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
 
Require Import depoolContract.DePoolFunc.
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.

Set Typeclasses Iterative Deepening.
Set Typeclasses Depth 100.


Require Import depoolContract.Lib.CommonModelProofs.
Module CommonModelProofs := CommonModelProofs StateMonadSig.
Import CommonModelProofs. 
Require Import depoolContract.Lib.Tactics.
Require Import depoolContract.Lib.ErrorValueProofs.

Require Import depoolContract.Lib.CommonStateProofs.

Import DePoolSpec.LedgerClass.SolidityNotations. 

Local Open Scope solidity_scope.

Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope solidity_scope.
Require Import Lists.List.
Import ListNotations.
Local Open Scope list_scope.


Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair.


Lemma ParticipantBase_Ф__setOrDeleteParticipant_exec : forall Л_addr Л_participant (l: Ledger),
 exec_state (ParticipantBase_Ф__setOrDeleteParticipant Л_addr Л_participant) l = 

 let roundQty := Л_participant ->> DePoolLib_ι_Participant_ι_roundQty in
 let m_participants := eval_state ( ↑5 ε ParticipantBase_ι_m_participants ) l in
 let bNoRounds := ( roundQty =? 0 ) in

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
 	 eval_state (  ParticipantBase_Ф__setOrDeleteParticipant Л_addr Л_participant ) l = I . 
 Proof.  
   intros. compute; destructIf; auto. 
 Qed. 
 
 
(*  function getOrCreateParticipant(address addr) internal view returns (DePoolLib.Participant) {
    optional(DePoolLib.Participant) optParticipant = m_participants.fetch(addr);
    if (optParticipant.hasValue()) {
        return optParticipant.get();
    }
    DePoolLib.Participant newParticipant = DePoolLib.Participant({
        roundQty: 0,
        reward: 0,
        haveVesting: false,
        haveLock: false,
        reinvest: true,
        withdrawValue: 0
    });
    return newParticipant;
} *)

(* Definition ParticipantBase_Ф_getOrCreateParticipant' ( Л_addr : XAddress ) : 
                                                        LedgerT (XValueValue DePoolLib_ι_Participant)  :=
    U0! Л_optParticipant := ↑5 D1! (D2! ParticipantBase_ι_m_participants) ->fetch $ Л_addr ; 
    If! (($ Л_optParticipant) ->hasValue ) then {
        ($Л_optParticipant) ->get >>= fun x => return! (xError x)
    }; 
    U0! Л_newParticipant := {||
        DePoolLib_ι_Participant_ι_roundQty := $ xInt0 ,
        DePoolLib_ι_Participant_ι_reward := $ xInt0 ,
        DePoolLib_ι_Participant_ι_haveVesting := $ xBoolFalse ,
        DePoolLib_ι_Participant_ι_haveLock := $ xBoolFalse ,
        DePoolLib_ι_Participant_ι_reinvest := $ xBoolTrue ,
        DePoolLib_ι_Participant_ι_withdrawValue := $ xInt0 
    ||} ;
        return! Л_newParticipant. *)

Lemma ParticipantBase_Ф_getOrCreateParticipant'_exec : forall ( Л_addr : XAddress ) 
                                                              (l: Ledger) ,
exec_state ( ParticipantBase_Ф_getOrCreateParticipant' Л_addr ) l = l.
Proof.
  intros. destruct l. compute; destructIf; auto.
Qed.

Lemma ParticipantBase_Ф_getOrCreateParticipant'_eval : forall ( Л_addr : XAddress ) 
                                                              (l: Ledger) ,
eval_state ( ParticipantBase_Ф_getOrCreateParticipant' Л_addr ) l =

let m_participants := eval_state ( ↑5 ε ParticipantBase_ι_m_participants ) l in
let optParticipant := m_participants ->fetch Л_addr in
let bOld := isSome optParticipant in
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


(* Definition fromValueValue {V} (x: XValueValue V) : V := xErrorMapDefaultF Datatypes.id x Datatypes.id.*)


(* Definition ParticipantBase_Ф_getOrCreateParticipant ( Л_addr : XAddress ) : LedgerT  DePoolLib_ι_Participant :=
  do r ← ParticipantBase_Ф_getOrCreateParticipant' Л_addr;
  return! (fromValueValue r). *)


Lemma ParticipantBase_Ф_getOrCreateParticipant_exec' : forall ( Л_addr : XAddress ) 
                                                              (l: Ledger) ,
exec_state ( ParticipantBase_Ф_getOrCreateParticipant Л_addr ) l = 
exec_state ( ParticipantBase_Ф_getOrCreateParticipant' Л_addr ) l.
Proof.
  intros. destruct l. compute; destructIf; auto.
Qed.


Lemma ParticipantBase_Ф_getOrCreateParticipant_exec : forall ( Л_addr : XAddress ) 
                                                              (l: Ledger) ,
exec_state ( ParticipantBase_Ф_getOrCreateParticipant Л_addr ) l = l.
Proof.
 intros. rewrite ParticipantBase_Ф_getOrCreateParticipant_exec'.
 rewrite ParticipantBase_Ф_getOrCreateParticipant'_exec.
 auto.
Qed.

Lemma ParticipantBase_Ф_getOrCreateParticipant_eval' : forall ( Л_addr : XAddress ) 
                                                              (l: Ledger) ,
eval_state ( ParticipantBase_Ф_getOrCreateParticipant Л_addr ) l = 

fromValueValue (eval_state ( ParticipantBase_Ф_getOrCreateParticipant' Л_addr ) l) .
Proof.
 intros.
 compute; destructIf; auto.
Qed.

Lemma ParticipantBase_Ф_getOrCreateParticipant_eval : forall ( Л_addr : XAddress ) 
                                                              (l: Ledger) ,
 eval_state ( ParticipantBase_Ф_getOrCreateParticipant Л_addr ) l = 

let m_participants := eval_state ( ↑5 ε ParticipantBase_ι_m_participants ) l in
let optParticipant := m_participants ->fetch Л_addr in
let bOld := isSome optParticipant in
  if bOld then  maybeGet optParticipant 
 else  
    {|
        DePoolLib_ι_Participant_ι_roundQty := 0 ;
        DePoolLib_ι_Participant_ι_reward := 0 ;
        DePoolLib_ι_Participant_ι_haveVesting := false ;
        DePoolLib_ι_Participant_ι_haveLock := false ;
        DePoolLib_ι_Participant_ι_reinvest := true ;
        DePoolLib_ι_Participant_ι_withdrawValue := 0 
    |}.
Proof.
 intros.
 rewrite  ParticipantBase_Ф_getOrCreateParticipant_eval'.
 rewrite  ParticipantBase_Ф_getOrCreateParticipant'_eval.
 simpl.
 destructIf; auto. 
Qed. 

