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
Module DePoolContract_Ф_addOrdinaryStake (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.



Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair.


Definition DePoolContract_Ф_addOrdinaryStake'_header ( Л_stake : XInteger64 ) (f: XInteger64 -> XInteger64 -> LedgerT True) : 
           LedgerT ( XErrorValue (XValueValue True) XInteger ) := 
 Require {{ msg_sender () ?!= $ xInt0 , $ Errors_ι_IS_EXT_MSG }} ;
  If!! ( ↑12 D2! DePoolContract_ι_m_poolClosed ) then {  
   return!!! ( DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_DEPOOL_CLOSED , $ xInt0 !) ) } ; 
  U0! Л_msgValue :=  msg_value () ; 
  If!! ( $ Л_msgValue ?< $ Л_stake !+ $ DePool_ι_STAKE_FEE ) then { 
   return!!! ( DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_FEE_TOO_SMALL , $ DePool_ι_STAKE_FEE !) ) } ; 
 U0! Л_fee := $ Л_msgValue !- $ Л_stake ;
  If! ( $ Л_stake ?< ↑12 D2! DePoolContract_ι_m_minStake ) then { 
   return!!! ( DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_STAKE_TOO_SMALL , ↑ε12  DePoolContract_ι_m_minStake !) )  } ;
        f Л_stake Л_fee.

Definition DePoolContract_Ф_addOrdinaryStake'_tailer (Л_stake Л_fee: XInteger64) : LedgerT True :=    
  U0! Л_participant := ParticipantBase_Ф_getOrCreateParticipant (! msg_sender () !) ; 
  U0! Л_round := RoundsBase_Ф_getRound0 () ;
  U0! Л_empty := $default ; 
  U0! {( Л_round , Л_participant )} :=  RoundsBase_Ф__addStakes (! $ Л_round , 
                                                                  $ Л_participant , 
                                                                    msg_sender () , 
                                                                  $ Л_stake , 
                                                                  $ Л_empty , 
                                              $ Л_empty !) ; 
  RoundsBase_Ф_setRound0 (! $ Л_round !) >>
  (ParticipantBase_Ф__setOrDeleteParticipant (! msg_sender () , $ Л_participant !)) >>
  (DePoolContract_Ф_sendAcceptAndReturnChange128 (! $ Л_fee !)) . 
    

Opaque DePoolContract_Ф_sendAcceptAndReturnChange128 RoundsBase_Ф__addStakes. 


Lemma addOrdinaryStake'_tailer_exec: forall (Л_stake Л_fee: Z) (l: Ledger), 
let sender := eval_state msg_sender l in 
let (participant, l_getcreate) := run (↓ ParticipantBase_Ф_getOrCreateParticipant sender) l in

let round := eval_state (↓ RoundsBase_Ф_getRound0 ) l_getcreate in
let (rp' , l_addStakes) := run (↓ RoundsBase_Ф__addStakes round participant sender Л_stake None None) l_getcreate in
let (round', participant') := rp' in
let l_setRound := exec_state (↓ RoundsBase_Ф_setRound0 round') l_addStakes in
let sender' := eval_state msg_sender l_setRound in  
let l_setParticipant := exec_state (↓ ParticipantBase_Ф__setOrDeleteParticipant sender' participant') l_setRound in
let l_sendAccept := exec_state (↓ DePoolContract_Ф_sendAcceptAndReturnChange128 Л_fee) l_setParticipant in

exec_state (DePoolContract_Ф_addOrdinaryStake'_tailer Л_stake Л_fee) l = l_sendAccept.

Proof.
  intros.
  destructLedger l. 
  compute.

  Time repeat destructIf_solve. idtac.

  all: destructFunction6 RoundsBase_Ф__addStakes; auto. idtac.
  all: try destruct x; auto. idtac.

  all: time repeat destructIf_solve. 

Qed.

Lemma addOrdinaryStake'_header_exec: forall (Л_stake: Z) (l: Ledger) f, 
    let sender := eval_state msg_sender l in 
    let isExtMsg : bool := negb (sender =? 0) in 
    let isPoolClosed : bool := eval_state (↑12 ε DePoolContract_ι_m_poolClosed) l in 
    let minStake := eval_state (↑12 ε DePoolContract_ι_m_minStake) l in 
    let STAKE_FEE :=  DePool_ι_STAKE_FEE in
    let msg_value := eval_state msg_value l in 
    let feeSmall := msg_value <? Л_stake + STAKE_FEE in
    let fee := msg_value - Л_stake in
    let stakeSmall := Л_stake <? minStake in

    exec_state (DePoolContract_Ф_addOrdinaryStake'_header Л_stake f) l = 
    if isExtMsg then 
     if isPoolClosed then exec_state (DePoolContract_Ф__sendError DePool_ι_STATUS_DEPOOL_CLOSED 0 ) l
     else if feeSmall then exec_state (DePoolContract_Ф__sendError DePool_ι_STATUS_FEE_TOO_SMALL 
                                                                    DePool_ι_STAKE_FEE ) l
     else if stakeSmall then exec_state (DePoolContract_Ф__sendError DePool_ι_STATUS_STAKE_TOO_SMALL 
                                                                     (eval_state (↑ε12  DePoolContract_ι_m_minStake) l) ) l
     else exec_state (f Л_stake fee) l
    else l.
Proof.
  intros.
  destructLedger l. 
  compute.

  Time repeat destructIf_solve. idtac.
  destructFunction2 f; auto. 


Qed.



Lemma addOrdinaryStake_eval: forall (Л_stake: Z) (l: Ledger), 
let sender := eval_state msg_sender l in 
let isExtMsg : bool := negb (sender =? 0) in 
let isPoolClosed : bool := eval_state (↑12 ε DePoolContract_ι_m_poolClosed) l in 
let minStake := eval_state (↑12 ε DePoolContract_ι_m_minStake) l in 
let STAKE_FEE := DePool_ι_STAKE_FEE in
let msg_value := eval_state msg_value l in 
let feeSmall := msg_value <? Л_stake + STAKE_FEE in
let stakeSmall := Л_stake <? minStake in

eval_state (DePoolContract_Ф_addOrdinaryStake' Л_stake) l = 
if isExtMsg then 
 if isPoolClosed then Value (Error I) 
 else if feeSmall then Value (Error I)
 else if stakeSmall then Value (Error I)
 else Value (Value I)
else Error Errors_ι_IS_EXT_MSG .
Proof.

  intros.
  destructLedger l. 
  compute.

  Time repeat destructIf_solve. idtac.

  all: destructFunction6 RoundsBase_Ф__addStakes; auto. idtac.
  all: try destruct x; auto. idtac.

  all: time repeat destructIf_solve. 
    
Qed. 

End DePoolContract_Ф_addOrdinaryStake.

  
