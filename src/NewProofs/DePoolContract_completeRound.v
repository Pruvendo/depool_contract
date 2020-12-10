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
Module DePoolContract_Ф_completeRound (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.

Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair.


Definition DePoolContract_Ф_completeRound_while1 (Л_maxQty Л_roundId: XInteger) : LedgerT (XBool # True) := 
         While  ( ↑17 D2! LocalState_ι_completeRound_Л_restParticipant ?> $ xInt0 ) do (
                U0! Л_curGroup := ( ( ↑17 D2! LocalState_ι_completeRound_Л_restParticipant ) ?< ( $ Л_maxQty ) !|
                                   ( ( (↑17 D2! LocalState_ι_completeRound_Л_msgQty) !+ $ xInt1 ) ?== $ DePool_ι_MAX_QTY_OF_OUT_ACTIONS ) ) ? 
             ( ↑17 D2! LocalState_ι_completeRound_Л_restParticipant ) :::  
                 ( $ Л_maxQty ) ;		                
                ( ->sendMessage {||
                contractMessage ::= {|| messageBounce ::= $xBoolFalse , messageFlag ::= $xInt1 ||} , 
                                contractFunction ::= DePoolContract_Ф_completeRoundF (!! $Л_roundId , $ Л_curGroup !!)
                                ||}	)  >>
                ( ↑17 U1! LocalState_ι_completeRound_Л_restParticipant !-= $ Л_curGroup ) >>
                continue! I
        )  .

Definition DePoolContract_Ф_completeRound_while2 (Л_participantQty Л_roundId: XInteger) := 
         While  ( ↑17 D2! LocalState_ι_completeRound_Л_i ?< $ Л_participantQty ) do (
                ( ->sendMessage {||
                            contractMessage ::= {|| messageBounce ::= $xBoolFalse , messageFlag ::= $ xInt1 ||} , 
                            contractFunction ::= DePoolContract_Ф_completeRoundWithChunkF (!! $Л_roundId , $ DePool_ι_MAX_MSGS_PER_TR !!)
                            ||}	)  >>
                    continue! I		
         ) .

Definition DePoolContract_Ф_completeRound' ( Л_roundId : XInteger64 )
                                    ( Л_participantQty : XInteger32 ) 
                                    : LedgerT ( XErrorValue True XInteger ) := 
Require2 {{ msg_sender () ?== tvm_address (),  $ Errors_ι_IS_NOT_DEPOOL }} ; 
tvm_accept () >> 
Require2 {{ RoundsBase_Ф_isRound2 (! $ Л_roundId !) !| ↑12 D2! DePoolContract_ι_m_poolClosed , $ InternalErrors_ι_ERROR522 }} ; 
U0! Л_optRound := RoundsBase_Ф_fetchRound (! $ Л_roundId !) ; 
Require2 {{ ($ Л_optRound) ->hasValue,  $ InternalErrors_ι_ERROR519 }} ; 
U0! Л_round := ($ Л_optRound) ->get ; 
Require {{ ( ( $ Л_round ->> RoundsBase_ι_Round_ι_step ) ?== ( $ RoundsBase_ι_RoundStepP_ι_Completing ) ) , $ InternalErrors_ι_ERROR518 }} ; 
( ->sendMessage {||
	                contractMessage ::= {|| messageBounce ::= $xBoolFalse , messageFlag ::= $xInt1 ||} , 
			           contractFunction ::= DePoolContract_Ф_completeRoundWithChunkF (!! $Л_roundId , $ xInt1 !!)
					||}	) >> 
tvm_commit () >> 
U0! Л_outActionQty := ( ( $ Л_participantQty !+ ( $ DePool_ι_MAX_MSGS_PER_TR ) !- $ xInt1 ) !/ ( $ DePool_ι_MAX_MSGS_PER_TR ) ) ; 
(If ( $ Л_outActionQty ?> ( $ DePool_ι_MAX_QTY_OF_OUT_ACTIONS ) ) then  {
	U0! Л_maxQty := ( $ DePool_ι_MAX_QTY_OF_OUT_ACTIONS ) !* ($ DePool_ι_MAX_MSGS_PER_TR ) ; 
	(↑17 U1! LocalState_ι_completeRound_Л_restParticipant := $ Л_participantQty) >> 

	( ↑17 U1! LocalState_ι_completeRound_Л_msgQty := $ xInt0 ) >>
        DePoolContract_Ф_completeRound_while1 Л_maxQty Л_roundId >> 
        $ I } 
        else {
                ( ↑17 U1! LocalState_ι_completeRound_Л_i := $ xInt0 ) >>
                DePoolContract_Ф_completeRound_while2 Л_participantQty Л_roundId >>  
                $I		
        } ).

Opaque DePoolContract_Ф_completeRound_while1 DePoolContract_Ф_completeRound_while2.

Lemma DePoolContract_Ф_completeRound'_exec : forall ( Л_roundId : XInteger64 ) 
                                                   ( Л_participantQty : XInteger32 ) 
                                                   (l: Ledger) , 
                                           
let req : bool := ( eval_state msg_sender l ) =? ( eval_state tvm_address  l )  in
let l_tvm_accept :=  exec_state ( ↓ tvm_accept ) l  in
let req1 : bool := (  ( eval_state ( ↓ RoundsBase_Ф_isRound2 Л_roundId ) l ) 
                      || ( eval_state ( ↑12 ε DePoolContract_ι_m_poolClosed ) l ) )%bool  in
let optRound := eval_state ( ↓ ( RoundsBase_Ф_fetchRound Л_roundId ) ) l_tvm_accept in
let req2 : bool :=  isSome optRound  in
let round := maybeGet optRound  in
let req3 : bool :=  eqb ( round ->> RoundsBase_ι_Round_ι_step ) RoundsBase_ι_RoundStepP_ι_Completing   in

let oldMessages := VMState_ι_messages ( Ledger_ι_VMState l_tvm_accept ) in
let newMessage  := {| contractAddress :=  0 ;
                      contractFunction := DePoolContract_Ф_completeRoundWithChunkF Л_roundId 1 ;
                      contractMessage := {| messageValue := default ;
                                            messageFlag  := 1 ; 
                                            messageBounce := false
                                            |} |} in 
let l_message := {$ l_tvm_accept With ( VMState_ι_messages , newMessage :: oldMessages ) $} in  
let l_tvm_commit := exec_state ( ↓ tvm_commit ) l_message in
let MAX_MSGS_PER_TR := DePool_ι_MAX_MSGS_PER_TR in
let MAX_QTY_OF_OUT_ACTIONS := DePool_ι_MAX_QTY_OF_OUT_ACTIONS in
let outActionQty := (Л_participantQty + MAX_MSGS_PER_TR - 1) / MAX_MSGS_PER_TR in

let if1 : bool := outActionQty >? MAX_QTY_OF_OUT_ACTIONS in
let maxQty := MAX_QTY_OF_OUT_ACTIONS * MAX_MSGS_PER_TR in

let l1 := {$ l_tvm_commit With (LocalState_ι_completeRound_Л_restParticipant ,  Л_participantQty);
                               (LocalState_ι_completeRound_Л_msgQty , 0) $} in
let l2 := {$ l_tvm_commit With (LocalState_ι_completeRound_Л_i , 0) $} in                               

exec_state (DePoolContract_Ф_completeRound' Л_roundId Л_participantQty) l = 
if req then 
        if req1 then 
                if req2 then 
                        if req3 then 
                                if if1 then exec_state (DePoolContract_Ф_completeRound_while1 maxQty Л_roundId) l1 
                                else exec_state (DePoolContract_Ф_completeRound_while2 Л_participantQty Л_roundId) l2
                        else l_tvm_accept
                else l_tvm_accept
        else l_tvm_accept
else l.
Proof.
        intros.
        destructLedger l. 
        compute.
        Time repeat destructIf_solve. 
        all: try destructFunction2 DePoolContract_Ф_completeRound_while1; auto. idtac.
        all: try destructFunction2 DePoolContract_Ф_completeRound_while2; auto. 
Qed. 

Lemma DePoolContract_Ф_completeRound'_eval : forall ( Л_roundId : XInteger64 ) 
                                                   ( Л_participantQty : XInteger32 ) 
                                                   (l: Ledger) , 
                                           
let req : bool := ( eval_state msg_sender l ) =? ( eval_state tvm_address  l )  in
let l_tvm_accept :=  exec_state ( ↓ tvm_accept ) l  in
let req1 : bool := (  ( eval_state ( ↓ RoundsBase_Ф_isRound2 Л_roundId ) l ) 
                      || ( eval_state ( ↑12 ε DePoolContract_ι_m_poolClosed ) l ) )%bool  in
let optRound := eval_state ( ↓ ( RoundsBase_Ф_fetchRound Л_roundId ) ) l_tvm_accept in
let req2 : bool :=  isSome optRound  in
let round := maybeGet optRound  in
let req3 : bool :=  eqb ( round ->> RoundsBase_ι_Round_ι_step ) RoundsBase_ι_RoundStepP_ι_Completing   in

let oldMessages := VMState_ι_messages ( Ledger_ι_VMState l_tvm_accept ) in
let newMessage  := {| contractAddress :=  0 ;
                      contractFunction := DePoolContract_Ф_completeRoundWithChunkF Л_roundId 1 ;
                      contractMessage := {| messageValue := default ;
                                            messageFlag  := 1 ; 
                                            messageBounce := false
                                            |} |} in 
let l_message := {$ l_tvm_accept With ( VMState_ι_messages , newMessage :: oldMessages ) $} in  
let l_tvm_commit := exec_state ( ↓ tvm_commit ) l_message in
let MAX_MSGS_PER_TR := DePool_ι_MAX_MSGS_PER_TR in
let MAX_QTY_OF_OUT_ACTIONS := DePool_ι_MAX_QTY_OF_OUT_ACTIONS in
let outActionQty := (Л_participantQty + MAX_MSGS_PER_TR - 1) / MAX_MSGS_PER_TR in

let if1 : bool := outActionQty >? MAX_QTY_OF_OUT_ACTIONS in
let maxQty := MAX_QTY_OF_OUT_ACTIONS * MAX_MSGS_PER_TR in

let l1 := {$ l_tvm_commit With (LocalState_ι_completeRound_Л_restParticipant ,  Л_participantQty);
                               (LocalState_ι_completeRound_Л_msgQty , 0) $} in
let l2 := {$ l_tvm_commit With (LocalState_ι_completeRound_Л_i , 0) $} in                               

eval_state (DePoolContract_Ф_completeRound' Л_roundId Л_participantQty) l = 
if req then 
        if req1 then 
                if req2 then 
                        if req3 then Value I                              
                        else Error InternalErrors_ι_ERROR518
                else Error InternalErrors_ι_ERROR519
        else Error InternalErrors_ι_ERROR522
else Error Errors_ι_IS_NOT_DEPOOL .
Proof.
        intros.
        destructLedger l. 
        compute.
        Time repeat destructIf_solve. 
        all: try destructFunction2 DePoolContract_Ф_completeRound_while1; auto. idtac.
        all: try destructFunction2 DePoolContract_Ф_completeRound_while2; auto. 
Qed.


End DePoolContract_Ф_completeRound.