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
Module DePoolContract_Ф_terminator (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.


Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair.

Import TVMModel.LedgerClass.
Opaque DePoolContract_Ф_startRoundCompleting roundStepEqb.


Definition DePoolContract_Ф_terminator_header f : LedgerT ( XErrorValue True XInteger ) := 
(*require(msg.pubkey() == tvm.pubkey(), Errors.IS_NOT_OWNER);*) 	 
Require2 {{ msg_pubkey () ?== tvm_pubkey () , ξ$ Errors_ι_IS_NOT_OWNER }} ; 
(*require(!m_poolClosed, Errors.DEPOOL_IS_CLOSED);*) 
Require {{ !¬ ↑12 D2! DePoolContract_ι_m_poolClosed , ξ$ Errors_ι_DEPOOL_IS_CLOSED }} ; 
(* m_poolClosed = true; *) 
(↑12 U1! DePoolContract_ι_m_poolClosed := $xBoolTrue) >> 
(* tvm.commit(); *) 
tvm_commit () >> 
(* tvm.accept(); *) 
tvm_accept () >> 


(* Round roundPre0 = getRoundPre0(); *) 
declareLocal Л_roundPre0 :>: RoundsBase_ι_Round := RoundsBase_Ф_getRoundPre0 (); 
(* Round round0 = getRound0(); *) 
declareLocal Л_round0 :>: RoundsBase_ι_Round := RoundsBase_Ф_getRound0 (); 
(*Round round1 = getRound1();*) 
(↑↑17 U2! LocalState_ι_terminator_Л_round1 := RoundsBase_Ф_getRound1 () ) >> 

(* roundPre0 = startRoundCompleting(roundPre0, CompletionReason.PoolClosed); *) 
U0! Л_roundPre0 := DePoolContract_Ф_startRoundCompleting (! $ Л_roundPre0 , 
														 ξ$ RoundsBase_ι_CompletionReasonP_ι_PoolClosed !) ; 
(*round0 = startRoundCompleting(round0, CompletionReason.PoolClosed);*) 
U0! Л_round0 := DePoolContract_Ф_startRoundCompleting (! $ Л_round0 , 
														 ξ$ RoundsBase_ι_CompletionReasonP_ι_PoolClosed !) ; 
(* if (round1.step == RoundStep.WaitingValidatorRequest) { 
	round1 = startRoundCompleting(round1, CompletionReason.PoolClosed); 
} *) 
(If (↑17 D2! LocalState_ι_terminator_Л_round1 ^^ RoundsBase_ι_Round_ι_step ?== ξ$ RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest) then { 
	↑↑17 U2! LocalState_ι_terminator_Л_round1 := DePoolContract_Ф_startRoundCompleting (! ↑17 D2! LocalState_ι_terminator_Л_round1 , 
																						  ξ$ RoundsBase_ι_CompletionReasonP_ι_PoolClosed !) 
}) >> f Л_roundPre0 Л_round0.


Definition DePoolContract_Ф_terminator_tailer Л_roundPre0 Л_round0 : LedgerT True := 
(* emit DePoolClosed(); *) 
->emit $ DePoolClosed >> 
(* setRoundPre0(roundPre0); *) 
(RoundsBase_Ф_setRoundPre0 (! $ Л_roundPre0 !) ) >> 
(* setRound0(round0); *) 
(RoundsBase_Ф_setRound0 (! $ Л_round0 !) ) >> 
(* setRound1(round1); *) 
(RoundsBase_Ф_setRound1 (! ↑17 D2! LocalState_ι_terminator_Л_round1 !) )  .


Lemma DePoolContract_Ф_terminator_eval : forall (l : Ledger),

let isOwner := eval_state msg_pubkey l =? eval_state tvm_pubkey l in
let isNotClosed := negb (eval_state (↑12 ε DePoolContract_ι_m_poolClosed) l) in

eval_state DePoolContract_Ф_terminator l =

if isOwner then 
   if isNotClosed then Value I
                  else Error Errors_ι_DEPOOL_IS_CLOSED
           else Error Errors_ι_IS_NOT_OWNER.
Proof.    
  
  
  intros.
  destructLedger l. 
  compute.
  Time repeat destructIf_solve. idtac.


  all: try destructFunction2 DePoolContract_Ф_startRoundCompleting; auto. idtac. 
  all: try destructFunction2 DePoolContract_Ф_startRoundCompleting; auto. idtac. 
  all: repeat destructIf_solve. idtac.
  all: try destructFunction2 DePoolContract_Ф_startRoundCompleting; auto. 
  
Qed.  
  
  

Lemma DePoolContract_Ф_terminator_tailer_exec : forall Л_roundPre0 Л_round0 (l : Ledger),
let oldEvents := eval_state (↑16 ε VMState_ι_events) l in
let l_emit := {$l With (VMState_ι_events ,  DePoolClosed :: oldEvents ) $} in
let l_setPre0 := exec_state (↓ RoundsBase_Ф_setRoundPre0 Л_roundPre0) l_emit in
let l_set0 := exec_state (↓ RoundsBase_Ф_setRound0 Л_round0) l_setPre0 in
let round1 := eval_state (↑17 ε LocalState_ι_terminator_Л_round1) l in
let l_set1 := exec_state (↓ RoundsBase_Ф_setRound1 round1) l_set0 in

exec_state (DePoolContract_Ф_terminator_tailer Л_roundPre0 Л_round0) l = l_set1.

Proof.
  intros.
  destructLedger l. 
  compute.
  Time repeat destructIf_solve. 
Qed.

Import LedgerClass.

Lemma DePoolContract_Ф_terminator_header_exec : forall f (l : Ledger),
let isOwner := eval_state msg_pubkey l =? eval_state tvm_pubkey l in
let isNotClosed := negb (eval_state (↑12 ε DePoolContract_ι_m_poolClosed) l) in

let closedDePool := {$ l With (DePoolContract_ι_m_poolClosed, true) $} in
let commited :=  exec_state (↓ tvm_commit) closedDePool in
let accepted :=  exec_state (↓ tvm_accept) commited in

let oldRoundPre0 := eval_state RoundsBase_Ф_getRoundPre0 l in
let oldRound0 := eval_state RoundsBase_Ф_getRound0 l in 
let oldRound1 := eval_state RoundsBase_Ф_getRound1 l in 

let round1ToBeUpdated : bool := eqb (RoundsBase_ι_Round_ι_step oldRound1) RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest in
let (srcPre0, l_pre0) := run (↓ DePoolContract_Ф_startRoundCompleting oldRoundPre0 RoundsBase_ι_CompletionReasonP_ι_PoolClosed) accepted in
let (src0, l_0) := run (↓ DePoolContract_Ф_startRoundCompleting oldRound0 RoundsBase_ι_CompletionReasonP_ι_PoolClosed) l_pre0 in
let (src1, l_1) := if round1ToBeUpdated then run (↓ DePoolContract_Ф_startRoundCompleting oldRound1 RoundsBase_ι_CompletionReasonP_ι_PoolClosed) l_0 
                                        else (oldRound1, l_0) in
let l' := exec_state (f srcPre0 src0) {$ l_1 With (LocalState_ι_terminator_Л_round1, src1) $} in                                        

exec_state (DePoolContract_Ф_terminator_header f) l =
if isOwner then 
    if isNotClosed then l'
                   else l else l.

Proof.

  intros.
  destructLedger l. 
  compute.
  Time repeat destructIf_solve. idtac.

  all: try destructFunction2 DePoolContract_Ф_startRoundCompleting; auto. idtac. 
  all: try destructFunction2 DePoolContract_Ф_startRoundCompleting; auto. idtac. 
  all: repeat destructIf_solve. idtac.
  all: try destructFunction2 DePoolContract_Ф_startRoundCompleting; auto. idtac.
  all: try destructFunction2 f; auto. idtac.
  all: try congruence.
Qed.

 End DePoolContract_Ф_terminator.