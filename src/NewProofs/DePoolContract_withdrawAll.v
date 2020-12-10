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
Module DePoolContract_Ф_withdrawAll (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.

Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair.

Lemma DePoolContract_Ф_withdrawAll_exec : forall (l : Ledger),
let sender := eval_state msg_sender l in
let isInternalMessage : bool := negb (sender =? 0) in
(* let dePool := Ledger_ι_DePoolContract l in *)
let isPoolClosed : bool := eval_state (↑ε12 DePoolContract_ι_m_poolClosed) l in
let optParticipant := eval_state (↓ ParticipantBase_Ф_fetchParticipant sender) l in
let isEmptyParticipant : bool := negb (isSome optParticipant) (* match optParticipant with | None => true | _ => false end *) in
let participant := maybeGet optParticipant (* match optParticipant with | None => default | Some p => p end *) in
let newParticipant := {$ participant with (DePoolLib_ι_Participant_ι_reinvest, false) $} in
let l_set := exec_state (↓ ParticipantBase_Ф__setOrDeleteParticipant sender newParticipant) l in
let l_send := exec_state (↓ DePoolContract_Ф_sendAcceptAndReturnChange) l_set in
let statusDepoolClosed := DePool_ι_STATUS_DEPOOL_CLOSED in
let statusNoParticipant := DePool_ι_STATUS_NO_PARTICIPANT in

exec_state (↓ DePoolContract_Ф_withdrawAll) l =
if isInternalMessage then 
    if isPoolClosed then exec_state (↓ DePoolContract_Ф__sendError statusDepoolClosed 0) l else
        if isEmptyParticipant then exec_state (↓ DePoolContract_Ф__sendError statusNoParticipant 0) l
        else l_send
else l.
Proof.
  intros.
  destructLedger l. 
  compute.

  Time repeat destructIf_solve. 
  
Qed.

Lemma DePoolContract_Ф_withdrawAll'_eval : forall (l : Ledger),
let sender := eval_state msg_sender l in
let isInternalMessage : bool := negb (sender =? 0) in
let isPoolClosed : bool := eval_state (↑ε12 DePoolContract_ι_m_poolClosed) l in
let optParticipant := eval_state (↓ ParticipantBase_Ф_fetchParticipant sender) l in
let isEmptyParticipant : bool := negb (isSome optParticipant) (* match optParticipant with | None => true | _ => false end *) in

eval_state (↓ DePoolContract_Ф_withdrawAll') l =

if isInternalMessage then 
    if isPoolClosed then Value (Error I) else
        if isEmptyParticipant then Value (Error I)
    else Value (Value I)
else  Error Errors_ι_IS_EXT_MSG .
Proof.

  intros.
  destructLedger l. 
  compute.

  Time repeat destructIf_solve. 
  
Qed.

Lemma DePoolContract_Ф_withdrawAll_eval : forall (l : Ledger),
let sender := eval_state msg_sender l in
let isInternalMessage : bool := negb (sender =? 0) in
let isPoolClosed : bool := eval_state (↑ε12 DePoolContract_ι_m_poolClosed) l in
let optParticipant := eval_state (↓ ParticipantBase_Ф_fetchParticipant sender) l in
let isEmptyParticipant : bool := negb (isSome optParticipant) (* match optParticipant with | None => true | _ => false end *) in

eval_state (↓ DePoolContract_Ф_withdrawAll) l =

if isInternalMessage then 
    if isPoolClosed then Value I else
        if isEmptyParticipant then Value I
    else Value I
else  Error Errors_ι_IS_EXT_MSG .
Proof.
  intros.

  assert (eval_state (↓ DePoolContract_Ф_withdrawAll ) l = 
  xErrorMapDefaultF (xValue ∘ fromValueValue) (eval_state (↓ DePoolContract_Ф_withdrawAll' ) l) xError ).
  unfold DePoolContract_Ф_withdrawAll.
  unfold callEmbeddedStateAdj.
  remember (DePoolContract_Ф_withdrawAll').
  setoid_rewrite runbind.
  setoid_rewrite eval_bind2.
  rewrite eval_get.
  rewrite exec_get.
  remember (run l0 (injEmbed (T:=LocalState) DePoolFuncs.DePoolSpec.LedgerClass.local0 l)).
  setoid_rewrite <- Heqp.
  destruct p.
  destruct x.
  auto. auto.

  (**********************)
  rewrite H.
  rewrite DePoolContract_Ф_withdrawAll'_eval.
  compute.
  repeat destructIf; auto.
Qed. 

End DePoolContract_Ф_withdrawAll.