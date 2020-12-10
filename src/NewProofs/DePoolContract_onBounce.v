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
Module DePoolContract_Ф_onBounce (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.

Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair.


Import TVMModel.LedgerClass.
Opaque roundStepEqb. 

Lemma letIf: forall X Y (b: bool) (f g: X*Ledger) (h: X -> Ledger -> Y), 
(let (x, t) := if b then f else g in h x t)=
if b then let (x, t) := f in h x t else
          let (x, t) := g in h x t .
Proof.
  intros.
  destruct b; auto.
Qed.

Lemma matchIf: forall X (b: bool) (f g: LedgerT X) (l: Ledger), 
(match (if b then f else g) with | SimpleState c => c end l)=
if b then match f with | SimpleState c => c end l else 
match g with | SimpleState c => c end l.
Proof.
  intros.
  destruct b; auto.
Qed.



Lemma DePoolContract_Ф_onBounce_exec : forall (l : Ledger) (body : TvmSlice),

let (functionId, body') := decode_uint32 body in
let process_new_stake_id := tvm_functionId IProxy_И_process_new_stakeF in 
let recover_stake_id := tvm_functionId IProxy_И_recover_stakeF in 

let (roundId, _) := decode_uint64 body' in
let optRound := eval_state (↓ RoundsBase_Ф_fetchRound roundId) l in
let round := maybeGet optRound in
let roundFound : bool := isSome optRound in
let isRound1 : bool := eval_state (↓ RoundsBase_Ф_isRound1 roundId) l in
let isRound2 : bool := eval_state (↓ RoundsBase_Ф_isRound2 roundId) l in 
let step := RoundsBase_ι_Round_ι_step round in
let step_wsa : bool := eqb step RoundsBase_ι_RoundStepP_ι_WaitingIfStakeAccepted in
let step_wr : bool := eqb step RoundsBase_ι_RoundStepP_ι_WaitingReward in
let step_wwe : bool := eqb step RoundsBase_ι_RoundStepP_ι_WaitingIfValidatorWinElections in

let oldEvents := eval_state ( ↑16 ε VMState_ι_events ) l in
let queryId := DePoolLib_ι_Request_ι_queryId (RoundsBase_ι_Round_ι_validatorRequest round) in
let l_emit1 := {$ l With VMState_ι_events := ProxyHasRejectedTheStake queryId :: oldEvents $} in
let l_emit2 := {$ l With VMState_ι_events := ProxyHasRejectedRecoverRequest roundId :: oldEvents $} in

let isProcessNewStake := functionId =? process_new_stake_id in
let isRecoverStake := functionId =? recover_stake_id in
let round_pns := 
    {$ round with (RoundsBase_ι_Round_ι_step , RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest) $} in
let round_recover_1 :=
    {$ round with (RoundsBase_ι_Round_ι_step , RoundsBase_ι_RoundStepP_ι_WaitingValidationStart) $} in
let round_recover_2 :=
    {$ round with (RoundsBase_ι_Round_ι_step , RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze) $} in 

exec_state (↓ DePoolContract_Ф_onBounce body) l = 

if (isProcessNewStake || isRecoverStake)%bool then 
    if (isProcessNewStake) then 
        if isRound1 then 
            if roundFound then 
                if step_wsa then exec_state (↓ RoundsBase_Ф_setRound roundId round_pns) l_emit1 
                            else l
            else l
        else l
    else 
        if isRound2 then 
            if roundFound then 
                if step_wr then exec_state (↓ RoundsBase_Ф_setRound roundId round_recover_2) l_emit2
                else l
            else l
        else if isRound1 then 
                if roundFound then
                    if step_wwe then exec_state (↓ RoundsBase_Ф_setRound roundId round_recover_1) l_emit2
                    else l
                else l
        else injEmbed (VMState_ι_savedDePoolContracts (Ledger_ι_VMState l)) l    
else  l.

Proof.

  intros.
  destructLedger l. 
  compute.

  all: destruct (decode_uint32 body). idtac.
  all: destruct (decode_uint64 t). idtac.


  repeat rewrite matchIf.  idtac.
  repeat rewrite letIf.  idtac.
  repeat rewrite matchIf.  idtac.
  repeat rewrite letIf.  idtac.
  repeat rewrite matchIf.  idtac.
  repeat rewrite letIf.  idtac.

  

  Time repeat destructIf_solve.  idtac.

  all: try setoid_rewrite H3 in H4; try discriminate. idtac.
  all: try setoid_rewrite H4 in H5; try discriminate.
(* Require Import depoolContract.Lib.CommonStateProofs.

apply ledgerEq; simpl; auto.
apply RoundsBaseEq; simpl; auto.
remember (match hmapLookup Z.eqb x0 RoundsBase_ι_m_rounds with
  | Some x1 => x1
  | None => default
end) as rx0.
setoid_rewrite <- Heqrx0.
destruct rx0; auto. *)
Qed.    




Lemma DePoolContract_Ф_onBounce_eval : forall (l : Ledger) (body : TvmSlice),

let (functionId, body') := decode_uint32 body in
let process_new_stake_id := tvm_functionId IProxy_И_process_new_stakeF in 
let recover_stake_id := tvm_functionId IProxy_И_recover_stakeF in 
let (roundId, _) := decode_uint64 body' in
let optRound := eval_state (↓ RoundsBase_Ф_fetchRound roundId) l in
let round := maybeGet optRound in
let roundFound : bool := isSome optRound in
let isRound1 : bool := eval_state (↓ RoundsBase_Ф_isRound1 roundId) l in
let isRound2 : bool := eval_state (↓ RoundsBase_Ф_isRound2 roundId) l in 
let step := RoundsBase_ι_Round_ι_step round in
let step_wsa : bool := roundStepEqb step RoundsBase_ι_RoundStepP_ι_WaitingIfStakeAccepted in
let step_wr : bool := roundStepEqb step RoundsBase_ι_RoundStepP_ι_WaitingReward in
let step_wwe : bool := roundStepEqb step RoundsBase_ι_RoundStepP_ι_WaitingIfValidatorWinElections in
let isProcessNewStake := eqb functionId  process_new_stake_id in
let isRecoverStake := eqb functionId  recover_stake_id in

eval_state (DePoolContract_Ф_onBounce body) l = 

if (isProcessNewStake || isRecoverStake)%bool then 
    if (isProcessNewStake) then 
        if isRound1 then 
            if roundFound then 
                if step_wsa then Value I 
                            else Error InternalErrors_ι_ERROR525
            else Error InternalErrors_ι_ERROR519
        else Error InternalErrors_ι_ERROR524
    else 
        if isRound2 then 
            if roundFound then 
                if step_wr then Value I
                else Error InternalErrors_ι_ERROR526
            else Error InternalErrors_ι_ERROR519
        else if isRound1 then 
                if roundFound then
                    if step_wwe then Value I
                    else Error InternalErrors_ι_ERROR527
                else Error InternalErrors_ι_ERROR519
        else Error InternalErrors_ι_ERROR528
else Value I.
Proof.

  intros.
  destructLedger l. 
  compute.

  Time repeat destructIf_solve.  idtac.

  all: destruct (decode_uint32 body). idtac.
  all: destruct (decode_uint64 t). idtac.
  all: try rewrite H. idtac.
  all: try rewrite H0. idtac.
  all: try rewrite H1. idtac.
  all: try rewrite H2. idtac.
  all: try rewrite H3; auto. idtac.
  all: try rewrite H4; auto. 
  
Qed.  
  
End DePoolContract_Ф_onBounce.