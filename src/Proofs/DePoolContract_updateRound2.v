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

Require Import depoolContract.Lib.CommonStateProofs.

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



(* function updateRound2(Round round2,
                          uint256 prevValidatorHash,
                          uint256 curValidatorHash,
                          uint32 validationStart
    )
        private returns (Round)
    {

 (*if1*) if (round2.step == RoundStep.WaitingValidatorRequest) {
            round2.step = RoundStep.WaitingUnfreeze;

 (*if2*)    if (round2.completionReason == CompletionReason.Undefined) {
                round2.completionReason = CompletionReason.NoValidatorRequest;
            }
            round2.unfreeze = 0;
 (*if3*) } else if (round2.step == RoundStep.Completing) {
            this.completeRoundWithChunk{bounce: false}(round2.id, 1);
         }


(*if4*) if (round2.vsetHashInElectionPhase != curValidatorHash &&
            round2.vsetHashInElectionPhase != prevValidatorHash &&
            round2.unfreeze == DePoolLib.MAX_TIME
        )
        {
            round2.unfreeze = validationStart + round2.stakeHeldFor;
        }


(*if5*) if (now >= uint(round2.unfreeze) + DePoolLib.ELECTOR_UNFREEZE_LAG) {

(*if6*)     if (round2.step == RoundStep.WaitingUnfreeze &&
                round2.completionReason != CompletionReason.Undefined
            )
            {
(*if7*)         if (round2.participantQty == 0) {
                    round2.step = RoundStep.Completed;
                    emit RoundCompleted(toTruncatedRound(round2));
                } else {
                    round2 = startRoundCompleting(round2, round2.completionReason);
                }
(*if8*)     } else if (
                round2.step == RoundStep.WaitingValidationStart ||
                round2.step == RoundStep.WaitingUnfreeze
            )
            {
                round2.step = RoundStep.WaitingReward;
                _recoverStake(round2.proxy, round2.id, round2.elector);
            }
        }

        return round2; 
        
        }   *) 

Ltac remDestructIf :=
  match goal with
    | |- ?x =>
      match x with
        | context [if ?b then _ else _] => case_eq b ; intros
        | _ => idtac
      end
  end.

  Ltac pr_numgoals := let n := numgoals in idtac "There are" n "goals".

Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo.
Opaque DePoolContract_Ф_startRoundCompleting ProxyBase_Ф__recoverStake.


Lemma DePoolContract_Ф_updateRound2_exec : forall ( Л_round2 : RoundsBase_ι_Round ) 
                                                   ( Л_prevValidatorHash : XInteger256 ) 
                                                   ( Л_curValidatorHash : XInteger256 ) 
                                                   ( Л_validationStart : XInteger32 )                                                  
                                                   (l: Ledger) ,                                                    
exec_state ( ↓ ( DePoolContract_Ф_updateRound2 Л_round2 Л_prevValidatorHash Л_curValidatorHash Л_validationStart ) ) l =    

let round2 := Л_round2 in
        (*(round2.step == RoundStep.WaitingValidatorRequest)*)
let if1 : bool  :=  eqb ( round2 ->> RoundsBase_ι_Round_ι_step )  RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest in
        (* (round2.completionReason == CompletionReason.Undefined) *)
let if2 : bool  :=  eqb ( round2 ->> RoundsBase_ι_Round_ι_completionReason )  RoundsBase_ι_CompletionReasonP_ι_Undefined in
        (* (round2.step == RoundStep.Completing) *)
let if3 : bool  :=  eqb (round2 ->> RoundsBase_ι_Round_ι_step )  RoundsBase_ι_RoundStepP_ι_Completing in 
        (*   (round2.vsetHashInElectionPhase != curValidatorHash &&
            round2.vsetHashInElectionPhase != prevValidatorHash &&
            round2.unfreeze == DePoolLib.MAX_TIME *)
let round2 := if if1 then 
                      if if2 then {$ round2 with (RoundsBase_ι_Round_ι_step, RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze);
                                                 (RoundsBase_ι_Round_ι_completionReason, RoundsBase_ι_CompletionReasonP_ι_NoValidatorRequest);
                                                 (RoundsBase_ι_Round_ι_unfreeze, 0) $}
                             else {$ round2 with (RoundsBase_ι_Round_ι_step, RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze);
                                                 (RoundsBase_ι_Round_ι_unfreeze, 0) $} 
                      else round2 in 

(* this.completeRoundWithChunk{bounce: false}(round2.id, 1); *)                      
let oldMessages := VMState_ι_messages ( Ledger_ι_VMState l ) in
let oldEvents := VMState_ι_events ( Ledger_ι_VMState l ) in
let newMessage  := {|  contractAddress :=  0 ;
                        contractFunction := DePoolContract_Ф_completeRoundWithChunkF round2->>RoundsBase_ι_Round_ι_id 1 ;
                        contractMessage := {| messageValue := 0 ;
                                              messageFlag  := 0 ; 
                                              messageBounce := false
                                                  |} |} in                      
let l' :=   if if1 then l
                   else if if3 then {$ l With (VMState_ι_messages, newMessage :: oldMessages ) $}
                               else l   
                      in                                             

let if4 : bool :=  (( negb ( eqb ( round2 ->> RoundsBase_ι_Round_ι_vsetHashInElectionPhase ) Л_curValidatorHash ) )  && 
                    ( negb ( eqb ( round2 ->> RoundsBase_ι_Round_ι_vsetHashInElectionPhase ) Л_prevValidatorHash ) )  && 
                    ( eqb (round2 ->> RoundsBase_ι_Round_ι_unfreeze) ( eval_state ( ↑9 ε DePoolLib_ι_MAX_TIME ) l ) ) )%bool   in
let round2 := if if4 then {$ round2 with (RoundsBase_ι_Round_ι_unfreeze, Л_validationStart + round2->>RoundsBase_ι_Round_ι_stakeHeldFor) $} 
                       else round2 in 

        (* (now >= uint(round2.unfreeze) + DePoolLib.ELECTOR_UNFREEZE_LAG) *)
let if5 : bool  := ( eval_state tvm_now  l ) >=? ( (round2 ->> RoundsBase_ι_Round_ι_unfreeze) + 
                                                   (eval_state ( ↑9 ε DePoolLib_ι_ELECTOR_UNFREEZE_LAG ) l ) ) in 
       (* ( round2.step == RoundStep.WaitingUnfreeze &&
            round2.completionReason != CompletionReason.Undefined ) *)
let if6 : bool := (( eqb (round2 ->> RoundsBase_ι_Round_ι_step) RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze ) &&
                     negb ( eqb (round2 ->> RoundsBase_ι_Round_ι_completionReason) RoundsBase_ι_CompletionReasonP_ι_Undefined ))%bool in
                (* round2.participantQty == 0 *)
let if7 : bool := ( round2 ->> RoundsBase_ι_Round_ι_participantQty ) =? 0  in
                (* round2.step == RoundStep.WaitingValidationStart ||
                   round2.step == RoundStep.WaitingUnfreeze *)
let if8 : bool :=  ( ( eqb (round2 ->> RoundsBase_ι_Round_ι_step) RoundsBase_ι_RoundStepP_ι_WaitingValidationStart ) ||
                     ( eqb (round2 ->> RoundsBase_ι_Round_ι_step) RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze ))%bool in  
let (round2, l'') := if if5 then 
                            if if6 then 
                                   run ( ↓ DePoolContract_Ф_startRoundCompleting round2 round2 ->> RoundsBase_ι_Round_ι_completionReason) l'
                                    else if if8 then ({$ round2 with (RoundsBase_ι_Round_ι_step, RoundsBase_ι_RoundStepP_ι_WaitingReward) $} , 
                                    exec_state ( ↓ ( ProxyBase_Ф__recoverStake round2 ->> RoundsBase_ι_Round_ι_proxy 
                                                                               round2 ->> RoundsBase_ι_Round_ι_id 
                                                                               round2 ->> RoundsBase_ι_Round_ι_elector ) ) l')
                                                else (round2, l')     
                     else (round2, l') in l''.
 Proof. 
  intros. destruct l. 
  
  destruct Ledger_ι_DebugDePool, Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ConfigParamsBase, Ledger_ι_ParticipantBase, 
  Ledger_ι_DePoolHelper, Ledger_ι_Errors, Ledger_ι_InternalErrors, Ledger_ι_DePoolLib, Ledger_ι_DePoolProxyContract, 
  Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_DePool, Ledger_ι_Participant, Ledger_ι_TestElector, 
  Ledger_ι_VMState, Ledger_ι_LocalState.

  destruct Л_round2.

  compute. idtac.

  Time  do 5 (
  
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
                                          (* simpl;  *)
                                          intros                                                              
      | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
      end

  end) . idtac.



  all : pr_numgoals.

  - idtac.

  assert ((if
  if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
  then false
  else true
 then
  if
   if
    RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
   then false
   else true
  then 0 =? DePoolLib_ι_MAX_TIME
  else false
 else false)  = if
 if
  if
   RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
  then false
  else true
 then
  if
   RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
   Л_prevValidatorHash
  then false
  else true
 else false
then 0 =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (0 =?
DePoolLib_ι_MAX_TIME); auto.

rewrite H1 in H4. idtac.
rewrite <- H4. idtac.

match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_startRoundCompleting ?a ?b] => remember (DePoolContract_Ф_startRoundCompleting a b) as l
            end
end.
destruct l.

match goal with 
| |- ?x  => match x with 
            | context [p ?a] => remember (p a)
            end
end.

destruct p0; auto.

- idtac.

assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then 0 =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then 0 =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (0 =?
DePoolLib_ι_MAX_TIME); auto.

rewrite H1 in H4. idtac.
rewrite <- H4 in H3. idtac.
rewrite H2 in H3. discriminate. 

- idtac.

assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then 0 =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then 0 =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (0 =?
DePoolLib_ι_MAX_TIME); auto.

rewrite H1 in H4. idtac.
rewrite <- H4 in H3. idtac.
rewrite H2 in H3. discriminate. 

- idtac. auto.

- idtac.

assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then 0 =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then 0 =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (0 =?
DePoolLib_ι_MAX_TIME); auto.


rewrite H1 in H4. idtac.
rewrite <- H4. idtac.

match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_startRoundCompleting ?a ?b] => remember (DePoolContract_Ф_startRoundCompleting a b) as l
            end
end.
destruct l.

match goal with 
| |- ?x  => match x with 
            | context [p ?a] => remember (p a)
            end
end.

destruct p0; auto.

- idtac.


assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then 0 =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then 0 =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (0 =?
DePoolLib_ι_MAX_TIME); auto.

rewrite H1 in H4. idtac.
rewrite <- H4 in H3. idtac.
rewrite H2 in H3. discriminate.

- idtac.


assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then 0 =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then 0 =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (0 =?
DePoolLib_ι_MAX_TIME); auto.

rewrite H1 in H4. idtac.
rewrite <- H4 in H3. idtac.
rewrite H2 in H3. discriminate.

- idtac. auto.

- idtac.

assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then 0 =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then 0 =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (0 =?
DePoolLib_ι_MAX_TIME); auto.


rewrite H1 in H4. idtac.
rewrite <- H4. idtac.
rewrite H2. rewrite H3.

match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_startRoundCompleting ?a ?b] => remember (DePoolContract_Ф_startRoundCompleting a b) as l
            end
end.
destruct l.

match goal with 
| |- ?x  => match x with 
            | context [p ?a] => remember (p a)
            end
end.

destruct p0; auto.

- idtac. rewrite H0 in H3. discriminate.

- idtac.

assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then 0 =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then 0 =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (0 =?
DePoolLib_ι_MAX_TIME); auto.

rewrite H1 in H4. idtac.
rewrite <- H4 in H3. idtac.
rewrite H2 in H3. discriminate.

- idtac. auto.

- idtac.

assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then 0 =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then 0 =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (0 =?
DePoolLib_ι_MAX_TIME); auto.


rewrite H1 in H4. idtac.
rewrite <- H4. idtac.
rewrite H2. rewrite H3. idtac.

match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_startRoundCompleting ?a ?b] => remember (DePoolContract_Ф_startRoundCompleting a b) as l
            end
end.
destruct l.

match goal with 
| |- ?x  => match x with 
            | context [p ?a] => remember (p a)
            end
end.

destruct p0; auto.

- idtac.

assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then 0 =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then 0 =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (0 =?
DePoolLib_ι_MAX_TIME); auto.


rewrite H1 in H4. idtac.
rewrite <- H4. idtac.
rewrite H2. rewrite H3. idtac.

match goal with 
  | |- ?x  => match x with 
              | context [ProxyBase_Ф__recoverStake ?a ?b ?c ] => remember (ProxyBase_Ф__recoverStake a b c ) as l
              end
  end.
  destruct l.
  
  match goal with 
  | |- ?x  => match x with 
              | context [p ?a] => remember (p a)
              end
  end.
  
  destruct p0; auto.

  - idtac.

  assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then 0 =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then 0 =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (0 =?
DePoolLib_ι_MAX_TIME); auto.

rewrite H1 in H4. idtac.
rewrite <- H4 in H3. idtac.
rewrite H2 in H3. discriminate.

- idtac. auto.

- idtac.

assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (RoundsBase_ι_Round_ι_unfreeze =?
DePoolLib_ι_MAX_TIME); auto.


rewrite H1 in H4. idtac.
rewrite <- H4. idtac.
rewrite H2. rewrite H3. idtac.

match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_startRoundCompleting ?a ?b] => remember (DePoolContract_Ф_startRoundCompleting a b) as l
            end
end.
destruct l.

match goal with 
| |- ?x  => match x with 
            | context [p ?a] => remember (p a)
            end
end.

destruct p0; auto.

- idtac.

assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (RoundsBase_ι_Round_ι_unfreeze =?
DePoolLib_ι_MAX_TIME); auto.


rewrite H1 in H4. idtac.
rewrite <- H4. idtac.
rewrite H2. rewrite H3. idtac.

Time  do 1 (
  
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
                                          (* simpl;  *)
                                          intros                                                              
      | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
      end

  end) . idtac.

  auto. auto.

  - idtac.

  assert ((if
  if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
  then false
  else true
  then
  if
   if
    RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
   then false
   else true
  then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
  else false
  else false)  = if
  if
  if
   RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
  then false
  else true
  then
  if
   RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
   Л_prevValidatorHash
  then false
  else true
  else false
  then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
  else false). idtac.
  
  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
  Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
  Л_prevValidatorHash); destruct (RoundsBase_ι_Round_ι_unfreeze =?
  DePoolLib_ι_MAX_TIME); auto.
  
  rewrite H1 in H4. idtac.
  rewrite <- H4 in H3. idtac.
  rewrite H2 in H3. discriminate.

  - idtac. auto.

  - idtac. 

  assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (RoundsBase_ι_Round_ι_unfreeze =?
DePoolLib_ι_MAX_TIME); auto.


rewrite H1 in H4. idtac.
rewrite <- H4. idtac.
rewrite H2. rewrite H3. idtac.

match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_startRoundCompleting ?a ?b] => remember (DePoolContract_Ф_startRoundCompleting a b) as l
            end
end.
destruct l.

match goal with 
| |- ?x  => match x with 
            | context [p ?a] => remember (p a)
            end
end.

destruct p0; auto.

- idtac.

assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (RoundsBase_ι_Round_ι_unfreeze =?
DePoolLib_ι_MAX_TIME); auto.


rewrite H1 in H4. idtac.
rewrite <- H4. idtac.
rewrite H2. rewrite H3. idtac.

Time  do 1 (
  
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
                                          (* simpl;  *)
                                          intros                                                              
      | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
      end

  end) . idtac.

  auto. auto.

  - idtac.

  assert ((if
  if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
  then false
  else true
  then
  if
   if
    RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
   then false
   else true
  then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
  else false
  else false)  = if
  if
  if
   RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
  then false
  else true
  then
  if
   RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
   Л_prevValidatorHash
  then false
  else true
  else false
  then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
  else false). idtac.
  
  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
  Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
  Л_prevValidatorHash); destruct (RoundsBase_ι_Round_ι_unfreeze =?
  DePoolLib_ι_MAX_TIME); auto.
  
  rewrite H1 in H4. idtac.
  rewrite <- H4 in H3. idtac.
  rewrite H2 in H3. discriminate.

  - idtac. auto.

  - idtac.
  assert ((if
  if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
  then false
  else true
  then
  if
   if
    RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
   then false
   else true
  then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
  else false
  else false)  = if
  if
  if
   RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
  then false
  else true
  then
  if
   RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
   Л_prevValidatorHash
  then false
  else true
  else false
  then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
  else false). idtac.
  
  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
  Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
  Л_prevValidatorHash); destruct (RoundsBase_ι_Round_ι_unfreeze =?
  DePoolLib_ι_MAX_TIME); auto.
  
  
  rewrite H1 in H4. idtac.
  rewrite <- H4. idtac.
  rewrite H2. rewrite H3. idtac.


  match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_startRoundCompleting ?a ?b] => remember (DePoolContract_Ф_startRoundCompleting a b) as l
            end
end.
destruct l.

match goal with 
| |- ?x  => match x with 
            | context [p ?a] => remember (p a)
            end
end.

destruct p0; auto.

- idtac.

assert ((if
  if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
  then false
  else true
  then
  if
   if
    RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
   then false
   else true
  then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
  else false
  else false)  = if
  if
  if
   RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
  then false
  else true
  then
  if
   RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
   Л_prevValidatorHash
  then false
  else true
  else false
  then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
  else false). idtac.
  
  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
  Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
  Л_prevValidatorHash); destruct (RoundsBase_ι_Round_ι_unfreeze =?
  DePoolLib_ι_MAX_TIME); auto.
  
  
  rewrite H1 in H4. idtac.
  rewrite <- H4. idtac.
  rewrite H2. rewrite H3. idtac.


  Time  do 1 (
    
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
                                            (* simpl;  *)
                                            intros                                                              
        | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
        end
  
    end) . idtac.
  
    auto. auto.

- idtac.

assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (RoundsBase_ι_Round_ι_unfreeze =?
DePoolLib_ι_MAX_TIME); auto.

rewrite H1 in H4. idtac.
rewrite <- H4 in H3. idtac.
rewrite H2 in H3. discriminate.

- idtac. auto.

- idtac.
assert ((if
  if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
  then false
  else true
  then
  if
   if
    RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
   then false
   else true
  then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
  else false
  else false)  = if
  if
  if
   RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
  then false
  else true
  then
  if
   RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
   Л_prevValidatorHash
  then false
  else true
  else false
  then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
  else false). idtac.
  
  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
  Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
  Л_prevValidatorHash); destruct (RoundsBase_ι_Round_ι_unfreeze =?
  DePoolLib_ι_MAX_TIME); auto.
  
  
  rewrite H1 in H4. idtac.
  rewrite <- H4. idtac.
  rewrite H2. rewrite H3. idtac.

  match goal with 
  | |- ?x  => match x with 
              | context [DePoolContract_Ф_startRoundCompleting ?a ?b] => remember (DePoolContract_Ф_startRoundCompleting a b) as l
              end
  end.
  destruct l.
  
  match goal with 
  | |- ?x  => match x with 
              | context [p ?a] => remember (p a)
              end
  end.
  
  destruct p0; auto.

- idtac.

assert ((if
  if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
  then false
  else true
  then
  if
   if
    RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
   then false
   else true
  then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
  else false
  else false)  = if
  if
  if
   RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
  then false
  else true
  then
  if
   RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
   Л_prevValidatorHash
  then false
  else true
  else false
  then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
  else false). idtac.
  
  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
  Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
  Л_prevValidatorHash); destruct (RoundsBase_ι_Round_ι_unfreeze =?
  DePoolLib_ι_MAX_TIME); auto.
  
  
  rewrite H1 in H4. idtac.
  rewrite <- H4. idtac.
  rewrite H2. rewrite H3. idtac.

  Time  do 1 (
    
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
                                            (* simpl;  *)
                                            intros                                                              
        | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
        end
  
    end) . idtac.
  
    auto. auto.

- idtac.

assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (RoundsBase_ι_Round_ι_unfreeze =?
DePoolLib_ι_MAX_TIME); auto.

rewrite H1 in H4. idtac.
rewrite <- H4 in H3. idtac.
rewrite H2 in H3. discriminate.

- idtac. auto.

 Qed.


  

Lemma DePoolContract_Ф_updateRound2_eval : forall ( Л_round2 : RoundsBase_ι_Round ) 
                                                   ( Л_prevValidatorHash : XInteger256 ) 
                                                   ( Л_curValidatorHash : XInteger256 ) 
                                                   ( Л_validationStart : XInteger32 )                                                  
                                                   (l: Ledger) ,                                                    
eval_state ( ↓ ( DePoolContract_Ф_updateRound2 Л_round2 Л_prevValidatorHash Л_curValidatorHash Л_validationStart ) ) l =    

let round2 := Л_round2 in
        (*(round2.step == RoundStep.WaitingValidatorRequest)*)
let if1 : bool  :=  eqb ( round2 ->> RoundsBase_ι_Round_ι_step )  RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest in
        (* (round2.completionReason == CompletionReason.Undefined) *)
let if2 : bool  :=  eqb ( round2 ->> RoundsBase_ι_Round_ι_completionReason )  RoundsBase_ι_CompletionReasonP_ι_Undefined in
        (* (round2.step == RoundStep.Completing) *)
let if3 : bool  :=  eqb (round2 ->> RoundsBase_ι_Round_ι_step )  RoundsBase_ι_RoundStepP_ι_Completing in 
        (*   (round2.vsetHashInElectionPhase != curValidatorHash &&
            round2.vsetHashInElectionPhase != prevValidatorHash &&
            round2.unfreeze == DePoolLib.MAX_TIME *)
let round2 := if if1 then 
                      if if2 then {$ round2 with (RoundsBase_ι_Round_ι_step, RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze);
                                                 (RoundsBase_ι_Round_ι_completionReason, RoundsBase_ι_CompletionReasonP_ι_NoValidatorRequest);
                                                 (RoundsBase_ι_Round_ι_unfreeze, 0) $}
                             else {$ round2 with (RoundsBase_ι_Round_ι_step, RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze);
                                                 (RoundsBase_ι_Round_ι_unfreeze, 0) $} 
                      else round2 in 

(* this.completeRoundWithChunk{bounce: false}(round2.id, 1); *)                      
let oldMessages := VMState_ι_messages ( Ledger_ι_VMState l ) in
let newMessage  := {|  contractAddress :=  0 ;
                        contractFunction := DePoolContract_Ф_completeRoundWithChunkF round2->>RoundsBase_ι_Round_ι_id 1 ;
                        contractMessage := {| messageValue := 0 ;
                                              messageFlag  := 0 ; 
                                              messageBounce := false
                                                  |} |} in                      
let l' :=   if if1 then l
                   else if if3 then {$ l With (VMState_ι_messages, newMessage :: oldMessages ) $}
                               else l   
                      in                                             

let if4 : bool :=  (( negb ( eqb ( round2 ->> RoundsBase_ι_Round_ι_vsetHashInElectionPhase ) Л_curValidatorHash ) )  && 
                    ( negb ( eqb ( round2 ->> RoundsBase_ι_Round_ι_vsetHashInElectionPhase ) Л_prevValidatorHash ) )  && 
                    ( eqb (round2 ->> RoundsBase_ι_Round_ι_unfreeze) ( eval_state ( ↑9 ε DePoolLib_ι_MAX_TIME ) l ) ) )%bool   in
let round2 := if if4 then {$ round2 with (RoundsBase_ι_Round_ι_unfreeze, Л_validationStart + round2->>RoundsBase_ι_Round_ι_stakeHeldFor) $} 
                       else round2 in 

        (* (now >= uint(round2.unfreeze) + DePoolLib.ELECTOR_UNFREEZE_LAG) *)
let if5 : bool  := ( eval_state tvm_now  l ) >=? ( (round2 ->> RoundsBase_ι_Round_ι_unfreeze) + 
                                                   (eval_state ( ↑9 ε DePoolLib_ι_ELECTOR_UNFREEZE_LAG ) l ) ) in 
       (* ( round2.step == RoundStep.WaitingUnfreeze &&
            round2.completionReason != CompletionReason.Undefined ) *)
let if6 : bool := (( eqb (round2 ->> RoundsBase_ι_Round_ι_step) RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze ) &&
                     negb ( eqb (round2 ->> RoundsBase_ι_Round_ι_completionReason) RoundsBase_ι_CompletionReasonP_ι_Undefined ))%bool in
                (* round2.step == RoundStep.WaitingValidationStart ||
                   round2.step == RoundStep.WaitingUnfreeze *)
let if8 : bool :=  ( ( eqb (round2 ->> RoundsBase_ι_Round_ι_step) RoundsBase_ι_RoundStepP_ι_WaitingValidationStart ) ||
                     ( eqb (round2 ->> RoundsBase_ι_Round_ι_step) RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze ))%bool in  
let round2 := if if5 then 
                            if if6 then 
                                   eval_state ( ↓ DePoolContract_Ф_startRoundCompleting round2 round2 ->> RoundsBase_ι_Round_ι_completionReason) l'
                                    else if if8 then {$ round2 with (RoundsBase_ι_Round_ι_step, RoundsBase_ι_RoundStepP_ι_WaitingReward) $} 
                                                else round2
                     else round2 in 
                     round2.

Proof. 
  intros. destruct l. 
  
  destruct Ledger_ι_DebugDePool, Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ConfigParamsBase, Ledger_ι_ParticipantBase, 
  Ledger_ι_DePoolHelper, Ledger_ι_Errors, Ledger_ι_InternalErrors, Ledger_ι_DePoolLib, Ledger_ι_DePoolProxyContract, 
  Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_DePool, Ledger_ι_Participant, Ledger_ι_TestElector, 
  Ledger_ι_VMState, Ledger_ι_LocalState.

  destruct Л_round2.

  compute. idtac.

  Time  do 5 (
  
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
                                          (* simpl;  *)
                                          intros                                                              
      | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
      end

  end) . idtac.

  all : pr_numgoals.

  - idtac.

  assert ((if
  if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
  then false
  else true
 then
  if
   if
    RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
   then false
   else true
  then 0 =? DePoolLib_ι_MAX_TIME
  else false
 else false)  = if
 if
  if
   RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
  then false
  else true
 then
  if
   RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
   Л_prevValidatorHash
  then false
  else true
 else false
then 0 =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (0 =?
DePoolLib_ι_MAX_TIME); auto.

rewrite H1 in H4. idtac.
rewrite <- H4. idtac.

match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_startRoundCompleting ?a ?b] => remember (DePoolContract_Ф_startRoundCompleting a b) as l
            end
end.
destruct l.

match goal with 
| |- ?x  => match x with 
            | context [p ?a] => remember (p a)
            end
end.

destruct p0; auto.

- idtac.

assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then 0 =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then 0 =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (0 =?
DePoolLib_ι_MAX_TIME); auto.

rewrite H1 in H4. idtac.
rewrite <- H4 in H3. idtac.
rewrite H2 in H3. discriminate. 

- idtac.

assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then 0 =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then 0 =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (0 =?
DePoolLib_ι_MAX_TIME); auto.

rewrite H1 in H4. idtac.
rewrite <- H4 in H3. idtac.
rewrite H2 in H3. discriminate. 

- idtac. 

assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then 0 =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then 0 =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (0 =?
DePoolLib_ι_MAX_TIME); auto.

rewrite H1 in H4. idtac.
rewrite <- H4. idtac.

auto.

- idtac.

assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then 0 =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then 0 =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (0 =?
DePoolLib_ι_MAX_TIME); auto.


rewrite H1 in H4. idtac.
rewrite <- H4. idtac.

match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_startRoundCompleting ?a ?b] => remember (DePoolContract_Ф_startRoundCompleting a b) as l
            end
end.
destruct l.

match goal with 
| |- ?x  => match x with 
            | context [p ?a] => remember (p a)
            end
end.

destruct p0; auto.

- idtac.


assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then 0 =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then 0 =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (0 =?
DePoolLib_ι_MAX_TIME); auto.

rewrite H1 in H4. idtac.
rewrite <- H4 in H3. idtac.
rewrite H2 in H3. discriminate.

- idtac.


assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then 0 =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then 0 =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (0 =?
DePoolLib_ι_MAX_TIME); auto.

rewrite H1 in H4. idtac.
rewrite <- H4 in H3. idtac.
rewrite H2 in H3. discriminate.

- idtac. 

assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then 0 =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then 0 =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (0 =?
DePoolLib_ι_MAX_TIME); auto.

rewrite H1 in H4. idtac.
rewrite <- H4. idtac.

auto.

- idtac.

assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then 0 =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then 0 =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (0 =?
DePoolLib_ι_MAX_TIME); auto.


rewrite H1 in H4. idtac.
rewrite <- H4. idtac.
rewrite H2. rewrite H3.

match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_startRoundCompleting ?a ?b] => remember (DePoolContract_Ф_startRoundCompleting a b) as l
            end
end.
destruct l.

match goal with 
| |- ?x  => match x with 
            | context [p ?a] => remember (p a)
            end
end.

destruct p0; auto.

- idtac. rewrite H0 in H3. discriminate.

- idtac.

assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then 0 =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then 0 =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (0 =?
DePoolLib_ι_MAX_TIME); auto.

rewrite H1 in H4. idtac.
rewrite <- H4 in H3. idtac.
rewrite H2 in H3. discriminate.

- idtac. 

assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then 0 =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then 0 =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (0 =?
DePoolLib_ι_MAX_TIME); auto.

rewrite H1 in H4. idtac.
rewrite <- H4. idtac.

auto.

- idtac.

assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then 0 =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then 0 =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (0 =?
DePoolLib_ι_MAX_TIME); auto.


rewrite H1 in H4. idtac.
rewrite <- H4. idtac.
rewrite H2. rewrite H3. idtac.

match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_startRoundCompleting ?a ?b] => remember (DePoolContract_Ф_startRoundCompleting a b) as l
            end
end.
destruct l.

match goal with 
| |- ?x  => match x with 
            | context [p ?a] => remember (p a)
            end
end.

destruct p0; auto.

- idtac.

assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then 0 =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then 0 =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (0 =?
DePoolLib_ι_MAX_TIME); auto.


rewrite H1 in H4. idtac.
rewrite <- H4. idtac.
rewrite H2. rewrite H3. idtac.

match goal with 
  | |- ?x  => match x with 
              | context [ProxyBase_Ф__recoverStake ?a ?b ?c ] => remember (ProxyBase_Ф__recoverStake a b c ) as l
              end
  end.
  destruct l.
  
  match goal with 
  | |- ?x  => match x with 
              | context [p ?a] => remember (p a)
              end
  end.
  
  destruct p0; auto.

- idtac.

  assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then 0 =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then 0 =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (0 =?
DePoolLib_ι_MAX_TIME); auto.

rewrite H1 in H4. idtac.
rewrite <- H4 in H3. idtac.
rewrite H2 in H3. discriminate.

- idtac. 

assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then 0 =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then 0 =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (0 =?
DePoolLib_ι_MAX_TIME); auto.

rewrite H1 in H4. idtac.
rewrite <- H4. idtac.

auto.

- idtac.

assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (RoundsBase_ι_Round_ι_unfreeze =?
DePoolLib_ι_MAX_TIME); auto.


rewrite H1 in H4. idtac.
rewrite <- H4. idtac.
rewrite H2. rewrite H3. idtac.

match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_startRoundCompleting ?a ?b] => remember (DePoolContract_Ф_startRoundCompleting a b) as l
            end
end.
destruct l.

match goal with 
| |- ?x  => match x with 
            | context [p ?a] => remember (p a)
            end
end.

destruct p0; auto.

- idtac.

assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (RoundsBase_ι_Round_ι_unfreeze =?
DePoolLib_ι_MAX_TIME); auto.


rewrite H1 in H4. idtac.
rewrite <- H4. idtac.
rewrite H2. rewrite H3. idtac.

Time  do 1 (
  
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
                                          (* simpl;  *)
                                          intros                                                              
      | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
      end

  end) . idtac.

  auto. auto.

  - idtac.

  assert ((if
  if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
  then false
  else true
  then
  if
   if
    RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
   then false
   else true
  then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
  else false
  else false)  = if
  if
  if
   RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
  then false
  else true
  then
  if
   RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
   Л_prevValidatorHash
  then false
  else true
  else false
  then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
  else false). idtac.
  
  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
  Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
  Л_prevValidatorHash); destruct (RoundsBase_ι_Round_ι_unfreeze =?
  DePoolLib_ι_MAX_TIME); auto.
  
  rewrite H1 in H4. idtac.
  rewrite <- H4 in H3. idtac.
  rewrite H2 in H3. discriminate.

  - idtac. 
  
  assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (RoundsBase_ι_Round_ι_unfreeze =?
DePoolLib_ι_MAX_TIME); auto.

rewrite H1 in H4. idtac.
rewrite <- H4. idtac.
  
  auto.

  - idtac. 

  assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (RoundsBase_ι_Round_ι_unfreeze =?
DePoolLib_ι_MAX_TIME); auto.


rewrite H1 in H4. idtac.
rewrite <- H4. idtac.
rewrite H2. rewrite H3. idtac.

match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_startRoundCompleting ?a ?b] => remember (DePoolContract_Ф_startRoundCompleting a b) as l
            end
end.
destruct l.

match goal with 
| |- ?x  => match x with 
            | context [p ?a] => remember (p a)
            end
end.

destruct p0; auto.

- idtac.

assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (RoundsBase_ι_Round_ι_unfreeze =?
DePoolLib_ι_MAX_TIME); auto.


rewrite H1 in H4. idtac.
rewrite <- H4. idtac.
rewrite H2. rewrite H3. idtac.

Time  do 1 (
  
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
                                          (* simpl;  *)
                                          intros                                                              
      | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
      end

  end) . idtac.

  auto. auto.

  - idtac.

  assert ((if
  if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
  then false
  else true
  then
  if
   if
    RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
   then false
   else true
  then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
  else false
  else false)  = if
  if
  if
   RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
  then false
  else true
  then
  if
   RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
   Л_prevValidatorHash
  then false
  else true
  else false
  then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
  else false). idtac.
  
  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
  Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
  Л_prevValidatorHash); destruct (RoundsBase_ι_Round_ι_unfreeze =?
  DePoolLib_ι_MAX_TIME); auto.
  
  rewrite H1 in H4. idtac.
  rewrite <- H4 in H3. idtac.
  rewrite H2 in H3. discriminate.

  - idtac. 
  
  assert ((if
  if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
  then false
  else true
  then
  if
   if
    RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
   then false
   else true
  then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
  else false
  else false)  = if
  if
  if
   RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
  then false
  else true
  then
  if
   RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
   Л_prevValidatorHash
  then false
  else true
  else false
  then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
  else false). idtac.
  
  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
  Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
  Л_prevValidatorHash); destruct (RoundsBase_ι_Round_ι_unfreeze =?
  DePoolLib_ι_MAX_TIME); auto.
  
  rewrite H1 in H4. idtac.
  rewrite <- H4. idtac.
  
  auto.

  - idtac.
  assert ((if
  if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
  then false
  else true
  then
  if
   if
    RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
   then false
   else true
  then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
  else false
  else false)  = if
  if
  if
   RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
  then false
  else true
  then
  if
   RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
   Л_prevValidatorHash
  then false
  else true
  else false
  then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
  else false). idtac.
  
  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
  Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
  Л_prevValidatorHash); destruct (RoundsBase_ι_Round_ι_unfreeze =?
  DePoolLib_ι_MAX_TIME); auto.
  
  
  rewrite H1 in H4. idtac.
  rewrite <- H4. idtac.
  rewrite H2. rewrite H3. idtac.


  match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_startRoundCompleting ?a ?b] => remember (DePoolContract_Ф_startRoundCompleting a b) as l
            end
end.
destruct l.

match goal with 
| |- ?x  => match x with 
            | context [p ?a] => remember (p a)
            end
end.

destruct p0; auto.

- idtac.

assert ((if
  if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
  then false
  else true
  then
  if
   if
    RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
   then false
   else true
  then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
  else false
  else false)  = if
  if
  if
   RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
  then false
  else true
  then
  if
   RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
   Л_prevValidatorHash
  then false
  else true
  else false
  then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
  else false). idtac.
  
  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
  Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
  Л_prevValidatorHash); destruct (RoundsBase_ι_Round_ι_unfreeze =?
  DePoolLib_ι_MAX_TIME); auto.
  
  
  rewrite H1 in H4. idtac.
  rewrite <- H4. idtac.
  rewrite H2. rewrite H3. idtac.


  Time  do 1 (
    
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
                                            (* simpl;  *)
                                            intros                                                              
        | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
        end
  
    end) . idtac.
  
    auto. auto.

- idtac.

assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (RoundsBase_ι_Round_ι_unfreeze =?
DePoolLib_ι_MAX_TIME); auto.

rewrite H1 in H4. idtac.
rewrite <- H4 in H3. idtac.
rewrite H2 in H3. discriminate.

- idtac. 

assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (RoundsBase_ι_Round_ι_unfreeze =?
DePoolLib_ι_MAX_TIME); auto.

rewrite H1 in H4. idtac.
rewrite <- H4. idtac.

auto.

- idtac.
assert ((if
  if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
  then false
  else true
  then
  if
   if
    RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
   then false
   else true
  then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
  else false
  else false)  = if
  if
  if
   RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
  then false
  else true
  then
  if
   RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
   Л_prevValidatorHash
  then false
  else true
  else false
  then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
  else false). idtac.
  
  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
  Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
  Л_prevValidatorHash); destruct (RoundsBase_ι_Round_ι_unfreeze =?
  DePoolLib_ι_MAX_TIME); auto.
  
  
  rewrite H1 in H4. idtac.
  rewrite <- H4. idtac.
  rewrite H2. rewrite H3. idtac.

  match goal with 
  | |- ?x  => match x with 
              | context [DePoolContract_Ф_startRoundCompleting ?a ?b] => remember (DePoolContract_Ф_startRoundCompleting a b) as l
              end
  end.
  destruct l.
  
  match goal with 
  | |- ?x  => match x with 
              | context [p ?a] => remember (p a)
              end
  end.
  
  destruct p0; auto.

- idtac.

assert ((if
  if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
  then false
  else true
  then
  if
   if
    RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
   then false
   else true
  then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
  else false
  else false)  = if
  if
  if
   RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
  then false
  else true
  then
  if
   RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
   Л_prevValidatorHash
  then false
  else true
  else false
  then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
  else false). idtac.
  
  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
  Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
  Л_prevValidatorHash); destruct (RoundsBase_ι_Round_ι_unfreeze =?
  DePoolLib_ι_MAX_TIME); auto.
  
  
  rewrite H1 in H4. idtac.
  rewrite <- H4. idtac.
  rewrite H2. rewrite H3. idtac.

  Time  do 1 (
    
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
                                            (* simpl;  *)
                                            intros                                                              
        | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
        end
  
    end) . idtac.
  
    auto. auto.

- idtac.

assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (RoundsBase_ι_Round_ι_unfreeze =?
DePoolLib_ι_MAX_TIME); auto.

rewrite H1 in H4. idtac.
rewrite <- H4 in H3. idtac.
rewrite H2 in H3. discriminate.

- idtac. 

assert ((if
if RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 if
  RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash
 then false
 else true
then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
else false
else false)  = if
if
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash
then false
else true
then
if
 RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
 Л_prevValidatorHash
then false
else true
else false
then RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME
else false). idtac.

destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_curValidatorHash); destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =?
Л_prevValidatorHash); destruct (RoundsBase_ι_Round_ι_unfreeze =?
DePoolLib_ι_MAX_TIME); auto.

rewrite H1 in H4. idtac.
rewrite <- H4. idtac.

auto.

 Qed.


