
Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.
Require Import omega.Omega.
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



(* function acceptRewardAndStartRoundCompleting(Round round2, uint64 value) private returns (Round) {
        uint64 effectiveStake = round2.stake - round2.unused;
        uint64 reward = value - effectiveStake;

        round2.grossReward = reward;

        reward = cutDePoolReward(reward, round2);
        round2.rewards = math.muldiv(reward, m_participantRewardFraction, 100);
        round2.rewards -= math.min(round2.rewards, round2.participantQty * RET_OR_REINV_FEE);
        uint64 validatorReward = math.muldiv(reward, m_validatorRewardFraction, 100);
        if (validatorReward != 0)
            m_validatorWallet.transfer(validatorReward, false, 1);

        uint64 associationReward = math.muldiv(reward, m_associationRewardFraction, 100);
        if (associationReward != 0)
             m_validatorWallet.transfer(validatorReward, false, 1);

        round2 = startRoundCompleting(round2, CompletionReason.RewardIsReceived);
        return round2; } *) 

Opaque DePoolContract_Ф_cutDePoolReward  DePoolContract_Ф_startRoundCompleting.    

Opaque intMin.

Lemma DePoolContract_Ф_acceptRewardAndStartRoundCompleting_eval : forall ( Л_round2 : RoundsBase_ι_Round ) 
                                                                          ( Л_value : XInteger64 ) 
                                                                          (l: Ledger) , 
eval_state ( DePoolContract_Ф_acceptRewardAndStartRoundCompleting Л_round2 Л_value ) l =

let round2 := Л_round2 in
let effectiveStake := ( round2 ->> RoundsBase_ι_Round_ι_stake ) - ( round2 ->> RoundsBase_ι_Round_ι_unused ) in
let reward := Л_value - effectiveStake in
let round2 := {$ round2 with RoundsBase_ι_Round_ι_grossReward := reward $} in
let (reward, l_cutDePoolReward) := run ( ↓ ( DePoolContract_Ф_cutDePoolReward reward round2 ) ) l in
let newReward := reward * ( eval_state ( ↑12 ε DePoolContract_ι_m_participantRewardFraction ) l_cutDePoolReward ) / 100 in
let newReward' := newReward - (intMin newReward ((round2 ->> RoundsBase_ι_Round_ι_participantQty)*
                                                (eval_state ( ↑12 ε DePoolContract_ι_RET_OR_REINV_FEE ) l_cutDePoolReward )) ) in
let round2' := {$ round2 with RoundsBase_ι_Round_ι_rewards := newReward' $} in

let validatorReward := reward * ( eval_state ( ↑12 ε DePoolContract_ι_m_validatorRewardFraction ) l_cutDePoolReward ) / 100 in
let if1 : bool := ( negb ( validatorReward =? 0 ) ) in
let l1 := if if1 then exec_state (  tvm_transfer (  eval_state ( ↑2 ε ValidatorBase_ι_m_validatorWallet ) l_cutDePoolReward )
                                                validatorReward  
                                                false  
                                                 1 
                                                default ) l_cutDePoolReward else l_cutDePoolReward in

let associationReward := reward * ( eval_state ( ↑12 ε DePoolContract_ι_m_validatorRewardFraction ) l1 ) / 100  in
let if2 : bool := ( negb ( associationReward =? 0 ) ) in
let l2 := if if2 then exec_state (  tvm_transfer (  eval_state ( ↑2 ε ValidatorBase_ι_m_validatorWallet ) l1 )
                                                associationReward  
                                                false  
                                                1
                                                default ) l1 else l1 in
 eval_state ( ↓ ( DePoolContract_Ф_startRoundCompleting round2' RoundsBase_ι_CompletionReasonP_ι_RewardIsReceived ) ) l2. 
 Proof. 
  intros.
  destruct Л_round2.
  destruct l as
   (Ledger_ι_DebugDePool, Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ConfigParamsBase, Ledger_ι_ParticipantBase, 
  Ledger_ι_DePoolHelper, Ledger_ι_Errors, Ledger_ι_InternalErrors, Ledger_ι_DePoolLib, Ledger_ι_DePoolProxyContract, 
  Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_DePool, Ledger_ι_Participant, Ledger_ι_TestElector, 
  Ledger_ι_VMState, Ledger_ι_LocalState).
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
                                              case_eq b ; (* use case_eq to see destruction results *)
                                              simpl  ; intros
            | context  [match DePoolContract_Ф_cutDePoolReward ?a ?b 
                                    with
                                    | SimpleState s => s
                                    end ?m] => idtac "found DePoolContract_Ф_cutDePoolReward ..."  a b ; 
                                                let p := fresh"p" in
                                                destruct (DePoolContract_Ф_cutDePoolReward a b ) as (p);
                                                let v := fresh"v" in
                                                let l := fresh"l" in 
                                                destruct (p m) as [v l]; 
                                                let Ledger_ι_DebugDePool := fresh "Ledger_ι_DebugDePool" in
                                                let Ledger_ι_ValidatorBase := fresh "Ledger_ι_ValidatorBase" in
                                                let Ledger_ι_ProxyBase := fresh "Ledger_ι_ProxyBase" in
                                                let Ledger_ι_ConfigParamsBase := fresh "Ledger_ι_ConfigParamsBase" in
                                                let Ledger_ι_ParticipantBase := fresh "Ledger_ι_ParticipantBase" in
                                                let Ledger_ι_DePoolHelper := fresh "Ledger_ι_DePoolHelper" in
                                                let Ledger_ι_Errors := fresh "Ledger_ι_Errors" in
                                                let Ledger_ι_InternalErrors := fresh "Ledger_ι_InternalErrors" in
                                                let Ledger_ι_DePoolLib := fresh "Ledger_ι_DePoolLib" in
                                                let Ledger_ι_DePoolProxyContract := fresh "Ledger_ι_DePoolProxyContract" in
                                                let Ledger_ι_RoundsBase := fresh "Ledger_ι_RoundsBase" in
                                                let Ledger_ι_DePoolContract := fresh "Ledger_ι_DePoolContract" in
                                                let Ledger_ι_DePool := fresh "Ledger_ι_DePool" in
                                                let Ledger_ι_Participant := fresh "Ledger_ι_Participant" in
                                                let Ledger_ι_TestElector := fresh "Ledger_ι_TestElector" in
                                                let Ledger_ι_VMState := fresh "Ledger_ι_VMState" in
                                                let Ledger_ι_LocalState := fresh "Ledger_ι_LocalState" in
                                                destruct l as
                                                (Ledger_ι_DebugDePool, Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ConfigParamsBase, Ledger_ι_ParticipantBase, 
                                              Ledger_ι_DePoolHelper, Ledger_ι_Errors, Ledger_ι_InternalErrors, Ledger_ι_DePoolLib, Ledger_ι_DePoolProxyContract, 
                                              Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_DePool, Ledger_ι_Participant, Ledger_ι_TestElector, 
                                              Ledger_ι_VMState, Ledger_ι_LocalState);
                                              destruct Ledger_ι_DebugDePool, Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ConfigParamsBase, Ledger_ι_ParticipantBase, 
                                              Ledger_ι_DePoolHelper, Ledger_ι_Errors, Ledger_ι_InternalErrors, Ledger_ι_DePoolLib, Ledger_ι_DePoolProxyContract, 
                                              Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_DePool, Ledger_ι_Participant, Ledger_ι_TestElector, 
                                              Ledger_ι_VMState, Ledger_ι_LocalState;
                                                (* destruct v ; *)
                                                simpl                                   
            | context  [match DePoolContract_Ф_startRoundCompleting ?a ?b
                  with
                  | SimpleState s => s
                  end ?m] => idtac "found DePoolContract_Ф_startRoundCompleting ..."  a b; 
                              let p := fresh"p" in
                              destruct (DePoolContract_Ф_startRoundCompleting a b) as (p);
                              let v := fresh"v" in
                              let l := fresh"l" in 
                              destruct (p m) as [v l]; 
                              let Ledger_ι_DebugDePool := fresh "Ledger_ι_DebugDePool" in
                              let Ledger_ι_ValidatorBase := fresh "Ledger_ι_ValidatorBase" in
                              let Ledger_ι_ProxyBase := fresh "Ledger_ι_ProxyBase" in
                              let Ledger_ι_ConfigParamsBase := fresh "Ledger_ι_ConfigParamsBase" in
                              let Ledger_ι_ParticipantBase := fresh "Ledger_ι_ParticipantBase" in
                              let Ledger_ι_DePoolHelper := fresh "Ledger_ι_DePoolHelper" in
                              let Ledger_ι_Errors := fresh "Ledger_ι_Errors" in
                              let Ledger_ι_InternalErrors := fresh "Ledger_ι_InternalErrors" in
                              let Ledger_ι_DePoolLib := fresh "Ledger_ι_DePoolLib" in
                              let Ledger_ι_DePoolProxyContract := fresh "Ledger_ι_DePoolProxyContract" in
                              let Ledger_ι_RoundsBase := fresh "Ledger_ι_RoundsBase" in
                              let Ledger_ι_DePoolContract := fresh "Ledger_ι_DePoolContract" in
                              let Ledger_ι_DePool := fresh "Ledger_ι_DePool" in
                              let Ledger_ι_Participant := fresh "Ledger_ι_Participant" in
                              let Ledger_ι_TestElector := fresh "Ledger_ι_TestElector" in
                              let Ledger_ι_VMState := fresh "Ledger_ι_VMState" in
                              let Ledger_ι_LocalState := fresh "Ledger_ι_LocalState" in
                              destruct l as
                              (Ledger_ι_DebugDePool, Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ConfigParamsBase, Ledger_ι_ParticipantBase, 
                            Ledger_ι_DePoolHelper, Ledger_ι_Errors, Ledger_ι_InternalErrors, Ledger_ι_DePoolLib, Ledger_ι_DePoolProxyContract, 
                            Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_DePool, Ledger_ι_Participant, Ledger_ι_TestElector, 
                            Ledger_ι_VMState, Ledger_ι_LocalState);
                            destruct Ledger_ι_DebugDePool, Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ConfigParamsBase, Ledger_ι_ParticipantBase, 
                            Ledger_ι_DePoolHelper, Ledger_ι_Errors, Ledger_ι_InternalErrors, Ledger_ι_DePoolLib, Ledger_ι_DePoolProxyContract, 
                            Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_DePool, Ledger_ι_Participant, Ledger_ι_TestElector, 
                            Ledger_ι_VMState, Ledger_ι_LocalState;
                            (*  destruct v ; *)
                              simpl                                                                                          
            | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
          end
      end) . 
     
      all: pr_numgoals.
 Qed. 

Lemma DePoolContract_Ф_acceptRewardAndStartRoundCompleting_exec : forall ( Л_round2 : RoundsBase_ι_Round ) 
                                                                          ( Л_value : XInteger64 ) 
                                                                          (l: Ledger) , 
exec_state ( DePoolContract_Ф_acceptRewardAndStartRoundCompleting Л_round2 Л_value ) l =

let round2 := Л_round2 in
let effectiveStake := ( round2 ->> RoundsBase_ι_Round_ι_stake ) - ( round2 ->> RoundsBase_ι_Round_ι_unused ) in
let reward := Л_value - effectiveStake in
let round2 := {$ round2 with RoundsBase_ι_Round_ι_grossReward := reward $} in
let (reward, l_cutDePoolReward) := run ( ↓ ( DePoolContract_Ф_cutDePoolReward reward round2 ) ) l in
let newReward := reward * ( eval_state ( ↑12 ε DePoolContract_ι_m_participantRewardFraction ) l_cutDePoolReward ) / 100 in
let newReward' := newReward - (intMin newReward ((round2 ->> RoundsBase_ι_Round_ι_participantQty)*
                                                (eval_state ( ↑12 ε DePoolContract_ι_RET_OR_REINV_FEE ) l_cutDePoolReward )) ) in
let round2' := {$ round2 with RoundsBase_ι_Round_ι_rewards := newReward' $} in

let validatorReward := reward * ( eval_state ( ↑12 ε DePoolContract_ι_m_validatorRewardFraction ) l_cutDePoolReward ) / 100 in
let if1 : bool := ( negb ( validatorReward =? 0 ) ) in
let l1 := if if1 then exec_state (  tvm_transfer (  eval_state ( ↑2 ε ValidatorBase_ι_m_validatorWallet ) l_cutDePoolReward )
                                                validatorReward  
                                                false  
                                                 1 
                                                default ) l_cutDePoolReward else l_cutDePoolReward in

let associationReward := reward * ( eval_state ( ↑12 ε DePoolContract_ι_m_validatorRewardFraction ) l1 ) / 100  in
let if2 : bool := ( negb ( associationReward =? 0 ) ) in
let l2 := if if2 then exec_state (  tvm_transfer (  eval_state ( ↑2 ε ValidatorBase_ι_m_validatorWallet ) l1 )
                                                associationReward  
                                                false  
                                                1
                                                default ) l1 else l1 in
 exec_state ( ↓ ( DePoolContract_Ф_startRoundCompleting round2' RoundsBase_ι_CompletionReasonP_ι_RewardIsReceived ) ) l2. 
 Proof. 
  intros.
  destruct Л_round2.
  destruct l as
   (Ledger_ι_DebugDePool, Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ConfigParamsBase, Ledger_ι_ParticipantBase, 
  Ledger_ι_DePoolHelper, Ledger_ι_Errors, Ledger_ι_InternalErrors, Ledger_ι_DePoolLib, Ledger_ι_DePoolProxyContract, 
  Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_DePool, Ledger_ι_Participant, Ledger_ι_TestElector, 
  Ledger_ι_VMState, Ledger_ι_LocalState).
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
                                              case_eq b ; (* use case_eq to see destruction results *)
                                              simpl  ; intros
            | context  [match DePoolContract_Ф_cutDePoolReward ?a ?b 
                                    with
                                    | SimpleState s => s
                                    end ?m] => idtac "found DePoolContract_Ф_cutDePoolReward ..."  a b ; 
                                                let p := fresh"p" in
                                                destruct (DePoolContract_Ф_cutDePoolReward a b ) as (p);
                                                let v := fresh"v" in
                                                let l := fresh"l" in 
                                                destruct (p m) as [v l]; 
                                                let Ledger_ι_DebugDePool := fresh "Ledger_ι_DebugDePool" in
                                                let Ledger_ι_ValidatorBase := fresh "Ledger_ι_ValidatorBase" in
                                                let Ledger_ι_ProxyBase := fresh "Ledger_ι_ProxyBase" in
                                                let Ledger_ι_ConfigParamsBase := fresh "Ledger_ι_ConfigParamsBase" in
                                                let Ledger_ι_ParticipantBase := fresh "Ledger_ι_ParticipantBase" in
                                                let Ledger_ι_DePoolHelper := fresh "Ledger_ι_DePoolHelper" in
                                                let Ledger_ι_Errors := fresh "Ledger_ι_Errors" in
                                                let Ledger_ι_InternalErrors := fresh "Ledger_ι_InternalErrors" in
                                                let Ledger_ι_DePoolLib := fresh "Ledger_ι_DePoolLib" in
                                                let Ledger_ι_DePoolProxyContract := fresh "Ledger_ι_DePoolProxyContract" in
                                                let Ledger_ι_RoundsBase := fresh "Ledger_ι_RoundsBase" in
                                                let Ledger_ι_DePoolContract := fresh "Ledger_ι_DePoolContract" in
                                                let Ledger_ι_DePool := fresh "Ledger_ι_DePool" in
                                                let Ledger_ι_Participant := fresh "Ledger_ι_Participant" in
                                                let Ledger_ι_TestElector := fresh "Ledger_ι_TestElector" in
                                                let Ledger_ι_VMState := fresh "Ledger_ι_VMState" in
                                                let Ledger_ι_LocalState := fresh "Ledger_ι_LocalState" in
                                                destruct l as
                                                (Ledger_ι_DebugDePool, Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ConfigParamsBase, Ledger_ι_ParticipantBase, 
                                              Ledger_ι_DePoolHelper, Ledger_ι_Errors, Ledger_ι_InternalErrors, Ledger_ι_DePoolLib, Ledger_ι_DePoolProxyContract, 
                                              Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_DePool, Ledger_ι_Participant, Ledger_ι_TestElector, 
                                              Ledger_ι_VMState, Ledger_ι_LocalState);
                                              destruct Ledger_ι_DebugDePool, Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ConfigParamsBase, Ledger_ι_ParticipantBase, 
                                              Ledger_ι_DePoolHelper, Ledger_ι_Errors, Ledger_ι_InternalErrors, Ledger_ι_DePoolLib, Ledger_ι_DePoolProxyContract, 
                                              Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_DePool, Ledger_ι_Participant, Ledger_ι_TestElector, 
                                              Ledger_ι_VMState, Ledger_ι_LocalState;
                                                (* destruct v ; *)
                                                simpl                                   
            | context  [match DePoolContract_Ф_startRoundCompleting ?a ?b
                  with
                  | SimpleState s => s
                  end ?m] => idtac "found DePoolContract_Ф_startRoundCompleting ..."  a b; 
                              let p := fresh"p" in
                              destruct (DePoolContract_Ф_startRoundCompleting a b) as (p);
                              let v := fresh"v" in
                              let l := fresh"l" in 
                              destruct (p m) as [v l]; 
                              let Ledger_ι_DebugDePool := fresh "Ledger_ι_DebugDePool" in
                              let Ledger_ι_ValidatorBase := fresh "Ledger_ι_ValidatorBase" in
                              let Ledger_ι_ProxyBase := fresh "Ledger_ι_ProxyBase" in
                              let Ledger_ι_ConfigParamsBase := fresh "Ledger_ι_ConfigParamsBase" in
                              let Ledger_ι_ParticipantBase := fresh "Ledger_ι_ParticipantBase" in
                              let Ledger_ι_DePoolHelper := fresh "Ledger_ι_DePoolHelper" in
                              let Ledger_ι_Errors := fresh "Ledger_ι_Errors" in
                              let Ledger_ι_InternalErrors := fresh "Ledger_ι_InternalErrors" in
                              let Ledger_ι_DePoolLib := fresh "Ledger_ι_DePoolLib" in
                              let Ledger_ι_DePoolProxyContract := fresh "Ledger_ι_DePoolProxyContract" in
                              let Ledger_ι_RoundsBase := fresh "Ledger_ι_RoundsBase" in
                              let Ledger_ι_DePoolContract := fresh "Ledger_ι_DePoolContract" in
                              let Ledger_ι_DePool := fresh "Ledger_ι_DePool" in
                              let Ledger_ι_Participant := fresh "Ledger_ι_Participant" in
                              let Ledger_ι_TestElector := fresh "Ledger_ι_TestElector" in
                              let Ledger_ι_VMState := fresh "Ledger_ι_VMState" in
                              let Ledger_ι_LocalState := fresh "Ledger_ι_LocalState" in
                              destruct l as
                              (Ledger_ι_DebugDePool, Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ConfigParamsBase, Ledger_ι_ParticipantBase, 
                            Ledger_ι_DePoolHelper, Ledger_ι_Errors, Ledger_ι_InternalErrors, Ledger_ι_DePoolLib, Ledger_ι_DePoolProxyContract, 
                            Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_DePool, Ledger_ι_Participant, Ledger_ι_TestElector, 
                            Ledger_ι_VMState, Ledger_ι_LocalState);
                            destruct Ledger_ι_DebugDePool, Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ConfigParamsBase, Ledger_ι_ParticipantBase, 
                            Ledger_ι_DePoolHelper, Ledger_ι_Errors, Ledger_ι_InternalErrors, Ledger_ι_DePoolLib, Ledger_ι_DePoolProxyContract, 
                            Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_DePool, Ledger_ι_Participant, Ledger_ι_TestElector, 
                            Ledger_ι_VMState, Ledger_ι_LocalState;
                            (*  destruct v ; *)
                              simpl                                                                                          
            | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
          end
      end) . 
     
      all: pr_numgoals.
 Qed. 
 