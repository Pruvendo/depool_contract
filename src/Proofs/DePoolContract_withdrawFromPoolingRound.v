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


Opaque RoundsBase_Ф_withdrawStakeInPoolingRound.

Lemma withdrawFromPoolingRound_exec: forall (Л_withdrawValue: Z) (l: Ledger),

 exec_state (DePoolContract_Ф_withdrawFromPoolingRound' Л_withdrawValue) l = 
 
 let sender := eval_state msg_sender l in 
 let isExtMsg : bool := negb (sender =? 0) in 
 let isPoolClosed : bool := eval_state (↑12 ε DePoolContract_ι_m_poolClosed) l in 
 let optParticipant := eval_state (↓ ParticipantBase_Ф_fetchParticipant sender) l in 
 let partHasValue : bool := xMaybeIsSome optParticipant in 
 let participant := maybeGet optParticipant  in 
 let minStake := eval_state (↑12 ε DePoolContract_ι_m_minStake) l in 
 let (rp', l_withdraw) := run (↓ RoundsBase_Ф_withdrawStakeInPoolingRound participant sender Л_withdrawValue minStake) l in
 let (removedPoolingStake, participant') := rp' in
 let sender' := eval_state msg_sender l_withdraw in 
 let l_set := exec_state (↓ ParticipantBase_Ф__setOrDeleteParticipant sender' participant') l_withdraw in
 let l_transfer := exec_state (tvm_transfer sender' removedPoolingStake false 64 default) l_set in 
 
 if isExtMsg then
    if isPoolClosed then exec_state (DePoolContract_Ф__sendError (eval_state (↑ε12 DePoolContract_ι_STATUS_DEPOOL_CLOSED) l) 0 ) l
       else if (negb partHasValue) then exec_state (DePoolContract_Ф__sendError (eval_state (↑ε12 DePoolContract_ι_STATUS_NO_PARTICIPANT) l) 0 ) l 
                                   else l_transfer
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
                                           (* simpl;  *)
                                           intros                                                              
       | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
       end

   end) . idtac.

   all: pr_numgoals.


  match goal with 
  | |- ?x  => match x with 
              | context [RoundsBase_Ф_withdrawStakeInPoolingRound ?a ?b ?c ?d] => remember (RoundsBase_Ф_withdrawStakeInPoolingRound a b c d)
              end
  end. idtac.

  destruct l. idtac.
  
  match goal with 
  | |- ?x  => match x with 
              | context [p ?a] => remember (p a)
              end
  end.
  
  destruct p0. idtac.
  destruct x; auto.

  all: pr_numgoals.
 
  match goal with 
  | |- ?x  => match x with 
              | context [RoundsBase_Ф_withdrawStakeInPoolingRound ?a ?b ?c ?d] => remember (RoundsBase_Ф_withdrawStakeInPoolingRound a b c d)
              end
  end. idtac.

  destruct l. idtac.
  
  match goal with 
  | |- ?x  => match x with 
              | context [p ?a] => remember (p a)
              end
  end.
  
  destruct p0. idtac.
  destruct x; auto.

  all: pr_numgoals.

  match goal with 
  | |- ?x  => match x with 
              | context [RoundsBase_Ф_withdrawStakeInPoolingRound ?a ?b ?c ?d] => remember (RoundsBase_Ф_withdrawStakeInPoolingRound a b c d)
              end
  end. idtac.

  destruct l. idtac.
  
  match goal with 
  | |- ?x  => match x with 
              | context [p ?a] => remember (p a)
              end
  end.
  
  destruct p0. idtac.
  destruct x; auto.
  destruct d. idtac.

  case (DePoolLib_ι_Participant_ι_roundQty =? 0); auto.

  all: pr_numgoals.

  match goal with 
  | |- ?x  => match x with 
              | context [RoundsBase_Ф_withdrawStakeInPoolingRound ?a ?b ?c ?d] => remember (RoundsBase_Ф_withdrawStakeInPoolingRound a b c d)
              end
  end. idtac.

  destruct l. idtac.
  
  match goal with 
  | |- ?x  => match x with 
              | context [p ?a] => remember (p a)
              end
  end.
  
  destruct p0. idtac.
  destruct x; auto.

  all: pr_numgoals.

 Qed.
 

Lemma withdrawFromPoolingRound_eval: forall (Л_withdrawValue: Z) (l: Ledger),
eval_state (↓ (DePoolContract_Ф_withdrawFromPoolingRound' Л_withdrawValue)) l = 

let sender := eval_state msg_sender l in 
let isExtMsg : bool := negb ( sender =? 0) in 
let isPoolClosed : bool := eval_state (↑12 ε DePoolContract_ι_m_poolClosed) l in 
let optParticipant := eval_state (↓ ParticipantBase_Ф_fetchParticipant sender) l in 
let partHasValue : bool := xMaybeIsSome optParticipant in 
if isExtMsg then
   if isPoolClosed then Value (Error I) 
      else if (negb partHasValue) then Value (Error I) else Value (Value I)
else Error (eval_state (↑ε7 Errors_ι_IS_EXT_MSG) l).  
Proof.
  intros.
  destruct l. 
  compute. idtac.
  idtac.

  Time repeat (
  
  
  match goal with
    | |- ?x =>
      match x with
      | context [let (x, t) := ?f in @?g x t] => replace (let (x, t) := f in g x t) with (g (fst f) (snd f)) by (symmetry; apply fstsndImplies)  ; simpl
        | context [if ?b then _ else _] =>  repeat rewrite ifSimpleState ; 
                                            repeat rewrite ifFunApply ;
                                            case b ; simpl
        | _ => auto
      end
  end) . 

Qed.



  
