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



Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo.    
Opaque DePoolContract_Ф_setLastRoundInfo.

Lemma DePoolContract_Ф_startRoundCompleting_exec : forall ( Л_round : RoundsBase_ι_Round ) 
                                                 ( Л_reason : RoundsBase_ι_CompletionReason )
                                                 (l: Ledger) , 
                                                 (*: LedgerT RoundsBase_ι_Round*)
exec_state (↓ DePoolContract_Ф_startRoundCompleting Л_round Л_reason ) l = 

let participantQty := Л_round ->> RoundsBase_ι_Round_ι_participantQty in

let round' := if (participantQty =? 0) then 
  {$ Л_round with ( RoundsBase_ι_Round_ι_completionReason , Л_reason ) ;
                  ( RoundsBase_ι_Round_ι_step , RoundsBase_ι_RoundStepP_ι_Completed );
                  ( RoundsBase_ι_Round_ι_handledStakesAndRewards , 0 );
                  ( RoundsBase_ι_Round_ι_validatorRemainingStake , 0 ) $} else
  {$ Л_round with ( RoundsBase_ι_Round_ι_completionReason , Л_reason ) ;
                  ( RoundsBase_ι_Round_ι_step , RoundsBase_ι_RoundStepP_ι_Completing );
                  ( RoundsBase_ι_Round_ι_handledStakesAndRewards , 0 );
                  ( RoundsBase_ι_Round_ι_validatorRemainingStake , 0 ) $}                
                  in
let oldMessages := VMState_ι_messages ( Ledger_ι_VMState l ) in
let newMessage1  := {| contractAddress :=  0 ;
                      contractFunction := DePoolContract_Ф_completeRoundF 
                                 ( round' ->> RoundsBase_ι_Round_ι_id ) 
                                 ( round' ->> RoundsBase_ι_Round_ι_participantQty )  ;
                      contractMessage := {| messageValue := (eval_state ( ↑12 ε DePoolContract_ι_VALUE_FOR_SELF_CALL) l ) ;
                                            messageFlag  := 1 ; 
                                            messageBounce := false
                                            |} |} in 
let newMessage2  := {| contractAddress :=  0 ;
                      contractFunction := DePoolContract_Ф_ticktockF  ;
                      contractMessage := {| messageValue := (eval_state ( ↑12 ε DePoolContract_ι_VALUE_FOR_SELF_CALL) l ) ;
                                            messageFlag  := 0 ; 
                                            messageBounce := false
                                            |} |} in                                             
        (* emit RoundCompleted(toTruncatedRound(round)); *)
let oldEvents := VMState_ι_events ( Ledger_ι_VMState l ) in
let tr := eval_state ( ↓ RoundsBase_Ф_toTruncatedRound round' ) l in
let newEvent  :=  RoundCompleted tr in
let l' := if (participantQty =? 0) then {$l With ( VMState_ι_messages , newMessage2 :: oldMessages ) $}
                                   else {$l With ( VMState_ι_messages , newMessage1 :: oldMessages ) $} in
let l'' := {$ l' With ( VMState_ι_events , newEvent :: oldEvents ) $} in

exec_state (↓ DePoolContract_Ф_setLastRoundInfo round') l''.
Proof. 
   intros. destruct l. 
  
   destruct Ledger_ι_DebugDePool, Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ConfigParamsBase, Ledger_ι_ParticipantBase, 
   Ledger_ι_DePoolHelper, Ledger_ι_Errors, Ledger_ι_InternalErrors, Ledger_ι_DePoolLib, Ledger_ι_DePoolProxyContract, 
   Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_DePool, Ledger_ι_Participant, Ledger_ι_TestElector, 
   Ledger_ι_VMState, Ledger_ι_LocalState.
 
   compute. idtac.
 
   Time repeat (
   
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
 
   end) . 
Qed.   


Lemma DePoolContract_Ф_startRoundCompleting_eval : forall ( Л_round : RoundsBase_ι_Round ) 
                                                 ( Л_reason : RoundsBase_ι_CompletionReason )
                                                 (l: Ledger) , 
                                                 (*: LedgerT RoundsBase_ι_Round*)
eval_state (↓ DePoolContract_Ф_startRoundCompleting Л_round Л_reason ) l = 

let participantQty := Л_round ->> RoundsBase_ι_Round_ι_participantQty in

let round' := if (participantQty =? 0) then 
  {$ Л_round with ( RoundsBase_ι_Round_ι_completionReason , Л_reason ) ;
                  ( RoundsBase_ι_Round_ι_step , RoundsBase_ι_RoundStepP_ι_Completed );
                  ( RoundsBase_ι_Round_ι_handledStakesAndRewards , 0 );
                  ( RoundsBase_ι_Round_ι_validatorRemainingStake , 0 ) $} else
  {$ Л_round with ( RoundsBase_ι_Round_ι_completionReason , Л_reason ) ;
                  ( RoundsBase_ι_Round_ι_step , RoundsBase_ι_RoundStepP_ι_Completing );
                  ( RoundsBase_ι_Round_ι_handledStakesAndRewards , 0 );
                  ( RoundsBase_ι_Round_ι_validatorRemainingStake , 0 ) $}                
                  in
round'.
Proof. 
   intros. destruct l. 
  
   destruct Ledger_ι_DebugDePool, Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ConfigParamsBase, Ledger_ι_ParticipantBase, 
   Ledger_ι_DePoolHelper, Ledger_ι_Errors, Ledger_ι_InternalErrors, Ledger_ι_DePoolLib, Ledger_ι_DePoolProxyContract, 
   Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_DePool, Ledger_ι_Participant, Ledger_ι_TestElector, 
   Ledger_ι_VMState, Ledger_ι_LocalState.
 
   compute. idtac.
 
   Time repeat (
   
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
 
   end) . 
Qed.   