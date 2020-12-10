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
Module DePoolContract_Ф_startRoundCompleting (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.



Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo.    
Opaque DePoolContract_Ф_setLastRoundInfo.

Lemma DePoolContract_Ф_startRoundCompleting_exec : forall ( Л_round : RoundsBase_ι_Round ) 
                                                 ( Л_reason : RoundsBase_ι_CompletionReason )
                                                 (l: Ledger) , 
                                                 (*: LedgerT RoundsBase_ι_Round*)
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
                      contractMessage := {| messageValue := DePool_ι_VALUE_FOR_SELF_CALL ;
                                            messageFlag  := 1 ; 
                                            messageBounce := false
                                            |} |} in 
let newMessage2  := {| contractAddress :=  0 ;
                      contractFunction := DePoolContract_Ф_ticktockF  ;
                      contractMessage := {| messageValue := DePool_ι_VALUE_FOR_SELF_CALL ;
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

exec_state (↓ DePoolContract_Ф_startRoundCompleting Л_round Л_reason ) l = 
exec_state (↓ DePoolContract_Ф_setLastRoundInfo round') l''.
Proof. 
  intros.
  destructLedger l. 
  compute.

  Time repeat destructIf_solve. 

Qed.   


Lemma DePoolContract_Ф_startRoundCompleting_eval : forall ( Л_round : RoundsBase_ι_Round ) 
                                                 ( Л_reason : RoundsBase_ι_CompletionReason )
                                                 (l: Ledger) , 
                                                 (*: LedgerT RoundsBase_ι_Round*)
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
eval_state (↓ DePoolContract_Ф_startRoundCompleting Л_round Л_reason ) l = round'.
Proof. 

  intros.
  destructLedger l. 
  compute.

  Time repeat destructIf_solve. 
Qed.   

End DePoolContract_Ф_startRoundCompleting.