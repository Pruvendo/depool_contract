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

Require Import depoolContract.Lib.CommonStateProofs.

Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope solidity_scope.
Require Import Lists.List.
Import ListNotations.
Local Open Scope list_scope.

Require Import depoolContract.DePoolConsts.
Module DePoolContract_Ф_totalParticipantFunds (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.



Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair.


Definition DePoolContract_Ф_totalParticipantFunds_while (Л_ingoreRoundId : XInteger64) : LedgerT (XBool # True) :=
  (While ((↑17 D2! LocalState_ι_totalParticipantFunds_Л_pair) ->hasValue) do ( 
  declareLocal {( Л_id :>: XInteger64 , Л_round :>: RoundsBase_ι_Round )} := (↑17 D2! LocalState_ι_totalParticipantFunds_Л_pair) ->get ; 
  declareLocal Л_step :>: RoundsBase_ι_RoundStep := $ (Л_round ->> RoundsBase_ι_Round_ι_step) ; 
  (If (( $Л_id ?!= $Л_ingoreRoundId) !& ( $Л_step ?!= ξ$ RoundsBase_ι_RoundStepP_ι_Completed )) then { 
  If ( $Л_step ?== ξ$ RoundsBase_ι_RoundStepP_ι_Completing) then { 
  If ( $ (Л_round ->> RoundsBase_ι_Round_ι_completionReason) ?== ξ$ RoundsBase_ι_CompletionReasonP_ι_ValidatorIsPunished) then { 
    (↑17 U1! LocalState_ι_totalParticipantFunds_Л_stakes !+= ( $ (Л_round ->> RoundsBase_ι_Round_ι_unused) !+ 
                                  $ (Л_round ->> RoundsBase_ι_Round_ι_recoveredStake)) !- 
                                  $ (Л_round ->> RoundsBase_ι_Round_ι_handledStakesAndRewards)) 
  } 
  else { 
    (↑17 U1! LocalState_ι_totalParticipantFunds_Л_stakes !+= ( $ (Л_round ->> RoundsBase_ι_Round_ι_stake) !+ 
       $ (Л_round ->> RoundsBase_ι_Round_ι_rewards)) !- $ (Л_round ->> RoundsBase_ι_Round_ι_handledStakesAndRewards)) 
  } 
  } else { If ( $Л_step ?== ξ$ RoundsBase_ι_RoundStepP_ι_PrePooling) !| 
        ( $Л_step ?== ξ$ RoundsBase_ι_RoundStepP_ι_Pooling) !| 
        ( $Л_step ?== ξ$ RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest) !| 
        (( $Л_step ?== ξ$ RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze) !& 
        ( $ (Л_round ->> RoundsBase_ι_Round_ι_completionReason) ?== ξ$ RoundsBase_ι_CompletionReasonP_ι_Undefined)) then { 
    (↑17 U1! LocalState_ι_totalParticipantFunds_Л_stakes !+= $ (Л_round ->> RoundsBase_ι_Round_ι_stake)) 
  } else { 
    (↑17 U1! LocalState_ι_totalParticipantFunds_Л_stakes !+= $ (Л_round ->> RoundsBase_ι_Round_ι_unused)) 
  } 
  } 
  }) >> 
  (↑↑17 U2! LocalState_ι_totalParticipantFunds_Л_pair := RoundsBase_Ф_nextRound (! $Л_id !)) >> 
  continue! I) ) . 

Definition DePoolContract_Ф_totalParticipantFunds_header (Л_ingoreRoundId : XInteger64) : LedgerT XInteger64 :=
  ( declareGlobal LocalState_ι_totalParticipantFunds_Л_stakes :>: XInteger64 := $ xInt0) >> 
  ( declareGlobal! LocalState_ι_totalParticipantFunds_Л_pair :>: ( XMaybe (XInteger64 # RoundsBase_ι_Round) ) := RoundsBase_Ф_minRound ()) >> 
  DePoolContract_Ф_totalParticipantFunds_while Л_ingoreRoundId >>
  return!! (↑17 D2! LocalState_ι_totalParticipantFunds_Л_stakes). 

Lemma DePoolContract_Ф_totalParticipantFunds_header_eq: DePoolContract_Ф_totalParticipantFunds = DePoolContract_Ф_totalParticipantFunds_header.
Proof.
  auto.
Qed.
  
Opaque DePoolContract_Ф_totalParticipantFunds_while.

Lemma DePoolContract_Ф_totalParticipantFunds_header_exec : forall ( Л_ingoreRoundId : XInteger64 ) (l: Ledger) ,
let l0 := {$ l  With ( LocalState_ι_totalParticipantFunds_Л_stakes , 0 );
                     ( LocalState_ι_totalParticipantFunds_Л_pair , ( eval_state ( ↓ RoundsBase_Ф_minRound ) l ) ) $} in 
let l' := exec_state (  DePoolContract_Ф_totalParticipantFunds_while Л_ingoreRoundId ) l0 in 

exec_state (  DePoolContract_Ф_totalParticipantFunds_header Л_ingoreRoundId ) l = l' .
Proof.
  intros. 

  destructLedger l. 
  compute. idtac.

  destructFunction1 DePoolContract_Ф_totalParticipantFunds_while; auto. idtac.
  destruct l; auto.

Qed. 

Lemma DePoolContract_Ф_totalParticipantFunds_header_eval : forall ( Л_ingoreRoundId : XInteger64 )
                                                           (l: Ledger) ,
let l0 := {$ l  With ( LocalState_ι_totalParticipantFunds_Л_stakes , 0 );
                     ( LocalState_ι_totalParticipantFunds_Л_pair , ( eval_state ( ↓ RoundsBase_Ф_minRound ) l ) ) $} in 
let l' := exec_state (  DePoolContract_Ф_totalParticipantFunds_while Л_ingoreRoundId ) l0 in 

eval_state (  DePoolContract_Ф_totalParticipantFunds_header Л_ingoreRoundId ) l = 
  eval_state (↑17 D2! LocalState_ι_totalParticipantFunds_Л_stakes) l'.
Proof.
  intros.
  destructLedger l. 
  compute. idtac.

  destructFunction1 DePoolContract_Ф_totalParticipantFunds_while; auto. 
Qed. 


End DePoolContract_Ф_totalParticipantFunds.