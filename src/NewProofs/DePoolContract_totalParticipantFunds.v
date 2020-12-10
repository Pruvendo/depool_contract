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

(* function totalParticipantFunds(uint64 ingoreRoundId) private view returns (uint64) { 
    uint64 stakes = 0; 
    optional(uint64, Round) pair = minRound(); 
    while (pair.hasValue()) { 
      (uint64 id, Round round) = pair.get(); 
      RoundStep step = round.step; 
      if (id != ingoreRoundId && step != RoundStep.Completed) { 
        if (step == RoundStep.Completing) { 
          if (round.completionReason == CompletionReason.ValidatorIsPunished) 
            stakes += (round.unused + round.recoveredStake) - round.handledStakesAndRewards; 
          else { 
            stakes += (round.stake + round.rewards) - round.handledStakesAndRewards; 
          } 
        } else if ( 
          step == RoundStep.PrePooling || 
          step == RoundStep.Pooling || 
          step == RoundStep.WaitingValidatorRequest || 
          step == RoundStep.WaitingUnfreeze && round.completionReason != CompletionReason.Undefined 
        ) { 
          stakes += round.stake; 
        } else { 
          stakes += round.unused; 
        } 
      } 
      pair = nextRound(id); 
    } 
    return stakes; 
  } *) 

Definition DePoolContract_Ф_totalParticipantFunds_while (Л_ingoreRoundId : XInteger64) 
                                                            : LedgerT (XBool # True) :=
  (While ((↑17 D2! LocalState_ι_totalParticipantFunds_Л_pair) ->hasValue) do ( 
                     (*     (uint64 id, Round round) = pair.get(); *) 
  declareLocal {( Л_id :>: XInteger64 , Л_round :>: RoundsBase_ι_Round )} := (↑17 D2! LocalState_ι_totalParticipantFunds_Л_pair) ->get ; 
                     (*    RoundStep step = round.step; *) 
  declareLocal Л_step :>: RoundsBase_ι_RoundStep := $ (Л_round ->> RoundsBase_ι_Round_ι_step) ; 
                     (*     if (id != ingoreRoundId && step != RoundStep.Completed) { *) 
  (If (( $Л_id ?!= $Л_ingoreRoundId) !& ( $Л_step ?!= ξ$ RoundsBase_ι_RoundStepP_ι_Completed )) then { 
                      (*       if (step == RoundStep.Completing) { *) 
  If ( $Л_step ?== ξ$ RoundsBase_ι_RoundStepP_ι_Completing) then { 
                       (*         if (round.completionReason == CompletionReason.ValidatorIsPunished) *) 
  If ( $ (Л_round ->> RoundsBase_ι_Round_ι_completionReason) ?== ξ$ RoundsBase_ι_CompletionReasonP_ι_ValidatorIsPunished) then { 
  (*           stakes += (round.unused + round.recoveredStake) - round.handledStakesAndRewards; *) 
    (↑17 U1! LocalState_ι_totalParticipantFunds_Л_stakes !+= ( $ (Л_round ->> RoundsBase_ι_Round_ι_unused) !+ 
                                  $ (Л_round ->> RoundsBase_ι_Round_ι_recoveredStake)) !- 
                                  $ (Л_round ->> RoundsBase_ι_Round_ι_handledStakesAndRewards)) 
  } 
  (*         else { *) 
  else { 
  (*           stakes += (round.stake + round.rewards) - round.handledStakesAndRewards; *) 
    (↑17 U1! LocalState_ι_totalParticipantFunds_Л_stakes !+= ( $ (Л_round ->> RoundsBase_ι_Round_ι_stake) !+ 
       $ (Л_round ->> RoundsBase_ι_Round_ι_rewards)) !- $ (Л_round ->> RoundsBase_ι_Round_ι_handledStakesAndRewards)) 
  (*         } *) 
  } 
  (*      } else if ( *) 
  (*        step == RoundStep.PrePooling || *) 
  (*         step == RoundStep.Pooling || *) 
  (*         step == RoundStep.WaitingValidatorRequest || *) 
  (*         step == RoundStep.WaitingUnfreeze && round.completionReason != CompletionReason.Undefined *) 
  (*       ) { *) 
  } else { If ( $Л_step ?== ξ$ RoundsBase_ι_RoundStepP_ι_PrePooling) !| 
        ( $Л_step ?== ξ$ RoundsBase_ι_RoundStepP_ι_Pooling) !| 
        ( $Л_step ?== ξ$ RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest) !| 
        (( $Л_step ?== ξ$ RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze) !& 
        ( $ (Л_round ->> RoundsBase_ι_Round_ι_completionReason) ?== ξ$ RoundsBase_ι_CompletionReasonP_ι_Undefined)) then { 
  (*         stakes += round.stake; *) 
    (↑17 U1! LocalState_ι_totalParticipantFunds_Л_stakes !+= $ (Л_round ->> RoundsBase_ι_Round_ι_stake)) 
  (*       } else { *) 
  } else { 
  (*        stakes += round.unused; *) 
    (↑17 U1! LocalState_ι_totalParticipantFunds_Л_stakes !+= $ (Л_round ->> RoundsBase_ι_Round_ι_unused)) 
  (*       } *) 
  } 
  (*     } *) 
  } 
  }) >> 
  (*     pair = nextRound(id); *) 
  (↑↑17 U2! LocalState_ι_totalParticipantFunds_Л_pair := RoundsBase_Ф_nextRound (! $Л_id !)) >> 
  (*   } *) 
  continue! I) ) . 

Lemma DePoolContract_Ф_totalParticipantFunds_exec : forall ( Л_ingoreRoundId : XInteger64 )
                                                           (l: Ledger) ,
let l_stakes := {$ l        With ( LocalState_ι_totalParticipantFunds_Л_stakes , 0 ) $} in 
let l_pair   := {$ l_stakes With ( LocalState_ι_totalParticipantFunds_Л_pair , 
                                   ( eval_state ( ↓ RoundsBase_Ф_minRound ) l_stakes ) ) $} in 
let l' := exec_state ( ↓ DePoolContract_Ф_totalParticipantFunds_while Л_ingoreRoundId ) l_pair in 

exec_state ( ↓ DePoolContract_Ф_totalParticipantFunds Л_ingoreRoundId ) l = l' .
Proof.
  intros. destruct l. 
Abort. 

Lemma DePoolContract_Ф_totalParticipantFunds_eval : forall ( Л_ingoreRoundId : XInteger64 )
                                                           (l: Ledger) ,
let l_stakes := {$ l        With ( LocalState_ι_totalParticipantFunds_Л_stakes , 0 ) $} in 
let l_pair   := {$ l_stakes With ( LocalState_ι_totalParticipantFunds_Л_pair , 
                                   ( eval_state ( ↓ RoundsBase_Ф_minRound ) l_stakes ) ) $} in 
let l' := exec_state ( ↓ DePoolContract_Ф_totalParticipantFunds_while Л_ingoreRoundId ) l_pair in 

eval_state ( ↓ DePoolContract_Ф_totalParticipantFunds Л_ingoreRoundId ) l = 
          eval_state ( ↑17 ε  LocalState_ι_totalParticipantFunds_Л_stakes ) l' .
Proof.
  intros. destruct l. 
Abort. 



End DePoolContract_Ф_totalParticipantFunds.