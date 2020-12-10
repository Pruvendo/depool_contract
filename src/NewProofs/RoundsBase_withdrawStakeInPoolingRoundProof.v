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
Module RoundsBase_Ф_withdrawStakeInPoolingRound (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.

Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair Z.ltb Z.sub intMin deleteListPair intMax.
Opaque RoundsBase_Ф_stakeSum RoundsBase_Ф_setRound0.


Lemma RoundsBase_Ф_withdrawStakeInPoolingRound'_eval : forall (participant : DePoolLib_ι_Participant ) 
                                                              (participantAddress : XAddress)
                                                              (targetAmount : XInteger64)
                                                              (minStake : XInteger64) 
                                                              (l : Ledger) , 
    let oldRound0 := eval_state RoundsBase_Ф_getRound0 l in                                                          
    let optsv := (oldRound0 ->> RoundsBase_ι_Round_ι_stakes) ->fetch participantAddress in 
    let oldsv := maybeGet optsv in
    
    let targetAmount' := intMin targetAmount (oldsv ->> RoundsBase_ι_StakeValue_ι_ordinary)  in 
    let newOrd := (oldsv ->> RoundsBase_ι_StakeValue_ι_ordinary) - targetAmount' in
    let restLessThanMin := (newOrd <? minStake) in
    let newOrd' := if restLessThanMin then 0 else newOrd in
    let targetAmount'' := if restLessThanMin then targetAmount' + newOrd else targetAmount' in
    let newsv := {$ oldsv with RoundsBase_ι_StakeValue_ι_ordinary := newOrd' $} in

    let stakeSum := eval_state (↓ RoundsBase_Ф_stakeSum newsv) l in 
    let emptyStake := (stakeSum =? 0) in

    let newParticipantRoundQty := if emptyStake then ((participant ->> DePoolLib_ι_Participant_ι_roundQty) -1) else
                                                      (participant ->> DePoolLib_ι_Participant_ι_roundQty) in                                                  
 
    let newParticipant := {$ participant with DePoolLib_ι_Participant_ι_roundQty := newParticipantRoundQty $} in      
    
    eval_state (↓ RoundsBase_Ф_withdrawStakeInPoolingRound' participant participantAddress targetAmount minStake) l =
    if negb (isSome optsv) then Error (0, participant) 
                           else Value ( targetAmount'' , newParticipant ).                                             
Proof. 

  intros.
  destructLedger l. 
  compute.

  Time repeat destructIf_solve. idtac.

  all: try destructFunction1  RoundsBase_Ф_stakeSum ; auto. idtac.
  all: try match goal with
       | H: (?x =? 0) = _ |- _ => try rewrite H
       end. idtac.

  all: destruct participant.     
  all: time repeat destructIf_solve. 

Qed.

Opaque RoundsBase_Ф_transferStakeInOneRound'.

Lemma RoundsBase_Ф_withdrawStakeInPoolingRound_eval : forall (participant : DePoolLib_ι_Participant ) 
                                                              (participantAddress : XAddress)
                                                              (targetAmount : XInteger64)
                                                              (minStake : XInteger64) 
                                                              (l : Ledger) , 
    let oldRound0 := eval_state RoundsBase_Ф_getRound0 l in                                                          
    let optsv := (oldRound0 ->> RoundsBase_ι_Round_ι_stakes) ->fetch participantAddress in 
    let oldsv := maybeGet optsv in
    
    let targetAmount' := intMin targetAmount (oldsv ->> RoundsBase_ι_StakeValue_ι_ordinary)  in 
    let newOrd := (oldsv ->> RoundsBase_ι_StakeValue_ι_ordinary) - targetAmount' in
    let restLessThanMin := (newOrd <? minStake) in
    let newOrd' := if restLessThanMin then 0 else newOrd in
    let targetAmount'' := if restLessThanMin then targetAmount' + newOrd else targetAmount' in
    let newsv := {$ oldsv with RoundsBase_ι_StakeValue_ι_ordinary := newOrd' $} in

    let stakeSum := eval_state (↓ RoundsBase_Ф_stakeSum newsv) l in 
    let emptyStake := (stakeSum =? 0) in

    let newParticipantRoundQty := if emptyStake then ((participant ->> DePoolLib_ι_Participant_ι_roundQty) -1) else
                                                      (participant ->> DePoolLib_ι_Participant_ι_roundQty) in                                                  
 
    let newParticipant := {$ participant with DePoolLib_ι_Participant_ι_roundQty := newParticipantRoundQty $} in      
    
    eval_state (↓ RoundsBase_Ф_withdrawStakeInPoolingRound participant participantAddress targetAmount minStake) l =
    if negb (isSome optsv) then  (0, participant) 
                           else  ( targetAmount'' , newParticipant ). 
Proof.
  intros.

  assert (eval_state (↓ RoundsBase_Ф_withdrawStakeInPoolingRound participant participantAddress targetAmount minStake ) l = 
          fromValueValue (eval_state (↓ RoundsBase_Ф_withdrawStakeInPoolingRound' participant participantAddress targetAmount minStake) l)).
  unfold RoundsBase_Ф_withdrawStakeInPoolingRound.
  unfold callEmbeddedStateAdj.
  remember (RoundsBase_Ф_withdrawStakeInPoolingRound' participant participantAddress targetAmount minStake).
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
  rewrite RoundsBase_Ф_withdrawStakeInPoolingRound'_eval.
  repeat rewrite if_fromValueValue; auto.
Qed.


Transparent RoundsBase_Ф_transferStakeInOneRound'.
Opaque RoundsBase_Ф_setRound0.  

Lemma RoundsBase_Ф_withdrawStakeInPoolingRound_exec : forall (participant : DePoolLib_ι_Participant ) 
                                                              (participantAddress : XAddress)
                                                              (targetAmount : XInteger64)
                                                              (minStake : XInteger64) 
                                                              (l : Ledger) , 
    let roundQty := eval_state (↑11 ε RoundsBase_ι_m_roundQty) l in 
    let oldRound0 := eval_state RoundsBase_Ф_getRound0 l in

    let optsv := (oldRound0 ->> RoundsBase_ι_Round_ι_stakes) ->fetch participantAddress in 
    let oldsv := maybeGet optsv in
    
    let targetAmount' := intMin targetAmount (oldsv ->> RoundsBase_ι_StakeValue_ι_ordinary)  in 
    let newOrd := (oldsv ->> RoundsBase_ι_StakeValue_ι_ordinary) - targetAmount' in
    let restLessThanMin := (newOrd <? minStake) in
    let newOrd' := if restLessThanMin then 0 else newOrd in
    let targetAmount'' := if restLessThanMin then targetAmount' + newOrd else targetAmount' in
    let newsv := {$ oldsv with RoundsBase_ι_StakeValue_ι_ordinary := newOrd' $} in

    let (stakeSum , l_sum) := run (↓ RoundsBase_Ф_stakeSum newsv) l in 

    let emptyStake := (stakeSum =? 0) in
    let newRoundParticipantQty := if emptyStake then ((oldRound0 ->> RoundsBase_ι_Round_ι_participantQty) -1) else
                                                      (oldRound0 ->> RoundsBase_ι_Round_ι_participantQty) in
                                
    let newRoundStake := (oldRound0 ->> RoundsBase_ι_Round_ι_stake) - targetAmount' in                                      
    let newRoundStake := if restLessThanMin then newRoundStake - newOrd else newRoundStake  in
    let newRoundStakes := if emptyStake then (oldRound0 ->> RoundsBase_ι_Round_ι_stakes) ->delete participantAddress else
                                             (oldRound0 ->> RoundsBase_ι_Round_ι_stakes) [participantAddress] ← newsv in

    let newRound0 :=  {$ oldRound0 with (RoundsBase_ι_Round_ι_participantQty, newRoundParticipantQty) ;
                                        (RoundsBase_ι_Round_ι_stake, newRoundStake) ; 
                                        (RoundsBase_ι_Round_ι_stakes, newRoundStakes) $}  in                                               
    let l_set := exec_state (↓ RoundsBase_Ф_setRound0 newRound0) l_sum in

exec_state (↓ RoundsBase_Ф_withdrawStakeInPoolingRound participant participantAddress targetAmount minStake) l = 
    if negb (isSome optsv) then l else l_set.
Proof. 

  intros.
  destructLedger l. 
  compute.

  Time repeat destructIf_solve.

  all: try destructFunction1  RoundsBase_Ф_stakeSum ; auto. idtac.
  all: try match goal with
       | H: (?x =? 0) = _ |- _ => try rewrite H
       end. idtac.

  all: time repeat destructIf_solve. idtac.   
  
  rewrite H in H1. discriminate. idtac.
  rewrite H in H1. discriminate. idtac.
  rewrite H in H1. discriminate. idtac.
  rewrite H in H1. discriminate. 
Qed.  

End RoundsBase_Ф_withdrawStakeInPoolingRound.