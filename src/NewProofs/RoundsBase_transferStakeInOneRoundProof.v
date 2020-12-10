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
Module RoundsBase_Ф_transferStakeInOneRound (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.


Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair Z.ltb Z.sub intMin deleteListPair intMax.

Opaque RoundsBase_Ф_stakeSum.


Lemma RoundsBase_Ф_transferStakeInOneRound'_eval : forall ( Л_round : RoundsBase_ι_Round ) 
                                                   ( Л_sourceParticipant : DePoolLib_ι_Participant ) 
                                                   ( Л_destinationParticipant : DePoolLib_ι_Participant ) 
                                                   ( Л_source : XAddress ) 
                                                   ( Л_destination : XAddress ) 
                                                   ( Л_amount : XInteger64 ) 
                                                   ( Л_minStake : XInteger64 ) 
                                                   (l: Ledger) ,
let optSourceStake :=  ( Л_round ->> RoundsBase_ι_Round_ι_stakes ) ->fetch Л_source in
let optSourceStake_hasValue := isSome optSourceStake in 
let round := Л_round in 
let sourceParticipant := Л_sourceParticipant in
let destinationParticipant := Л_destinationParticipant in 
let source := Л_source in
let destination := Л_destination in
let amount := Л_amount in
let minStake := Л_minStake in             
  
let sourceStake := maybeGet optSourceStake in

let round_stakes := round ->> RoundsBase_ι_Round_ι_stakes in
let prevSource_source := round_stakes [ source ] in
let prevSourceStake := prevSource_source ->> RoundsBase_ι_StakeValue_ι_ordinary in
let newSourceStake := if ( ( sourceStake ->> RoundsBase_ι_StakeValue_ι_ordinary ) >=? amount ) then ( sourceStake ->> RoundsBase_ι_StakeValue_ι_ordinary ) - amount 
                                                                                               else 0 in
let deltaDestinationStake := if ( ( sourceStake ->> RoundsBase_ι_StakeValue_ι_ordinary ) >=? amount ) then amount 
                                                                                                      else sourceStake ->> RoundsBase_ι_StakeValue_ι_ordinary in                            
let newDestStake := ( ( ( round ->> RoundsBase_ι_Round_ι_stakes ) [ destination ] ) ->> RoundsBase_ι_StakeValue_ι_ordinary ) + deltaDestinationStake  in
let bReturn2 := ((0 <? newSourceStake) && (newSourceStake <? Л_minStake) || (0 <? newDestStake) && (newDestStake <? minStake))%bool in    
let sourceStake := {$ sourceStake with ( RoundsBase_ι_StakeValue_ι_ordinary , newSourceStake ) $} in
let round_participantQty := round ->> RoundsBase_ι_Round_ι_participantQty in

let stakeSum := eval_state ( ↓ RoundsBase_Ф_stakeSum sourceStake ) l in
let sumZero :=  stakeSum =? 0 in
let round := {$ round with 
             ( RoundsBase_ι_Round_ι_participantQty , 
                      if sumZero then round_participantQty - 1
                                 else round_participantQty ) ;
             ( RoundsBase_ι_Round_ι_stakes , if sumZero then round_stakes ->delete source
                                                        else round_stakes [ source ] ←  sourceStake ) $} in
let sourceParticipant_roundQty := sourceParticipant ->> DePoolLib_ι_Participant_ι_roundQty in
let sourceParticipant := {$ sourceParticipant with ( DePoolLib_ι_Participant_ι_roundQty , 
                              if sumZero then sourceParticipant_roundQty - 1
                                         else sourceParticipant_roundQty ) $} in
              
let round_stakes := round ->> RoundsBase_ι_Round_ι_stakes in
let round_stakes_destination := round_stakes [ destination ] in
let round_stakes_destination_ordinary := ( round_stakes_destination ->> RoundsBase_ι_StakeValue_ι_ordinary ) + deltaDestinationStake in
let round_participantQty := round ->> RoundsBase_ι_Round_ι_participantQty in
let round_stakes_exists_destination := isSome (hmapLookup Z.eqb destination round_stakes) in

let round := {$ round with 
             ( RoundsBase_ι_Round_ι_participantQty , if negb round_stakes_exists_destination
                                                     then round_participantQty + 1
                                                     else round_participantQty ) ;
             ( RoundsBase_ι_Round_ι_stakes , round_stakes [ destination ] ←  {$ round_stakes_destination with 
                            RoundsBase_ι_StakeValue_ι_ordinary := round_stakes_destination_ordinary $} ) $} in

let destinationParticipant_roundQty := destinationParticipant ->> DePoolLib_ι_Participant_ι_roundQty in
let destinationParticipant := {$ destinationParticipant with ( DePoolLib_ι_Participant_ι_roundQty , 
                                                     if negb round_stakes_exists_destination
                                                     then destinationParticipant_roundQty + 1
                                                     else destinationParticipant_roundQty ) $} in

eval_state (↓ (RoundsBase_Ф_transferStakeInOneRound' Л_round Л_sourceParticipant Л_destinationParticipant Л_source Л_destination Л_amount  Л_minStake ) ) l =

if negb ( optSourceStake_hasValue ) then Error ( Л_round , 0 , 0 , Л_sourceParticipant , Л_destinationParticipant ) 
        else if bReturn2 then Error (Л_round, 0, prevSourceStake, Л_sourceParticipant, Л_destinationParticipant) 
                         else Value (round, deltaDestinationStake, prevSourceStake, sourceParticipant, destinationParticipant ).
Proof.  
    intros.
    destructLedger l. 
    compute.

    enough (forall X Y (a b: X), a = b -> Value (B:=Y) a = Value b) as H100.

    Time repeat destructIf_solve.

    all: try destructFunction1  RoundsBase_Ф_stakeSum ; auto. idtac.
    all: try match goal with
         | H: (?x =? 0) = _ |- _ => try rewrite H
         end. idtac.

    all: try destruct Л_round; try destruct Л_destinationParticipant; try destruct Л_sourceParticipant.
    all: time repeat destructIf_solve. idtac.

    rewrite H3 in H2. rewrite H2 in H4. discriminate. idtac.
    rewrite H3 in H2. rewrite H2 in H4. discriminate. idtac.
    rewrite H3 in H2. rewrite H2 in H4. discriminate. idtac.
    rewrite H3 in H2. rewrite H2 in H4. discriminate. idtac.
    rewrite H3 in H2. rewrite H2 in H4. discriminate. idtac.
    rewrite H3 in H2. rewrite H2 in H4. discriminate. idtac.
    rewrite H3 in H2. rewrite H2 in H4. discriminate. idtac.
    rewrite H3 in H2. rewrite H2 in H4. discriminate. idtac.

  intros. congruence.
 
 Qed.  

Lemma RoundsBase_Ф_transferStakeInOneRound_eval : forall ( Л_round : RoundsBase_ι_Round ) 
                                                   ( Л_sourceParticipant : DePoolLib_ι_Participant ) 
                                                   ( Л_destinationParticipant : DePoolLib_ι_Participant ) 
                                                   ( Л_source : XAddress ) 
                                                   ( Л_destination : XAddress ) 
                                                   ( Л_amount : XInteger64 ) 
                                                   ( Л_minStake : XInteger64 ) 
                                                   (l: Ledger) ,
let optSourceStake :=  ( Л_round ->> RoundsBase_ι_Round_ι_stakes ) ->fetch Л_source in
let optSourceStake_hasValue := isSome optSourceStake in 
let round := Л_round in 
let sourceParticipant := Л_sourceParticipant in
let destinationParticipant := Л_destinationParticipant in 
let source := Л_source in
let destination := Л_destination in
let amount := Л_amount in
let minStake := Л_minStake in             
  
let sourceStake := maybeGet optSourceStake in

let round_stakes := round ->> RoundsBase_ι_Round_ι_stakes in
let prevSource_source := round_stakes [ source ] in
let prevSourceStake := prevSource_source ->> RoundsBase_ι_StakeValue_ι_ordinary in
let newSourceStake := if ( ( sourceStake ->> RoundsBase_ι_StakeValue_ι_ordinary ) >=? amount ) then ( sourceStake ->> RoundsBase_ι_StakeValue_ι_ordinary ) - amount 
                                                                                               else 0 in
let deltaDestinationStake := if ( ( sourceStake ->> RoundsBase_ι_StakeValue_ι_ordinary ) >=? amount ) then amount 
                                                                                                      else sourceStake ->> RoundsBase_ι_StakeValue_ι_ordinary in                            
let newDestStake := ( ( ( round ->> RoundsBase_ι_Round_ι_stakes ) [ destination ] ) ->> RoundsBase_ι_StakeValue_ι_ordinary ) + deltaDestinationStake  in
let bReturn2 := ((0 <? newSourceStake) && (newSourceStake <? Л_minStake) || (0 <? newDestStake) && (newDestStake <? minStake))%bool in    
let sourceStake := {$ sourceStake with ( RoundsBase_ι_StakeValue_ι_ordinary , newSourceStake ) $} in
let round_participantQty := round ->> RoundsBase_ι_Round_ι_participantQty in

let stakeSum := eval_state ( ↓ RoundsBase_Ф_stakeSum sourceStake ) l in
let sumZero :=  stakeSum =? 0 in
let round := {$ round with 
             ( RoundsBase_ι_Round_ι_participantQty , 
                      if sumZero then round_participantQty - 1
                                 else round_participantQty ) ;
             ( RoundsBase_ι_Round_ι_stakes , if sumZero then round_stakes ->delete source
                                                        else round_stakes [ source ] ←  sourceStake ) $} in
let sourceParticipant_roundQty := sourceParticipant ->> DePoolLib_ι_Participant_ι_roundQty in
let sourceParticipant := {$ sourceParticipant with ( DePoolLib_ι_Participant_ι_roundQty , 
                              if sumZero then sourceParticipant_roundQty - 1
                                         else sourceParticipant_roundQty ) $} in
              
let round_stakes := round ->> RoundsBase_ι_Round_ι_stakes in
let round_stakes_destination := round_stakes [ destination ] in
let round_stakes_destination_ordinary := ( round_stakes_destination ->> RoundsBase_ι_StakeValue_ι_ordinary ) + deltaDestinationStake in
let round_participantQty := round ->> RoundsBase_ι_Round_ι_participantQty in
let round_stakes_exists_destination := isSome (hmapLookup Z.eqb destination round_stakes) in

let round := {$ round with 
             ( RoundsBase_ι_Round_ι_participantQty , if negb round_stakes_exists_destination
                                                     then round_participantQty + 1
                                                     else round_participantQty ) ;
             ( RoundsBase_ι_Round_ι_stakes , round_stakes [ destination ] ←  {$ round_stakes_destination with 
                            RoundsBase_ι_StakeValue_ι_ordinary := round_stakes_destination_ordinary $} ) $} in

let destinationParticipant_roundQty := destinationParticipant ->> DePoolLib_ι_Participant_ι_roundQty in
let destinationParticipant := {$ destinationParticipant with ( DePoolLib_ι_Participant_ι_roundQty , 
                                                     if negb round_stakes_exists_destination
                                                     then destinationParticipant_roundQty + 1
                                                     else destinationParticipant_roundQty ) $} in

eval_state (↓ RoundsBase_Ф_transferStakeInOneRound Л_round Л_sourceParticipant Л_destinationParticipant Л_source Л_destination Л_amount  Л_minStake  ) l =

if negb ( optSourceStake_hasValue ) then  ( Л_round , 0 , 0 , Л_sourceParticipant , Л_destinationParticipant ) 
        else if bReturn2 then  (Л_round, 0, prevSourceStake, Л_sourceParticipant, Л_destinationParticipant) 
                         else  (round, deltaDestinationStake, prevSourceStake, sourceParticipant, destinationParticipant ).

 Proof.
  intros.

  assert (eval_state (↓ RoundsBase_Ф_transferStakeInOneRound Л_round Л_sourceParticipant Л_destinationParticipant Л_source Л_destination Л_amount  Л_minStake ) l = 
          fromValueValue (eval_state (↓ RoundsBase_Ф_transferStakeInOneRound' Л_round Л_sourceParticipant Л_destinationParticipant Л_source Л_destination Л_amount  Л_minStake) l)).
  unfold RoundsBase_Ф_transferStakeInOneRound.
  unfold callEmbeddedStateAdj.
  remember (RoundsBase_Ф_transferStakeInOneRound' Л_round Л_sourceParticipant Л_destinationParticipant Л_source Л_destination Л_amount  Л_minStake).
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
  rewrite RoundsBase_Ф_transferStakeInOneRound'_eval.
  repeat rewrite if_fromValueValue; auto.
Qed.

Lemma RoundsBase_Ф_transferStakeInOneRound_exec : forall ( Л_round : RoundsBase_ι_Round ) 
                                                         ( Л_sourceParticipant : DePoolLib_ι_Participant ) 
                                                         ( Л_destinationParticipant : DePoolLib_ι_Participant ) 
                                                         ( Л_source : XAddress ) 
                                                         ( Л_destination : XAddress ) 
                                                         ( Л_amount : XInteger64 ) 
                                                         ( Л_minStake : XInteger64 ) 
                                                         ( l: Ledger ) , 
let optSourceStake :=  ( Л_round ->> RoundsBase_ι_Round_ι_stakes ) ->fetch Л_source in
let optSourceStake_hasValue := isSome optSourceStake in 
let round := Л_round in 
let sourceParticipant := Л_sourceParticipant in
let destinationParticipant := Л_destinationParticipant in 
let source := Л_source in
let destination := Л_destination in
let amount := Л_amount in
let minStake := Л_minStake in             
  
let sourceStake := maybeGet optSourceStake in

let round_stakes := round ->> RoundsBase_ι_Round_ι_stakes in
let prevSource_source := round_stakes [ source ] in
let prevSourceStake := prevSource_source ->> RoundsBase_ι_StakeValue_ι_ordinary in
let newSourceStake := if ( ( sourceStake ->> RoundsBase_ι_StakeValue_ι_ordinary ) >=? amount ) then ( sourceStake ->> RoundsBase_ι_StakeValue_ι_ordinary ) - amount 
                                                                                               else 0 in
let deltaDestinationStake := if ( ( sourceStake ->> RoundsBase_ι_StakeValue_ι_ordinary ) >=? amount ) then amount 
                                                                                                      else sourceStake ->> RoundsBase_ι_StakeValue_ι_ordinary in                            
let newDestStake := ( ( ( round ->> RoundsBase_ι_Round_ι_stakes ) [ destination ] ) ->> RoundsBase_ι_StakeValue_ι_ordinary ) + deltaDestinationStake  in
let bReturn2 := ((0 <? newSourceStake) && (newSourceStake <? Л_minStake) || (0 <? newDestStake) && (newDestStake <? minStake))%bool in    
let sourceStake := {$ sourceStake with ( RoundsBase_ι_StakeValue_ι_ordinary , newSourceStake ) $} in

let l_sum := exec_state ( ↓ RoundsBase_Ф_stakeSum sourceStake ) l in

    exec_state (↓ RoundsBase_Ф_transferStakeInOneRound Л_round Л_sourceParticipant Л_destinationParticipant Л_source Л_destination Л_amount Л_minStake ) l = 
    if negb ( optSourceStake_hasValue ) then l
        else if bReturn2 then l else l_sum.  
Proof. 
  intros.
  destructLedger l. 
  compute.
  Time repeat destructIf_solve.
  destructFunction1  RoundsBase_Ф_stakeSum ; auto. idtac.
  Time repeat destructIf_solve. idtac.
  destructFunction1  RoundsBase_Ф_stakeSum ; auto. idtac.
  Time repeat destructIf_solve. 
Qed. 

 
End RoundsBase_Ф_transferStakeInOneRound.