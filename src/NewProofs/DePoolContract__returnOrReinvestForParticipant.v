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
Module DePoolContract_Ф__returnOrReinvestForParticipant (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.


(* Lemma ifSimpleState: forall X (b: bool) (f g: Ledger -> X * Ledger), 
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

Ltac remDestructIf :=
  match goal with
    | |- ?x =>
      match x with
        | context [if ?b then _ else _] => case_eq b ; intros
        | _ => idtac
      end
  end.
 *)


Ltac pr_numgoals := let n := numgoals in idtac "There are" n "goals".

Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair Z.ltb Z.sub intMin deleteListPair intMax.

Opaque RoundsBase_Ф__addStakes DePoolContract_Ф_cutWithdrawalValue RoundsBase_Ф_stakeSum.

Definition DePoolContract_Ф__returnOrReinvestForParticipant' ( Л_round2 : RoundsBase_ι_Round )
                                                             ( Л_round0 : RoundsBase_ι_Round )
                                                             ( Л_addr : XAddress )
                                                             ( Л_stakes : RoundsBase_ι_StakeValue ) 
                                                             ( Л_isValidator : XBool )
                                                             ( Л_round1ValidatorsElectedFor : XInteger32 )
                                                             ( f : XBool -> XBool ->  RoundsBase_ι_StakeValue -> XInteger -> XAddress -> XInteger32 -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) )
                                                  : LedgerT ( XErrorValue ( RoundsBase_ι_Round # RoundsBase_ι_Round ) XInteger ) := 
(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round2 := $ Л_round2) >> 
(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round0 := $ Л_round0) >>
U0! Л_stakeSum := RoundsBase_Ф_stakeSum (! $ Л_stakes !) ;
U0! Л_stakeIsLost := ($ (Л_round2 ->> RoundsBase_ι_Round_ι_completionReason) ) ?== ($ RoundsBase_ι_CompletionReasonP_ι_ValidatorIsPunished) ; 		
U0! Л_optParticipant := ParticipantBase_Ф_fetchParticipant (! $ Л_addr !) ; 
Require {{ $ Л_optParticipant ->hasValue , $ InternalErrors_ι_ERROR511 }} ; 

(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_participant := $ Л_optParticipant ->get) >> 
(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_participant ^^ DePoolLib_ι_Participant_ι_roundQty !--) >>

( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds := $ Л_stakeIsLost ? 
   ( D1! (D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2) ^^ RoundsBase_ι_Round_ι_stake !- 
     D1! (D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2) ^^ RoundsBase_ι_Round_ι_unused ) !- 
     D1! (D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2) ^^ RoundsBase_ι_Round_ι_recoveredStake 
                              ::: $ xInt0 )  >> f Л_stakeIsLost Л_isValidator Л_stakes Л_stakeSum Л_addr Л_round1ValidatorsElectedFor. 

Lemma DePoolContract_Ф__returnOrReinvestForParticipant'_exec : forall
                                                                (l : Ledger)
                                                                ( Л_round2 : RoundsBase_ι_Round )
                                                                ( Л_round0 : RoundsBase_ι_Round )
                                                                ( Л_addr : XAddress )
                                                                ( Л_stakes : RoundsBase_ι_StakeValue ) 
                                                                ( Л_isValidator : XBool ) 
                                                                ( Л_round1ValidatorsElectedFor : XInteger32 )
                                                                ( f : XBool -> XBool ->  RoundsBase_ι_StakeValue -> XInteger -> XAddress -> XInteger32 -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) ),
let (stakeSum, l_sum) := run (↓ RoundsBase_Ф_stakeSum Л_stakes) l in
let stakeIsLost : bool := eqb (Л_round2 ->> RoundsBase_ι_Round_ι_completionReason) RoundsBase_ι_CompletionReasonP_ι_ValidatorIsPunished in
let optParticipant := eval_state (↓ ParticipantBase_Ф_fetchParticipant Л_addr) l_sum in
let isSomeParticipant : bool := isSome optParticipant in
let participant := maybeGet optParticipant in 
let participant_newRoundQty :=
    {$ participant with (DePoolLib_ι_Participant_ι_roundQty, (participant ->> DePoolLib_ι_Participant_ι_roundQty) - 1 ) $} in 
let lostFunds := if stakeIsLost
    then    (Л_round2 ->> RoundsBase_ι_Round_ι_stake  -
              Л_round2 ->> RoundsBase_ι_Round_ι_unused)  -
              Л_round2 ->> RoundsBase_ι_Round_ι_recoveredStake
    else 0 in 
let l_local := {$ l_sum With (LocalState_ι__returnOrReinvestForParticipant_Л_round2, Л_round2);
                              (LocalState_ι__returnOrReinvestForParticipant_Л_round0, Л_round0);
                              (LocalState_ι__returnOrReinvestForParticipant_Л_participant, participant_newRoundQty);
                              (LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds, lostFunds) $} in

exec_state (DePoolContract_Ф__returnOrReinvestForParticipant' Л_round2 Л_round0 Л_addr Л_stakes Л_isValidator Л_round1ValidatorsElectedFor f) l =
    if  isSomeParticipant then                             
        exec_state (f stakeIsLost Л_isValidator Л_stakes stakeSum Л_addr Л_round1ValidatorsElectedFor) l_local
        else {$ l_sum With (LocalState_ι__returnOrReinvestForParticipant_Л_round2, Л_round2);
                           (LocalState_ι__returnOrReinvestForParticipant_Л_round0, Л_round0) $}.
Proof.

  intros.
  destructLedger l. 
  compute.

  Time repeat destructIf_solve.

  all: try destructFunction1  RoundsBase_Ф_stakeSum ; auto. idtac.
  all: time repeat destructIf_solve. idtac.  
  all: try destructFunction5 f ; auto.
Qed.  

Definition DePoolContract_Ф__returnOrReinvestForParticipant_tailer1 ( Л_stakeIsLost: XBool ) 
                                                                    ( Л_isValidator : XBool )
                                                                    ( Л_stakes : RoundsBase_ι_StakeValue ) 
                                                                    ( Л_stakeSum: XInteger )
                                                                    ( Л_addr : XAddress )
                                                                    ( Л_round1ValidatorsElectedFor : XInteger32 )
                                                                    ( f : RoundsBase_ι_StakeValue -> XBool -> XBool -> XAddress -> XInteger32 -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) )
                                                  : LedgerT ( RoundsBase_ι_Round # RoundsBase_ι_Round ) :=  
(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake := $default) >>
(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_reward := $default) >>

(
	If ($ Л_stakeIsLost) then {
   ( If ( $ Л_isValidator ) 
     then {
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake := $ ( Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary ) ) >>  
           U0! Л_delta := math->min2 (! ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake ,
                                         ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds !) ; 
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake !-= $ Л_delta ) >>  
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds !-= $ Л_delta ) >> 
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ^^ RoundsBase_ι_Round_ι_validatorRemainingStake
                       := D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake )
     } 
     else {
		(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake := math->muldiv (! 
                D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_unused !+
                D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_recoveredStake !-
                D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_validatorRemainingStake, 
				$ Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary , 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_stake !-
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_validatorStake !))
} )
	} else {
    (↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_reward := math->muldiv (! $ Л_stakeSum , 
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_rewards ,
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_stake !) ) >>
		(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_participant ^^ DePoolLib_ι_Participant_ι_reward 
                           !+=  D2! LocalState_ι__returnOrReinvestForParticipant_Л_reward ) >>
		(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake := $ ( Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary ) !+ 
                                                                            (D2! LocalState_ι__returnOrReinvestForParticipant_Л_reward))
	}
) >> 
( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ^^ RoundsBase_ι_Round_ι_handledStakesAndRewards !+= D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake ) >> 
  f Л_stakes Л_stakeIsLost Л_isValidator Л_addr Л_round1ValidatorsElectedFor.


Lemma DePoolContract_Ф__returnOrReinvestForParticipant_tailer1_exec : forall
                                                            ( l : Ledger )
                                                            ( Л_stakeIsLost: XBool ) 
                                                            ( Л_isValidator : XBool )
                                                            ( Л_stakes : RoundsBase_ι_StakeValue ) 
                                                            ( Л_stakeSum: XInteger)
                                                            ( Л_addr : XAddress)
                                                            ( Л_round1ValidatorsElectedFor : XInteger32 )
                                                            ( f : RoundsBase_ι_StakeValue -> XBool -> XBool -> XAddress -> XInteger32 -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) ),

let newStake := 0 in
let reward := 0 in
let lostFunds := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds) l in
let round2 :=  eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_round2) l in
let participant := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_participant) l in
let delta := intMin ( Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary) lostFunds in
let newStake := if Л_stakeIsLost then 
                    if Л_isValidator then 
                        Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary - delta
                                     else (round2 ->> RoundsBase_ι_Round_ι_unused + 
                                           round2 ->> RoundsBase_ι_Round_ι_recoveredStake - 
                                           round2 ->> RoundsBase_ι_Round_ι_validatorRemainingStake) *  
                                           (Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary) /
                                           (round2 ->> RoundsBase_ι_Round_ι_stake - round2 ->> RoundsBase_ι_Round_ι_validatorStake) 
                                 else Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary + 
                                 Л_stakeSum * (round2 ->> RoundsBase_ι_Round_ι_rewards) / (round2 ->> RoundsBase_ι_Round_ι_stake)  in
let lostFunds :=   if Л_stakeIsLost then 
                        if Л_isValidator then lostFunds - delta else lostFunds 
                                     else lostFunds in
let reward :=  if Л_stakeIsLost then reward
                                 else Л_stakeSum *  (round2 ->> RoundsBase_ι_Round_ι_rewards) / (round2 ->> RoundsBase_ι_Round_ι_stake) in 
let round2 :=  if Л_stakeIsLost then 
                        if Л_isValidator then  {$ round2 with RoundsBase_ι_Round_ι_validatorRemainingStake := newStake $}     
                                         else round2 
                                     else round2 in   
let participant := if Л_stakeIsLost then participant
                                    else {$ participant with DePoolLib_ι_Participant_ι_reward := participant ->> DePoolLib_ι_Participant_ι_reward + reward $} in 
let round2 := {$round2 with RoundsBase_ι_Round_ι_handledStakesAndRewards :=  round2 ->> RoundsBase_ι_Round_ι_handledStakesAndRewards + newStake$} in

 exec_state (DePoolContract_Ф__returnOrReinvestForParticipant_tailer1 Л_stakeIsLost Л_isValidator Л_stakes Л_stakeSum Л_addr Л_round1ValidatorsElectedFor f) l =
 exec_state (f Л_stakes Л_stakeIsLost Л_isValidator Л_addr Л_round1ValidatorsElectedFor) {$ l With (LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds, lostFunds);
                                                                      (LocalState_ι__returnOrReinvestForParticipant_Л_round2, round2);
                                                                      (LocalState_ι__returnOrReinvestForParticipant_Л_participant, participant);
                                                                      (LocalState_ι__returnOrReinvestForParticipant_Л_newStake, newStake);
                                                                      (LocalState_ι__returnOrReinvestForParticipant_Л_reward, reward) $}.
Proof.

  intros.
  destructLedger l. 
  compute.

  Time repeat destructIf_solve.

Qed.

Definition DePoolContract_Ф__returnOrReinvestForParticipant_tailer2 ( Л_stakes : RoundsBase_ι_StakeValue ) 
                                                                    ( Л_stakeIsLost : XBool )  
                                                                    ( Л_isValidator : XBool ) 
                                                                    ( Л_addr : XAddress)
                                                                    ( Л_round1ValidatorsElectedFor : XInteger32 )
                                                                    ( f: RoundsBase_ι_StakeValue -> XBool -> XBool -> XAddress -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) )
                                                            : LedgerT ( RoundsBase_ι_Round # RoundsBase_ι_Round ) :=  
(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting := $ ( Л_stakes ->> RoundsBase_ι_StakeValue_ι_vesting ) ) >> 
( If ( ( ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting ) ->hasValue ) 
then
{ 
  (↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_params := 
             ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting ) ->get )  >> 

 ( If ($ Л_stakeIsLost) then { 
   ( If ( $ Л_isValidator ) 
     then {
           U0! Л_delta := math->min2 (! ↑17 D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params ) ^^ 
                                             RoundsBase_ι_InvestParams_ι_remainingAmount ,
                                         ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds !) ; 
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_params ^^ 
                                             RoundsBase_ι_InvestParams_ι_remainingAmount !-= $ Л_delta ) >>  
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds !-= $ Л_delta ) >> 
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ^^ RoundsBase_ι_Round_ι_validatorRemainingStake
                       !+= D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params )
                                            ^^ RoundsBase_ι_InvestParams_ι_remainingAmount )
     } (*+*)
     else {
		( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_params ^^ 
                                             RoundsBase_ι_InvestParams_ι_remainingAmount := math->muldiv (! 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_unused !+
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_recoveredStake !-
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_validatorRemainingStake
              , 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params )
                                            ^^ RoundsBase_ι_InvestParams_ι_remainingAmount , 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_stake !-
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_validatorStake !) )
} ) 
	} ) (*+*) >>
                       (* round2.handledStakesAndRewards += params.remainingAmount; *)
  ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ^^ RoundsBase_ι_Round_ι_handledStakesAndRewards  !+=
    D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params ) ^^ RoundsBase_ι_InvestParams_ι_remainingAmount ) 
>> (* + *)  
  U0! Л_withdrawalVesting := $ default ;

                       (*  (newVesting, withdrawalVesting, tonsForOwner) = cutWithdrawalValue(
                                params,
                                isValidator && round2.completionReason != CompletionReason.RewardIsReceived,
                                round1ValidatorsElectedFor + round2.validatorsElectedFor
            ); *)
  U0! {( Л_newVesting , Л_withdrawalVesting , Л_tonsForOwner )} := DePoolContract_Ф_cutWithdrawalValue (!
                               ( ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_params ) ,
                                 $ Л_isValidator !&  ( D1! ( ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) 
                                                       ^^ RoundsBase_ι_Round_ι_completionReason ) ?!=
                                                       $ RoundsBase_ι_CompletionReasonP_ι_RewardIsReceived ,
                                                     ( $ Л_round1ValidatorsElectedFor !+
                                                     ( D1! ( ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^
                                                             RoundsBase_ι_Round_ι_validatorsElectedFor  ) ) 
                                                      !) ;         

  ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting := $ Л_newVesting ) >>
  ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake !+= $ Л_withdrawalVesting ) >>
           (*  if (tonsForOwner > 0)
                newVesting.get().owner.transfer(tonsForOwner, false, 1); *)
 ( If ( $ Л_tonsForOwner ?> $ xInt0 )
   then {
	(D1! ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting) ->get) ^^ RoundsBase_ι_InvestParams_ι_owner ) ->transfer 
            (! $ Л_tonsForOwner , $ xBoolFalse, $ xInt1 !)
        } ) 
} ) >> f Л_stakes Л_stakeIsLost Л_isValidator Л_addr.

Lemma DePoolContract_Ф__returnOrReinvestForParticipant_tailer2_exec : forall
                                                            ( l : Ledger)
                                                            ( Л_stakes : RoundsBase_ι_StakeValue ) 
                                                            ( Л_stakeIsLost : XBool )  
                                                            ( Л_isValidator : XBool ) 
                                                            ( Л_addr : XAddress )
                                                            ( Л_round1ValidatorsElectedFor : XInteger32 )
                                                            ( f: RoundsBase_ι_StakeValue -> XBool -> XBool -> XAddress -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) ),
let lostFunds := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds) l in
let round2 := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_round2) l in
let newStake := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_newStake) l in

let optNewVesting := Л_stakes ->> RoundsBase_ι_StakeValue_ι_vesting in
let isNewVesting := isSome optNewVesting in
let params := maybeGet optNewVesting in
let oldVestingAmount := params ->> RoundsBase_ι_InvestParams_ι_remainingAmount in
let oldVestingValidatorRemainingStake := round2 ->> RoundsBase_ι_Round_ι_validatorRemainingStake  in
let deltaVestingValidator := intMin oldVestingAmount lostFunds in
let amount := if Л_stakeIsLost then
                  if Л_isValidator then oldVestingAmount - deltaVestingValidator
                                   else (round2 ->> RoundsBase_ι_Round_ι_unused + round2 ->> RoundsBase_ι_Round_ι_recoveredStake - round2 ->> RoundsBase_ι_Round_ι_validatorRemainingStake) *
                                        (params ->> RoundsBase_ι_InvestParams_ι_remainingAmount) / (round2 ->> RoundsBase_ι_Round_ι_stake - round2 ->> RoundsBase_ι_Round_ι_validatorStake) 
                                  else oldVestingAmount in
let lostFunds := if Л_stakeIsLost then 
                      if Л_isValidator then lostFunds - deltaVestingValidator 
                                       else lostFunds 
                                    else lostFunds in 
let validatorRemainingStake := if Л_stakeIsLost then 
                      if Л_isValidator then oldVestingValidatorRemainingStake + amount
                                       else oldVestingValidatorRemainingStake 
                                    else oldVestingValidatorRemainingStake in 
let params := {$ params with RoundsBase_ι_InvestParams_ι_remainingAmount := amount $} in
let bPunish := (Л_isValidator && negb (eqb round2 ->> RoundsBase_ι_Round_ι_completionReason RoundsBase_ι_CompletionReasonP_ι_RewardIsReceived))%bool in
let punishInterval := Л_round1ValidatorsElectedFor + (round2 ->> RoundsBase_ι_Round_ι_validatorsElectedFor) in

let (p, l') := run (↓ DePoolContract_Ф_cutWithdrawalValue params bPunish punishInterval) l in
let (p, tonsForOwner) := p in
let (newVesting, withdrawalVesting) := p in
let round2 := {$round2 with (RoundsBase_ι_Round_ι_handledStakesAndRewards, round2 ->> RoundsBase_ι_Round_ι_handledStakesAndRewards + amount) ;
                            (RoundsBase_ι_Round_ι_validatorRemainingStake, validatorRemainingStake) $} in
let l'' := if (tonsForOwner >? 0) then exec_state (↓ tvm_transfer ((maybeGet newVesting) ->> RoundsBase_ι_InvestParams_ι_owner) tonsForOwner false 1 default) l' else l' in 

exec_state (DePoolContract_Ф__returnOrReinvestForParticipant_tailer2 Л_stakes Л_stakeIsLost Л_isValidator Л_addr Л_round1ValidatorsElectedFor f) l = 

if isNewVesting then 
 exec_state (f Л_stakes Л_stakeIsLost Л_isValidator Л_addr) {$ l'' With (LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds, lostFunds);
                                                                       (LocalState_ι__returnOrReinvestForParticipant_Л_round2, round2);
                                                                       (LocalState_ι__returnOrReinvestForParticipant_Л_newStake, newStake + withdrawalVesting);
                                                                       (LocalState_ι__returnOrReinvestForParticipant_Л_newVesting, newVesting);
                                                                       (LocalState_ι__returnOrReinvestForParticipant_Л_params, params) $} else
 exec_state (f Л_stakes Л_stakeIsLost Л_isValidator Л_addr) {$ l With (LocalState_ι__returnOrReinvestForParticipant_Л_newVesting, optNewVesting) $}    .
Proof.

  intros.
  destructLedger l. 
  compute. idtac.

  destruct Л_stakes; destruct RoundsBase_ι_StakeValue_ι_vesting; try destruct r. idtac.

  all: cycle 1. idtac.

  destructFunction3 DePoolContract_Ф_cutWithdrawalValue ; auto. idtac.  
  destruct x; destruct x; auto. idtac.

  Time repeat destructIf_solve. idtac.
  all: try destructFunction3 DePoolContract_Ф_cutWithdrawalValue ; auto. idtac.  
  all: try destruct x; try destruct x; auto. idtac.
  all: time repeat destructIf_solve. idtac.


  all: try match goal with 
  | |- ?G => match G with 
             | context [DePoolContract_Ф_cutWithdrawalValue ?a ?b ?c] => 
                   let m := fresh "m" in
                   let p := fresh "p" in
                   remember (DePoolContract_Ф_cutWithdrawalValue a b c) as m
             end      
  end.

  all: try setoid_rewrite <- Heqm in Heqm0. idtac.
  all: try rewrite Heqm0. idtac.
  all: try rewrite <- Heqr. idtac.
  all: try rewrite H2; auto. idtac.
  all: try rewrite H1; auto. 
Qed.

Definition DePoolContract_Ф__returnOrReinvestForParticipant_tailer3  
                   (Л_stakes : RoundsBase_ι_StakeValue) 
                   (Л_stakeIsLost : XBool )
                   (Л_isValidator : XBool )
                   (Л_addr : XAddress)
                   (f: RoundsBase_ι_StakeValue -> XBool -> XBool -> XAddress -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) )
                                               : LedgerT ( RoundsBase_ι_Round # RoundsBase_ι_Round ) := 
(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue := $ xInt1) >>
U0! Л_curPause := math->min2 (! (D1! (↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_participant) ^^ DePoolLib_ι_Participant_ι_withdrawValue) ,
								(↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake) !) ;
( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue !+= $Л_curPause ) >>
( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_participant ^^ DePoolLib_ι_Participant_ι_withdrawValue !-= 
                                 $Л_curPause ) >>
( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake !-= $Л_curPause ) >>
( If ( ( ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake ) ?< 
                                          (↑12 D2! DePoolContract_ι_m_minStake ) ) then {
	( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue !+= 
                           D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake ) >>
	( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake := $xInt0 )
} ) >> f Л_stakes Л_stakeIsLost Л_isValidator Л_addr.


Lemma DePoolContract_Ф__returnOrReinvestForParticipant_tailer3_exec : forall
                                                            (l : Ledger)
                                                            (Л_stakes : RoundsBase_ι_StakeValue) 
                                                            (Л_stakeIsLost : XBool )
                                                            (Л_isValidator : XBool )
                                                            (Л_addr : XAddress)
                                                            (f: RoundsBase_ι_StakeValue -> XBool -> XBool -> XAddress -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) ),


let newStake := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_newStake) l in
let participant := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_participant) l in
let m_minStake := eval_state (↑12 ε DePoolContract_ι_m_minStake) l in

let curPause := intMin (participant ->> DePoolLib_ι_Participant_ι_withdrawValue) newStake in
let attachedValue := 1 + curPause in
let participant := {$ participant with (DePoolLib_ι_Participant_ι_withdrawValue, (participant ->> DePoolLib_ι_Participant_ι_withdrawValue) - curPause)$} in
let newStake := newStake - curPause in
let attachedValue := if (newStake <? m_minStake) then attachedValue + newStake else attachedValue in
let newStake := if (newStake <? m_minStake) then 0 else newStake in

exec_state (DePoolContract_Ф__returnOrReinvestForParticipant_tailer3 Л_stakes Л_stakeIsLost Л_isValidator Л_addr f) l = 

exec_state (f Л_stakes Л_stakeIsLost Л_isValidator Л_addr)
{$ l With (LocalState_ι__returnOrReinvestForParticipant_Л_participant, participant);
        (LocalState_ι__returnOrReinvestForParticipant_Л_newStake, newStake);
        (LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue, attachedValue)$}.
Proof.

  intros.
  destructLedger l. 
  compute. idtac.

  Time repeat destructIf_solve.     
Qed.


Definition DePoolContract_Ф__returnOrReinvestForParticipant_tailer4  
                                              (Л_stakes : RoundsBase_ι_StakeValue) 
                                              (Л_stakeIsLost : XBool )
                                              (Л_isValidator : XBool )
                                              (Л_addr : XAddress)
                                              (f: XAddress -> RoundsBase_ι_StakeValue -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) )
                                               : LedgerT ( RoundsBase_ι_Round # RoundsBase_ι_Round ) := 
(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newLock := 
                 $ ( Л_stakes ->> RoundsBase_ι_StakeValue_ι_lock ) ) >> (* + *)(* $ [( default , default )]. *) 

( If ( ( ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock ) ->hasValue ) (* + *)
then
{ 
                                   (* InvestParams params = newLock.get(); *)
  (↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_params := 
             ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock ) ->get )       >> (* + *)
	( If ( $ Л_stakeIsLost ) then {
  
   ( If ( $ Л_isValidator ) 
     then {
           U0! Л_delta := math->min2 (! ↑17 D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params ) ^^ 
                                                         RoundsBase_ι_InvestParams_ι_remainingAmount ,
                                         ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds !) ; 
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_params ^^ 
                                             RoundsBase_ι_InvestParams_ι_remainingAmount !-= $ Л_delta ) >>  
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds !-= $ Л_delta ) >> 
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ^^ RoundsBase_ι_Round_ι_validatorRemainingStake
                       !+= D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params )
                                            ^^ RoundsBase_ι_InvestParams_ι_remainingAmount )
     } (* + *)
     else {
		( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_params ^^ 
                                             RoundsBase_ι_InvestParams_ι_remainingAmount := math->muldiv (! 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_unused !+
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_recoveredStake !-
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_validatorRemainingStake
              , 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params )
                                            ^^ RoundsBase_ι_InvestParams_ι_remainingAmount , 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_stake !-
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_validatorStake !) )
} ) 
	}  )  >>  (* + *)
                      (*********round2.handledStakesAndRewards += params.remainingAmount;************)
  ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ^^ RoundsBase_ι_Round_ι_handledStakesAndRewards !+=
  ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params ^^ RoundsBase_ι_InvestParams_ι_remainingAmount ) ) >>
   (* + *)

  U0! Л_withdrawalLock := $ default ; (* + *)
                      (* (newLock, withdrawalLock) = cutWithdrawalValue(params); *************)
  U0! {( Л_newLock , Л_withdrawalLock , _ )} := DePoolContract_Ф_cutWithdrawalValue 
             (! ( ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_params ) , $ xBoolFalse , $ xInt0 !) ;
  ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newLock := $ Л_newLock ) >>
  (If  ( $ Л_withdrawalLock ?!= $xInt0 ) then {
                      (* params.owner.transfer(withdrawalLock, false, 1); *)
   ( D1! ( ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_params ) ^^ RoundsBase_ι_InvestParams_ι_owner ) ->transfer 
            (! $ Л_withdrawalLock  , $xBoolFalse, $ xInt1 !)
     } ) 
} )  >> f Л_addr Л_stakes.

Lemma DePoolContract_Ф__returnOrReinvestForParticipant_tailer4_exec : forall
                                                            (l : Ledger)
                                                            (Л_stakes : RoundsBase_ι_StakeValue ) 
                                                            (Л_stakeIsLost : XBool )  
                                                            (Л_isValidator : XBool ) 
                                                            (Л_addr : XAddress)
                                                            (f: XAddress -> RoundsBase_ι_StakeValue -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) ),
 let lostFunds := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds) l in
 let round2 := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_round2) l in
 let optNewLock := Л_stakes ->> RoundsBase_ι_StakeValue_ι_lock in
 let isNewLock := isSome optNewLock in
 let params := maybeGet optNewLock in
 let oldLockAmount := params ->> RoundsBase_ι_InvestParams_ι_remainingAmount in
 let oldLockValidatorRemainingStake := round2 ->> RoundsBase_ι_Round_ι_validatorRemainingStake  in
 let deltaLockValidator := intMin oldLockAmount lostFunds in
 let amount := if Л_stakeIsLost then
                    if Л_isValidator then oldLockAmount - deltaLockValidator
                                     else (round2 ->> RoundsBase_ι_Round_ι_unused + round2 ->> RoundsBase_ι_Round_ι_recoveredStake - round2 ->> RoundsBase_ι_Round_ι_validatorRemainingStake) *
                                          (params ->> RoundsBase_ι_InvestParams_ι_remainingAmount) / (round2 ->> RoundsBase_ι_Round_ι_stake - round2 ->> RoundsBase_ι_Round_ι_validatorStake) 
                                   else oldLockAmount in
 let lostFunds := if Л_stakeIsLost then 
                        if Л_isValidator then lostFunds - deltaLockValidator 
                                         else lostFunds 
                                      else lostFunds in 
 let validatorRemainingStake := if Л_stakeIsLost then 
                        if Л_isValidator then oldLockValidatorRemainingStake + amount
                                         else oldLockValidatorRemainingStake 
                                      else oldLockValidatorRemainingStake in 
 let params := {$params with RoundsBase_ι_InvestParams_ι_remainingAmount := amount$} in 
 let (p, l') := run (↓ DePoolContract_Ф_cutWithdrawalValue params false 0) l in
 let (p, _) := p in
 let (newLock, withdrawalLock) := p in
 let round2 := {$round2 with (RoundsBase_ι_Round_ι_handledStakesAndRewards, round2 ->> RoundsBase_ι_Round_ι_handledStakesAndRewards + amount) ;
                             (RoundsBase_ι_Round_ι_validatorRemainingStake, validatorRemainingStake) $} in
 let l'' := if negb (withdrawalLock =? 0) then exec_state (↓ tvm_transfer (params ->> RoundsBase_ι_InvestParams_ι_owner) 
                                                                          withdrawalLock false 1 default) l' else l' in 

 exec_state (DePoolContract_Ф__returnOrReinvestForParticipant_tailer4 Л_stakes Л_stakeIsLost Л_isValidator Л_addr f) l = 
if isNewLock then 
 exec_state (f Л_addr Л_stakes) {$ l'' With (LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds, lostFunds);
        (LocalState_ι__returnOrReinvestForParticipant_Л_round2, round2);
        (* (LocalState_ι__returnOrReinvestForParticipant_Л_newStake, newStake + withdrawalLock); *)
        (LocalState_ι__returnOrReinvestForParticipant_Л_newLock, newLock);
        (LocalState_ι__returnOrReinvestForParticipant_Л_params, params) $} else
    exec_state (f Л_addr Л_stakes) {$ l With (LocalState_ι__returnOrReinvestForParticipant_Л_newLock, optNewLock) $} .
Proof.

  intros.
  destructLedger l. 
  compute. idtac.

  destruct Л_stakes; destruct RoundsBase_ι_StakeValue_ι_lock; try destruct r. idtac.

  all: cycle 1. idtac.

  destructFunction3 DePoolContract_Ф_cutWithdrawalValue ; auto. idtac.  
  destruct x; destruct x; auto. idtac.

  Time repeat destructIf_solve. idtac.
  all: try destructFunction3 DePoolContract_Ф_cutWithdrawalValue ; auto. idtac.  
  all: try destruct x; try destruct x; auto. idtac.
  all: time repeat destructIf_solve. idtac.


  all: try match goal with 
  | |- ?G => match G with 
             | context [DePoolContract_Ф_cutWithdrawalValue ?a ?b ?c] => 
                   let m := fresh "m" in
                   let p := fresh "p" in
                   remember (DePoolContract_Ф_cutWithdrawalValue a b c) as m
             end      
  end.

  all: try setoid_rewrite <- Heqm in Heqm0. idtac.
  all: try rewrite Heqm0. idtac.
  all: try rewrite <- Heqr. idtac.
  all: try rewrite H0; auto. 
Qed.  
  

Definition DePoolContract_Ф__returnOrReinvestForParticipant_tailer5 (Л_addr : XAddress) 
                                                                    (Л_stakes : RoundsBase_ι_StakeValue)
                            (f: XAddress -> RoundsBase_ι_StakeValue -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) )
                            : LedgerT ( RoundsBase_ι_Round # RoundsBase_ι_Round ):= 
(If (↑12 D2! DePoolContract_ι_m_poolClosed) then { 
	(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue !+=
                         D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake) >>
	(If ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting) ->hasValue) then { 
	(D1! ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting) ->get) ^^ 
                                  RoundsBase_ι_InvestParams_ι_owner ) ->transfer 
                                (! D1! ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting) ->get) ^^ 
                                  RoundsBase_ι_InvestParams_ι_remainingAmount , $xBoolFalse, $ xInt1 !)
	}) >>
	(If ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock) ->hasValue) then { 
	(D1! ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock) ->get) ^^ RoundsBase_ι_InvestParams_ι_owner ) 
                                                                                          ->transfer 
            (! D1! ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock) ->get) ^^ 
                                  RoundsBase_ι_InvestParams_ι_remainingAmount , $xBoolFalse, $ xInt1 !)
    }) 
 } else { 
	(If ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting) ->hasValue) !& 
		(D1! ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting) ->get) ^^ RoundsBase_ι_InvestParams_ι_remainingAmount ?== $xInt0)
	then { 
		 ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting ->reset 
	}) >>
	(If ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock) ->hasValue) !& 
		(D1! ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock) ->get) ^^ RoundsBase_ι_InvestParams_ι_remainingAmount ?== $xInt0)
	then { 
		↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newLock ->reset 
	}) >>
	(If ( !¬ (D1! (↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_participant) ^^ DePoolLib_ι_Participant_ι_reinvest)) then { 
		(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue !+= D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake) >>
		(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake := $xInt0)
	}) >>
	(↑↑17 U2! {( LocalState_ι__returnOrReinvestForParticipant_Л_round0, 
			    LocalState_ι__returnOrReinvestForParticipant_Л_participant )} := RoundsBase_Ф__addStakes (! (↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_round0) , 
				(↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_participant) ,
				$Л_addr ,
				(↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake) , 
				(↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting) ,
				(↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock)   !) )
 
 })  >> f Л_addr Л_stakes.

Lemma DePoolContract_Ф__returnOrReinvestForParticipant_tailer5_exec : forall
                                                            (l : Ledger)
                                                            (Л_addr : XAddress)
                                                            (Л_stakes : RoundsBase_ι_StakeValue ) 
                                                            (f: XAddress -> RoundsBase_ι_StakeValue -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) ),

let m_poolClosed : bool := eval_state (↑12 ε DePoolContract_ι_m_poolClosed) l in
let attachedValue := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue) l in
let newStake := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_newStake) l in
let participant := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_participant) l in
let reinvest : bool := participant ->> DePoolLib_ι_Participant_ι_reinvest in
let newOptVesting := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_newVesting) l in
let newOptLock := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_newLock) l in
let isVesting : bool := isSome newOptVesting in
let isLock : bool := isSome newOptLock in
let newVesting := maybeGet newOptVesting in
let newLock := maybeGet newOptLock in
let round0 := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_round0) l in 

let attachedValue := if m_poolClosed then attachedValue + newStake 
                        else if (negb reinvest) then attachedValue + newStake else attachedValue in
let newOptVesting := if m_poolClosed then newOptVesting else
                     if (isVesting && (newVesting ->> RoundsBase_ι_InvestParams_ι_remainingAmount =? 0))%bool then None
                     else newOptVesting in
let newOptLock := if m_poolClosed then newOptLock else
                     if (isLock && (newLock ->> RoundsBase_ι_InvestParams_ι_remainingAmount =? 0))%bool then None
                     else newOptLock in
let newStake := if m_poolClosed then newStake else
                        if (negb reinvest) then 0 else newStake in
let (rp, l') :=  if m_poolClosed then 
                    if isVesting then 
                    let lv := exec_state (↓ tvm_transfer (newVesting ->> RoundsBase_ι_InvestParams_ι_owner) 
                                                     (newVesting ->> RoundsBase_ι_InvestParams_ι_remainingAmount) 
                                                     false 1 default) l in
                    if isLock then ((round0, participant), exec_state (↓ tvm_transfer (newLock ->> RoundsBase_ι_InvestParams_ι_owner) 
                                            (newLock ->> RoundsBase_ι_InvestParams_ι_remainingAmount) 
                                            false 1 default) lv)
                              else ((round0, participant), lv)
                    else if isLock then ((round0, participant) , exec_state (↓ tvm_transfer (newLock ->> RoundsBase_ι_InvestParams_ι_owner) 
                                            (newLock ->> RoundsBase_ι_InvestParams_ι_remainingAmount) 
                                            false 1 default) l)
                            else ((round0, participant) , l)
                  else  run (↓ RoundsBase_Ф__addStakes round0 participant Л_addr newStake newOptVesting newOptLock) l in
let (round0, participant) := rp in   

exec_state (DePoolContract_Ф__returnOrReinvestForParticipant_tailer5 Л_addr Л_stakes f) l = 
exec_state (f Л_addr Л_stakes) {$l' With 
        (LocalState_ι__returnOrReinvestForParticipant_Л_newStake, newStake ); 
        (LocalState_ι__returnOrReinvestForParticipant_Л_newLock, newOptLock);
        (LocalState_ι__returnOrReinvestForParticipant_Л_newVesting, newOptVesting);
        (LocalState_ι__returnOrReinvestForParticipant_Л_round0, round0);
        (LocalState_ι__returnOrReinvestForParticipant_Л_participant, participant);
        (LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue, attachedValue) $}   .                                                               
Proof.

  intros.
  destructLedger l. 
  compute. idtac.

  Time repeat destructIf_solve. idtac.

  all: try destructFunction6 RoundsBase_Ф__addStakes ; auto. idtac.  
  all: try rewrite H0 in H3; try discriminate. idtac.
  all: try destruct x; auto. 
Qed.    
 


 Definition DePoolContract_Ф__returnOrReinvestForParticipant_tailer6 (Л_addr : XAddress) 
                                                                     (Л_stakes : RoundsBase_ι_StakeValue): LedgerT ( RoundsBase_ι_Round # RoundsBase_ι_Round ) := 
 ParticipantBase_Ф__setOrDeleteParticipant (! $Л_addr , (↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_participant)  !) >>

 ( ->sendMessage {|| contractAddress ::= $ Л_addr ,
			   contractFunction ::=  IParticipant_И_onRoundCompleteF (!! 
                    ↑17 D1! (D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2) ^^ RoundsBase_ι_Round_ι_id ,
																	   ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_reward ,
																	   $ Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary ,
																	   (($ Л_stakes ->> RoundsBase_ι_StakeValue_ι_vesting) ->hasValue ) ? 
																			  (D1! (($ Л_stakes ->> RoundsBase_ι_StakeValue_ι_vesting) ->get) ^^ 
                                                   RoundsBase_ι_InvestParams_ι_remainingAmount) ::: $xInt0, 
																	   (($ Л_stakes ->> RoundsBase_ι_StakeValue_ι_lock) ->hasValue ) ? 
																			  (D1! (($ Л_stakes ->> RoundsBase_ι_StakeValue_ι_lock) ->get) ^^ 
                                                    RoundsBase_ι_InvestParams_ι_remainingAmount) ::: $xInt0 ,
																	   D1! (↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_participant) ^^ DePoolLib_ι_Participant_ι_reinvest , 
																	   (completionReason2XInteger (!! 
                                              ↑17 D1! (D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2) ^^ 
                                                    RoundsBase_ι_Round_ι_completionReason !!) ) 
			                                                          !!) ,
			   contractMessage ::= {|| messageValue ::= ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue , 
			                          messageBounce ::= $xBoolFalse ||} ||} ) >> 
 return# ( ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_round0 , 
           ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ). 


Lemma DePoolContract_Ф__returnOrReinvestForParticipant_tailer6_exec : forall
                                                            (l : Ledger)
                                                            (Л_addr : XAddress)
                                                            (Л_stakes : RoundsBase_ι_StakeValue ) ,
 let participant := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_participant) l in
 let round2 := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_round2) l in
 let attachedValue := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue) l in
 let reward := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_reward) l in
 let isVesting := isSome (Л_stakes ->> RoundsBase_ι_StakeValue_ι_vesting) in
 let vestingAmount := (maybeGet (Л_stakes ->> RoundsBase_ι_StakeValue_ι_vesting)) ->> RoundsBase_ι_InvestParams_ι_remainingAmount in
 let isLock := isSome (Л_stakes ->> RoundsBase_ι_StakeValue_ι_lock) in
 let lockAmount := (maybeGet (Л_stakes ->> RoundsBase_ι_StakeValue_ι_lock)) ->> RoundsBase_ι_InvestParams_ι_remainingAmount in


 let l' := exec_state (↓ ParticipantBase_Ф__setOrDeleteParticipant Л_addr participant) l in
 let oldMessages := eval_state (↑16 ε VMState_ι_messages) l in 
 let newMessage  := {| contractAddress  :=  Л_addr ;
                       contractFunction := IParticipant_И_onRoundCompleteF (round2 ->> RoundsBase_ι_Round_ι_id)
                                                                            reward
                                                                           (Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary)
                                                                           (if isVesting then vestingAmount else 0)
                                                                           (if isLock then lockAmount else 0)
                                                                           (participant ->> DePoolLib_ι_Participant_ι_reinvest)
                                                                           (completionReason2XInteger (round2 ->> RoundsBase_ι_Round_ι_completionReason)) ;
                       contractMessage :=  {| messageValue := attachedValue;
                                             messageFlag := 0 ;
                                             messageBounce := false |} |} in 

exec_state (DePoolContract_Ф__returnOrReinvestForParticipant_tailer6 Л_addr Л_stakes ) l =
 {$l' With VMState_ι_messages := newMessage :: oldMessages $}.
Proof.

  intros.
  destructLedger l. 
  compute. idtac.

  Time repeat destructIf_solve.

Qed.    


Lemma DePoolContract_Ф__returnOrReinvestForParticipant'_eval : forall
                                                                (l : Ledger)
                                                                ( Л_round2 : RoundsBase_ι_Round )
                                                                ( Л_round0 : RoundsBase_ι_Round )
                                                                ( Л_addr : XAddress )
                                                                ( Л_stakes : RoundsBase_ι_StakeValue ) 
                                                                ( Л_isValidator : XBool ) 
                                                                ( Л_round1ValidatorsElectedFor : XInteger32 )
                                                                ( f : XBool -> XBool ->  RoundsBase_ι_StakeValue -> XInteger -> XAddress -> XInteger32 -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) ),
let (stakeSum, l_sum) := run (↓ RoundsBase_Ф_stakeSum Л_stakes) l in
let stakeIsLost : bool := eqb (Л_round2 ->> RoundsBase_ι_Round_ι_completionReason) RoundsBase_ι_CompletionReasonP_ι_ValidatorIsPunished in
let optParticipant := eval_state (↓ ParticipantBase_Ф_fetchParticipant Л_addr) l_sum in
let isSomeParticipant : bool := isSome optParticipant in
let participant := maybeGet optParticipant in 
let participant_newRoundQty :=
    {$ participant with (DePoolLib_ι_Participant_ι_roundQty, (participant ->> DePoolLib_ι_Participant_ι_roundQty) - 1 ) $} in 
let lostFunds := if stakeIsLost
    then    (Л_round2 ->> RoundsBase_ι_Round_ι_stake  -
              Л_round2 ->> RoundsBase_ι_Round_ι_unused)  -
              Л_round2 ->> RoundsBase_ι_Round_ι_recoveredStake
    else 0 in 
let l_local := {$ l_sum With (LocalState_ι__returnOrReinvestForParticipant_Л_round2, Л_round2);
                              (LocalState_ι__returnOrReinvestForParticipant_Л_round0, Л_round0);
                              (LocalState_ι__returnOrReinvestForParticipant_Л_participant, participant_newRoundQty);
                              (LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds, lostFunds) $} in

eval_state (DePoolContract_Ф__returnOrReinvestForParticipant' Л_round2 Л_round0 Л_addr Л_stakes Л_isValidator Л_round1ValidatorsElectedFor f) l =
    if isSomeParticipant then Value (eval_state (f stakeIsLost Л_isValidator Л_stakes stakeSum Л_addr Л_round1ValidatorsElectedFor) l_local)
        else Error InternalErrors_ι_ERROR511 .
Proof.            
  
  intros.
  destructLedger l. 
  compute.

  Time repeat destructIf_solve.

  all: try destructFunction1  RoundsBase_Ф_stakeSum ; auto. idtac.
  all: time repeat destructIf_solve. idtac.  
  all: try destructFunction5 f ; auto.

Qed.  

Lemma DePoolContract_Ф__returnOrReinvestForParticipant_tailer1_eval : forall
                                                            ( l : Ledger )
                                                            ( Л_stakeIsLost: XBool ) 
                                                            ( Л_isValidator : XBool )
                                                            ( Л_stakes : RoundsBase_ι_StakeValue ) 
                                                            ( Л_stakeSum: XInteger)
                                                            ( Л_addr : XAddress)
                                                            ( Л_round1ValidatorsElectedFor : XInteger32 )
                                                            ( f : RoundsBase_ι_StakeValue -> XBool -> XBool -> XAddress -> XInteger32 -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) ),

let newStake := 0 in
let reward := 0 in
let lostFunds := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds) l in
let round2 :=  eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_round2) l in
let participant := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_participant) l in
let delta := intMin ( Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary) lostFunds in
let newStake := if Л_stakeIsLost then 
                    if Л_isValidator then 
                        Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary - delta
                                     else (round2 ->> RoundsBase_ι_Round_ι_unused + 
                                           round2 ->> RoundsBase_ι_Round_ι_recoveredStake - 
                                           round2 ->> RoundsBase_ι_Round_ι_validatorRemainingStake) *  
                                           (Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary) /
                                           (round2 ->> RoundsBase_ι_Round_ι_stake - round2 ->> RoundsBase_ι_Round_ι_validatorStake) 
                                 else Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary + 
                                 Л_stakeSum * (round2 ->> RoundsBase_ι_Round_ι_rewards) / (round2 ->> RoundsBase_ι_Round_ι_stake)  in
let lostFunds :=   if Л_stakeIsLost then 
                        if Л_isValidator then lostFunds - delta else lostFunds 
                                     else lostFunds in
let reward :=  if Л_stakeIsLost then reward
                                 else Л_stakeSum *  (round2 ->> RoundsBase_ι_Round_ι_rewards) / (round2 ->> RoundsBase_ι_Round_ι_stake) in 
let round2 :=  if Л_stakeIsLost then 
                        if Л_isValidator then  {$ round2 with RoundsBase_ι_Round_ι_validatorRemainingStake := newStake $}     
                                         else round2 
                                     else round2 in   
let participant := if Л_stakeIsLost then participant
                                    else {$ participant with DePoolLib_ι_Participant_ι_reward := participant ->> DePoolLib_ι_Participant_ι_reward + reward $} in 
let round2 := {$round2 with RoundsBase_ι_Round_ι_handledStakesAndRewards :=  round2 ->> RoundsBase_ι_Round_ι_handledStakesAndRewards + newStake$} in

 eval_state (DePoolContract_Ф__returnOrReinvestForParticipant_tailer1 Л_stakeIsLost Л_isValidator Л_stakes Л_stakeSum Л_addr Л_round1ValidatorsElectedFor f) l =
 eval_state (f Л_stakes Л_stakeIsLost Л_isValidator Л_addr Л_round1ValidatorsElectedFor) {$ l With (LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds, lostFunds);
                                                                      (LocalState_ι__returnOrReinvestForParticipant_Л_round2, round2);
                                                                      (LocalState_ι__returnOrReinvestForParticipant_Л_participant, participant);
                                                                      (LocalState_ι__returnOrReinvestForParticipant_Л_newStake, newStake);
                                                                      (LocalState_ι__returnOrReinvestForParticipant_Л_reward, reward) $}.
Proof.

  intros.
  destructLedger l. 
  compute.

  Time repeat destructIf_solve.

Qed.

Lemma DePoolContract_Ф__returnOrReinvestForParticipant_tailer2_eval : forall
                                                            ( l : Ledger)
                                                            ( Л_stakes : RoundsBase_ι_StakeValue ) 
                                                            ( Л_stakeIsLost : XBool )  
                                                            ( Л_isValidator : XBool ) 
                                                            ( Л_addr : XAddress )
                                                            ( Л_round1ValidatorsElectedFor : XInteger32 )
                                                            ( f: RoundsBase_ι_StakeValue -> XBool -> XBool -> XAddress -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) ),
let lostFunds := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds) l in
let round2 := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_round2) l in
let newStake := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_newStake) l in

let optNewVesting := Л_stakes ->> RoundsBase_ι_StakeValue_ι_vesting in
let isNewVesting := isSome optNewVesting in
let params := maybeGet optNewVesting in
let oldVestingAmount := params ->> RoundsBase_ι_InvestParams_ι_remainingAmount in
let oldVestingValidatorRemainingStake := round2 ->> RoundsBase_ι_Round_ι_validatorRemainingStake  in
let deltaVestingValidator := intMin oldVestingAmount lostFunds in
let amount := if Л_stakeIsLost then
                  if Л_isValidator then oldVestingAmount - deltaVestingValidator
                                   else (round2 ->> RoundsBase_ι_Round_ι_unused + round2 ->> RoundsBase_ι_Round_ι_recoveredStake - round2 ->> RoundsBase_ι_Round_ι_validatorRemainingStake) *
                                        (params ->> RoundsBase_ι_InvestParams_ι_remainingAmount) / (round2 ->> RoundsBase_ι_Round_ι_stake - round2 ->> RoundsBase_ι_Round_ι_validatorStake) 
                                  else oldVestingAmount in
let lostFunds := if Л_stakeIsLost then 
                      if Л_isValidator then lostFunds - deltaVestingValidator 
                                       else lostFunds 
                                    else lostFunds in 
let validatorRemainingStake := if Л_stakeIsLost then 
                      if Л_isValidator then oldVestingValidatorRemainingStake + amount
                                       else oldVestingValidatorRemainingStake 
                                    else oldVestingValidatorRemainingStake in 
let params := {$ params with RoundsBase_ι_InvestParams_ι_remainingAmount := amount $} in
let bPunish := (Л_isValidator && negb (eqb round2 ->> RoundsBase_ι_Round_ι_completionReason RoundsBase_ι_CompletionReasonP_ι_RewardIsReceived))%bool in
let punishInterval := Л_round1ValidatorsElectedFor + (round2 ->> RoundsBase_ι_Round_ι_validatorsElectedFor) in

let (p, l') := run (↓ DePoolContract_Ф_cutWithdrawalValue params bPunish punishInterval) l in
let (p, tonsForOwner) := p in
let (newVesting, withdrawalVesting) := p in
let round2 := {$round2 with (RoundsBase_ι_Round_ι_handledStakesAndRewards, round2 ->> RoundsBase_ι_Round_ι_handledStakesAndRewards + amount) ;
                            (RoundsBase_ι_Round_ι_validatorRemainingStake, validatorRemainingStake) $} in
let l'' := if (tonsForOwner >? 0) then exec_state (↓ tvm_transfer ((maybeGet newVesting) ->> RoundsBase_ι_InvestParams_ι_owner) tonsForOwner false 1 default) l' else l' in 

eval_state (DePoolContract_Ф__returnOrReinvestForParticipant_tailer2 Л_stakes Л_stakeIsLost Л_isValidator Л_addr Л_round1ValidatorsElectedFor f) l = 

if isNewVesting then 
 eval_state (f Л_stakes Л_stakeIsLost Л_isValidator Л_addr) {$ l'' With (LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds, lostFunds);
                                                                       (LocalState_ι__returnOrReinvestForParticipant_Л_round2, round2);
                                                                       (LocalState_ι__returnOrReinvestForParticipant_Л_newStake, newStake + withdrawalVesting);
                                                                       (LocalState_ι__returnOrReinvestForParticipant_Л_newVesting, newVesting);
                                                                       (LocalState_ι__returnOrReinvestForParticipant_Л_params, params) $} else
 eval_state (f Л_stakes Л_stakeIsLost Л_isValidator Л_addr) {$ l With (LocalState_ι__returnOrReinvestForParticipant_Л_newVesting, optNewVesting) $}    .
Proof.

  intros.
  destructLedger l. 
  compute. idtac.

  destruct Л_stakes; destruct RoundsBase_ι_StakeValue_ι_vesting; try destruct r. idtac.

  all: cycle 1. idtac.

  destructFunction3 DePoolContract_Ф_cutWithdrawalValue ; auto. idtac.  
  destruct x; destruct x; auto. idtac.

  Time repeat destructIf_solve. idtac.
  all: try destructFunction3 DePoolContract_Ф_cutWithdrawalValue ; auto. idtac.  
  all: try destruct x; try destruct x; auto. idtac.
  all: time repeat destructIf_solve. idtac.


  all: try match goal with 
  | |- ?G => match G with 
             | context [DePoolContract_Ф_cutWithdrawalValue ?a ?b ?c] => 
                   let m := fresh "m" in
                   let p := fresh "p" in
                   remember (DePoolContract_Ф_cutWithdrawalValue a b c) as m
             end      
  end.

  all: try setoid_rewrite <- Heqm in Heqm0. idtac.
  all: try rewrite Heqm0. idtac.
  all: try rewrite <- Heqr. idtac.
  all: try rewrite H2; auto. idtac.
  all: try rewrite H1; auto. 
Qed.


Lemma DePoolContract_Ф__returnOrReinvestForParticipant_tailer3_eval : forall
                                                            (l : Ledger)
                                                            (Л_stakes : RoundsBase_ι_StakeValue) 
                                                            (Л_stakeIsLost : XBool )
                                                            (Л_isValidator : XBool )
                                                            (Л_addr : XAddress)
                                                            (f: RoundsBase_ι_StakeValue -> XBool -> XBool -> XAddress -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) ),


let newStake := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_newStake) l in
let participant := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_participant) l in
let m_minStake := eval_state (↑12 ε DePoolContract_ι_m_minStake) l in

let curPause := intMin (participant ->> DePoolLib_ι_Participant_ι_withdrawValue) newStake in
let attachedValue := 1 + curPause in
let participant := {$participant with (DePoolLib_ι_Participant_ι_withdrawValue, (participant ->> DePoolLib_ι_Participant_ι_withdrawValue) - curPause)$} in
let newStake := newStake - curPause in
let attachedValue := if (newStake <? m_minStake) then attachedValue + newStake else attachedValue in
let newStake := if (newStake <? m_minStake) then 0 else newStake in

eval_state (DePoolContract_Ф__returnOrReinvestForParticipant_tailer3 Л_stakes Л_stakeIsLost Л_isValidator Л_addr f) l = 

eval_state (f Л_stakes Л_stakeIsLost Л_isValidator Л_addr)
{$ l With (LocalState_ι__returnOrReinvestForParticipant_Л_participant, participant);
        (LocalState_ι__returnOrReinvestForParticipant_Л_newStake, newStake);
        (LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue, attachedValue)$}.
Proof.

  intros.
  destructLedger l. 
  compute. idtac.

  Time repeat destructIf_solve.     
Qed.



Lemma DePoolContract_Ф__returnOrReinvestForParticipant_tailer4_eval : forall
                                                            (l : Ledger)
                                                            (Л_stakes : RoundsBase_ι_StakeValue ) 
                                                            (Л_stakeIsLost : XBool )  
                                                            (Л_isValidator : XBool ) 
                                                            (Л_addr : XAddress)
                                                            (f: XAddress -> RoundsBase_ι_StakeValue -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) ),
 let lostFunds := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds) l in
 let round2 := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_round2) l in
 let optNewLock := Л_stakes ->> RoundsBase_ι_StakeValue_ι_lock in
 let isNewLock := isSome optNewLock in
 let params := maybeGet optNewLock in
 let oldLockAmount := params ->> RoundsBase_ι_InvestParams_ι_remainingAmount in
 let oldLockValidatorRemainingStake := round2 ->> RoundsBase_ι_Round_ι_validatorRemainingStake  in
 let deltaLockValidator := intMin oldLockAmount lostFunds in
 let amount := if Л_stakeIsLost then
                    if Л_isValidator then oldLockAmount - deltaLockValidator
                                     else (round2 ->> RoundsBase_ι_Round_ι_unused + round2 ->> RoundsBase_ι_Round_ι_recoveredStake - round2 ->> RoundsBase_ι_Round_ι_validatorRemainingStake) *
                                          (params ->> RoundsBase_ι_InvestParams_ι_remainingAmount) / (round2 ->> RoundsBase_ι_Round_ι_stake - round2 ->> RoundsBase_ι_Round_ι_validatorStake) 
                                   else oldLockAmount in
 let lostFunds := if Л_stakeIsLost then 
                        if Л_isValidator then lostFunds - deltaLockValidator 
                                         else lostFunds 
                                      else lostFunds in 
 let validatorRemainingStake := if Л_stakeIsLost then 
                        if Л_isValidator then oldLockValidatorRemainingStake + amount
                                         else oldLockValidatorRemainingStake 
                                      else oldLockValidatorRemainingStake in 
 let params := {$params with RoundsBase_ι_InvestParams_ι_remainingAmount := amount$} in 
 let (p, l') := run (↓ DePoolContract_Ф_cutWithdrawalValue params false 0) l in
 let (p, _) := p in
 let (newLock, withdrawalLock) := p in
 let round2 := {$round2 with (RoundsBase_ι_Round_ι_handledStakesAndRewards, round2 ->> RoundsBase_ι_Round_ι_handledStakesAndRewards + amount) ;
                             (RoundsBase_ι_Round_ι_validatorRemainingStake, validatorRemainingStake) $} in
 let l'' := if negb (withdrawalLock =? 0) then exec_state (↓ tvm_transfer (params ->> RoundsBase_ι_InvestParams_ι_owner) 
                                                                          withdrawalLock false 1 default) l' else l' in 

 eval_state (DePoolContract_Ф__returnOrReinvestForParticipant_tailer4 Л_stakes Л_stakeIsLost Л_isValidator Л_addr f) l = 
if isNewLock then 
 eval_state (f Л_addr Л_stakes) {$ l'' With (LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds, lostFunds);
        (LocalState_ι__returnOrReinvestForParticipant_Л_round2, round2);     
        (LocalState_ι__returnOrReinvestForParticipant_Л_newLock, newLock);
        (LocalState_ι__returnOrReinvestForParticipant_Л_params, params) $} else
 eval_state (f Л_addr Л_stakes) {$ l With (LocalState_ι__returnOrReinvestForParticipant_Л_newLock, optNewLock) $} .
Proof.

  intros.
  destructLedger l. 
  compute. idtac.

  destruct Л_stakes; destruct RoundsBase_ι_StakeValue_ι_lock; try destruct r. idtac.

  all: cycle 1. idtac.

  destructFunction3 DePoolContract_Ф_cutWithdrawalValue ; auto. idtac.  
  destruct x; destruct x; auto. idtac.

  Time repeat destructIf_solve. idtac.
  all: try destructFunction3 DePoolContract_Ф_cutWithdrawalValue ; auto. idtac.  
  all: try destruct x; try destruct x; auto. idtac.
  all: time repeat destructIf_solve. idtac.


  all: try match goal with 
  | |- ?G => match G with 
             | context [DePoolContract_Ф_cutWithdrawalValue ?a ?b ?c] => 
                   let m := fresh "m" in
                   let p := fresh "p" in
                   remember (DePoolContract_Ф_cutWithdrawalValue a b c) as m
             end      
  end.

  all: try setoid_rewrite <- Heqm in Heqm0. idtac.
  all: try rewrite Heqm0. idtac.
  all: try rewrite <- Heqr. idtac.
  all: try rewrite H0; auto. 
Qed.  


Lemma DePoolContract_Ф__returnOrReinvestForParticipant_tailer5_eval : forall
                                                            (l : Ledger)
                                                            (Л_addr : XAddress)
                                                            (Л_stakes : RoundsBase_ι_StakeValue ) 
                                                            (f: XAddress -> RoundsBase_ι_StakeValue -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) ),

let m_poolClosed : bool := eval_state (↑12 ε DePoolContract_ι_m_poolClosed) l in
let attachedValue := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue) l in
let newStake := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_newStake) l in
let participant := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_participant) l in
let reinvest : bool := participant ->> DePoolLib_ι_Participant_ι_reinvest in
let newOptVesting := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_newVesting) l in
let newOptLock := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_newLock) l in
let isVesting : bool := isSome newOptVesting in
let isLock : bool := isSome newOptLock in
let newVesting := maybeGet newOptVesting in
let newLock := maybeGet newOptLock in
let round0 := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_round0) l in 

let attachedValue := if m_poolClosed then attachedValue + newStake 
                        else if (negb reinvest) then attachedValue + newStake else attachedValue in
let newOptVesting := if m_poolClosed then newOptVesting else
                     if (isVesting && (newVesting ->> RoundsBase_ι_InvestParams_ι_remainingAmount =? 0))%bool then None
                     else newOptVesting in
let newOptLock := if m_poolClosed then newOptLock else
                     if (isLock && (newLock ->> RoundsBase_ι_InvestParams_ι_remainingAmount =? 0))%bool then None
                     else newOptLock in
let newStake := if m_poolClosed then newStake else
                        if (negb reinvest) then 0 else newStake in
let (rp, l') :=  if m_poolClosed then 
                    if isVesting then 
                    let lv := exec_state (↓ tvm_transfer (newVesting ->> RoundsBase_ι_InvestParams_ι_owner) 
                                                     (newVesting ->> RoundsBase_ι_InvestParams_ι_remainingAmount) 
                                                     false 1 default) l in
                    if isLock then ((round0, participant), exec_state (↓ tvm_transfer (newLock ->> RoundsBase_ι_InvestParams_ι_owner) 
                                            (newLock ->> RoundsBase_ι_InvestParams_ι_remainingAmount) 
                                            false 1 default) lv)
                              else ((round0, participant), lv)
                    else if isLock then ((round0, participant) , exec_state (↓ tvm_transfer (newLock ->> RoundsBase_ι_InvestParams_ι_owner) 
                                            (newLock ->> RoundsBase_ι_InvestParams_ι_remainingAmount) 
                                            false 1 default) l)
                            else ((round0, participant) , l)
                  else  run (↓ RoundsBase_Ф__addStakes round0 participant Л_addr newStake newOptVesting newOptLock) l in
let (round0, participant) := rp in   

eval_state (DePoolContract_Ф__returnOrReinvestForParticipant_tailer5 Л_addr Л_stakes f) l = 
eval_state (f Л_addr Л_stakes) {$l' With 
        (LocalState_ι__returnOrReinvestForParticipant_Л_newStake, newStake ); 
        (LocalState_ι__returnOrReinvestForParticipant_Л_newLock, newOptLock);
        (LocalState_ι__returnOrReinvestForParticipant_Л_newVesting, newOptVesting);
        (LocalState_ι__returnOrReinvestForParticipant_Л_round0, round0);
        (LocalState_ι__returnOrReinvestForParticipant_Л_participant, participant);
        (LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue, attachedValue) $}   .                                                               
Proof.

  intros.
  destructLedger l. 
  compute. idtac.

  Time repeat destructIf_solve. idtac.

  all: try destructFunction6 RoundsBase_Ф__addStakes ; auto. idtac.  
  all: try rewrite H0 in H3; try discriminate. idtac.
  all: try destruct x; auto. 
Qed.    


Lemma DePoolContract_Ф__returnOrReinvestForParticipant_tailer6_eval : forall
                                                            (l : Ledger)
                                                            (Л_addr : XAddress)
                                                            (Л_stakes : RoundsBase_ι_StakeValue ) ,
 let round0 := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_round0) l in
 let round2 := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_round2) l in

eval_state (DePoolContract_Ф__returnOrReinvestForParticipant_tailer6 Л_addr Л_stakes ) l = (round0, round2).


Proof.

  intros.
  destructLedger l. 
  compute. idtac.

  Time repeat destructIf_solve.

Qed.    

End DePoolContract_Ф__returnOrReinvestForParticipant.