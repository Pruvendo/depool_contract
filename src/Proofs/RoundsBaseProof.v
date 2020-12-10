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



(* Existing Instance embeddedLocalState.
 
Existing Instance monadStateT.
Existing Instance monadStateStateT. *)

(* Existing Instance embeddedLocalState.
Existing Instance embeddedMultisig. *)

(* 
     function _addStakes(
        Round round,
        DePoolLib.Participant participant,
        address participantAddress,
        uint64 stake,
        optional(InvestParams) vesting,
        optional(InvestParams) lock
    )
        internal inline returns (Round, DePoolLib.Participant)
    {
        if (stake == 0 && !vesting.hasValue() && !lock.hasValue()) {
            return (round, participant);
        }

        if (!round.stakes.exists(participantAddress)) {
            round.participantQty++;
            participant.roundQty++;
        }

        round.stake += stake;
        StakeValue sv = round.stakes[participantAddress];
        sv.ordinary += stake;

        if (vesting.hasValue()) {
            participant.haveVesting = true;
            round.stake += vesting.get().amount;
            sv.vesting = vesting;
        }

        if (lock.hasValue()) {
            participant.haveLock = true;
            round.stake += lock.get().amount;
            sv.lock = lock;
        }

        round.stakes[participantAddress] = sv;
        return (round, participant);
    }

Definition RoundsBase_Ф__addStakes' (Л_round : RoundsBase_ι_Round )
								                    (Л_participant : DePoolLib_ι_Participant ) 
								                    (Л_participantAddress: XAddress) 
								                    (Л_stake: XInteger64) 
								                    (Л_vesting: XMaybe RoundsBase_ι_InvestParams) 
								                    (Л_lock: XMaybe RoundsBase_ι_InvestParams) 
                    : LedgerT  (XValueValue ( RoundsBase_ι_Round # DePoolLib_ι_Participant)) :=  							   
 (* initialize local variables *)						
 (↑17 U1! LocalState_ι__addStakes_Л_round := $ Л_round) >>
 (↑17 U1! LocalState_ι__addStakes_Л_participant := $ Л_participant) >> 

 (*
 if (stake == 0 && !vesting.hasValue() && !lock.hasValue()) {
            return (round, participant);
        }
 *)
 
  If! ( ( $ Л_stake ?== $ xInt0 ) !&  ( !¬ ($ Л_vesting ->hasValue) ) !& ( !¬ ($ Л_lock ->hasValue) ) ) then { 
    return! (xError (  [( Л_round , Л_participant )] ))  
  } ; 

		 (* >> [? LocalState_ι__addStakes_return ?] ;   *)
					   
  (*
  if (!round.stakes.exists(participantAddress)) {
            round.participantQty++;
            participant.roundQty++;
        }
  *)
  ( If ( !¬ (D1! (↑17 D2! LocalState_ι__addStakes_Л_round ^^ RoundsBase_ι_Round_ι_stakes) ->exists $ Л_participantAddress) ) then  {
		(↑17 U1! LocalState_ι__addStakes_Л_round ^^ RoundsBase_ι_Round_ι_participantQty !++) >>
		(↑17 U1! LocalState_ι__addStakes_Л_participant ^^ DePoolLib_ι_Participant_ι_roundQty !++)
	} ) >>
						
  (*round.stake += stake;
        StakeValue sv = round.stakes[participantAddress];
		sv.ordinary += stake;*)			
  (↑17 U1! LocalState_ι__addStakes_Л_round ^^ RoundsBase_ι_Round_ι_stake !+= $ Л_stake) >> 			  
  (↑17 U1! LocalState_ι__addStakes_Л_sv := D1! (D2! LocalState_ι__addStakes_Л_round ^^ RoundsBase_ι_Round_ι_stakes) [[ $ Л_participantAddress ]] ) >> 
  (↑17 U1! LocalState_ι__addStakes_Л_sv ^^ RoundsBase_ι_StakeValue_ι_ordinary !+= $ Л_stake) >> 

  (If  ($ Л_vesting ->hasValue) then {
	  
	(↑17 U1! LocalState_ι__addStakes_Л_participant ^^ DePoolLib_ι_Participant_ι_haveVesting := $ xBoolTrue ) >>

	 (* (If  (D1! ($ Л_vesting ->get) ^^ RoundsBase_ι_InvestParams_ι_isActive) then { *)
		(↑17 U1! LocalState_ι__addStakes_Л_round ^^ RoundsBase_ι_Round_ι_stake !+= (D1! ($ Л_vesting ->get) ^^ RoundsBase_ι_InvestParams_ι_amount))
	  (* }) *) >>

	 (↑17 U1! LocalState_ι__addStakes_Л_sv ^^ RoundsBase_ι_StakeValue_ι_vesting := $ Л_vesting) 
  }) >> 

  (*

  if (lock.hasValue()) {
            participant.haveLock = true;
            
                round.stake += lock.get().amount;
           
            sv.lock = lock;
        }
  
  *)

  (If  ($ Л_lock ->hasValue) then {
	  
	(↑17 U1! LocalState_ι__addStakes_Л_participant ^^ DePoolLib_ι_Participant_ι_haveLock := $ xBoolTrue ) >>

	(*  (If (D1! ($ Л_lock ->get) ^^ RoundsBase_ι_InvestParams_ι_isActive) then { *)
		(↑17 U1! LocalState_ι__addStakes_Л_round ^^ RoundsBase_ι_Round_ι_stake !+= (D1! ($ Л_lock ->get) ^^ RoundsBase_ι_InvestParams_ι_amount))
	 (*  }) *) >>

	 (↑17 U1! LocalState_ι__addStakes_Л_sv ^^ RoundsBase_ι_StakeValue_ι_lock := $ Л_lock) 
  }) >>		

  return# ( ↑ε17 LocalState_ι__addStakes_Л_round , ↑ε17 LocalState_ι__addStakes_Л_participant).	

*) 

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


(*
function toTruncatedRound(Round round) internal pure returns (TruncatedRound r) {
        return TruncatedRound({
            id: round.id,
            supposedElectedAt: round.supposedElectedAt,
            unfreeze: round.unfreeze,
            stakeHeldFor: round.stakeHeldFor,
            vsetHashInElectionPhase: round.vsetHashInElectionPhase,
            step: round.step,
            completionReason: round.completionReason,

            stake: round.stake,
            recoveredStake: round.recoveredStake,
            unused: round.unused,
            isValidatorStakeCompleted: round.isValidatorStakeCompleted,
            rewards: round.rewards,
            participantQty: round.participantQty,
            validatorStake: round.validatorStake,
            validatorRemainingStake: round.validatorRemainingStake,
            handledStakesAndRewards: round.handledStakesAndRewards
        }
*)

(* Definition RoundsBase_Ф_toTruncatedRound ( Л_round : RoundsBase_ι_Round ) : LedgerT RoundsBase_ι_TruncatedRound := 
  {|| RoundsBase_ι_TruncatedRound_ι_id := $ Л_round ->> RoundsBase_ι_Round_ι_id ,
      RoundsBase_ι_TruncatedRound_ι_supposedElectedAt := $ Л_round ->> RoundsBase_ι_Round_ι_supposedElectedAt,
      RoundsBase_ι_TruncatedRound_ι_unfreeze := $ Л_round ->> RoundsBase_ι_Round_ι_unfreeze , 
      RoundsBase_ι_TruncatedRound_ι_stakeHeldFor := $ Л_round ->> RoundsBase_ι_Round_ι_stakeHeldFor , 
      RoundsBase_ι_TruncatedRound_ι_vsetHashInElectionPhase := $ Л_round ->> RoundsBase_ι_Round_ι_vsetHashInElectionPhase ,
      RoundsBase_ι_TruncatedRound_ι_step := $ Л_round ->> RoundsBase_ι_Round_ι_step ,
      RoundsBase_ι_TruncatedRound_ι_completionReason := $ Л_round ->> RoundsBase_ι_Round_ι_completionReason ,
      RoundsBase_ι_TruncatedRound_ι_stake := $ Л_round ->> RoundsBase_ι_Round_ι_stake ,
      RoundsBase_ι_TruncatedRound_ι_recoveredStake := $ Л_round ->> RoundsBase_ι_Round_ι_recoveredStake ,
      RoundsBase_ι_TruncatedRound_ι_unused := $ Л_round ->> RoundsBase_ι_Round_ι_unused ,
      RoundsBase_ι_TruncatedRound_ι_isValidatorStakeCompleted := $ Л_round ->> RoundsBase_ι_Round_ι_isValidatorStakeCompleted ,
      RoundsBase_ι_TruncatedRound_ι_rewards := $ Л_round ->> RoundsBase_ι_Round_ι_rewards ,
      RoundsBase_ι_TruncatedRound_ι_participantQty := $ Л_round ->> RoundsBase_ι_Round_ι_participantQty ,
      RoundsBase_ι_TruncatedRound_ι_validatorStake := $ Л_round ->> RoundsBase_ι_Round_ι_validatorStake ,
      RoundsBase_ι_TruncatedRound_ι_validatorRemainingStake := $ Л_round ->> RoundsBase_ι_Round_ι_validatorRemainingStake ,
      RoundsBase_ι_TruncatedRound_ι_handledStakesAndRewards := $ Л_round ->> RoundsBase_ι_Round_ι_handledStakesAndRewards ||}.

 *)


 Lemma RoundsBase_Ф_toTruncatedRound_exec : forall ( Л_round : RoundsBase_ι_Round ) (l: Ledger) , 
 	 exec_state (  RoundsBase_Ф_toTruncatedRound Л_round ) l = l .  
 Proof. 
   intros. destruct l. auto. 
 Qed. 
 
 Lemma RoundsBase_Ф_toTruncatedRound_eval : forall ( Л_round : RoundsBase_ι_Round ) (l: Ledger) , 
    eval_state (RoundsBase_Ф_toTruncatedRound Л_round ) l = 
    RoundsBase_ι_TruncatedRoundC (Л_round ->> RoundsBase_ι_Round_ι_id)
                                 (Л_round ->> RoundsBase_ι_Round_ι_supposedElectedAt)
                                 (Л_round ->> RoundsBase_ι_Round_ι_unfreeze)
                                 (Л_round ->> RoundsBase_ι_Round_ι_stakeHeldFor)
                                 (Л_round ->> RoundsBase_ι_Round_ι_vsetHashInElectionPhase)
                                 (Л_round ->> RoundsBase_ι_Round_ι_step)
                                 (Л_round ->> RoundsBase_ι_Round_ι_completionReason)
                                 (Л_round ->> RoundsBase_ι_Round_ι_stake)
                                 (Л_round ->> RoundsBase_ι_Round_ι_recoveredStake)
                                 (Л_round ->> RoundsBase_ι_Round_ι_unused)
                                 (Л_round ->> RoundsBase_ι_Round_ι_isValidatorStakeCompleted)
                                 (Л_round ->> RoundsBase_ι_Round_ι_rewards)
                                 (Л_round ->> RoundsBase_ι_Round_ι_participantQty)
                                 (Л_round ->> RoundsBase_ι_Round_ι_validatorStake)
                                 (Л_round ->> RoundsBase_ι_Round_ι_validatorRemainingStake)
                                 (Л_round ->> RoundsBase_ι_Round_ι_handledStakesAndRewards).
 Proof. 
   intros. destruct l. auto. 
 Qed. 


Opaque hmapLookup Z.add Z.eqb hmapInsert. 

Lemma RoundsBase_Ф__addStakes'_exec : forall  (Л_round : RoundsBase_ι_Round ) 
                                             (Л_participant : DePoolLib_ι_Participant ) 
                                             (Л_participantAddress : Z ) 
                                             (Л_stake : Z ) 
                                             (Л_vesting: option RoundsBase_ι_InvestParams) 
                                             (Л_lock: option RoundsBase_ι_InvestParams) 
                                             (l: Ledger) ,                                            
exec_state (↓ (RoundsBase_Ф__addStakes' Л_round Л_participant Л_participantAddress Л_stake Л_vesting Л_lock) ) l  = l.
Proof.
  intros.
  destruct l. 
  compute.

  Time repeat (
  
  
  match goal with
    | |- ?x =>
      match x with
        | context [if ?b then _ else _] =>  repeat rewrite ifSimpleState ; 
                                            repeat rewrite ifFunApply ;
                                            (* let rem := fresh "rem" in  *)
                                            (* set (rem:= b) ;  *)
                                            case b (* compute; auto *)
        | _ => auto
      end
  end).

Qed. 

Lemma RoundsBase_Ф__addStakes_exec : forall  (Л_round : RoundsBase_ι_Round ) 
                                             (Л_participant : DePoolLib_ι_Participant ) 
                                             (Л_participantAddress : Z ) 
                                             (Л_stake : Z ) 
                                             (Л_vesting: option RoundsBase_ι_InvestParams) 
                                             (Л_lock: option RoundsBase_ι_InvestParams) 
                                             (l: Ledger) ,                                            
exec_state (↓ (RoundsBase_Ф__addStakes Л_round Л_participant Л_participantAddress Л_stake Л_vesting Л_lock) ) l  = l.
Proof.
  intros.
  Opaque RoundsBase_Ф__addStakes'.
  assert (exec_state
  (↓ RoundsBase_Ф__addStakes Л_round Л_participant Л_participantAddress
       Л_stake Л_vesting Л_lock) l = exec_state
       (↓ RoundsBase_Ф__addStakes' Л_round Л_participant Л_participantAddress
            Л_stake Л_vesting Л_lock) l).
  unfold   RoundsBase_Ф__addStakes.
  unfold callEmbeddedStateAdj.
  unfold fromValueValue.
  remember (RoundsBase_Ф__addStakes' Л_round Л_participant Л_participantAddress
  Л_stake Л_vesting Л_lock).
  setoid_rewrite runbind.
  setoid_rewrite exec_bind.
  rewrite eval_get.
  rewrite exec_get.
  remember (run l0 (injEmbed (T:=LocalState) DePoolFuncs.DePoolSpec.LedgerClass.local0 l)).
  
  setoid_rewrite <- Heqp.
  destruct p.
  destruct x.
  auto. auto.
  rewrite H.
  rewrite RoundsBase_Ф__addStakes'_exec.
  auto.
Qed.  


Transparent RoundsBase_Ф__addStakes'.

(*  
Definition RoundsBase_Ф__addStakes (Л_round : RoundsBase_ι_Round )
                                  (Л_participant : DePoolLib_ι_Participant ) 
                                  (Л_participantAddress: XAddress) 
                                  (Л_stake: XInteger64) 
                                  (Л_vesting: XMaybe RoundsBase_ι_InvestParams) 
                                  (Л_lock: XMaybe RoundsBase_ι_InvestParams) 
                            : LedgerT  ( RoundsBase_ι_Round # DePoolLib_ι_Participant)   :=  							   
do r ← RoundsBase_Ф__addStakes' Л_round Л_participant Л_participantAddress Л_stake Л_vesting Л_lock;
  return! (fromValueValue r).
*)

Lemma RoundsBase_Ф__addStakes'_eval : forall ( Л_round : RoundsBase_ι_Round ) 
                                             ( Л_participant : DePoolLib_ι_Participant ) 
                                             ( Л_participantAddress : XAddress ) 
                                             ( Л_stake : XInteger64 ) 
                                             ( Л_vesting: XMaybe RoundsBase_ι_InvestParams) 
                                             ( Л_lock: XMaybe RoundsBase_ι_InvestParams) 
                                           (* paexists lstake *)
                                             (l: Ledger) , 
let stakeZero := ( Л_stake =? 0 ) in
let oPart := ( hmapLookup Z.eqb Л_participantAddress (Л_round ->> RoundsBase_ι_Round_ι_stakes) ) in

let round_participantQty := if ( negb (xMaybeIsSome oPart) : bool )
                            then Л_round ->> RoundsBase_ι_Round_ι_participantQty + 1
                            else Л_round ->> RoundsBase_ι_Round_ι_participantQty in
let participant_roundQty := if ( negb (xMaybeIsSome oPart) : bool )
                            then Л_participant ->> DePoolLib_ι_Participant_ι_roundQty + 1
                            else Л_participant ->> DePoolLib_ι_Participant_ι_roundQty in
        
let participant_haveVesting := ( ( xMaybeIsSome Л_vesting : bool  ) ||  (Л_participant ->> DePoolLib_ι_Participant_ι_haveVesting))%bool in
let participant_haveLock := (( xMaybeIsSome Л_lock : bool  ) || (Л_participant ->> DePoolLib_ι_Participant_ι_haveLock))%bool in

let round_stake := Л_round ->> RoundsBase_ι_Round_ι_stake + Л_stake in
let round_stake := if ( xMaybeIsSome Л_vesting : bool  )
                   then round_stake + ( ( maybeGet Л_vesting ) ->> RoundsBase_ι_InvestParams_ι_amount )
                   else round_stake in
let round_stake := if ( xMaybeIsSome Л_lock : bool  )
                   then round_stake + ( ( maybeGet Л_lock ) ->> RoundsBase_ι_InvestParams_ι_amount )
                   else round_stake in

let sv := ( Л_round ->> RoundsBase_ι_Round_ι_stakes ) [ Л_participantAddress ] in
let sv_vesting := if ( xMaybeIsSome Л_vesting : bool )
                  then Л_vesting
                  else sv ->> RoundsBase_ι_StakeValue_ι_vesting in
let sv_lock := if ( xMaybeIsSome Л_lock : bool )
               then Л_lock
               else sv ->> RoundsBase_ι_StakeValue_ι_lock in

let sv_ordinary := ( sv ->> RoundsBase_ι_StakeValue_ι_ordinary ) + Л_stake in
let sv := {$ sv with ( RoundsBase_ι_StakeValue_ι_ordinary , sv_ordinary ) ;
                     ( RoundsBase_ι_StakeValue_ι_vesting , sv_vesting ) ;
                     ( RoundsBase_ι_StakeValue_ι_lock , sv_lock ) $} in
let participant := {$ Л_participant with 
                             ( DePoolLib_ι_Participant_ι_roundQty , participant_roundQty ) ;
                             ( DePoolLib_ι_Participant_ι_haveVesting , participant_haveVesting ) ;
                             ( DePoolLib_ι_Participant_ι_haveLock , participant_haveLock )
                            $} in
let round_stakes := Л_round ->> RoundsBase_ι_Round_ι_stakes in                            
let round := {$ Л_round with ( RoundsBase_ι_Round_ι_participantQty , round_participantQty ) ; 
                             ( RoundsBase_ι_Round_ι_stake ,          round_stake ) ; 
                             ( RoundsBase_ι_Round_ι_stakes ,         round_stakes [ Л_participantAddress ] ←  sv ) $} in

eval_state ( ↓ (RoundsBase_Ф__addStakes' Л_round Л_participant Л_participantAddress 
                                       Л_stake Л_vesting     Л_lock) ) l = (* xError ( [( Л_round , Л_participant )] ). *)

if ( stakeZero && ( negb ( xMaybeIsSome Л_vesting : bool ) ) &&  ( negb ( xMaybeIsSome Л_lock : bool ) ) )%bool
then xError ( Л_round , Л_participant )
else 
     xValue ( round , participant ) .
Proof.
  intros.
  destruct l. 
  compute. idtac.

 do 5 (
  
  
  match goal with
    | |- ?x =>
      match x with
        | context [if ?b then _ else _] =>  repeat rewrite ifSimpleState ; 
                                            repeat rewrite ifFunApply ;
                                            compute ;
                                            (* let rem := fresh "rem" in  *)
                                            (* set (rem:= b) ;  *)
                                            case_eq b ; intros (* compute; auto *)
        | _ => auto
      end
  end) . idtac.

  all: destruct Л_round; destruct Л_lock; destruct Л_vesting; destruct (Л_stake =? 0); destruct (hmapLookup Z.eqb Л_participantAddress RoundsBase_ι_Round_ι_stakes);  try discriminate.
  
  all: enough (forall X Y (a b: X), a = b -> Value (B:=Y) a = Value b) as H100.
  all: try apply H100.
  all: try apply pairEq; compute; auto.
  all: try apply RoundEq; compute; auto.
  all: try  destruct Л_participant; auto.

  all: intros; congruence.

Qed.





 (* 

function stakeSum(StakeValue stakes) internal inline returns (uint64) {
    optional(InvestParams) v = stakes.vesting;
    optional(InvestParams) l = stakes.lock;
    return
        stakes.ordinary +
        (v.hasValue() ? v.get().amount : 0) +
        (l.hasValue() ? l.get().amount : 0);
}
 *)

(*  Definition RoundsBase_Ф_stakeSum ( Л_stakes : RoundsBase_ι_StakeValue ) : LedgerT XInteger64 := 
    U0! Л_v :=  D0! Л_stakes ^^ RoundsBase_ι_StakeValue_ι_vesting ;
    U0! Л_l :=  D0! Л_stakes ^^ RoundsBase_ι_StakeValue_ι_lock ; 
    
    D0! Л_stakes ^^ RoundsBase_ι_StakeValue_ι_ordinary !+
       ( (( $ Л_v ->hasValue ) ) ?  (  D1! ( $ Л_v ->get ) ^^ RoundsBase_ι_InvestParams_ι_amount ) ::: $ xInt0 ) !+
       ( (( $ Л_l ->hasValue ) ) ?  (  D1! ( $ Л_l ->get ) ^^ RoundsBase_ι_InvestParams_ι_amount ) ::: $ xInt0 ) .

 *)

Lemma RoundsBase_Ф_stakeSum_exec : forall (stakes: RoundsBase_ι_StakeValue) 
                                          (l: Ledger) , 
    exec_state (↓ RoundsBase_Ф_stakeSum stakes) l = l .
Proof.
  intros.
  destruct l. compute. 
  repeat destructIf; auto.    
Qed.

Lemma RoundsBase_Ф_stakeSum_eval : forall (stakes: RoundsBase_ι_StakeValue) 
                                          (l: Ledger) , 
let ordStake := RoundsBase_ι_StakeValue_ι_ordinary stakes in
let vestingStake := RoundsBase_ι_InvestParams_ι_amount (maybeGet (RoundsBase_ι_StakeValue_ι_vesting stakes)) in
let lockStake := RoundsBase_ι_InvestParams_ι_amount (maybeGet (RoundsBase_ι_StakeValue_ι_lock stakes)) in                                                                
    eval_state (↓ RoundsBase_Ф_stakeSum stakes) l = ordStake + vestingStake + lockStake.
Proof.
  intros.
  destruct l. compute. 
  destruct stakes;
  destruct RoundsBase_ι_StakeValue_ι_vesting;
  destruct RoundsBase_ι_StakeValue_ι_lock; try lia.
Qed.

Lemma RoundsBase_Ф_stakeSum_run : forall (stakes: RoundsBase_ι_StakeValue) 
                                          (l: Ledger) , 
let ordStake := RoundsBase_ι_StakeValue_ι_ordinary stakes in
let vestingStake := RoundsBase_ι_InvestParams_ι_amount (maybeGet (RoundsBase_ι_StakeValue_ι_vesting stakes)) in
let lockStake := RoundsBase_ι_InvestParams_ι_amount (maybeGet (RoundsBase_ι_StakeValue_ι_lock stakes)) in                                                                
    run (↓ RoundsBase_Ф_stakeSum stakes) l = (ordStake + vestingStake + lockStake, l).
Proof.
  intros.
  rewrite run_eval_exec.
  rewrite RoundsBase_Ф_stakeSum_eval ,  RoundsBase_Ф_stakeSum_exec.
  auto.    
Qed.



(* 
function withdrawStakeInPoolingRound(
        DePoolLib.Participant participant,
        address participantAddress,
        uint64 targetAmount,
        uint64 minStake
    )
        internal inline returns (uint64, DePoolLib.Participant)
    {
        Round round = getRound0();
        optional(StakeValue) optSv = round.stakes.fetch(participantAddress);
        if (!optSv.hasValue()) {
            return (0, participant);
        }
        StakeValue sv = optSv.get();
        targetAmount = math.min(targetAmount, sv.ordinary);
        sv.ordinary -= targetAmount;
        round.stake -= targetAmount;
        if (sv.ordinary < minStake) {
            round.stake -= sv.ordinary;
            targetAmount += sv.ordinary;
            sv.ordinary = 0;
        }

        if (stakeSum(sv) == 0) {
            --round.participantQty;
            delete round.stakes[participantAddress];
            --participant.roundQty;
        } else {
            round.stakes[participantAddress] = sv;
        }
        setRound0(round);
        return (targetAmount, participant);
    }

 *)

(* Definition RoundsBase_Ф_withdrawStakeInPoolingRound'' (Л_participant : DePoolLib_ι_Participant ) 
													(Л_participantAddress : XAddress)
													(Л_targetAmount : XInteger64)
													(Л_minStake : XInteger64) : LedgerT ( XValueValue (XInteger64 # DePoolLib_ι_Participant) )  := 
(↑17 U1! LocalState_ι_withdrawStakeInPoolingRound_Л_targetAmount := $ Л_targetAmount) >>
(↑17 U1! LocalState_ι_withdrawStakeInPoolingRound_Л_participant := $ Л_participant)  >>
(↑↑17 U2! LocalState_ι_withdrawStakeInPoolingRound_Л_round := RoundsBase_Ф_getRound0 () ) >>
U0! Л_optSv := (D1! (↑17 D2! LocalState_ι_withdrawStakeInPoolingRound_Л_round ^^ RoundsBase_ι_Round_ι_stakes) ->fetch $ Л_participantAddress) ;
 If! ( !¬ ($ Л_optSv) ->hasValue ) then {
     return! (xError ( [( xInt0, Л_participant )] ) ) 
 } ;
(↑17 U1! LocalState_ι_withdrawStakeInPoolingRound_Л_sv := ($ Л_optSv) ->get) >>
(↑17 U1! LocalState_ι_withdrawStakeInPoolingRound_Л_targetAmount := math->min2 (! ε LocalState_ι_withdrawStakeInPoolingRound_Л_targetAmount ,
                                                                                 D2! LocalState_ι_withdrawStakeInPoolingRound_Л_sv ^^ RoundsBase_ι_StakeValue_ι_ordinary !) ) >>
(↑17 U1! LocalState_ι_withdrawStakeInPoolingRound_Л_sv ^^ RoundsBase_ι_StakeValue_ι_ordinary !-= ε LocalState_ι_withdrawStakeInPoolingRound_Л_targetAmount) >>
(↑17 U1! LocalState_ι_withdrawStakeInPoolingRound_Л_round ^^ RoundsBase_ι_Round_ι_stake !-= ε LocalState_ι_withdrawStakeInPoolingRound_Л_targetAmount) >>
(If (↑17 D2! LocalState_ι_withdrawStakeInPoolingRound_Л_sv ^^ RoundsBase_ι_StakeValue_ι_ordinary ?< $ Л_minStake ) then {
	(↑17 U1! LocalState_ι_withdrawStakeInPoolingRound_Л_round ^^ RoundsBase_ι_Round_ι_stake !-= D1! (ε LocalState_ι_withdrawStakeInPoolingRound_Л_sv) ^^  RoundsBase_ι_StakeValue_ι_ordinary) >>
	(↑17 U1! LocalState_ι_withdrawStakeInPoolingRound_Л_targetAmount !+= D1! (ε LocalState_ι_withdrawStakeInPoolingRound_Л_sv) ^^  RoundsBase_ι_StakeValue_ι_ordinary) >>
	(↑17 U1! LocalState_ι_withdrawStakeInPoolingRound_Л_sv ^^ RoundsBase_ι_StakeValue_ι_ordinary := $ xInt0 )
}) >>
(If (RoundsBase_Ф_stakeSum (! ↑ε17 LocalState_ι_withdrawStakeInPoolingRound_Л_sv  !) ?== $xInt0 ) then {
	(↑17 U1! LocalState_ι_withdrawStakeInPoolingRound_Л_round ^^ RoundsBase_ι_Round_ι_participantQty !--) >>
	(↑17 U1! delete LocalState_ι_withdrawStakeInPoolingRound_Л_round ^^ RoundsBase_ι_Round_ι_stakes [[ $ Л_participantAddress ]] ) >>
	(↑17 U1! LocalState_ι_withdrawStakeInPoolingRound_Л_participant ^^ DePoolLib_ι_Participant_ι_roundQty !--)
} else {
	(↑17 U1! LocalState_ι_withdrawStakeInPoolingRound_Л_round ^^ RoundsBase_ι_Round_ι_stakes [[ $ Л_participantAddress ]] := ε LocalState_ι_withdrawStakeInPoolingRound_Л_sv)
}) >>
(RoundsBase_Ф_setRound0 (! ↑17 D2! LocalState_ι_withdrawStakeInPoolingRound_Л_round !)) >>
return#  ( ↑ε17 LocalState_ι_withdrawStakeInPoolingRound_Л_targetAmount , ↑ε17 LocalState_ι_withdrawStakeInPoolingRound_Л_participant ).   *)

(* Definition RoundsBase_Ф_withdrawStakeInPoolingRound (Л_participant : DePoolLib_ι_Participant ) 
													                          (Л_participantAddress : XAddress)
													                          (Л_targetAmount : XInteger64)
													                          (Л_minStake : XInteger64) 
                                         : LedgerT  (XInteger64 # DePoolLib_ι_Participant) := 
do r ← RoundsBase_Ф_withdrawStakeInPoolingRound' Л_participant Л_participantAddress Л_targetAmount 	Л_minStake	;
return! (fromValueValue r). *)		 					

Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair.
 
Opaque Z.ltb Z.sub intMin deleteListPair intMax.



Lemma RoundsBase_Ф_transferStakeInOneRound'_exec : forall ( Л_round : RoundsBase_ι_Round ) 
                                                         ( Л_sourceParticipant : DePoolLib_ι_Participant ) 
                                                         ( Л_destinationParticipant : DePoolLib_ι_Participant ) 
                                                         ( Л_source : XAddress ) 
                                                         ( Л_destination : XAddress ) 
                                                         ( Л_amount : XInteger64 ) 
                                                         ( Л_minStake : XInteger64 ) 
                                                         (l: Ledger) , 
 	 exec_state (↓ RoundsBase_Ф_transferStakeInOneRound' Л_round Л_sourceParticipant Л_destinationParticipant Л_source Л_destination Л_amount Л_minStake ) l = l .  
Proof. 
  intros.
  destruct l. 
  compute.
  (* all: try pr_numgoals. *)

  Time repeat (
  
  
  match goal with
    | |- ?x =>
      match x with
        | context [if ?b then _ else _] =>  repeat rewrite ifSimpleState ; 
                                            repeat rewrite ifFunApply ;
                                            (* let rem := fresh "rem" in  *)
                                            (* set (rem:= b) ;  *)
                                            time case b (* compute; auto *)
        | _ => idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
      end
  end).

Qed. 

 
Lemma RoundsBase_Ф_transferStakeInOneRound'_eval : forall ( Л_round : RoundsBase_ι_Round ) 
                                                   ( Л_sourceParticipant : DePoolLib_ι_Participant ) 
                                                   ( Л_destinationParticipant : DePoolLib_ι_Participant ) 
                                                   ( Л_source : XAddress ) 
                                                   ( Л_destination : XAddress ) 
                                                   ( Л_amount : XInteger64 ) 
                                                   ( Л_minStake : XInteger64 ) 
                                                   (l: Ledger) ,
let optSourceStake :=  ( Л_round ->> RoundsBase_ι_Round_ι_stakes ) ->fetch Л_source in
let optSourceStake_hasValue := xMaybeIsSome optSourceStake in 
let round := Л_round in 
let sourceParticipant := Л_sourceParticipant in
let destinationParticipant := Л_destinationParticipant in 
let source := Л_source in
let destination := Л_destination in
let amount := Л_amount in
let minStake := Л_minStake in             
  
let sourceStake :=  ( maybeGet optSourceStake ) in

let round_stakes := round ->> RoundsBase_ι_Round_ι_stakes in
let prevSource_source := round_stakes [ source ] in
let prevSourceStake := prevSource_source ->> RoundsBase_ι_StakeValue_ι_ordinary in
let newSourceStake := if ( ( sourceStake ->> RoundsBase_ι_StakeValue_ι_ordinary ) >=? amount )                                                 
                      then ( sourceStake ->> RoundsBase_ι_StakeValue_ι_ordinary ) - amount 
                      else 0 in
let deltaDestinationStake := if ( ( sourceStake ->> RoundsBase_ι_StakeValue_ι_ordinary ) >=? amount )
                             then amount
                             else sourceStake ->> RoundsBase_ι_StakeValue_ι_ordinary
                             in                            
let newDestStake := ( ( ( round ->> RoundsBase_ι_Round_ι_stakes ) [ destination ] ) ->> 
    RoundsBase_ι_StakeValue_ι_ordinary ) + deltaDestinationStake  in

let bReturn2 := ((0 <? newSourceStake) && (newSourceStake <? Л_minStake) ||   (0 <? newDestStake) && (newDestStake <? minStake))%bool in
    
let sourceStake := {$ sourceStake with ( RoundsBase_ι_StakeValue_ι_ordinary , newSourceStake ) $} in
let round_participantQty := round ->> RoundsBase_ι_Round_ι_participantQty in

let stakeSum := eval_state ( ↓ RoundsBase_Ф_stakeSum sourceStake ) l in
let round := {$ round with 
             ( RoundsBase_ι_Round_ι_participantQty , 
                      if ( stakeSum  =? 0 )
                      then round_participantQty - 1
                      else round_participantQty ) ;
             ( RoundsBase_ι_Round_ι_stakes , if (  stakeSum  =? 0 )
                                             then round_stakes ->delete source
                                             else round_stakes [ source ] ←  sourceStake ) $} in
let sourceParticipant_roundQty := sourceParticipant ->> DePoolLib_ι_Participant_ι_roundQty in
let sourceParticipant := {$ sourceParticipant with ( DePoolLib_ι_Participant_ι_roundQty , 
                              if (  stakeSum  =? 0 )
                              then sourceParticipant_roundQty - 1
                              else sourceParticipant_roundQty ) $} in
              
let round_stakes := round ->> RoundsBase_ι_Round_ι_stakes in
let round_stakes_destination := round_stakes [ destination ] in
let round_stakes_destination_ordinary := ( round_stakes_destination ->> RoundsBase_ι_StakeValue_ι_ordinary ) + deltaDestinationStake in
let round_participantQty := round ->> RoundsBase_ι_Round_ι_participantQty in
let round_stakes_exists_destination := hmapLookup Z.eqb destination round_stakes in

let round := {$ round with 
             ( RoundsBase_ι_Round_ι_participantQty , if ( negb (xMaybeIsSome round_stakes_exists_destination) : bool)
                                                     then round_participantQty + 1
                                                     else round_participantQty ) ;
             ( RoundsBase_ι_Round_ι_stakes , round_stakes [ destination ] ←  {$ round_stakes_destination with 
                            RoundsBase_ι_StakeValue_ι_ordinary := round_stakes_destination_ordinary $} ) $} in

let destinationParticipant_roundQty := destinationParticipant ->> DePoolLib_ι_Participant_ι_roundQty in
let destinationParticipant := {$ destinationParticipant with ( DePoolLib_ι_Participant_ι_roundQty , 
                                                     if (negb (xMaybeIsSome round_stakes_exists_destination) : bool)
                                                     then destinationParticipant_roundQty + 1
                                                     else destinationParticipant_roundQty ) $} in

eval_state (  ↓ (RoundsBase_Ф_transferStakeInOneRound' Л_round Л_sourceParticipant Л_destinationParticipant 
                                                   Л_source Л_destination Л_amount  Л_minStake ) ) l =

if ( negb ( optSourceStake_hasValue ) ) then 
     Error ( Л_round , 0 , 0 , Л_sourceParticipant , Л_destinationParticipant ) 
else if ( bReturn2 ) then 
     Error (Л_round, 0, prevSourceStake, Л_sourceParticipant, Л_destinationParticipant) 
else 
     Value (round, deltaDestinationStake, prevSourceStake, sourceParticipant, destinationParticipant )  .
 Proof. 
 
  intros.
  destruct l. 
  compute. idtac.

  enough (forall X Y (a b: X), a = b -> Value (B:=Y) a = Value b) as H100.
  
 Time repeat (
  
  
  match goal with
    | |- ?x =>
      match x with
        | context [if ?b then _ else _] =>  repeat rewrite ifSimpleState ; 
                                            repeat rewrite ifFunApply ;
                                            (* compute ; *)
                                            (* let rem := fresh "rem" in  *)
                                            (* set (rem:= b) ;  *)
                                            time case_eq b ; intros (* compute; auto *)
        | _ => auto
      end
  end) . idtac.

  all: destruct Л_round. idtac.
  all: try apply H100.
  all: repeat (apply pairEq; simpl); auto. idtac. 
  all: destruct Л_destinationParticipant; auto. idtac.
  all: destruct Л_sourceParticipant; auto. idtac.

  
  intros. congruence.
 
 Qed.  


Opaque RoundsBase_Ф_stakeSum RoundsBase_Ф_setRound0.

Lemma RoundsBase_Ф_withdrawStakeInPoolingRound'_exec : forall (participant : DePoolLib_ι_Participant ) 
                                                              (participantAddress : XAddress)
                                                              (targetAmount : XInteger64)
                                                              (minStake : XInteger64) 
                                                              (l : Ledger) , 
exec_state (↓ RoundsBase_Ф_withdrawStakeInPoolingRound' participant participantAddress targetAmount minStake) l = 

(*     let oldRounds := eval_state (↑11 ε RoundsBase_ι_m_rounds) l in   *)
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

    let (stakeSum, l_sum) := run (↓ RoundsBase_Ф_stakeSum newsv) l in 
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
    if negb (isSome optsv) then l else l_set.
Proof. 

  intros. destruct l. 
  
  destruct Ledger_ι_DebugDePool, Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ConfigParamsBase, Ledger_ι_ParticipantBase, 
  Ledger_ι_DePoolHelper, Ledger_ι_Errors, Ledger_ι_InternalErrors, Ledger_ι_DePoolLib, Ledger_ι_DePoolProxyContract, 
  Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_DePool, Ledger_ι_Participant, Ledger_ι_TestElector, 
  Ledger_ι_VMState, Ledger_ι_LocalState.

  compute; auto. idtac.

  Time repeat (
  
  time match goal with

    | |- ?x =>
      match x with
             
      | context [if ?b then _ else _] =>  idtac "if..." b; 
                                          repeat rewrite ifSimpleState ; 
                                          repeat rewrite ifFunApply ;                               
                                          case_eq b ; 
                                          (* simpl;  *)
                                          intros                                                              
      | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
      end

  end) . idtac.

  match goal with 
    | |- ?x  => match x with 
                | context [RoundsBase_Ф_stakeSum ?a] => remember (RoundsBase_Ф_stakeSum a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.

    match goal with 
    | |- ?x  => match x with 
                | context [RoundsBase_Ф_stakeSum ?a] => remember (RoundsBase_Ф_stakeSum a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.

    match goal with 
    | |- ?x  => match x with 
                | context [RoundsBase_Ф_stakeSum ?a] => remember (RoundsBase_Ф_stakeSum a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.

    destruct (x=?0); auto. idtac.

    match goal with 
    | |- ?x  => match x with 
                | context [RoundsBase_Ф_stakeSum ?a] => remember (RoundsBase_Ф_stakeSum a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.

    destruct (x=?0); auto. 
Qed.  



Lemma RoundsBase_Ф_withdrawStakeInPoolingRound'_eval : forall (participant : DePoolLib_ι_Participant ) 
                                                              (participantAddress : XAddress)
                                                              (targetAmount : XInteger64)
                                                              (minStake : XInteger64) 
                                                              (l : Ledger) , 
    eval_state (↓ RoundsBase_Ф_withdrawStakeInPoolingRound' participant participantAddress targetAmount minStake) l =

    let oldRound0 := eval_state RoundsBase_Ф_getRound0 l in                                                          
    let optsv := (oldRound0 ->> RoundsBase_ι_Round_ι_stakes) ->fetch participantAddress in 
    let oldsv := maybeGet optsv in
    
    let targetAmount' := intMin targetAmount (oldsv ->> RoundsBase_ι_StakeValue_ι_ordinary)  in 
    let newOrd := (oldsv ->> RoundsBase_ι_StakeValue_ι_ordinary) - targetAmount' in
    let restLessThanMin := (newOrd <? minStake) in
    let newOrd' := if restLessThanMin then 0 else newOrd in
    let targetAmount'' := if restLessThanMin then targetAmount' + newOrd else targetAmount' in
    let newsv := {$ oldsv with RoundsBase_ι_StakeValue_ι_ordinary := newOrd' $} in

    let (stakeSum, _) := run (↓ RoundsBase_Ф_stakeSum newsv) l in 
    let emptyStake := (stakeSum =? 0) in

    let newParticipantRoundQty := if emptyStake then ((participant ->> DePoolLib_ι_Participant_ι_roundQty) -1) else
                                                      (participant ->> DePoolLib_ι_Participant_ι_roundQty) in                                                  
 
    let newParticipant := {$ participant with DePoolLib_ι_Participant_ι_roundQty := newParticipantRoundQty $} in      
    
    
     
    if negb (isSome optsv) then Error (0, participant) 
                           else Value ( targetAmount'' , newParticipant ).                                             
Proof. 

  intros. destruct l. 
  
  destruct Ledger_ι_DebugDePool, Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ConfigParamsBase, Ledger_ι_ParticipantBase, 
  Ledger_ι_DePoolHelper, Ledger_ι_Errors, Ledger_ι_InternalErrors, Ledger_ι_DePoolLib, Ledger_ι_DePoolProxyContract, 
  Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_DePool, Ledger_ι_Participant, Ledger_ι_TestElector, 
  Ledger_ι_VMState, Ledger_ι_LocalState.

  compute; auto. idtac.

  Time repeat (
  
  time match goal with

    | |- ?x =>
      match x with
             
      | context [if ?b then _ else _] =>  idtac "if..." b; 
                                          repeat rewrite ifSimpleState ; 
                                          repeat rewrite ifFunApply ;                               
                                          case_eq b ; 
                                          (* simpl;  *)
                                          intros                                                              
      | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
      end

  end) . idtac.

  match goal with 
    | |- ?x  => match x with 
                | context [RoundsBase_Ф_stakeSum ?a] => remember (RoundsBase_Ф_stakeSum a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.

    match goal with 
    | |- ?x  => match x with 
                | context [RoundsBase_Ф_stakeSum ?a] => remember (RoundsBase_Ф_stakeSum a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.

    match goal with 
    | |- ?x  => match x with 
                | context [RoundsBase_Ф_stakeSum ?a] => remember (RoundsBase_Ф_stakeSum a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.

    destruct (x=?0); auto. idtac.

    match goal with 
    | |- ?x  => match x with 
                | context [RoundsBase_Ф_setRound0 ?a] => remember (RoundsBase_Ф_setRound0 a ) as l1
                end
    end.
    destruct l1.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p0 ?a] => remember (p0 a)
                end
    end.
  
    destruct p1; auto.
    destruct participant; auto.

    match goal with 
    | |- ?x  => match x with 
                | context [RoundsBase_Ф_stakeSum ?a] => remember (RoundsBase_Ф_stakeSum a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.

    destruct (x=?0); auto. 

    match goal with 
    | |- ?x  => match x with 
                | context [RoundsBase_Ф_setRound0 ?a] => remember (RoundsBase_Ф_setRound0 a ) as l1
                end
    end.
    destruct l1.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p0 ?a] => remember (p0 a)
                end
    end.
  
    destruct p1; auto.
    destruct participant; auto.

Qed.

Opaque RoundsBase_Ф_withdrawStakeInPoolingRound'.

Lemma RoundsBase_Ф_withdrawStakeInPoolingRound_exec : forall (participant : DePoolLib_ι_Participant ) 
                                                              (participantAddress : XAddress)
                                                              (targetAmount : XInteger64)
                                                              (minStake : XInteger64) 
                                                              (l : Ledger) , 
   exec_state (↓ RoundsBase_Ф_withdrawStakeInPoolingRound participant participantAddress targetAmount minStake) l = 

(*     let oldRounds := eval_state (↑11 ε RoundsBase_ι_m_rounds) l in   *)
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

    let (stakeSum, l_sum) := run (↓ RoundsBase_Ф_stakeSum newsv) l in 
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
    if negb (isSome optsv) then l else l_set.
Proof.
  
  intros.
  assert (exec_state (↓ RoundsBase_Ф_withdrawStakeInPoolingRound participant participantAddress targetAmount minStake) l = 
  exec_state (↓ RoundsBase_Ф_withdrawStakeInPoolingRound' participant participantAddress targetAmount minStake) l).
  unfold  RoundsBase_Ф_withdrawStakeInPoolingRound.
  unfold callEmbeddedStateAdj.
  unfold fromValueValue.
  remember (RoundsBase_Ф_withdrawStakeInPoolingRound' participant participantAddress targetAmount minStake).
  setoid_rewrite runbind.
  setoid_rewrite exec_bind.
  rewrite eval_get.
  rewrite exec_get.
  remember (run l0 (injEmbed (T:=LocalState) DePoolFuncs.DePoolSpec.LedgerClass.local0 l)).
  setoid_rewrite <- Heqp.
  destruct p.
  destruct x.
  auto. auto.
  rewrite H.
  rewrite RoundsBase_Ф_withdrawStakeInPoolingRound'_exec.
  auto.
Qed.

Lemma if_fromValueValue: forall X (b: bool) (x y: XValueValue X),
fromValueValue (if b then x else y) = if b then (fromValueValue x) else (fromValueValue y).
Proof.
  intros.
  destruct b; auto.
  
Qed.

Lemma let_fromValueValue: forall X Y (f: X -> XValueValue Y) x,
fromValueValue (let a := x in f a) = fromValueValue (f x).
Proof.
  intros.
  auto.
  
Qed.


Lemma RoundsBase_Ф_withdrawStakeInPoolingRound_eval : forall (participant : DePoolLib_ι_Participant ) 
                                                              (participantAddress : XAddress)
                                                              (targetAmount : XInteger64)
                                                              (minStake : XInteger64) 
                                                              (l : Ledger) , 
        eval_state (↓ RoundsBase_Ф_withdrawStakeInPoolingRound participant participantAddress targetAmount minStake) l =
  

    let oldRound0 := eval_state RoundsBase_Ф_getRound0 l in                                                          
    let optsv := (oldRound0 ->> RoundsBase_ι_Round_ι_stakes) ->fetch participantAddress in 
    let oldsv := maybeGet optsv in
    
    let targetAmount' := intMin targetAmount (oldsv ->> RoundsBase_ι_StakeValue_ι_ordinary)  in 
    let newOrd := (oldsv ->> RoundsBase_ι_StakeValue_ι_ordinary) - targetAmount' in
    let restLessThanMin := (newOrd <? minStake) in
    let newOrd' := if restLessThanMin then 0 else newOrd in
    let targetAmount'' := if restLessThanMin then targetAmount' + newOrd else targetAmount' in
    let newsv := {$ oldsv with RoundsBase_ι_StakeValue_ι_ordinary := newOrd' $} in

    let (stakeSum, _) := run (↓ RoundsBase_Ф_stakeSum newsv) l in 
    let emptyStake := (stakeSum =? 0) in

    let newParticipantRoundQty := if emptyStake then ((participant ->> DePoolLib_ι_Participant_ι_roundQty) -1) else
                                                      (participant ->> DePoolLib_ι_Participant_ι_roundQty) in                                                  
 
    let newParticipant := {$ participant with DePoolLib_ι_Participant_ι_roundQty := newParticipantRoundQty $} in      
    
    
   
    if negb (isSome optsv) then  (0, participant) 
                           else  ( targetAmount'' , newParticipant ).
 Proof.
  intros.
  assert (eval_state (↓ RoundsBase_Ф_withdrawStakeInPoolingRound participant participantAddress targetAmount minStake) l = 
  fromValueValue (eval_state (↓ RoundsBase_Ф_withdrawStakeInPoolingRound' participant participantAddress targetAmount minStake) l)).
  unfold  RoundsBase_Ф_withdrawStakeInPoolingRound.
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
  rewrite H.
  rewrite RoundsBase_Ф_withdrawStakeInPoolingRound'_eval.
  Opaque fromValueValue.
  compute. idtac.
  match goal with 
    | |- ?x  => match x with 
                | context [RoundsBase_Ф_stakeSum ?a] => remember (RoundsBase_Ф_stakeSum a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
  repeat rewrite if_fromValueValue.
  auto.  
 Qed.
 
Transparent RoundsBase_Ф_withdrawStakeInPoolingRound'.

(* 
function transferStakeInOneRound(
        Round round,
        DePoolLib.Participant sourceParticipant,
        DePoolLib.Participant destinationParticipant,
        address source,
        address destination,
        uint64 amount,
        uint64 minStake
    )
        internal inline
        returns (
            Round, // updated round
            uint64, // transferred value
            uint64, // prev ordinary stake of source
            DePoolLib.Participant, // updated source participant
            DePoolLib.Participant // updated destination participant
        )
    {
        optional(StakeValue) optSourceStake = round.stakes.fetch(source);
        if (!optSourceStake.hasValue())
            return (round, 0, 0, sourceParticipant, destinationParticipant);
        StakeValue sourceStake = optSourceStake.get();
        uint64 prevSourceStake = round.stakes[source].ordinary;
        uint64 newSourceStake;
        uint64 deltaDestinationStake;
        if (sourceStake.ordinary >= amount) {
            newSourceStake = sourceStake.ordinary - amount;
            deltaDestinationStake = amount;
        } else {
            newSourceStake = 0;
            deltaDestinationStake = sourceStake.ordinary;
        }


        uint64 newDestStake = round.stakes[destination].ordinary + deltaDestinationStake;
        if ((0 < newSourceStake && newSourceStake < minStake) ||
            (0 < newDestStake && newDestStake < minStake)) {
            return (round, 0, prevSourceStake, sourceParticipant, destinationParticipant);
        }

        sourceStake.ordinary = newSourceStake;
        if (stakeSum(sourceStake) == 0) {
            --round.participantQty;
            delete round.stakes[source];
            --sourceParticipant.roundQty;
        } else {
            round.stakes[source] = sourceStake;
        }

        if (!round.stakes.exists(destination)) {
            ++round.participantQty;
            ++destinationParticipant.roundQty;
        }
        round.stakes[destination].ordinary += deltaDestinationStake;

        return (round, deltaDestinationStake, prevSourceStake, sourceParticipant, destinationParticipant);
    }
*)

(*Definition RoundsBase_Ф_transferStakeInOneRound' ( Л_round : RoundsBase_ι_Round )
                                     (Л_sourceParticipant: DePoolLib_ι_Participant) (Л_destinationParticipant: DePoolLib_ι_Participant)
(Л_source : XAddress) (Л_destination: XAddress) (Л_amount: XInteger64) (Л_minStake : XInteger64)
 : LedgerT ( XValueValue ( RoundsBase_ι_Round # XInteger64 # XInteger64 # DePoolLib_ι_Participant # DePoolLib_ι_Participant) ) :=

		(*initialize pseudo locals*)
		(↑17 U1! LocalState_ι_transferStakeInOneRound_Л_round := ($ Л_round) ) >>
		(↑17 U1! LocalState_ι_transferStakeInOneRound_Л_sourceParticipant := ($ Л_sourceParticipant) ) >>
		(↑17 U1! LocalState_ι_transferStakeInOneRound_Л_destinationParticipant := ($ Л_destinationParticipant) ) >> 
		(* optional(StakeValue) optSourceStake = round.stakes.fetch(source); *)
		U0! Л_optSourceStake := D1! (D0! Л_round ^^ RoundsBase_ι_Round_ι_stakes) ->fetch ($ Л_source) ;  
        (* if (!optSourceStake.hasValue())
			return (round, 0, 0, sourceParticipant, destinationParticipant); *)
		If!! ( !¬ ($ Л_optSourceStake ->hasValue) ) then {
			 return! (xError ( [( Л_round, xInt0, xInt0, Л_sourceParticipant, Л_destinationParticipant )] ) )
		}  ; 				   
		(* StakeValue sourceStake = optSourceStake.get(); *)
		(↑17 U1! LocalState_ι_transferStakeInOneRound_Л_sourceStake := ($ Л_optSourceStake ->get) ) >> 
		(* uint64 prevSourceStake = round.stakes[source].ordinary; *)
		U0! Л_prevSourceStake := (D1! (D1! (D0! Л_round ^^ RoundsBase_ι_Round_ι_stakes) [[ $ Л_source ]] ) ^^ RoundsBase_ι_StakeValue_ι_ordinary ) ; 
		(* uint64 newSourceStake; *)
		(* uint64 deltaDestinationStake; *)
		
        (* if (sourceStake.ordinary >= amount) {
            newSourceStake = sourceStake.ordinary - amount;
            deltaDestinationStake = amount;
        } else {
            newSourceStake = 0;
            deltaDestinationStake = sourceStake.ordinary;
		} *)  
		(If ( ↑17 D2! LocalState_ι_transferStakeInOneRound_Л_sourceStake ^^ RoundsBase_ι_StakeValue_ι_ordinary ?>= $  Л_amount) then {

		   (↑17 U1! LocalState_ι_transferStakeInOneRound_Л_newSourceStake := (D2! LocalState_ι_transferStakeInOneRound_Л_sourceStake ^^ RoundsBase_ι_StakeValue_ι_ordinary) !- ($ Л_amount))  >>
	 	   (↑17 U1! LocalState_ι_transferStakeInOneRound_Л_deltaDestinationStake := ($ Л_amount)) 
		 
		} else { 
			
		(↑17 U1! LocalState_ι_transferStakeInOneRound_Л_newSourceStake := $ xInt0 )  >>
		(↑17 U1! LocalState_ι_transferStakeInOneRound_Л_deltaDestinationStake := D2! LocalState_ι_transferStakeInOneRound_Л_sourceStake ^^ RoundsBase_ι_StakeValue_ι_ordinary) 
 
		}) >> 
		(* uint64 newDestStake = round.stakes[destination].ordinary + deltaDestinationStake; *)
		U0! Л_newDestStake := (D1! (D1! ( ↑17 D2! LocalState_ι_transferStakeInOneRound_Л_round ^^ RoundsBase_ι_Round_ι_stakes) [[ $ Л_destination ]] ) ^^ RoundsBase_ι_StakeValue_ι_ordinary) 
		                      !+ ( ↑ε17 LocalState_ι_transferStakeInOneRound_Л_deltaDestinationStake  );


        (* if ((0 < newSourceStake && newSourceStake < minStake) ||
            (0 < newDestStake && newDestStake < minStake)) {
            return (round, 0, prevSourceStake, sourceParticipant, destinationParticipant);
		} *)
		If! ((($ xInt0 ?< (↑ε17 LocalState_ι_transferStakeInOneRound_Л_newSourceStake))!&
			((↑ε17 LocalState_ι_transferStakeInOneRound_Л_newSourceStake) ?< $ Л_minStake)) !| 
			 (($ xInt0 ?< $ Л_newDestStake) !& ($ Л_newDestStake ?< $ Л_minStake) )) then {
			return! (xError ( [( Л_round, xInt0, Л_prevSourceStake, Л_sourceParticipant, Л_destinationParticipant )] ))
		}; 

		(* sourceStake.ordinary = newSourceStake; *)
		(↑17 U1! LocalState_ι_transferStakeInOneRound_Л_sourceStake ^^ RoundsBase_ι_StakeValue_ι_ordinary := ε LocalState_ι_transferStakeInOneRound_Л_newSourceStake) >>
		
        (* if (stakeSum(sourceStake) == 0) {
            --round.participantQty;
            delete round.stakes[source];
            --sourceParticipant.roundQty;
        } else {
            round.stakes[source] = sourceStake;
		} *)
		
		( If (RoundsBase_Ф_stakeSum (! ↑ε17 LocalState_ι_transferStakeInOneRound_Л_sourceStake !) ?== $ xInt0) then 
		{ 
			(↑17 U1! LocalState_ι_transferStakeInOneRound_Л_round ^^ RoundsBase_ι_Round_ι_participantQty !--)   >> 
		 ( ↑17 U1! delete LocalState_ι_transferStakeInOneRound_Л_round ^^ RoundsBase_ι_Round_ι_stakes [[ $ Л_source ]] ) >>
			(↑17 U1! LocalState_ι_transferStakeInOneRound_Л_sourceParticipant ^^ DePoolLib_ι_Participant_ι_roundQty !--) 
		 } else {
			 (↑17 U1! LocalState_ι_transferStakeInOneRound_Л_round ^^ RoundsBase_ι_Round_ι_stakes [[ $ Л_source ]] := ε LocalState_ι_transferStakeInOneRound_Л_sourceStake)
		} ) >>

        (* if (!round.stakes.exists(destination)) {
            ++round.participantQty;
            ++destinationParticipant.roundQty;
		} *)

		(If ( !¬ (D1! (↑17 D2! LocalState_ι_transferStakeInOneRound_Л_round ^^ RoundsBase_ι_Round_ι_stakes) ->exists $ Л_destination ) ) then {
			(↑17 U1! LocalState_ι_transferStakeInOneRound_Л_round ^^ RoundsBase_ι_Round_ι_participantQty !++) >>
			(↑17 U1! LocalState_ι_transferStakeInOneRound_Л_destinationParticipant ^^ DePoolLib_ι_Participant_ι_roundQty !++)
		} ) >>
		
		(*round.stakes[destination].ordinary += deltaDestinationStake;*)
		(↑17 U1! LocalState_ι_transferStakeInOneRound_Л_round ^^ RoundsBase_ι_Round_ι_stakes [[ $ Л_destination ]] ^^ RoundsBase_ι_StakeValue_ι_ordinary !+= ε LocalState_ι_transferStakeInOneRound_Л_deltaDestinationStake) >>
		
		(*return (round, deltaDestinationStake, prevSourceStake, sourceParticipant, destinationParticipant);*)
		return# (↑ε17 LocalState_ι_transferStakeInOneRound_Л_round , 
				 ↑ε17 LocalState_ι_transferStakeInOneRound_Л_deltaDestinationStake, 
				 $ Л_prevSourceStake, 
				 ↑ε17 LocalState_ι_transferStakeInOneRound_Л_sourceParticipant, 
				 ↑ε17 LocalState_ι_transferStakeInOneRound_Л_destinationParticipant ).*)
		
(* Definition RoundsBase_Ф_transferStakeInOneRound ( Л_round : RoundsBase_ι_Round )
				                                        (Л_sourceParticipant: DePoolLib_ι_Participant) 
                                                (Л_destinationParticipant: DePoolLib_ι_Participant)
				                                        (Л_source : XAddress) 
                                                (Л_destination: XAddress) 
                                                (Л_amount: XInteger64) 
                                                (Л_minStake : XInteger64)
				  : LedgerT ( RoundsBase_ι_Round # XInteger64 # XInteger64 # DePoolLib_ι_Participant # DePoolLib_ι_Participant) :=
do r ← 	RoundsBase_Ф_transferStakeInOneRound' Л_round Л_sourceParticipant Л_destinationParticipant Л_source Л_destination Л_amount  Л_minStake ;
return! (fromValueValue r). *)

Ltac pr_numgoals := let n := numgoals in fail "There are" n "goals".






 
(*  
function getRounds() external view returns (mapping(uint64 => TruncatedRound) rounds) {
        optional(uint64, Round) pair = minRound();
        while (pair.hasValue()) {
            (uint64 id, Round round) = pair.get();
            TruncatedRound r = toTruncatedRound(round);
            rounds[r.id] = r;
            pair = nextRound(id);
        }
        return rounds;
    }
 *)
    
(*  Definition RoundsBase_Ф_getRounds : LedgerT (XHMap XInteger64 RoundsBase_ι_TruncatedRound) := 
	(↑17 U1! LocalState_ι_getRounds_Л_rounds := $default ) >>
	(↑↑17 U2! LocalState_ι_getRounds_Л_pair := RoundsBase_Ф_minRound () ) >>
	(While ((↑17 D2! LocalState_ι_getRounds_Л_pair) ->hasValue) do (
		U0! {( Л_id, Л_round )} := (↑17 D2! LocalState_ι_getRounds_Л_pair) ->get ;
		U0! Л_r := RoundsBase_Ф_toTruncatedRound (! $ Л_round !) ; 
		(↑17 U1! LocalState_ι_getRounds_Л_rounds [[ $ (Л_r ->> RoundsBase_ι_TruncatedRound_ι_id ) ]] := $ Л_r) >>
		(↑↑17 U2! LocalState_ι_getRounds_Л_pair := RoundsBase_Ф_nextRound (! $ Л_id !) ) >>
		continue! I
	)) >> 
	↑17 D2! LocalState_ι_getRounds_Л_rounds. *) 

 Lemma RoundsBase_Ф_getRounds_exec' : forall (l: Ledger) , 
   exists (ls: LocalState),
 	 exec_state RoundsBase_Ф_getRounds l = {$ l with Ledger_ι_LocalState := ls $} .  
 Proof. 
   intros.  
   Opaque fold_left.
   compute. idtac.
   match goal with
   | |- ?G => match G with
              | context [fold_left ?f _ _ ] => remember f
              end
   end. idtac.
   remember (
   (fun
      s0 : LedgerP Z Z Z Z Z Z Z Z bool string string list option
             (fun X Y : Type => list (X * Y)) prod =>
    (false, I, s0))).
   assert (forall l, exists ls b, p l = (b, {$l with Ledger_ι_LocalState := ls $} )) . idtac. 
   intros.
   exists (Ledger_ι_LocalState (snd (p l0))), (fst (p l0)).
   rewrite Heqp.
   simpl.
   destruct l0; auto.
   rewrite Heqp in  Heqs.
   clear Heqp.
   generalize dependent p.
   induction (listInfinite True); intros.

   remember (H {$ l with Ledger_ι_LocalState :=  {$ Ledger_ι_LocalState l with (LocalState_ι_getRounds_Л_rounds , default); 
                                        (LocalState_ι_getRounds_Л_pair , eval_state RoundsBase_Ф_minRound l)  $} $} ).
   clear Heqe. inversion_clear e. idtac.
   inversion_clear H0. idtac.  
   exists x.

   Transparent fold_left.
   compute. idtac. destruct l. 
   simpl in H1.
   destruct Ledger_ι_LocalState. idtac.
   compute in H1. rewrite H1. idtac.
   auto.

   simpl.
   remember (s (SimpleState p) a).
   destruct s0.

   match goal with
   | |- ?G => match G with
              | context [ match fold_left s l0 (SimpleState p0) with
              | SimpleState c => c
              end ?l ] => remember l
              end
   end. idtac.

   remember (IHl0 p0).
   clear Heqe.
   clear IHl0.
   assert (forall
   l : LedgerP Z Z Z Z Z Z Z Z bool string string list option
         (fun X Y : Type => list (X * Y)) prod,
 exists
   (ls : LocalStateP Z Z Z Z Z Z bool list option
           (fun X Y : Type => list (X * Y)) prod) 
 (b : bool * True), p0 l = (b, {$l with Ledger_ι_LocalState := ls $})).

 intros.
 exists (Ledger_ι_LocalState (snd (p0 l2))), (fst (p0 l2)).
 rewrite Heqs in Heqs0. idtac.
 inversion_clear Heqs0. idtac.

 remember (H l2). idtac.
 inversion_clear e0.
 inversion_clear H0.
 rewrite ?H1.

 destruct x0. idtac.

 match goal with
    | |- ?x =>
      match x with
        | context [if ?b then _ else _] =>  repeat rewrite ifSimpleState ; 
                                            repeat rewrite ifFunApply ;
                                            (* let rem := fresh "rem" in  *)
                                            (* set (rem:= b) ;  *)
                                            time case b (* compute; auto *)
        | _ => auto
      end
 end. idtac.
 simpl. destruct l2 .  auto. 

 match goal with
 | |- ?x =>
   match x with
     | context [if ?b then _ else _] =>  repeat rewrite ifSimpleState ; 
                                         repeat rewrite ifFunApply ;
                                         (* let rem := fresh "rem" in  *)
                                         (* set (rem:= b) ;  *)
                                         time case b (* compute; auto *)
     | _ => auto
   end
end. idtac.
destruct l2. destruct x. compute. auto.
destruct l2. destruct x. compute. auto.

apply e. idtac.
intros.

exists (Ledger_ι_LocalState (snd (p0 l2))), (fst (p0 l2)).
 rewrite Heqs in Heqs0. idtac.
 inversion_clear Heqs0. idtac.

 remember (H l2). idtac.
 inversion_clear e0.
 inversion_clear H1.
 rewrite ?H2.

 destruct x0. idtac.

 match goal with
    | |- ?x =>
      match x with
        | context [if ?b then _ else _] =>  repeat rewrite ifSimpleState ; 
                                            repeat rewrite ifFunApply ;
                                            (* let rem := fresh "rem" in  *)
                                            (* set (rem:= b) ;  *)
                                            time case b (* compute; auto *)
        | _ => auto
      end
 end. idtac.
 simpl. destruct l2 .  auto. 

 match goal with
 | |- ?x =>
   match x with
     | context [if ?b then _ else _] =>  repeat rewrite ifSimpleState ; 
                                         repeat rewrite ifFunApply ;
                                         (* let rem := fresh "rem" in  *)
                                         (* set (rem:= b) ;  *)
                                         time case b (* compute; auto *)
     | _ => auto
   end
end. idtac.
destruct l2. destruct x. compute. auto.
destruct l2. destruct x. compute. auto.

Qed. 

Lemma RoundsBase_Ф_getRounds_exec : forall (l: Ledger) , 
 exec_state (↓ RoundsBase_Ф_getRounds) l = l .
 Proof.
   intros.
   Opaque  RoundsBase_Ф_getRounds.
   compute.
   remember (run RoundsBase_Ф_getRounds {$l with Ledger_ι_LocalState := DePoolFuncs.DePoolSpec.LedgerClass.local0 $} ).
   remember (RoundsBase_Ф_getRounds_exec' {$l with Ledger_ι_LocalState := DePoolFuncs.DePoolSpec.LedgerClass.local0 $} ).
   clear Heqe.
   inversion_clear e.
   assert (snd p = {$ l with Ledger_ι_LocalState := x $} ).
   rewrite Heqp.
   rewrite run_eval_exec.
   rewrite H.
   auto.
   compute in Heqp.
   rewrite <- Heqp.
   destruct p.
   simpl in H0.
   rewrite H0.
   destruct l. destruct x. auto.
 Qed.

Lemma RoundsBase_Ф_getRounds_eval : forall (l: Ledger) , 
eval_state (  RoundsBase_Ф_getRounds ) l = xHMapEmpty . 
Proof. 
intros. destruct l. auto. 
Abort. 

 

 
