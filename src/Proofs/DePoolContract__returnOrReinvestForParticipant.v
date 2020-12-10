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

Ltac remDestructIf :=
  match goal with
    | |- ?x =>
      match x with
        | context [if ?b then _ else _] => case_eq b ; intros
        | _ => idtac
      end
  end.

  Ltac pr_numgoals := let n := numgoals in idtac "There are" n "goals".

Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo.

(*
function _returnOrReinvestForParticipant(
        Round round2,
        Round round0,
        address addr,
        StakeValue stakes,
        bool isValidator
    ) private returns (Round, Round) {
        uint64 stakeSum = stakeSum(stakes);
        bool stakeIsLost = round2.completionReason == CompletionReason.ValidatorIsPunished;
        optional(DePoolLib.Participant) optParticipant = fetchParticipant(addr);
        require(optParticipant.hasValue(), InternalErrors.ERROR511);
        DePoolLib.Participant participant = optParticipant.get();
        --participant.roundQty;
        uint64 lostFunds = stakeIsLost? (round2.stake - round2.unused) - round2.recoveredStake : 0;  //header

        // upd ordinary stake
        uint64 newStake;
        uint64 reward;
        if (stakeIsLost) {
            if (isValidator) {
                newStake = stakes.ordinary;
                uint64 delta = math.min(newStake, lostFunds);
                newStake -= delta;
                lostFunds -= delta;
                round2.validatorRemainingStake += newStake;
            } else {
                newStake = math.muldiv(
                    round2.unused + round2.recoveredStake - round2.validatorRemainingStake,
                    stakes.ordinary,
                    round2.stake - round2.validatorStake
                );
            }
        } else {
            reward = math.muldiv(stakeSum, round2.rewards, round2.stake);
            participant.reward += reward;
            newStake = stakes.ordinary + reward;
        }
        round2.handledStakesAndRewards += newStake;  //tailer1

        // upd vesting
        optional(InvestParams) newVesting = stakes.vesting;
        if (newVesting.hasValue()) {
            if (stakeIsLost) {
                InvestParams params = newVesting.get();
                if (isValidator) {
                    uint64 delta = math.min(params.amount, lostFunds);
                    params.amount -= delta;
                    lostFunds -= delta;
                    round2.validatorRemainingStake += params.amount;
                } else {
                    params.amount = math.muldiv(
                        round2.unused + round2.recoveredStake - round2.validatorRemainingStake,
                        params.amount,
                        round2.stake - round2.validatorStake
                    );
                }
                newVesting.set(params);
            }
            round2.handledStakesAndRewards += newVesting.get().amount;
            uint64 withdrawalVesting;
            (newVesting, withdrawalVesting) = cutWithdrawalValue(newVesting.get());
            newStake += withdrawalVesting;
        }   //tailer2

        // pause stake and newStake
        uint64 attachedValue = 1;
        uint64 curPause = math.min(participant.withdrawValue, newStake);
        attachedValue += curPause;
        participant.withdrawValue -= curPause;
        newStake -= curPause;
        if (newStake < m_minStake) { // whole stake is transferred to the participant
            attachedValue += newStake;
            newStake = 0;
        }   //tailer3

        // upd lock
        optional(InvestParams) newLock = stakes.lock;
        if (newLock.hasValue()) {
            if (stakeIsLost) {
                InvestParams params = newLock.get();
                if (isValidator) {
                    uint64 delta = math.min(params.amount, lostFunds);
                    params.amount -= delta;
                    lostFunds -= delta;
                    round2.validatorRemainingStake += params.amount;
                } else {
                    params.amount = math.muldiv(
                        round2.unused + round2.recoveredStake - round2.validatorRemainingStake,
                        params.amount,
                        round2.stake - round2.validatorStake
                    );
                }
                newLock.set(params);
            }
            round2.handledStakesAndRewards += newLock.get().amount;
            uint64 withdrawalLock;
            (newLock, withdrawalLock) = cutWithdrawalValue(newLock.get());
            if (withdrawalLock != 0) {
                newLock.get().owner.transfer(withdrawalLock, false, 1);
            }
        }  //tailer4

        if (m_poolClosed) {
            attachedValue += newStake;
            if (newVesting.hasValue()) {
                newVesting.get().owner.transfer(newVesting.get().amount, false, 1);
            }
            if (newLock.hasValue()) {
                newLock.get().owner.transfer(newLock.get().amount, false, 1);
            }
        } else {
            if (newVesting.hasValue() && newVesting.get().amount == 0) newVesting.reset();
            if (newLock.hasValue() && newLock.get().amount == 0) newLock.reset();

            if (!participant.reinvest) {
                attachedValue += newStake;
                newStake = 0;
            }
            (round0, participant) = _addStakes(round0, participant, addr, newStake, newVesting, newLock);
        } //tailer5

        _setOrDeleteParticipant(addr, participant);
        IParticipant(addr).onRoundComplete{value: attachedValue, bounce: false}(
            round2.id,
            reward,
            stakes.ordinary,
            stakes.vesting.hasValue() ? stakes.vesting.get().amount : 0,
            stakes.lock.hasValue() ? stakes.lock.get().amount : 0,
            participant.reinvest,
            uint8(round2.completionReason)
        );

        return (round0, round2); //tailer6
    }
*)

Opaque RoundsBase_Ф__addStakes DePoolContract_Ф_cutWithdrawalValue RoundsBase_Ф_stakeSum.

Definition DePoolContract_Ф__returnOrReinvestForParticipant' ( Л_round2 : RoundsBase_ι_Round )
                                                              ( Л_round0 : RoundsBase_ι_Round )
                                                              ( Л_addr : XAddress )
                                                              ( Л_stakes : RoundsBase_ι_StakeValue ) 
                                                              ( Л_isValidator : XBool )
                                                              ( f : XBool -> XBool ->  RoundsBase_ι_StakeValue -> XInteger -> XAddress -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) )
                                                  : LedgerT ( XErrorValue ( RoundsBase_ι_Round # RoundsBase_ι_Round ) XInteger ) := 
(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round2 := $ Л_round2) >> 
(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round0 := $ Л_round0) >>
U0! Л_stakeSum := RoundsBase_Ф_stakeSum (! $ Л_stakes !) ;
U0! Л_stakeIsLost := ($ (Л_round2 ->> RoundsBase_ι_Round_ι_completionReason) ) ?== ($ RoundsBase_ι_CompletionReasonP_ι_ValidatorIsPunished) ; 		
U0! Л_optParticipant := ParticipantBase_Ф_fetchParticipant (! $ Л_addr !) ; 
Require {{ $ Л_optParticipant ->hasValue , ↑8 D2! InternalErrors_ι_ERROR511 }} ; 

(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_participant := $ Л_optParticipant ->get) >> 
(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_participant ^^ DePoolLib_ι_Participant_ι_roundQty !--) >>

( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds := $ Л_stakeIsLost ? 
   ( D1! (D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2) ^^ RoundsBase_ι_Round_ι_stake !- 
     D1! (D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2) ^^ RoundsBase_ι_Round_ι_unused ) !- 
     D1! (D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2) ^^ RoundsBase_ι_Round_ι_recoveredStake 
                              ::: $ xInt0 )  >> f Л_stakeIsLost Л_isValidator Л_stakes Л_stakeSum Л_addr. 
                              
Lemma DePoolContract_Ф__returnOrReinvestForParticipant'_exec : forall
                                                                (l : Ledger)
                                                                ( Л_round2 : RoundsBase_ι_Round )
                                                                ( Л_round0 : RoundsBase_ι_Round )
                                                                ( Л_addr : XAddress )
                                                                ( Л_stakes : RoundsBase_ι_StakeValue ) 
                                                                ( Л_isValidator : XBool ) 
                                                                ( f : XBool -> XBool ->  RoundsBase_ι_StakeValue -> XInteger -> XAddress -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) ),
exec_state (DePoolContract_Ф__returnOrReinvestForParticipant' Л_round2 Л_round0 Л_addr Л_stakes Л_isValidator f) l =

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
    if  isSomeParticipant then                             
        exec_state (f stakeIsLost Л_isValidator Л_stakes stakeSum Л_addr) l_local
        else {$ l_sum With (LocalState_ι__returnOrReinvestForParticipant_Л_round2, Л_round2);
                           (LocalState_ι__returnOrReinvestForParticipant_Л_round0, Л_round0) $}.
Proof.
    intros. destruct l. 
  
    destruct Ledger_ι_DebugDePool, Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ConfigParamsBase, Ledger_ι_ParticipantBase, 
    Ledger_ι_DePoolHelper, Ledger_ι_Errors, Ledger_ι_InternalErrors, Ledger_ι_DePoolLib, Ledger_ι_DePoolProxyContract, 
    Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_DePool, Ledger_ι_Participant, Ledger_ι_TestElector, 
    Ledger_ι_VMState, Ledger_ι_LocalState.
  
    destruct Л_round2.
  
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
  
    end) . idtac.

  match goal with 
  | |- ?x  => match x with 
              | context [RoundsBase_Ф_stakeSum Л_stakes] => remember (RoundsBase_Ф_stakeSum Л_stakes) as l
              end
  end.
  destruct l.
  
  match goal with 
  | |- ?x  => match x with 
              | context [p ?a] => remember (p a)
              end
  end.
  
  destruct p0; auto.

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
  
    end) . idtac.

  match goal with 
  | |- ?x  => match x with 
              | context [f ?a ?b ?c ?d ?e] => remember (f a b c d e) as l0
              end
  end.
  destruct l0.
  
  match goal with 
  | |- ?x  => match x with 
              | context [p0 ?a] => remember (p0 a)
              end
  end.

  destruct p1; auto.
  match goal with 
  | |- ?x  => match x with 
              | context [RoundsBase_Ф_stakeSum Л_stakes] => remember (RoundsBase_Ф_stakeSum Л_stakes) as l
              end
  end.
  destruct l.
  
  match goal with 
  | |- ?x  => match x with 
              | context [p ?a] => remember (p a)
              end
  end.
  
  destruct p0; auto.

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
  
    end) . idtac.

    match goal with 
    | |- ?x  => match x with 
                | context [f ?a ?b ?c ?d ?e] => remember (f a b c d e) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p0 ?a] => remember (p0 a)
                end
    end.
  
    destruct p1; auto.

Qed.

                              

Definition DePoolContract_Ф__returnOrReinvestForParticipant_tailer1 ( Л_stakeIsLost: XBool ) 
                                                                    ( Л_isValidator : XBool )
                                                                    ( Л_stakes : RoundsBase_ι_StakeValue ) 
                                                                    ( Л_stakeSum: XInteger )
                                                                    ( Л_addr : XAddress )
                                                                    ( f : RoundsBase_ι_StakeValue -> XBool -> XBool -> XAddress -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) )
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
  f Л_stakes Л_stakeIsLost Л_isValidator Л_addr.


Lemma DePoolContract_Ф__returnOrReinvestForParticipant_tailer1_exec : forall
                                                            (l : Ledger)
                                                            ( Л_stakeIsLost: XBool ) 
                                                            ( Л_isValidator : XBool )
                                                            ( Л_stakes : RoundsBase_ι_StakeValue ) 
                                                            ( Л_stakeSum: XInteger)
                                                            ( Л_addr : XAddress)
                                                            ( f : RoundsBase_ι_StakeValue -> XBool -> XBool -> XAddress -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) ),

 exec_state (DePoolContract_Ф__returnOrReinvestForParticipant_tailer1 Л_stakeIsLost Л_isValidator Л_stakes Л_stakeSum Л_addr f) l =

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
let  lostFunds :=   if Л_stakeIsLost then 
                        if Л_isValidator then lostFunds - delta else lostFunds 
                                     else lostFunds in
let  reward :=  if Л_stakeIsLost then reward
                                 else Л_stakeSum *  (round2 ->> RoundsBase_ι_Round_ι_rewards) / (round2 ->> RoundsBase_ι_Round_ι_stake) in 
let  round2 :=  if Л_stakeIsLost then 
                        if Л_isValidator then  {$ round2 with RoundsBase_ι_Round_ι_validatorRemainingStake := newStake $}     
                                         else round2 
                                     else round2 in   
let participant := if Л_stakeIsLost then participant
                                    else {$ participant with DePoolLib_ι_Participant_ι_reward := participant ->> DePoolLib_ι_Participant_ι_reward + reward $} in 
let round2 := {$round2 with RoundsBase_ι_Round_ι_handledStakesAndRewards :=  round2 ->> RoundsBase_ι_Round_ι_handledStakesAndRewards + newStake$} in

exec_state (f Л_stakes Л_stakeIsLost Л_isValidator Л_addr) {$ l With (LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds, lostFunds);
        (LocalState_ι__returnOrReinvestForParticipant_Л_round2, round2);
        (LocalState_ι__returnOrReinvestForParticipant_Л_participant, participant);
        (LocalState_ι__returnOrReinvestForParticipant_Л_newStake, newStake);
        (LocalState_ι__returnOrReinvestForParticipant_Л_reward, reward) $}.
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
                                            case_eq b ; 
                                            (* simpl;  *)
                                            intros                                                              
        | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
        end
  
    end) . 
Qed.    

 

Definition DePoolContract_Ф__returnOrReinvestForParticipant_tailer2  ( Л_stakes : RoundsBase_ι_StakeValue ) 
                                                                     ( Л_stakeIsLost : XBool )  
                                                                     ( Л_isValidator : XBool ) 
                                                                     ( Л_addr : XAddress)
                                                                     ( f: RoundsBase_ι_StakeValue -> XBool -> XBool -> XAddress -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) )
                                                            : LedgerT ( RoundsBase_ι_Round # RoundsBase_ι_Round ) :=  
(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting := $ ( Л_stakes ->> RoundsBase_ι_StakeValue_ι_vesting ) ) >> 

( If ( ( ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting ) ->hasValue ) 
then
{ (
  (↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_params := 
             ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting ) ->get ) >>
	If ($ Л_stakeIsLost) then {
  
   ( If ( $ Л_isValidator ) 
     then {
           U0! Л_delta := math->min2 (! ↑17 D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params ) ^^ RoundsBase_ι_InvestParams_ι_amount ,
                                         ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds !) ; 
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_params ^^ 
                                             RoundsBase_ι_InvestParams_ι_amount !-= $ Л_delta ) >>  
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds !-= $ Л_delta ) >> 
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ^^ RoundsBase_ι_Round_ι_validatorRemainingStake
                       !+= D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params )
                                            ^^ RoundsBase_ι_InvestParams_ι_amount )
     } 
     else {
		( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_params ^^ 
                                             RoundsBase_ι_InvestParams_ι_amount := math->muldiv (! 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_unused !+
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_recoveredStake !-
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_validatorRemainingStake
              , 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params )
                                            ^^ RoundsBase_ι_InvestParams_ι_amount , 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_stake !-
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_validatorStake !) )
} ) 
	}  ) >>
  ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ^^ RoundsBase_ι_Round_ι_handledStakesAndRewards  !+=
      ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params ^^ RoundsBase_ι_InvestParams_ι_amount ) ) >>
  U0! Л_withdrawalVesting := $ default ;
  U0! {( Л_newVesting , Л_withdrawalVesting )} := DePoolContract_Ф_cutWithdrawalValue 
                              (! ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_params !) ;

  ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting := $ Л_newVesting ) >>
  ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake !+= $ Л_withdrawalVesting ) 
} ) >> f Л_stakes Л_stakeIsLost Л_isValidator Л_addr.

Lemma DePoolContract_Ф__returnOrReinvestForParticipant_tailer2_exec : forall
                                                            (l : Ledger)
                                                            (Л_stakes : RoundsBase_ι_StakeValue ) 
                                                            (Л_stakeIsLost : XBool )  
                                                            (Л_isValidator : XBool ) 
                                                            (Л_addr : XAddress)
                                                            (f: RoundsBase_ι_StakeValue -> XBool -> XBool -> XAddress -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) ),

 exec_state (DePoolContract_Ф__returnOrReinvestForParticipant_tailer2 Л_stakes Л_stakeIsLost Л_isValidator Л_addr f) l = 

 let lostFunds := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds) l in
 let round2 := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_round2) l in
 let newStake := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_newStake) l in

 let optNewVesting := Л_stakes ->> RoundsBase_ι_StakeValue_ι_vesting in
 let isNewVesting := isSome optNewVesting in
 let params := maybeGet optNewVesting in
 let oldVestingAmount := params ->> RoundsBase_ι_InvestParams_ι_amount in
 let oldVestingValidatorRemainingStake := round2 ->> RoundsBase_ι_Round_ι_validatorRemainingStake  in
 let deltaVestingValidator := intMin oldVestingAmount lostFunds in
 let amount := if Л_stakeIsLost then
                    if Л_isValidator then oldVestingAmount - deltaVestingValidator
                                     else (round2 ->> RoundsBase_ι_Round_ι_unused + round2 ->> RoundsBase_ι_Round_ι_recoveredStake - round2 ->> RoundsBase_ι_Round_ι_validatorRemainingStake) *
                                          (params ->> RoundsBase_ι_InvestParams_ι_amount) / (round2 ->> RoundsBase_ι_Round_ι_stake - round2 ->> RoundsBase_ι_Round_ι_validatorStake) 
                                   else oldVestingAmount in
 let lostFunds := if Л_stakeIsLost then 
                        if Л_isValidator then lostFunds - deltaVestingValidator 
                                         else lostFunds 
                                      else lostFunds in 
 let validatorRemainingStake := if Л_stakeIsLost then 
                        if Л_isValidator then  oldVestingValidatorRemainingStake + amount
                                         else oldVestingValidatorRemainingStake 
                                      else oldVestingValidatorRemainingStake in 
 let params := {$params with RoundsBase_ι_InvestParams_ι_amount := amount$} in
 let (p, l') := run (↓ DePoolContract_Ф_cutWithdrawalValue params) l in
 let (newVesting, withdrawalVesting) := p in
 let round2 := {$round2 with (RoundsBase_ι_Round_ι_handledStakesAndRewards, round2 ->> RoundsBase_ι_Round_ι_handledStakesAndRewards + amount) ;
                             (RoundsBase_ι_Round_ι_validatorRemainingStake, validatorRemainingStake) $} in
 
if isNewVesting then 
 exec_state (f Л_stakes Л_stakeIsLost Л_isValidator Л_addr) {$ l' With (LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds, lostFunds);
        (LocalState_ι__returnOrReinvestForParticipant_Л_round2, round2);
        (LocalState_ι__returnOrReinvestForParticipant_Л_newStake, newStake + withdrawalVesting);
        (LocalState_ι__returnOrReinvestForParticipant_Л_newVesting, newVesting);
        (LocalState_ι__returnOrReinvestForParticipant_Л_params, params) $} else
    exec_state (f Л_stakes Л_stakeIsLost Л_isValidator Л_addr) {$ l With (LocalState_ι__returnOrReinvestForParticipant_Л_newVesting, optNewVesting) $}    .
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
                                            case_eq b ; 
                                            (* simpl;  *)
                                            intros                                                              
        | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
        end
  
    end) . 

    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x ; auto. idtac.


    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x ; auto. idtac.


    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x ; auto. idtac.

    destruct Л_stakes. idtac.

    destruct RoundsBase_ι_StakeValue_ι_vesting; auto. idtac.
    destruct r. idtac.


    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l0
                end
    end.
    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l1
                end
    end.
    setoid_rewrite <- Heql0 in Heql1.
    rewrite Heql1. idtac.
    destruct l0. idtac.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end. idtac.
  
    destruct p0; auto.
    destruct x ; auto. idtac.

    discriminate.

    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x ; auto. idtac.

    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x ; auto. idtac.

    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x ; auto. idtac.

    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x ; auto. 

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

exec_state (DePoolContract_Ф__returnOrReinvestForParticipant_tailer3 Л_stakes Л_stakeIsLost Л_isValidator Л_addr f) l = 

let newStake := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_newStake) l in
let participant := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_participant) l in
let m_minStake := eval_state (↑12 ε DePoolContract_ι_m_minStake) l in

let curPause := intMin (participant ->> DePoolLib_ι_Participant_ι_withdrawValue) newStake in
let attachedValue := 1 + curPause in
let participant := {$participant with (DePoolLib_ι_Participant_ι_withdrawValue, (participant ->> DePoolLib_ι_Participant_ι_withdrawValue) - curPause)$} in
let newStake := newStake - curPause in
let attachedValue := if (newStake <? m_minStake) then attachedValue + newStake else attachedValue in
let newStake := if (newStake <? m_minStake) then 0 else newStake in

exec_state (f Л_stakes Л_stakeIsLost Л_isValidator Л_addr)
{$ l With (LocalState_ι__returnOrReinvestForParticipant_Л_participant, participant);
        (LocalState_ι__returnOrReinvestForParticipant_Л_newStake, newStake);
        (LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue, attachedValue)$}.
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
                                            case_eq b ; 
                                            (* simpl;  *)
                                            intros                                                              
        | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
        end
  
    end) .         
Qed.


Definition DePoolContract_Ф__returnOrReinvestForParticipant_tailer4  
                                              (Л_stakes : RoundsBase_ι_StakeValue) 
                                              (Л_stakeIsLost : XBool )
                                              (Л_isValidator : XBool )
                                              (Л_addr : XAddress)
                                              (f: XAddress -> RoundsBase_ι_StakeValue -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) )
                                               : LedgerT ( RoundsBase_ι_Round # RoundsBase_ι_Round ) := 
(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newLock := $ ( Л_stakes ->> RoundsBase_ι_StakeValue_ι_lock ) ) >> 
( If ( ( ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock ) ->hasValue )
then
{ (
  (↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_params := 
             ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock ) ->get ) >>
	If ($ Л_stakeIsLost) then {
  
   ( If ( $ Л_isValidator ) 
     then {
           U0! Л_delta := math->min2 (! ↑17 D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params ) ^^ RoundsBase_ι_InvestParams_ι_amount ,
                                         ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds !) ; 
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_params ^^ 
                                             RoundsBase_ι_InvestParams_ι_amount !-= $ Л_delta ) >>  
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds !-= $ Л_delta ) >> 
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ^^ RoundsBase_ι_Round_ι_validatorRemainingStake
                       !+= D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params )
                                            ^^ RoundsBase_ι_InvestParams_ι_amount )
     } 
     else {
		( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_params ^^ 
                                             RoundsBase_ι_InvestParams_ι_amount := math->muldiv (! 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_unused !+
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_recoveredStake !-
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_validatorRemainingStake
              , 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params )
                                            ^^ RoundsBase_ι_InvestParams_ι_amount , 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_stake !-
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_validatorStake !) )
} ) 
	}  ) >>
  ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ^^ RoundsBase_ι_Round_ι_handledStakesAndRewards !+=
  ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params ^^ RoundsBase_ι_InvestParams_ι_amount ) ) >>

  U0! Л_withdrawalLock := $ default ;
  U0! {( Л_newLock , Л_withdrawalLock )} := DePoolContract_Ф_cutWithdrawalValue 
             (! ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_params !) ;
  ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newLock := $ Л_newLock ) >>
  (If  ( $ Л_withdrawalLock ?!= $xInt0 ) then {
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

 exec_state (DePoolContract_Ф__returnOrReinvestForParticipant_tailer4 Л_stakes Л_stakeIsLost Л_isValidator Л_addr f) l = 

 let lostFunds := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds) l in
 let round2 := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_round2) l in
(*  let newStake := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_newStake) l in *) 

 let optNewLock := Л_stakes ->> RoundsBase_ι_StakeValue_ι_lock in
 let isNewLock := isSome optNewLock in
 let params := maybeGet optNewLock in
 let oldLockAmount := params ->> RoundsBase_ι_InvestParams_ι_amount in
 let oldLockValidatorRemainingStake := round2 ->> RoundsBase_ι_Round_ι_validatorRemainingStake  in
 let deltaLockValidator := intMin oldLockAmount lostFunds in
 let amount := if Л_stakeIsLost then
                    if Л_isValidator then oldLockAmount - deltaLockValidator
                                     else (round2 ->> RoundsBase_ι_Round_ι_unused + round2 ->> RoundsBase_ι_Round_ι_recoveredStake - round2 ->> RoundsBase_ι_Round_ι_validatorRemainingStake) *
                                          (params ->> RoundsBase_ι_InvestParams_ι_amount) / (round2 ->> RoundsBase_ι_Round_ι_stake - round2 ->> RoundsBase_ι_Round_ι_validatorStake) 
                                   else oldLockAmount in
 let lostFunds := if Л_stakeIsLost then 
                        if Л_isValidator then lostFunds - deltaLockValidator 
                                         else lostFunds 
                                      else lostFunds in 
 let validatorRemainingStake := if Л_stakeIsLost then 
                        if Л_isValidator then oldLockValidatorRemainingStake + amount
                                         else oldLockValidatorRemainingStake 
                                      else oldLockValidatorRemainingStake in 
 let params := {$params with RoundsBase_ι_InvestParams_ι_amount := amount$} in 
 let (p, l') := run (↓ DePoolContract_Ф_cutWithdrawalValue params) l in
 let (newLock, withdrawalLock) := p in
 let round2 := {$round2 with (RoundsBase_ι_Round_ι_handledStakesAndRewards, round2 ->> RoundsBase_ι_Round_ι_handledStakesAndRewards + amount) ;
                             (RoundsBase_ι_Round_ι_validatorRemainingStake, validatorRemainingStake) $} in
 let l'' := if negb (withdrawalLock =? 0) then exec_state (↓ tvm_transfer (params ->> RoundsBase_ι_InvestParams_ι_owner) 
                                                                          withdrawalLock false 1 default) l' else l' in 
if isNewLock then 
 exec_state (f Л_addr Л_stakes) {$ l'' With (LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds, lostFunds);
        (LocalState_ι__returnOrReinvestForParticipant_Л_round2, round2);
        (* (LocalState_ι__returnOrReinvestForParticipant_Л_newStake, newStake + withdrawalLock); *)
        (LocalState_ι__returnOrReinvestForParticipant_Л_newLock, newLock);
        (LocalState_ι__returnOrReinvestForParticipant_Л_params, params) $} else
    exec_state (f Л_addr Л_stakes) {$ l With (LocalState_ι__returnOrReinvestForParticipant_Л_newLock, optNewLock) $} .
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
                                            case_eq b ; 
                                            (* simpl;  *)
                                            intros                                                              
        | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
        end
  
    end) . idtac.

    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x ; auto. idtac.

    destruct (x0 =? 0); auto. idtac.


    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x ; auto. idtac.

    destruct (x0 =? 0); auto. idtac.


    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x ; auto. idtac.

    destruct (x0 =? 0); auto. idtac.

    destruct Л_stakes. idtac.

    destruct RoundsBase_ι_StakeValue_ι_lock; auto. idtac.
    destruct r. idtac.


    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l0
                end
    end.
    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l1
                end
    end.
    setoid_rewrite <- Heql0 in Heql1.
    rewrite Heql1. idtac.
    destruct l0. idtac.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end. idtac.
  
    destruct p0; auto.
    destruct x ; auto. idtac.

    destruct (x0 =? 0); auto. idtac.

    discriminate.

    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x ; auto. idtac.

    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x ; auto. idtac.

    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x ; auto. idtac.

    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x ; auto. 

Qed.


(* if (m_poolClosed) {
	attachedValue += newStake;
	if (newVesting.hasValue()) {
		newVesting.get().owner.transfer(newVesting.get().amount, false, 1);
	}
	if (newLock.hasValue()) {
		newLock.get().owner.transfer(newLock.get().amount, false, 1);
	}
} else {
	if (newVesting.hasValue() && newVesting.get().amount == 0) newVesting.reset();
	if (newLock.hasValue() && newLock.get().amount == 0) newLock.reset();

	if (!participant.reinvest) {
		attachedValue += newStake;
		newStake = 0;
	}
	(round0, participant) = _addStakes(round0, participant, addr, newStake, newVesting, newLock);
} *)

Definition DePoolContract_Ф__returnOrReinvestForParticipant_tailer5 (Л_addr : XAddress) 
                                                                    (Л_stakes : RoundsBase_ι_StakeValue)
                            (f: XAddress -> RoundsBase_ι_StakeValue -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) )
                            : LedgerT ( RoundsBase_ι_Round # RoundsBase_ι_Round ):= 
(If (↑12 D2! DePoolContract_ι_m_poolClosed) then { 
	(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue !+= D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake) >>
	(If ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting) ->hasValue) then { 
	(D1! ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting) ->get) ^^ RoundsBase_ι_InvestParams_ι_owner ) ->transfer 
                                (! D1! ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting) ->get) ^^ RoundsBase_ι_InvestParams_ι_amount , $xBoolFalse, $ xInt1 !)
	}) >>
	(If ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock) ->hasValue) then { 
	(D1! ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock) ->get) ^^ RoundsBase_ι_InvestParams_ι_owner ) ->transfer 
            (! D1! ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock) ->get) ^^ RoundsBase_ι_InvestParams_ι_amount , $xBoolFalse, $ xInt1 !)
    }) 
 } else { 
	(If ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting) ->hasValue) !& 
		(D1! ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting) ->get) ^^ RoundsBase_ι_InvestParams_ι_amount ?== $xInt0)
	then { 
		 ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting ->reset 
	}) >>
	(If ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock) ->hasValue) !& 
		(D1! ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock) ->get) ^^ RoundsBase_ι_InvestParams_ι_amount ?== $xInt0)
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
 exec_state (DePoolContract_Ф__returnOrReinvestForParticipant_tailer5 Л_addr Л_stakes f) l = 

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
                     if (isVesting && (newVesting ->> RoundsBase_ι_InvestParams_ι_amount =? 0))%bool then None
                     else newOptVesting in
let newOptLock := if m_poolClosed then newOptLock else
                     if (isLock && (newLock ->> RoundsBase_ι_InvestParams_ι_amount =? 0))%bool then None
                     else newOptLock in
let newStake := if m_poolClosed then newStake else
                        if (negb reinvest) then 0 else newStake in
let (rp, l') :=  if m_poolClosed then 
                    if isVesting then 
                    let lv := exec_state (↓ tvm_transfer (newVesting ->> RoundsBase_ι_InvestParams_ι_owner) 
                                                     (newVesting ->> RoundsBase_ι_InvestParams_ι_amount) 
                                                     false 1 default) l in
                    if isLock then ((round0, participant), exec_state (↓ tvm_transfer (newLock ->> RoundsBase_ι_InvestParams_ι_owner) 
                                            (newLock ->> RoundsBase_ι_InvestParams_ι_amount) 
                                            false 1 default) lv)
                              else ((round0, participant), lv)
                    else if isLock then ((round0, participant) , exec_state (↓ tvm_transfer (newLock ->> RoundsBase_ι_InvestParams_ι_owner) 
                                            (newLock ->> RoundsBase_ι_InvestParams_ι_amount) 
                                            false 1 default) l)
                            else ((round0, participant) , l)
                  else  run (↓ RoundsBase_Ф__addStakes round0 participant Л_addr newStake newOptVesting newOptLock) l in
let (round0, participant) := rp in                   
exec_state (f Л_addr Л_stakes) {$l' With 
        (LocalState_ι__returnOrReinvestForParticipant_Л_newStake, newStake ); 
        (LocalState_ι__returnOrReinvestForParticipant_Л_newLock, newOptLock);
        (LocalState_ι__returnOrReinvestForParticipant_Л_newVesting, newOptVesting);
        (LocalState_ι__returnOrReinvestForParticipant_Л_round0, round0);
        (LocalState_ι__returnOrReinvestForParticipant_Л_participant, participant);
        (LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue, attachedValue) $}   .                                                               
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
                                            case_eq b ; 
                                            (* simpl;  *)
                                            intros                                                              
        | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
        end
  
    end) . idtac.

    match goal with 
    | |- ?x  => match x with 
                | context [RoundsBase_Ф__addStakes ?a ?b ?c ?d ?e ?g] => remember (RoundsBase_Ф__addStakes a b c d e g) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x; auto.

    match goal with 
    | |- ?x  => match x with 
                | context [RoundsBase_Ф__addStakes ?a ?b ?c ?d ?e ?g] => remember (RoundsBase_Ф__addStakes a b c d e g) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x; auto.

    match goal with 
    | |- ?x  => match x with 
                | context [RoundsBase_Ф__addStakes ?a ?b ?c ?d ?e ?g] => remember (RoundsBase_Ф__addStakes a b c d e g) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x; auto.

    match goal with 
    | |- ?x  => match x with 
                | context [RoundsBase_Ф__addStakes ?a ?b ?c ?d ?e ?g] => remember (RoundsBase_Ф__addStakes a b c d e g) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x; auto.

    match goal with 
    | |- ?x  => match x with 
                | context [RoundsBase_Ф__addStakes ?a ?b ?c ?d ?e ?g] => remember (RoundsBase_Ф__addStakes a b c d e g) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x; auto.

    match goal with 
    | |- ?x  => match x with 
                | context [RoundsBase_Ф__addStakes ?a ?b ?c ?d ?e ?g] => remember (RoundsBase_Ф__addStakes a b c d e g) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x; auto.

    match goal with 
    | |- ?x  => match x with 
                | context [RoundsBase_Ф__addStakes ?a ?b ?c ?d ?e ?g] => remember (RoundsBase_Ф__addStakes a b c d e g) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x; auto.
Qed.    

 Definition DePoolContract_Ф__returnOrReinvestForParticipant_tailer6 (Л_addr : XAddress) 
                                                                     (Л_stakes : RoundsBase_ι_StakeValue): LedgerT ( RoundsBase_ι_Round # RoundsBase_ι_Round ) := 
 ParticipantBase_Ф__setOrDeleteParticipant (! $Л_addr , (↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_participant)  !) >>
 ( ->sendMessage {|| contractAddress := $ Л_addr ,
			   contractFunction :=  IParticipant_И_onRoundCompleteF (!! ↑17 D1! (D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2) ^^ RoundsBase_ι_Round_ι_id ,
																	   ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_reward ,
																	   $ Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary ,
																	   (($ Л_stakes ->> RoundsBase_ι_StakeValue_ι_vesting) ->hasValue ) ? 
																			  (D1! (($ Л_stakes ->> RoundsBase_ι_StakeValue_ι_vesting) ->get) ^^ RoundsBase_ι_InvestParams_ι_amount) ::: $xInt0, 
																	   (($ Л_stakes ->> RoundsBase_ι_StakeValue_ι_lock) ->hasValue ) ? 
																			  (D1! (($ Л_stakes ->> RoundsBase_ι_StakeValue_ι_lock) ->get) ^^ RoundsBase_ι_InvestParams_ι_amount) ::: $xInt0 ,
																	   D1! (↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_participant) ^^ DePoolLib_ι_Participant_ι_reinvest , 
																	   (completionReason2XInteger (!! ↑17 D1! (D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2) ^^ RoundsBase_ι_Round_ι_completionReason !!) ) 
			                                                          !!) ,
			   contractMessage := {|| messageValue := ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue , 
			                          messageBounce := $xBoolFalse ||} ||} ) >> 
 return# ( ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_round0 , 
           ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ).


Lemma DePoolContract_Ф__returnOrReinvestForParticipant_tailer6_exec : forall
                                                            (l : Ledger)
                                                            (Л_addr : XAddress)
                                                            (Л_stakes : RoundsBase_ι_StakeValue ) ,
                                                           
 exec_state (DePoolContract_Ф__returnOrReinvestForParticipant_tailer6 Л_addr Л_stakes ) l = 

 let participant := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_participant) l in
 let round2 := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_round2) l in
 let attachedValue := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue) l in
 let reward := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_reward) l in
 let isVesting := isSome (Л_stakes ->> RoundsBase_ι_StakeValue_ι_vesting) in
 let vestingAmount := (maybeGet (Л_stakes ->> RoundsBase_ι_StakeValue_ι_vesting)) ->> RoundsBase_ι_InvestParams_ι_amount in
 let isLock := isSome (Л_stakes ->> RoundsBase_ι_StakeValue_ι_lock) in
 let lockAmount := (maybeGet (Л_stakes ->> RoundsBase_ι_StakeValue_ι_lock)) ->> RoundsBase_ι_InvestParams_ι_amount in


 let l' := exec_state (↓ ParticipantBase_Ф__setOrDeleteParticipant Л_addr participant) l in
 let oldMessages := eval_state (↑16 ε VMState_ι_messages) l in 
 let newMessage  := {| contractAddress :=  Л_addr;
                       contractFunction := IParticipant_И_onRoundCompleteF (round2 ->> RoundsBase_ι_Round_ι_id)
                                                                            reward
                                                                           (Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary)
                                                                           (if isVesting then vestingAmount else 0)
                                                                           (if isLock then lockAmount else 0)
                                                                           (participant ->> DePoolLib_ι_Participant_ι_reinvest)
                                                                           (completionReason2XInteger (round2 ->> RoundsBase_ι_Round_ι_completionReason));
                       contractMessage :=  {| messageValue := attachedValue;
                                             messageFlag := 0 ;
                                             messageBounce := false |} |} in 

 {$l' With VMState_ι_messages := newMessage :: oldMessages $}.
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
                                            case_eq b ; 
                                            (* simpl;  *)
                                            intros                                                              
        | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
        end
  
    end) . 
Qed.    
 

Lemma DePoolContract_Ф__returnOrReinvestForParticipant'_eval : forall
                                                                (l : Ledger)
                                                                ( Л_round2 : RoundsBase_ι_Round )
                                                                ( Л_round0 : RoundsBase_ι_Round )
                                                                ( Л_addr : XAddress )
                                                                ( Л_stakes : RoundsBase_ι_StakeValue ) 
                                                                ( Л_isValidator : XBool ) 
                                                                ( f : XBool -> XBool ->  RoundsBase_ι_StakeValue -> XInteger -> XAddress -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) ),
eval_state (DePoolContract_Ф__returnOrReinvestForParticipant' Л_round2 Л_round0 Л_addr Л_stakes Л_isValidator f) l =

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
    if  isSomeParticipant then                             
        Value (eval_state (f stakeIsLost Л_isValidator Л_stakes stakeSum Л_addr) l_local)
        else Error (eval_state (↑8 D2! InternalErrors_ι_ERROR511) l_sum).
Proof.
    intros. destruct l. 
  
    destruct Ledger_ι_DebugDePool, Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ConfigParamsBase, Ledger_ι_ParticipantBase, 
    Ledger_ι_DePoolHelper, Ledger_ι_Errors, Ledger_ι_InternalErrors, Ledger_ι_DePoolLib, Ledger_ι_DePoolProxyContract, 
    Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_DePool, Ledger_ι_Participant, Ledger_ι_TestElector, 
    Ledger_ι_VMState, Ledger_ι_LocalState.
  
    destruct Л_round2.
  
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
  
    end) . idtac.

  match goal with 
  | |- ?x  => match x with 
              | context [RoundsBase_Ф_stakeSum Л_stakes] => remember (RoundsBase_Ф_stakeSum Л_stakes) as l
              end
  end.
  destruct l.
  
  match goal with 
  | |- ?x  => match x with 
              | context [p ?a] => remember (p a)
              end
  end.
  
  destruct p0; auto.

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
  
    end) . idtac.

  match goal with 
  | |- ?x  => match x with 
              | context [f ?a ?b ?c ?d ?e] => remember (f a b c d e) as l0
              end
  end.
  destruct l0.
  
  match goal with 
  | |- ?x  => match x with 
              | context [p0 ?a] => remember (p0 a)
              end
  end.

  destruct p1; auto.

  match goal with 
  | |- ?x  => match x with 
              | context [RoundsBase_Ф_stakeSum Л_stakes] => remember (RoundsBase_Ф_stakeSum Л_stakes) as l
              end
  end.
  destruct l.
  
  match goal with 
  | |- ?x  => match x with 
              | context [p ?a] => remember (p a)
              end
  end.
  
  destruct p0; auto.

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
  
    end) . idtac.

    match goal with 
    | |- ?x  => match x with 
                | context [f ?a ?b ?c ?d ?e] => remember (f a b c d e) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p0 ?a] => remember (p0 a)
                end
    end.
  
    destruct p1; auto.

Qed.


Lemma DePoolContract_Ф__returnOrReinvestForParticipant_tailer1_eval : forall
                                                            (l : Ledger)
                                                            ( Л_stakeIsLost: XBool ) 
                                                            ( Л_isValidator : XBool )
                                                            ( Л_stakes : RoundsBase_ι_StakeValue ) 
                                                            ( Л_stakeSum: XInteger)
                                                            ( Л_addr : XAddress)
                                                            ( f : RoundsBase_ι_StakeValue -> XBool -> XBool -> XAddress -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) ),

 eval_state (DePoolContract_Ф__returnOrReinvestForParticipant_tailer1 Л_stakeIsLost Л_isValidator Л_stakes Л_stakeSum Л_addr f) l =

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
let  lostFunds :=   if Л_stakeIsLost then 
                        if Л_isValidator then lostFunds - delta else lostFunds 
                                     else lostFunds in
let  reward :=  if Л_stakeIsLost then reward
                                 else Л_stakeSum *  (round2 ->> RoundsBase_ι_Round_ι_rewards) / (round2 ->> RoundsBase_ι_Round_ι_stake) in 
let  round2 :=  if Л_stakeIsLost then 
                        if Л_isValidator then  {$ round2 with RoundsBase_ι_Round_ι_validatorRemainingStake := newStake $}     
                                         else round2 
                                     else round2 in   
let participant := if Л_stakeIsLost then participant
                                    else {$ participant with DePoolLib_ι_Participant_ι_reward := participant ->> DePoolLib_ι_Participant_ι_reward + reward $} in 
let round2 := {$round2 with RoundsBase_ι_Round_ι_handledStakesAndRewards :=  round2 ->> RoundsBase_ι_Round_ι_handledStakesAndRewards + newStake$} in

eval_state (f Л_stakes Л_stakeIsLost Л_isValidator Л_addr) {$ l With (LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds, lostFunds);
        (LocalState_ι__returnOrReinvestForParticipant_Л_round2, round2);
        (LocalState_ι__returnOrReinvestForParticipant_Л_participant, participant);
        (LocalState_ι__returnOrReinvestForParticipant_Л_newStake, newStake);
        (LocalState_ι__returnOrReinvestForParticipant_Л_reward, reward) $}.
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
                                            case_eq b ; 
                                            (* simpl;  *)
                                            intros                                                              
        | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
        end
  
    end) . 
Qed.    


Lemma DePoolContract_Ф__returnOrReinvestForParticipant_tailer2_eval : forall
                                                            (l : Ledger)
                                                            (Л_stakes : RoundsBase_ι_StakeValue ) 
                                                            (Л_stakeIsLost : XBool )  
                                                            (Л_isValidator : XBool ) 
                                                            (Л_addr : XAddress)
                                                            (f: RoundsBase_ι_StakeValue -> XBool -> XBool -> XAddress -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) ),

 eval_state (DePoolContract_Ф__returnOrReinvestForParticipant_tailer2 Л_stakes Л_stakeIsLost Л_isValidator Л_addr f) l = 

 let lostFunds := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds) l in
 let round2 := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_round2) l in
 let newStake := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_newStake) l in

 let optNewVesting := Л_stakes ->> RoundsBase_ι_StakeValue_ι_vesting in
 let isNewVesting := isSome optNewVesting in
 let params := maybeGet optNewVesting in
 let oldVestingAmount := params ->> RoundsBase_ι_InvestParams_ι_amount in
 let oldVestingValidatorRemainingStake := round2 ->> RoundsBase_ι_Round_ι_validatorRemainingStake  in
 let deltaVestingValidator := intMin oldVestingAmount lostFunds in
 let amount := if Л_stakeIsLost then
                    if Л_isValidator then oldVestingAmount - deltaVestingValidator
                                     else (round2 ->> RoundsBase_ι_Round_ι_unused + round2 ->> RoundsBase_ι_Round_ι_recoveredStake - round2 ->> RoundsBase_ι_Round_ι_validatorRemainingStake) *
                                          (params ->> RoundsBase_ι_InvestParams_ι_amount) / (round2 ->> RoundsBase_ι_Round_ι_stake - round2 ->> RoundsBase_ι_Round_ι_validatorStake) 
                                   else oldVestingAmount in
 let lostFunds := if Л_stakeIsLost then 
                        if Л_isValidator then lostFunds - deltaVestingValidator 
                                         else lostFunds 
                                      else lostFunds in 
 let validatorRemainingStake := if Л_stakeIsLost then 
                        if Л_isValidator then  oldVestingValidatorRemainingStake + amount
                                         else oldVestingValidatorRemainingStake 
                                      else oldVestingValidatorRemainingStake in 
 let params := {$params with RoundsBase_ι_InvestParams_ι_amount := amount$} in
 let (p, l') := run (↓ DePoolContract_Ф_cutWithdrawalValue params) l in
 let (newVesting, withdrawalVesting) := p in
 let round2 := {$round2 with (RoundsBase_ι_Round_ι_handledStakesAndRewards, round2 ->> RoundsBase_ι_Round_ι_handledStakesAndRewards + amount) ;
                             (RoundsBase_ι_Round_ι_validatorRemainingStake, validatorRemainingStake) $} in
 
if isNewVesting then 
 eval_state (f Л_stakes Л_stakeIsLost Л_isValidator Л_addr) {$ l' With (LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds, lostFunds);
        (LocalState_ι__returnOrReinvestForParticipant_Л_round2, round2);
        (LocalState_ι__returnOrReinvestForParticipant_Л_newStake, newStake + withdrawalVesting);
        (LocalState_ι__returnOrReinvestForParticipant_Л_newVesting, newVesting);
        (LocalState_ι__returnOrReinvestForParticipant_Л_params, params) $} else
    eval_state (f Л_stakes Л_stakeIsLost Л_isValidator Л_addr) {$ l With (LocalState_ι__returnOrReinvestForParticipant_Л_newVesting, optNewVesting) $}    .
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
                                            case_eq b ; 
                                            (* simpl;  *)
                                            intros                                                              
        | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
        end
  
    end) . 

    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x ; auto. idtac.


    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x ; auto. idtac.


    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x ; auto. idtac.

    destruct Л_stakes. idtac.

    destruct RoundsBase_ι_StakeValue_ι_vesting; auto. idtac.
    destruct r. idtac.


    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l0
                end
    end.
    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l1
                end
    end.
    setoid_rewrite <- Heql0 in Heql1.
    rewrite Heql1. idtac.
    destruct l0. idtac.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end. idtac.
  
    destruct p0; auto.
    destruct x ; auto. idtac.

    discriminate.

    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x ; auto. idtac.

    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x ; auto. idtac.

    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x ; auto. idtac.

    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x ; auto. 

Qed.    

Lemma DePoolContract_Ф__returnOrReinvestForParticipant_tailer3_eval : forall
                                                            (l : Ledger)
                                                            (Л_stakes : RoundsBase_ι_StakeValue) 
                                                            (Л_stakeIsLost : XBool )
                                                            (Л_isValidator : XBool )
                                                            (Л_addr : XAddress)
                                                            (f: RoundsBase_ι_StakeValue -> XBool -> XBool -> XAddress -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) ),

eval_state (DePoolContract_Ф__returnOrReinvestForParticipant_tailer3 Л_stakes Л_stakeIsLost Л_isValidator Л_addr f) l = 

let newStake := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_newStake) l in
let participant := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_participant) l in
let m_minStake := eval_state (↑12 ε DePoolContract_ι_m_minStake) l in

let curPause := intMin (participant ->> DePoolLib_ι_Participant_ι_withdrawValue) newStake in
let attachedValue := 1 + curPause in
let participant := {$participant with (DePoolLib_ι_Participant_ι_withdrawValue, (participant ->> DePoolLib_ι_Participant_ι_withdrawValue) - curPause)$} in
let newStake := newStake - curPause in
let attachedValue := if (newStake <? m_minStake) then attachedValue + newStake else attachedValue in
let newStake := if (newStake <? m_minStake) then 0 else newStake in

eval_state (f Л_stakes Л_stakeIsLost Л_isValidator Л_addr)
{$ l With (LocalState_ι__returnOrReinvestForParticipant_Л_participant, participant);
        (LocalState_ι__returnOrReinvestForParticipant_Л_newStake, newStake);
        (LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue, attachedValue)$}.
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
                                            case_eq b ; 
                                            (* simpl;  *)
                                            intros                                                              
        | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
        end
  
    end) .         
Qed.


Lemma DePoolContract_Ф__returnOrReinvestForParticipant_tailer4_eval : forall
                                                            (l : Ledger)
                                                            (Л_stakes : RoundsBase_ι_StakeValue ) 
                                                            (Л_stakeIsLost : XBool )  
                                                            (Л_isValidator : XBool ) 
                                                            (Л_addr : XAddress)
                                                            (f: XAddress -> RoundsBase_ι_StakeValue -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) ),

 eval_state (DePoolContract_Ф__returnOrReinvestForParticipant_tailer4 Л_stakes Л_stakeIsLost Л_isValidator Л_addr f) l = 

 let lostFunds := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds) l in
 let round2 := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_round2) l in
(*  let newStake := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_newStake) l in *) 

 let optNewLock := Л_stakes ->> RoundsBase_ι_StakeValue_ι_lock in
 let isNewLock := isSome optNewLock in
 let params := maybeGet optNewLock in
 let oldLockAmount := params ->> RoundsBase_ι_InvestParams_ι_amount in
 let oldLockValidatorRemainingStake := round2 ->> RoundsBase_ι_Round_ι_validatorRemainingStake  in
 let deltaLockValidator := intMin oldLockAmount lostFunds in
 let amount := if Л_stakeIsLost then
                    if Л_isValidator then oldLockAmount - deltaLockValidator
                                     else (round2 ->> RoundsBase_ι_Round_ι_unused + round2 ->> RoundsBase_ι_Round_ι_recoveredStake - round2 ->> RoundsBase_ι_Round_ι_validatorRemainingStake) *
                                          (params ->> RoundsBase_ι_InvestParams_ι_amount) / (round2 ->> RoundsBase_ι_Round_ι_stake - round2 ->> RoundsBase_ι_Round_ι_validatorStake) 
                                   else oldLockAmount in
 let lostFunds := if Л_stakeIsLost then 
                        if Л_isValidator then lostFunds - deltaLockValidator 
                                         else lostFunds 
                                      else lostFunds in 
 let validatorRemainingStake := if Л_stakeIsLost then 
                        if Л_isValidator then oldLockValidatorRemainingStake + amount
                                         else oldLockValidatorRemainingStake 
                                      else oldLockValidatorRemainingStake in 
 let params := {$params with RoundsBase_ι_InvestParams_ι_amount := amount$} in 
 let (p, l') := run (↓ DePoolContract_Ф_cutWithdrawalValue params) l in
 let (newLock, withdrawalLock) := p in
 let round2 := {$round2 with (RoundsBase_ι_Round_ι_handledStakesAndRewards, round2 ->> RoundsBase_ι_Round_ι_handledStakesAndRewards + amount) ;
                             (RoundsBase_ι_Round_ι_validatorRemainingStake, validatorRemainingStake) $} in
 let l'' := if negb (withdrawalLock =? 0) then exec_state (↓ tvm_transfer (params ->> RoundsBase_ι_InvestParams_ι_owner) 
                                                                          withdrawalLock false 1 default) l' else l' in 
if isNewLock then 
 eval_state (f Л_addr Л_stakes) {$ l'' With (LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds, lostFunds);
        (LocalState_ι__returnOrReinvestForParticipant_Л_round2, round2);
        (* (LocalState_ι__returnOrReinvestForParticipant_Л_newStake, newStake + withdrawalLock); *)
        (LocalState_ι__returnOrReinvestForParticipant_Л_newLock, newLock);
        (LocalState_ι__returnOrReinvestForParticipant_Л_params, params) $} else
    eval_state (f Л_addr Л_stakes) {$ l With (LocalState_ι__returnOrReinvestForParticipant_Л_newLock, optNewLock) $} .
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
                                            case_eq b ; 
                                            (* simpl;  *)
                                            intros                                                              
        | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
        end
  
    end) . idtac.

    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x ; auto. idtac.

    destruct (x0 =? 0); auto. idtac.


    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x ; auto. idtac.

    destruct (x0 =? 0); auto. idtac.


    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x ; auto. idtac.

    destruct (x0 =? 0); auto. idtac.

    destruct Л_stakes. idtac.

    destruct RoundsBase_ι_StakeValue_ι_lock; auto. idtac.
    destruct r. idtac.


    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l0
                end
    end.
    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l1
                end
    end.
    setoid_rewrite <- Heql0 in Heql1.
    rewrite Heql1. idtac.
    destruct l0. idtac.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end. idtac.
  
    destruct p0; auto.
    destruct x ; auto. idtac.

    destruct (x0 =? 0); auto. idtac.

    discriminate.

    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x ; auto. idtac.

    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x ; auto. idtac.

    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x ; auto. idtac.

    match goal with 
    | |- ?x  => match x with 
                | context [DePoolContract_Ф_cutWithdrawalValue ?a ] => remember (DePoolContract_Ф_cutWithdrawalValue a ) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x ; auto. 

Qed.


Lemma DePoolContract_Ф__returnOrReinvestForParticipant_tailer5_eval : forall
                                                            (l : Ledger)
                                                            (Л_addr : XAddress)
                                                            (Л_stakes : RoundsBase_ι_StakeValue ) 
                                                            (f: XAddress -> RoundsBase_ι_StakeValue -> LedgerT (RoundsBase_ι_Round # RoundsBase_ι_Round) ),
 eval_state (DePoolContract_Ф__returnOrReinvestForParticipant_tailer5 Л_addr Л_stakes f) l = 

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
                     if (isVesting && (newVesting ->> RoundsBase_ι_InvestParams_ι_amount =? 0))%bool then None
                     else newOptVesting in
let newOptLock := if m_poolClosed then newOptLock else
                     if (isLock && (newLock ->> RoundsBase_ι_InvestParams_ι_amount =? 0))%bool then None
                     else newOptLock in
let newStake := if m_poolClosed then newStake else
                        if (negb reinvest) then 0 else newStake in
let (rp, l') :=  if m_poolClosed then 
                    if isVesting then 
                    let lv := exec_state (↓ tvm_transfer (newVesting ->> RoundsBase_ι_InvestParams_ι_owner) 
                                                     (newVesting ->> RoundsBase_ι_InvestParams_ι_amount) 
                                                     false 1 default) l in
                    if isLock then ((round0, participant), exec_state (↓ tvm_transfer (newLock ->> RoundsBase_ι_InvestParams_ι_owner) 
                                            (newLock ->> RoundsBase_ι_InvestParams_ι_amount) 
                                            false 1 default) lv)
                              else ((round0, participant), lv)
                    else if isLock then ((round0, participant) , exec_state (↓ tvm_transfer (newLock ->> RoundsBase_ι_InvestParams_ι_owner) 
                                            (newLock ->> RoundsBase_ι_InvestParams_ι_amount) 
                                            false 1 default) l)
                            else ((round0, participant) , l)
                  else  run (↓ RoundsBase_Ф__addStakes round0 participant Л_addr newStake newOptVesting newOptLock) l in
let (round0, participant) := rp in                   
eval_state (f Л_addr Л_stakes) {$l' With 
        (LocalState_ι__returnOrReinvestForParticipant_Л_newStake, newStake ); 
        (LocalState_ι__returnOrReinvestForParticipant_Л_newLock, newOptLock);
        (LocalState_ι__returnOrReinvestForParticipant_Л_newVesting, newOptVesting);
        (LocalState_ι__returnOrReinvestForParticipant_Л_round0, round0);
        (LocalState_ι__returnOrReinvestForParticipant_Л_participant, participant);
        (LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue, attachedValue) $}   .                                                               
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
                                            case_eq b ; 
                                            (* simpl;  *)
                                            intros                                                              
        | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
        end
  
    end) . idtac.

    match goal with 
    | |- ?x  => match x with 
                | context [RoundsBase_Ф__addStakes ?a ?b ?c ?d ?e ?g] => remember (RoundsBase_Ф__addStakes a b c d e g) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x; auto.

    match goal with 
    | |- ?x  => match x with 
                | context [RoundsBase_Ф__addStakes ?a ?b ?c ?d ?e ?g] => remember (RoundsBase_Ф__addStakes a b c d e g) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x; auto.

    match goal with 
    | |- ?x  => match x with 
                | context [RoundsBase_Ф__addStakes ?a ?b ?c ?d ?e ?g] => remember (RoundsBase_Ф__addStakes a b c d e g) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x; auto.

    match goal with 
    | |- ?x  => match x with 
                | context [RoundsBase_Ф__addStakes ?a ?b ?c ?d ?e ?g] => remember (RoundsBase_Ф__addStakes a b c d e g) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x; auto.

    match goal with 
    | |- ?x  => match x with 
                | context [RoundsBase_Ф__addStakes ?a ?b ?c ?d ?e ?g] => remember (RoundsBase_Ф__addStakes a b c d e g) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x; auto.

    match goal with 
    | |- ?x  => match x with 
                | context [RoundsBase_Ф__addStakes ?a ?b ?c ?d ?e ?g] => remember (RoundsBase_Ф__addStakes a b c d e g) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x; auto.

    match goal with 
    | |- ?x  => match x with 
                | context [RoundsBase_Ф__addStakes ?a ?b ?c ?d ?e ?g] => remember (RoundsBase_Ф__addStakes a b c d e g) as l0
                end
    end.
    destruct l0.
    
    match goal with 
    | |- ?x  => match x with 
                | context [p ?a] => remember (p a)
                end
    end.
  
    destruct p0; auto.
    destruct x; auto.
Qed.    


Lemma DePoolContract_Ф__returnOrReinvestForParticipant_tailer6_eval : forall
                                                            (l : Ledger)
                                                            (Л_addr : XAddress)
                                                            (Л_stakes : RoundsBase_ι_StakeValue ) ,
                                                           
 eval_state (DePoolContract_Ф__returnOrReinvestForParticipant_tailer6 Л_addr Л_stakes ) l = 

 let round2 := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_round2) l in
 let round0 := eval_state (↑17 ε LocalState_ι__returnOrReinvestForParticipant_Л_round0) l in

 (round0, round2).
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
  
    end) . 
Qed.    
