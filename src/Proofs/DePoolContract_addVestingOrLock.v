
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



 (* function addVestingOrLock(uint64 stake, 
                             address beneficiary, 
                             uint32 withdrawalPeriod, 
                             uint32 totalPeriod, 
                             bool isVesting) private { :  LedgerT (XErrorValue (XValueValue True) XInteger)
(*if1*) if (m_poolClosed) {
            return _sendError(STATUS_DEPOOL_CLOSED, 0);
        }

(*req*) require(beneficiary.isStdAddrWithoutAnyCast(), Errors.INVALID_ADDRESS);

(*if2*) if (beneficiary == address(0)) {
            beneficiary = msg.sender;
        }

        uint64 msgValue = uint64(msg.value);
(*if3*) if (msgValue < uint(stake) + STAKE_FEE) {
            return _sendError(STATUS_FEE_TOO_SMALL, STAKE_FEE);
        }
        uint64 fee = msgValue - stake;

        uint64 halfStake = stake / 2;
(*if4*) if (halfStake < m_minStake) {
            return _sendError(STATUS_STAKE_TOO_SMALL, 2 * m_minStake);
        }

(*if5*) if (withdrawalPeriod > totalPeriod) {
            return _sendError(STATUS_WITHDRAWAL_PERIOD_GREATER_TOTAL_PERIOD, 0);
        }

(*if6*) if (totalPeriod >= 18 * (365 days)) { // ~18 years
            return _sendError(STATUS_TOTAL_PERIOD_MORE_18YEARS, 0);
        }

(*if7*) if (withdrawalPeriod == 0) {
            return _sendError(STATUS_WITHDRAWAL_PERIOD_IS_ZERO, 0);
        }

(*if8*)  if (totalPeriod % withdrawalPeriod != 0) {
            return _sendError(STATUS_TOTAL_PERIOD_IS_NOT_DIVED_BY_WITHDRAWAL_PERIOD, 0);
        }

        DePoolLib.Participant participant = getOrCreateParticipant(beneficiary);
(*if9*) if (isVesting) {
(*if10*)     if (participant.haveVesting) {
                return _sendError(STATUS_PARTICIPANT_HAVE_ALREADY_VESTING, 0);
            }
        } else {
(*if11*)     if (participant.haveLock) {
                return _sendError(STATUS_PARTICIPANT_HAVE_ALREADY_LOCK, 0);
            }
        }

        uint64 withdrawalValue = math.muldiv(halfStake, withdrawalPeriod, totalPeriod);
(*if12*)if (withdrawalValue == 0) {
            return _sendError(STATUS_PERIOD_PAYMENT_IS_ZERO, 0);
        }

        InvestParams vestingOrLock = InvestParams({
            amount: halfStake,
            lastWithdrawalTime: uint64(now),
            withdrawalPeriod: withdrawalPeriod,
            withdrawalValue: withdrawalValue,
            owner: msg.sender
        });

        optional(InvestParams) v;
        optional(InvestParams) l;
(*if13*)if (isVesting) {
            v.set(vestingOrLock);
        } else {
            l.set(vestingOrLock);
        }

        Round round = getRoundPre0();
        (round, participant) = _addStakes(round, participant, beneficiary, 0, v, l);
        setRoundPre0(round);

        round = getRound0();
        (round, participant) = _addStakes(round, participant, beneficiary, 0, v, l);
        setRound0(round);

        _setOrDeleteParticipant(beneficiary, participant);
        sendAcceptAndReturnChange128(fee);
    }
		
*)
(* Check intMulDiv.
Check exec_state ( ↓ ( DePoolContract_Ф_addVestingOrLock' default default default default default )) default .
 *)

 Opaque DePoolContract_Ф_sendAcceptAndReturnChange128 RoundsBase_Ф__addStakes.

(*  Parameter foo: XInteger -> LedgerT True.

 Compute ForIndexed (xListCons xInt1 (xListCons xInt0 xListNil)) do (fun (i: XInteger) => foo i).
 *)


Definition DePoolContract_Ф_addVestingOrLock'_tailer1 (Л_stake Л_halfStake Л_withdrawalPeriod Л_withdrawalValue Л_beneficiary: XInteger) 
                                                     (Л_isVesting: XBool)
                                                     (Л_participant: DePoolLib_ι_Participant)
                                                     (Л_fee: XInteger) : LedgerT True :=
( ↑17 U1! LocalState_ι_addVestingOrLock_Л_participant := $ Л_participant ) >>                                                     
( 
ForIndexed (xListCons xInt0 (xListCons xInt1 xListNil)) do (fun (i: XInteger) => 
U0! Л_isFirstPart := ( $ i ?== $ xInt0 ) ;
U0! Л_vestingOrLock := {|| 
    RoundsBase_ι_InvestParams_ι_amount := $ Л_isFirstPart ? $ Л_halfStake ::: $Л_stake !- $Л_halfStake,
    RoundsBase_ι_InvestParams_ι_lastWithdrawalTime := tvm_now () ,
    RoundsBase_ι_InvestParams_ι_withdrawalPeriod := $ Л_withdrawalPeriod ,
    RoundsBase_ι_InvestParams_ι_withdrawalValue := $ Л_withdrawalValue ,
    RoundsBase_ι_InvestParams_ι_owner := msg_sender () ||} ;

( ↑17 U1! LocalState_ι_addVestingOrLock_Л_v := $ default ) >>
( ↑17 U1! LocalState_ι_addVestingOrLock_Л_l := $ default ) >>

If ( $ Л_isVesting )
then
{
  ↑17 U1! LocalState_ι_addVestingOrLock_Л_v ->set ( $ Л_vestingOrLock )
}
else
{
 ↑17 U1! LocalState_ι_addVestingOrLock_Л_l ->set ( $ Л_vestingOrLock )
} >> 

U0! Л_round := $Л_isFirstPart ? RoundsBase_Ф_getRoundPre0 () ::: RoundsBase_Ф_getRound0 ; 
U0! Л_participant := ↑17 D2! LocalState_ι_addVestingOrLock_Л_participant ;
U0!  {( Л_round, Л_participant )} := RoundsBase_Ф__addStakes (! ($ Л_round) ,  ( $ Л_participant ) ,
                                                            ( $ Л_beneficiary ) ,
                                                            ( $ xInt0 ) , 
                                                            ( ↑17 D2! LocalState_ι_addVestingOrLock_Л_v ),
                                                            ( ↑17 D2! LocalState_ι_addVestingOrLock_Л_l )  !) ;
(↑17 U1! LocalState_ι_addVestingOrLock_Л_participant := $ Л_participant) >>                                                            
$ Л_isFirstPart ? RoundsBase_Ф_setRoundPre0 (! $ Л_round !) ::: RoundsBase_Ф_setRound0 (! $ Л_round !) 
) ) >> 

ParticipantBase_Ф__setOrDeleteParticipant (! ($ Л_beneficiary) ,  ↑17 D2! LocalState_ι_addVestingOrLock_Л_participant  !)  >>
DePoolContract_Ф_sendAcceptAndReturnChange128 (! $ Л_fee !) .		


 

Lemma DePoolContract_Ф_addVestingOrLock'_tailer_exec : forall (Л_stake Л_halfStake Л_withdrawalPeriod Л_withdrawalValue Л_beneficiary: XInteger) 
                                                     (Л_isVesting: XBool)
                                                     (Л_participant: DePoolLib_ι_Participant)
                                                     (Л_fee: XInteger)
                                                     (l: Ledger) , 
exec_state (DePoolContract_Ф_addVestingOrLock'_tailer1 Л_stake Л_halfStake Л_withdrawalPeriod Л_withdrawalValue Л_beneficiary Л_isVesting Л_participant Л_fee) l =                                                     

let beneficiary := Л_beneficiary in

let vestingOrLockPre0 := RoundsBase_ι_InvestParamsC 
                        Л_halfStake
                       ( eval_state tvm_now l ) 
                        Л_withdrawalPeriod 
                        Л_withdrawalValue
                       ( eval_state  msg_sender  l ) in
let vvPre0 := if Л_isVesting then ( xMaybeSome vestingOrLockPre0 ) else None in 
let llPre0 := if ( negb Л_isVesting ) then ( xMaybeSome vestingOrLockPre0 ) else None  in 
let roundPre0 := eval_state ( ↓ RoundsBase_Ф_getRoundPre0 ) l in
let l_localPre0 := {$l With (LocalState_ι_addVestingOrLock_Л_v , vvPre0) ; (LocalState_ι_addVestingOrLock_Л_l , llPre0) ;  (LocalState_ι_addVestingOrLock_Л_participant, Л_participant) $} in
let ( rp', l_addStakes ) := run ( ↓ ( RoundsBase_Ф__addStakes roundPre0 Л_participant beneficiary 0 vvPre0 llPre0 ) ) l_localPre0 in 
let ( roundPre0' , participant' ) := rp' in
let l_addStakes' := {$l_addStakes With (LocalState_ι_addVestingOrLock_Л_participant, participant') $} in
let l_setRoundPre0 := exec_state ( ↓ ( RoundsBase_Ф_setRoundPre0 roundPre0' ) ) l_addStakes'  in 


let vestingOrLock0 := RoundsBase_ι_InvestParamsC 
                        (Л_stake - Л_halfStake)
                       ( eval_state tvm_now l_setRoundPre0 ) 
                        Л_withdrawalPeriod 
                        Л_withdrawalValue
                       ( eval_state  msg_sender  l_setRoundPre0 ) in  
let vv0 := if Л_isVesting then ( xMaybeSome vestingOrLock0 ) else None in 
let ll0 := if ( negb Л_isVesting ) then ( xMaybeSome vestingOrLock0 ) else None  in
let round0 := eval_state ( ↓ RoundsBase_Ф_getRound0 ) l_setRoundPre0 in
let l_local0 := {$l_setRoundPre0 With (LocalState_ι_addVestingOrLock_Л_v , vv0) ; (LocalState_ι_addVestingOrLock_Л_l , ll0)  $} in
let ( rp'', l_addStakes'' ) := run ( ↓ ( RoundsBase_Ф__addStakes round0 participant' beneficiary 0 vv0 ll0 ) ) l_local0 in 
let ( round0' , participant'') := rp'' in
let l_addStakes''' := {$l_addStakes'' With (LocalState_ι_addVestingOrLock_Л_participant, participant'') $} in
let l_setRound0 := exec_state ( ↓ ( RoundsBase_Ф_setRound0 round0' ) ) l_addStakes'''  in

let l_setOrDeleteParticipant := exec_state ( ↓ ( ParticipantBase_Ф__setOrDeleteParticipant beneficiary participant'' ) ) l_setRound0 in 
let l_send := exec_state ( ↓ ( DePoolContract_Ф_sendAcceptAndReturnChange128 Л_fee ) ) l_setOrDeleteParticipant in 

l_send. 
Proof.
        intros.
        destruct l as
         (Ledger_ι_DebugDePool, Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ConfigParamsBase, Ledger_ι_ParticipantBase, 
        Ledger_ι_DePoolHelper, Ledger_ι_Errors, Ledger_ι_InternalErrors, Ledger_ι_DePoolLib, Ledger_ι_DePoolProxyContract, 
        Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_DePool, Ledger_ι_Participant, Ledger_ι_TestElector, 
        Ledger_ι_VMState, Ledger_ι_LocalState).
        destruct Ledger_ι_DebugDePool, Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ConfigParamsBase, Ledger_ι_ParticipantBase, 
        Ledger_ι_DePoolHelper, Ledger_ι_Errors, Ledger_ι_InternalErrors, Ledger_ι_DePoolLib, Ledger_ι_DePoolProxyContract, 
        Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_DePool, Ledger_ι_Participant, Ledger_ι_TestElector, 
        Ledger_ι_VMState, Ledger_ι_LocalState.
      
        compute. idtac.
          
        replace (0 =? 0) with true.
        replace (0 =? 1) with false.
        replace (1 =? 0) with false.
        replace (1 =? 1) with true.

          
        Time  repeat (
            
            time match goal with
              | |- ?x =>
                match x with
     
                  | context [if ?b then _ else _] =>  idtac "if..." b; 
                                                    repeat rewrite ifSimpleState ; 
                                                    repeat rewrite ifFunApply ;                                          
                                                    case_eq b ; (* use case_eq to see destruction results *)
                                                    simpl  ; intros                                                                                                
                   
                  | context  [match RoundsBase_Ф__addStakes ?a ?b ?c ?d ?e ?f
                                          with
                                          | SimpleState s => s
                                          end ?m] => idtac "found RoundsBase_Ф__addStakes ..."  a b c d e f; 
                                                      let p := fresh"p" in
                                                      destruct (RoundsBase_Ф__addStakes a b c d e f) as (p);
                                                      let v := fresh"v" in
                                                      let l := fresh"l" in 
                                                      destruct (p m) as [v l]; 
                                                      let Ledger_ι_DebugDePool := fresh "Ledger_ι_DebugDePool" in
                                                      let Ledger_ι_ValidatorBase := fresh "Ledger_ι_ValidatorBase" in
                                                      let Ledger_ι_ProxyBase := fresh "Ledger_ι_ProxyBase" in
                                                      let Ledger_ι_ConfigParamsBase := fresh "Ledger_ι_ConfigParamsBase" in
                                                      let Ledger_ι_ParticipantBase := fresh "Ledger_ι_ParticipantBase" in
                                                      let Ledger_ι_DePoolHelper := fresh "Ledger_ι_DePoolHelper" in
                                                      let Ledger_ι_Errors := fresh "Ledger_ι_Errors" in
                                                      let Ledger_ι_InternalErrors := fresh "Ledger_ι_InternalErrors" in
                                                      let Ledger_ι_DePoolLib := fresh "Ledger_ι_DePoolLib" in
                                                      let Ledger_ι_DePoolProxyContract := fresh "Ledger_ι_DePoolProxyContract" in
                                                      let Ledger_ι_RoundsBase := fresh "Ledger_ι_RoundsBase" in
                                                      let Ledger_ι_DePoolContract := fresh "Ledger_ι_DePoolContract" in
                                                      let Ledger_ι_DePool := fresh "Ledger_ι_DePool" in
                                                      let Ledger_ι_Participant := fresh "Ledger_ι_Participant" in
                                                      let Ledger_ι_TestElector := fresh "Ledger_ι_TestElector" in
                                                      let Ledger_ι_VMState := fresh "Ledger_ι_VMState" in
                                                      let Ledger_ι_LocalState := fresh "Ledger_ι_LocalState" in
                                                      destruct l as
                                                      (Ledger_ι_DebugDePool, Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ConfigParamsBase, Ledger_ι_ParticipantBase, 
                                                    Ledger_ι_DePoolHelper, Ledger_ι_Errors, Ledger_ι_InternalErrors, Ledger_ι_DePoolLib, Ledger_ι_DePoolProxyContract, 
                                                    Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_DePool, Ledger_ι_Participant, Ledger_ι_TestElector, 
                                                    Ledger_ι_VMState, Ledger_ι_LocalState);
                                                    destruct Ledger_ι_DebugDePool, Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ConfigParamsBase, Ledger_ι_ParticipantBase, 
                                                    Ledger_ι_DePoolHelper, Ledger_ι_Errors, Ledger_ι_InternalErrors, Ledger_ι_DePoolLib, Ledger_ι_DePoolProxyContract, 
                                                    Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_DePool, Ledger_ι_Participant, Ledger_ι_TestElector, 
                                                    Ledger_ι_VMState, Ledger_ι_LocalState;
                                                      destruct v ;
                                                      simpl                                   
                   | context  [match DePoolContract_Ф_sendAcceptAndReturnChange128 ?a 
                        with
                        | SimpleState s => s
                        end ?m] => idtac "found DePoolContract_Ф_sendAcceptAndReturnChange128 ..."  a; 
                                    let p := fresh"p" in
                                    destruct (DePoolContract_Ф_sendAcceptAndReturnChange128 a) as (p);
                                    let v := fresh"v" in
                                    let l := fresh"l" in 
                                    destruct (p m) as [v l]; 
                                    let Ledger_ι_DebugDePool := fresh "Ledger_ι_DebugDePool" in
                                    let Ledger_ι_ValidatorBase := fresh "Ledger_ι_ValidatorBase" in
                                    let Ledger_ι_ProxyBase := fresh "Ledger_ι_ProxyBase" in
                                    let Ledger_ι_ConfigParamsBase := fresh "Ledger_ι_ConfigParamsBase" in
                                    let Ledger_ι_ParticipantBase := fresh "Ledger_ι_ParticipantBase" in
                                    let Ledger_ι_DePoolHelper := fresh "Ledger_ι_DePoolHelper" in
                                    let Ledger_ι_Errors := fresh "Ledger_ι_Errors" in
                                    let Ledger_ι_InternalErrors := fresh "Ledger_ι_InternalErrors" in
                                    let Ledger_ι_DePoolLib := fresh "Ledger_ι_DePoolLib" in
                                    let Ledger_ι_DePoolProxyContract := fresh "Ledger_ι_DePoolProxyContract" in
                                    let Ledger_ι_RoundsBase := fresh "Ledger_ι_RoundsBase" in
                                    let Ledger_ι_DePoolContract := fresh "Ledger_ι_DePoolContract" in
                                    let Ledger_ι_DePool := fresh "Ledger_ι_DePool" in
                                    let Ledger_ι_Participant := fresh "Ledger_ι_Participant" in
                                    let Ledger_ι_TestElector := fresh "Ledger_ι_TestElector" in
                                    let Ledger_ι_VMState := fresh "Ledger_ι_VMState" in
                                    let Ledger_ι_LocalState := fresh "Ledger_ι_LocalState" in
                                    destruct l as
                                    (Ledger_ι_DebugDePool, Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ConfigParamsBase, Ledger_ι_ParticipantBase, 
                                  Ledger_ι_DePoolHelper, Ledger_ι_Errors, Ledger_ι_InternalErrors, Ledger_ι_DePoolLib, Ledger_ι_DePoolProxyContract, 
                                  Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_DePool, Ledger_ι_Participant, Ledger_ι_TestElector, 
                                  Ledger_ι_VMState, Ledger_ι_LocalState);
                                  destruct Ledger_ι_DebugDePool, Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ConfigParamsBase, Ledger_ι_ParticipantBase, 
                                  Ledger_ι_DePoolHelper, Ledger_ι_Errors, Ledger_ι_InternalErrors, Ledger_ι_DePoolLib, Ledger_ι_DePoolProxyContract, 
                                  Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_DePool, Ledger_ι_Participant, Ledger_ι_TestElector, 
                                  Ledger_ι_VMState, Ledger_ι_LocalState;
                                  (*  destruct v ; *)
                                    simpl                                                                                           
                  | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
                end
            end) . 

            Transparent Z.eqb.

            all: compute; auto.

            all: pr_numgoals.
Qed.           




Definition DePoolContract_Ф_addVestingOrLock'_header ( Л_stake : XInteger64 )
                                                      ( Л_beneficiary : XAddress )
                                                      ( Л_withdrawalPeriod : XInteger32 )
                                                      ( Л_totalPeriod : XInteger32 )
                                                      ( Л_isVesting : XBool ) 
                                                      ( f : XInteger -> XInteger -> XInteger -> XInteger -> XInteger -> XBool -> DePoolLib_ι_Participant -> XInteger -> LedgerT True):  
                                                      LedgerT (XValueValue True) := 
If!! ( ↑ε12 DePoolContract_ι_m_poolClosed ) 
then {
   DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_DEPOOL_CLOSED , $ xInt0  !) >>=
	fun x => return! ( xError x) 
 } ; 
   (* if (!beneficiary.isStdAddrWithoutAnyCast() || beneficiary == address(0))
    return _sendError(STATUS_INVALID_ADDRESS, 0);   
   if (msg.sender == beneficiary)
    return _sendError(STATUS_INVALID_BENEFICIARY, 0); *)
If!! ( ( !¬ ( ( $ Л_beneficiary ) ->isStdAddrWithoutAnyCast() )) !| ( $ Л_beneficiary ?== $ xInt0 ) ) 
then {  
   DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_INVALID_ADDRESS , $ xInt0  !) >>=
	fun x => return! ( xError x)
 } ; 

If!! ( ( msg_sender () ) ?== $ Л_beneficiary ) 
then { 
   DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_INVALID_BENEFICIARY , $ xInt0  !) >>=
	fun x => return! ( xError x) 
 } ; 
     
U0! Л_msgValue := msg_value () ; 
If!! ( $ Л_msgValue ?< ( $ Л_stake !+ ( ↑12 D2! DePoolContract_ι_STAKE_FEE ) ) ) 
then
{
DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_FEE_TOO_SMALL ,
        ↑ε12 DePoolContract_ι_STAKE_FEE !) >>=
fun x => return! ( xError x )
} ; 

U0! Л_fee := $ Л_msgValue !- $ Л_stake ;
U0! Л_halfStake := $ Л_stake !/ $ xInt2 ; 

If!! ( $ Л_halfStake ?< ↑12 D2! DePoolContract_ι_m_minStake )
then
{
DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_STAKE_TOO_SMALL ,
        $ xInt2 !* ( ↑12 D2! DePoolContract_ι_m_minStake ) !) >>=
fun x => return! ( xError x )
} ;  

If!! ( $ Л_withdrawalPeriod ?> $ Л_totalPeriod )
then 
{
DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_WITHDRAWAL_PERIOD_GREATER_TOTAL_PERIOD ,
        $ xInt0 !) >>=
fun x => return! ( xError x )
} ;

If!! ( $ Л_totalPeriod ?>= $ xInt18 !* $ xInt365 !* $ x1_day )
then
{
DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_TOTAL_PERIOD_MORE_18YEARS ,
        $ xInt0 !) >>=
fun x => return! ( xError x )
} ; 

If!! ( $ Л_withdrawalPeriod ?== $ xInt0 )
then
{
DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_WITHDRAWAL_PERIOD_IS_ZERO ,
        $ xInt0 !) >>=
fun x => return! ( xError x )
} ; 

If!! ( $ Л_totalPeriod !% $ Л_withdrawalPeriod ?!= $ xInt0 )
then
{ 
DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_TOTAL_PERIOD_IS_NOT_DIVISIBLE_BY_WITHDRAWAL_PERIOD ,
        $ xInt0 !) >>=
fun x => return! ( xError x )
} ; 

U0! Л_participant := ParticipantBase_Ф_getOrCreateParticipant (! $ Л_beneficiary !) ;
If! ( $ Л_isVesting )
then {
If! ( $ Л_participant ->> DePoolLib_ι_Participant_ι_haveVesting )
then {
DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_PARTICIPANT_ALREADY_HAS_VESTING ,
        $ xInt0 !) >>=
fun x => return! ( xError x )
} ; $ I
}
else
{
If! ( $ Л_participant ->> DePoolLib_ι_Participant_ι_haveLock )
then {
DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_PARTICIPANT_ALREADY_HAS_LOCK ,
        $ xInt0 !) >>=
fun x => return! ( xError x )
} ; $ I
} ; 


U0! Л_withdrawalValue := math->muldiv (! $ Л_halfStake , $ Л_withdrawalPeriod , $ Л_totalPeriod !) ; 
              (* If! ( $ Л_withdrawalValue ?== $ xInt0 )
              then
              {
              DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_PERIOD_PAYMENT_IS_ZERO , $ xInt0 !) >>=
              fun x => return! ( xError x )
              } ;  *)

f Л_stake Л_halfStake Л_withdrawalPeriod Л_withdrawalValue Л_beneficiary Л_isVesting Л_participant Л_fee.

		

(* Check RoundsBase_ι_InvestParamsC. *)

Opaque Z.eqb.

Lemma DePoolContract_Ф_addVestingOrLock'_header_exec : forall ( Л_stake : XInteger64 )
                                                ( Л_beneficiary : XAddress )
                                                ( Л_withdrawalPeriod : XInteger32 )
                                                ( Л_totalPeriod : XInteger32 )
                                                ( Л_isVesting : XBool )
                                                ( f : XInteger -> XInteger -> XInteger -> XInteger -> XInteger -> XBool -> DePoolLib_ι_Participant -> XInteger -> LedgerT True )
                                                ( l: Ledger ) , 

exec_state (DePoolContract_Ф_addVestingOrLock'_header Л_stake Л_beneficiary Л_withdrawalPeriod Л_totalPeriod Л_isVesting f) l =

let if1 : bool := eval_state ( ↑12 ε DePoolContract_ι_m_poolClosed ) l in 
let if2 : bool := ((negb (isStdAddrWithoutAnyCast Л_beneficiary)) || (Л_beneficiary =? 0))%bool in 
let beneficiary := Л_beneficiary in
let msgSender := eval_state msg_sender l in
let if3 : bool := msgSender =? beneficiary in
let msgValue := eval_state  msg_value l in
let STAKE_FEE := eval_state ( ↑12 ε DePoolContract_ι_STAKE_FEE ) l in 
let if4 : bool := msgValue <? Л_stake + STAKE_FEE in 
let fee := msgValue - Л_stake  in
let halfStake := Л_stake / 2  in
let m_minStake := eval_state ( ↑12 ε DePoolContract_ι_m_minStake ) l in
let if5 : bool := halfStake <? m_minStake in
let if6 : bool := Л_withdrawalPeriod >? Л_totalPeriod in
let if7 : bool := Л_totalPeriod >=? 18 * 365 * 86400 in
let if8 : bool := Л_withdrawalPeriod =? 0  in
let if9 : bool := negb ( Z.modulo Л_totalPeriod Л_withdrawalPeriod  =? 0 ) in
let (participant, l_getcreate) := run ( ↓ ParticipantBase_Ф_getOrCreateParticipant beneficiary ) l in
let if10 : bool := Л_isVesting in
let if11 : bool := participant ->> DePoolLib_ι_Participant_ι_haveVesting  in
let if12 : bool := participant ->> DePoolLib_ι_Participant_ι_haveLock  in
let withdrawalValue :=  halfStake * Л_withdrawalPeriod / Л_totalPeriod  in
(* let if13 : bool := withdrawalValue =? 0  in *)

if if1 then exec_state ( ↓ ( DePoolContract_Ф__sendError ( eval_state ( ↑12 ε DePoolContract_ι_STATUS_DEPOOL_CLOSED ) l ) 0 ) ) l else 
        if if2 then exec_state ( ↓ ( DePoolContract_Ф__sendError ( eval_state ( ↑12 ε DePoolContract_ι_STATUS_INVALID_ADDRESS ) l ) 0 ) ) l else 
                if if3 then exec_state ( ↓ ( DePoolContract_Ф__sendError ( eval_state ( ↑12 ε DePoolContract_ι_STATUS_INVALID_BENEFICIARY ) l ) 0 ) ) l else
                        if if4 then exec_state ( ↓ ( DePoolContract_Ф__sendError 
                        ( eval_state ( ↑12 ε DePoolContract_ι_STATUS_FEE_TOO_SMALL ) l ) 
                        ( eval_state ( ↑12 ε DePoolContract_ι_STAKE_FEE ) l ) ) ) l else
                                if if5 then exec_state ( ↓ ( DePoolContract_Ф__sendError 
                                ( eval_state ( ↑12 ε DePoolContract_ι_STATUS_STAKE_TOO_SMALL ) l ) 
                                ( 2 * ( eval_state ( ↑12 ε DePoolContract_ι_m_minStake ) l ) ) ) ) l else 
                                        if if6 then exec_state ( ↓ ( DePoolContract_Ф__sendError 
                                        ( eval_state ( ↑12 ε DePoolContract_ι_STATUS_WITHDRAWAL_PERIOD_GREATER_TOTAL_PERIOD ) l ) 0 ) ) l else
        if if7 then exec_state ( ↓ ( DePoolContract_Ф__sendError 
        ( eval_state ( ↑12 ε DePoolContract_ι_STATUS_TOTAL_PERIOD_MORE_18YEARS ) l ) 0 ) ) l else 
                if if8 then exec_state ( ↓ ( DePoolContract_Ф__sendError 
                ( eval_state ( ↑12 ε DePoolContract_ι_STATUS_WITHDRAWAL_PERIOD_IS_ZERO ) l ) 0 ) ) l else
                        if if9 then exec_state ( ↓ ( DePoolContract_Ф__sendError 
                        ( eval_state ( ↑12 ε DePoolContract_ι_STATUS_TOTAL_PERIOD_IS_NOT_DIVISIBLE_BY_WITHDRAWAL_PERIOD ) l ) 0 ) ) l else
                                    if (if10 && if11)%bool then exec_state ( ↓ ( DePoolContract_Ф__sendError 
                                    ( eval_state ( ↑12 ε DePoolContract_ι_STATUS_PARTICIPANT_ALREADY_HAS_VESTING ) l ) 0 ) ) l else
                                        if ((negb if10) && if12)%bool then exec_state ( ↓ ( DePoolContract_Ф__sendError 
                                        ( eval_state ( ↑12 ε DePoolContract_ι_STATUS_PARTICIPANT_ALREADY_HAS_LOCK ) l ) 0 ) ) l else 
        (* if if13 then exec_state ( ↓ ( DePoolContract_Ф__sendError 
        ( eval_state ( ↑12 ε DePoolContract_ι_STATUS_PERIOD_PAYMENT_IS_ZERO ) l ) 0 ) ) l 
                else *) exec_state (f Л_stake halfStake Л_withdrawalPeriod withdrawalValue Л_beneficiary Л_isVesting participant fee) l_getcreate .

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
                                                case_eq b ; 
                                                simpl  ; intros 
            | context  [match f ?a ?b ?c ?d ?e ?g
                  with
                  | SimpleState s => s
                  end ?m] => idtac "found f ..." a b c d e g; 
                             let p := fresh"p" in
                             destruct (f a b c d e g) as (p);
                             let v := fresh"v" in
                             let l := fresh"l" in 
                             destruct (p m) as [v l]; 
                             destruct l ; 
                             (* destruct v ; *)
                             simpl                                                                                                   
            | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
            end
      
       
        end) . 

        all: pr_numgoals.

        
        match goal with 
        | |- ?G => match G with
                   | context [f ?a ?b ?c ?d ?e ?g ?h ?i] => destruct (f a b c d e g h i)
                   end
        end.

        match goal with 
        | |- ?G => match G with
                   | context [p ?a] => destruct (p a)
                   end
        end.

        auto.

        match goal with 
        | |- ?G => match G with
                   | context [f ?a ?b ?c ?d ?e ?g ?h ?i] => destruct (f a b c d e g h i)
                   end
        end.

        match goal with 
        | |- ?G => match G with
                   | context [p ?a] => destruct (p a)
                   end
        end.

        auto.

        match goal with 
        | |- ?G => match G with
                   | context [f ?a ?b ?c ?d ?e ?g ?h ?i] => destruct (f a b c d e g h i)
                   end
        end.

        match goal with 
        | |- ?G => match G with
                   | context [p ?a] => destruct (p a)
                   end
        end.

        auto.

        match goal with 
        | |- ?G => match G with
                   | context [f ?a ?b ?c ?d ?e ?g ?h ?i] => destruct (f a b c d e g h i)
                   end
        end.

        match goal with 
        | |- ?G => match G with
                   | context [p ?a] => destruct (p a)
                   end
        end.

        auto.

Qed.        
 



 Lemma DePoolContract_Ф_addVestingOrLock'_eval : forall ( Л_stake : XInteger64 )
                                                ( Л_beneficiary : XAddress )
                                                ( Л_withdrawalPeriod : XInteger32 )
                                                ( Л_totalPeriod : XInteger32 )
                                                ( Л_isVesting : XBool )
                                                ( l: Ledger ) , 

eval_state (DePoolContract_Ф_addVestingOrLock' Л_stake Л_beneficiary Л_withdrawalPeriod Л_totalPeriod Л_isVesting) l =

let if1 : bool := eval_state ( ↑12 ε DePoolContract_ι_m_poolClosed ) l in 
let if2 : bool := ((negb (isStdAddrWithoutAnyCast Л_beneficiary)) || (Л_beneficiary =? 0))%bool in 
let beneficiary := Л_beneficiary in
let msgSender := eval_state msg_sender l in
let if3 : bool := msgSender =? beneficiary in
let msgValue := eval_state  msg_value l in
let STAKE_FEE := eval_state ( ↑12 ε DePoolContract_ι_STAKE_FEE ) l in 
let if4 : bool := msgValue <? Л_stake + STAKE_FEE in 
let fee := msgValue - Л_stake  in
let halfStake := Л_stake / 2  in
let m_minStake := eval_state ( ↑12 ε DePoolContract_ι_m_minStake ) l in
let if5 : bool := halfStake <? m_minStake in
let if6 : bool := Л_withdrawalPeriod >? Л_totalPeriod in
let if7 : bool := Л_totalPeriod >=? 18 * 365 * 86400 in
let if8 : bool := Л_withdrawalPeriod =? 0  in
let if9 : bool := negb ( Z.modulo Л_totalPeriod Л_withdrawalPeriod  =? 0 ) in
let (participant, l_getcreate) := run ( ↓ ParticipantBase_Ф_getOrCreateParticipant beneficiary ) l in
let if10 : bool := Л_isVesting in
let if11 : bool := participant ->> DePoolLib_ι_Participant_ι_haveVesting  in
let if12 : bool := participant ->> DePoolLib_ι_Participant_ι_haveLock  in
let withdrawalValue :=  halfStake * Л_withdrawalPeriod / Л_totalPeriod  in
let if13 : bool := withdrawalValue =? 0  in

if if1 then Error I else 
        if if2 then Error I else 
                if if3 then Error I else
                        if if4 then Error I else
                                if if5 then Error I else 
                                        if if6 then Error I else
        if if7 then Error I else 
                if if8 then Error I else
                        if if9 then Error I else
                                    if (if10 && if11)%bool then Error I else
                                        if ((negb if10) && if12)%bool then Error I else 
        (* if if13 then Error I else *) Value I  .
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
                                                case_eq b ; 
                                                simpl  ; intros 
             | context  [match RoundsBase_Ф__addStakes ?a ?b ?c ?d ?e ?f
                  with
                  | SimpleState s => s
                  end ?m] => idtac "found RoundsBase_Ф__addStakes ..."  a b c d e f; 
                             let p := fresh"p" in
                             destruct (RoundsBase_Ф__addStakes a b c d e f) as (p);
                             let v := fresh"v" in
                             let l := fresh"l" in 
                             destruct (p m) as [v l]; 
                             destruct l ; 
                             destruct v ;
                             simpl 
            | context  [match DePoolContract_Ф_sendAcceptAndReturnChange128 ?a 
                  with
                  | SimpleState s => s
                  end ?m] => idtac "found DePoolContract_Ф_sendAcceptAndReturnChange128 ..."  a ; 
                             let p := fresh"p" in
                             destruct (DePoolContract_Ф_sendAcceptAndReturnChange128 a ) as (p);
                             let v := fresh"v" in
                             let l := fresh"l" in 
                             destruct (p m) as [v l]; 
                             destruct l ; 
                             destruct v ; 
                             simpl                                                    
            | context [let (x, t) := ?f in @?g x t] => idtac "let..." f g; 
                                                 replace (let (x, t) := f in g x t) with (g (fst f) (snd f)) 
                                                          by (symmetry; apply fstsndImplies) ;
                                                 destruct (snd f);          
                                                 simpl                                                                                                                          
            | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
            end
      
       
        end) . 

        all: pr_numgoals. 
        
Qed.      

