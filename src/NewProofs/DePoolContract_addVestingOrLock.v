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
Module DePoolContract_Ф_addVestingOrLock (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.

Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair.

Opaque DePoolContract_Ф_sendAcceptAndReturnChange128 RoundsBase_Ф__addStakes.


Definition DePoolContract_Ф_addVestingOrLock'_tailer (Л_stake Л_halfStake Л_withdrawalPeriod Л_withdrawalValue Л_beneficiary: XInteger) 
                                                     (Л_isVesting: XBool)
                                                     (Л_participant: DePoolLib_ι_Participant)
                                                     (Л_fee: XInteger) : LedgerT True :=
( ↑17 U1! LocalState_ι_addVestingOrLock_Л_participant := $ Л_participant ) >> 
( 
ForIndexed (xListCons xInt0 (xListCons xInt1 xListNil)) do (fun (i: XInteger) => 
declareLocal Л_isFirstPart :>: XBool := ( $ i ?== $ xInt0 ) ; 
declareLocal Л_vestingOrLock :>: RoundsBase_ι_InvestParams := {|| 
  RoundsBase_ι_InvestParams_ι_remainingAmount ::= $ Л_isFirstPart ? $ Л_halfStake ::: $Л_stake !- $Л_halfStake, 
  RoundsBase_ι_InvestParams_ι_lastWithdrawalTime ::= tvm_now () , 
  RoundsBase_ι_InvestParams_ι_withdrawalPeriod ::= $ Л_withdrawalPeriod , 
  RoundsBase_ι_InvestParams_ι_withdrawalValue ::= $ Л_withdrawalValue , 
  RoundsBase_ι_InvestParams_ι_owner ::= msg_sender () ||} ; 

declareGlobal LocalState_ι_addVestingOrLock_Л_v :>: ( XMaybe RoundsBase_ι_InvestParams ) ; 
declareGlobal LocalState_ι_addVestingOrLock_Л_l  :>: ( XMaybe RoundsBase_ι_InvestParams ) ; 
If ( $ Л_isVesting ) 
then 
{ 
 ↑17 U1! LocalState_ι_addVestingOrLock_Л_v ->set ( $ Л_vestingOrLock ) 
} 
else 
{ 
 ↑17 U1! LocalState_ι_addVestingOrLock_Л_l ->set ( $ Л_vestingOrLock ) 
} >> 
declareLocal Л_round :>: RoundsBase_ι_Round := $ Л_isFirstPart ? RoundsBase_Ф_getRoundPre0 () ::: RoundsBase_Ф_getRound0 () ; 
ς U0! Л_participant := ↑17 D2! LocalState_ι_addVestingOrLock_Л_participant ;
U0! {( Л_round , Л_participant )} := RoundsBase_Ф__addStakes (! ( $ Л_round) , ( $ Л_participant ) , 
                              ( $ Л_beneficiary ) , 
                              ( $ xInt0 ) , 
                              ( ↑17 D2! LocalState_ι_addVestingOrLock_Л_v ), 
                              ( ↑17 D2! LocalState_ι_addVestingOrLock_Л_l ) !) ; 
( ↑17 U1! LocalState_ι_addVestingOrLock_Л_participant := $ Л_participant ) >>
 $ Л_isFirstPart ? RoundsBase_Ф_setRoundPre0 (! $ Л_round !) ::: RoundsBase_Ф_setRound0 (! $ Л_round !) 
) ) >> 
ParticipantBase_Ф__setOrDeleteParticipant (! ( $ Л_beneficiary) , ↑17 D2! LocalState_ι_addVestingOrLock_Л_participant !) >> 
DePoolContract_Ф_sendAcceptAndReturnChange128 (! $ Л_fee !) .		


Definition DePoolContract_Ф_addVestingOrLock'_header ( Л_stake : XInteger64 )
                                                      ( Л_beneficiary : XAddress )
                                                      ( Л_withdrawalPeriod : XInteger32 )
                                                      ( Л_totalPeriod : XInteger32 )
                                                      ( Л_isVesting : XBool ) 
                                                      
                                                      : LedgerT (XValueValue True) :=  
If!! ( ↑ε12 DePoolContract_ι_m_poolClosed ) 
then { 
 return!!! ( DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_DEPOOL_CLOSED , $ xInt0 !) ) 
 } ; 
If!! ( ( !¬ ( ( $ Л_beneficiary ) ->isStdAddrWithoutAnyCast() ) ) !| ( $ Л_beneficiary ?== $ xInt0 ) ) 
then { 
 return!!! ( DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_INVALID_ADDRESS , $ xInt0 !) ) 
 } ; 

If!! ( ( msg_sender () ) ?== $ Л_beneficiary ) 
then { 
 return!!! ( DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_INVALID_BENEFICIARY , $ xInt0 !) ) 
 } ; 
declareLocal Л_msgValue :>: XInteger64 := msg_value () ;
 
If!! ( $ Л_msgValue ?< ( $ Л_stake !+ ( $ DePool_ι_STAKE_FEE ) ) ) 
then 
{ 
 return!!! (DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_FEE_TOO_SMALL , 
                      $ DePool_ι_STAKE_FEE !) ) 
} ; 
declareLocal Л_fee :>: XInteger64 := $ Л_msgValue !- $ Л_stake ; 
declareLocal Л_halfStake :>: XInteger64 := $ Л_stake !/ $ xInt2 ; 

If!! ( $ Л_halfStake ?< ↑12 D2! DePoolContract_ι_m_minStake ) 
then 
{ 
return!!! (DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_STAKE_TOO_SMALL , $ xInt2 !* ( ↑12 D2! DePoolContract_ι_m_minStake ) !) ) 
} ; 

If!! ( $ Л_withdrawalPeriod ?> $ Л_totalPeriod ) 
then 
{ 
return!!! ( DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_WITHDRAWAL_PERIOD_GREATER_TOTAL_PERIOD , $ xInt0 !) ) 
} ; 

If!! ( $ Л_totalPeriod ?>= ( $ xInt18 !* $ xInt365 !* $ x1_day ) ) 
then 
{ 
return!!! (DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_TOTAL_PERIOD_MORE_18YEARS , $ xInt0 !) ) 
} ; 

If!! ( $ Л_withdrawalPeriod ?== $ xInt0 ) 
then 
{ 
return!!! (DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_WITHDRAWAL_PERIOD_IS_ZERO , $ xInt0 !) ) 
} ; 

If!! ( ( $ Л_totalPeriod !% $ Л_withdrawalPeriod ) ?!= $ xInt0 ) 
then 
{ 
return!!! ( DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_TOTAL_PERIOD_IS_NOT_DIVISIBLE_BY_WITHDRAWAL_PERIOD , $ xInt0 !) ) 
} ; 
declareLocal Л_participant :>: DePoolLib_ι_Participant := ParticipantBase_Ф_getOrCreateParticipant (! $ Л_beneficiary !) ; 
If! ( $ Л_isVesting ) 
then { 
If! ( $ Л_participant ->> DePoolLib_ι_Participant_ι_haveVesting ) 
then { 
return!!! ( DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_PARTICIPANT_ALREADY_HAS_VESTING , $ xInt0 !) ) 
} ; $ I 
} 
else 
{ 
If! ( $ Л_participant ->> DePoolLib_ι_Participant_ι_haveLock ) 
then { 
return!!! ( DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_PARTICIPANT_ALREADY_HAS_LOCK , $ xInt0 !) ) 
} ; $ I 
} ; 
declareLocal Л_withdrawalValue :>: XInteger64 := math->muldiv (! $ Л_halfStake , $ Л_withdrawalPeriod , $ Л_totalPeriod !) ; 
DePoolContract_Ф_addVestingOrLock'_tailer Л_stake Л_halfStake Л_withdrawalPeriod Л_withdrawalValue Л_beneficiary 
                                          Л_isVesting Л_participant Л_fee  .                                                      

Lemma DePoolContract_Ф_addVestingOrLock'_tailer_exec : forall (Л_stake Л_halfStake Л_withdrawalPeriod Л_withdrawalValue Л_beneficiary: XInteger) 
                                                     (Л_isVesting: XBool)
                                                     (Л_participant: DePoolLib_ι_Participant)
                                                     (Л_fee: XInteger)
                                                     (l: Ledger) , 
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

exec_state (DePoolContract_Ф_addVestingOrLock'_tailer Л_stake Л_halfStake Л_withdrawalPeriod Л_withdrawalValue Л_beneficiary Л_isVesting Л_participant Л_fee) l =                                                     
l_send. 
Proof.

        intros. 
        destruct l as
         (Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ParticipantBase, 
        Ledger_ι_DePoolProxyContract, 
        Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_VMState, Ledger_ι_LocalState).

        destruct Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase,Ledger_ι_ParticipantBase, 
        Ledger_ι_DePoolProxyContract, 
        Ledger_ι_RoundsBase, Ledger_ι_DePoolContract,  Ledger_ι_VMState, Ledger_ι_LocalState.
      
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
                                                      
                                                      let Ledger_ι_ValidatorBase := fresh "Ledger_ι_ValidatorBase" in
                                                      let Ledger_ι_ProxyBase := fresh "Ledger_ι_ProxyBase" in
                                                      
                                                      let Ledger_ι_ParticipantBase := fresh "Ledger_ι_ParticipantBase" in
                                                      
                                                      let Ledger_ι_DePoolProxyContract := fresh "Ledger_ι_DePoolProxyContract" in
                                                      let Ledger_ι_RoundsBase := fresh "Ledger_ι_RoundsBase" in
                                                      let Ledger_ι_DePoolContract := fresh "Ledger_ι_DePoolContract" in
                                                      let Ledger_ι_VMState := fresh "Ledger_ι_VMState" in
                                                      let Ledger_ι_LocalState := fresh "Ledger_ι_LocalState" in
                                                      destruct l as
                                                      (Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase,  Ledger_ι_ParticipantBase, 
                                                    Ledger_ι_DePoolProxyContract, 
                                                    Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, 
                                                    Ledger_ι_VMState, Ledger_ι_LocalState);

                                                    destruct Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ParticipantBase, 
                                                    Ledger_ι_DePoolProxyContract, 
                                                    Ledger_ι_RoundsBase, Ledger_ι_DePoolContract,  
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
                                   
                                    let Ledger_ι_ValidatorBase := fresh "Ledger_ι_ValidatorBase" in
                                    let Ledger_ι_ProxyBase := fresh "Ledger_ι_ProxyBase" in
                                   
                                    let Ledger_ι_ParticipantBase := fresh "Ledger_ι_ParticipantBase" in
                                    
                                    let Ledger_ι_DePoolProxyContract := fresh "Ledger_ι_DePoolProxyContract" in
                                    let Ledger_ι_RoundsBase := fresh "Ledger_ι_RoundsBase" in
                                    let Ledger_ι_DePoolContract := fresh "Ledger_ι_DePoolContract" in
                                    
                                    let Ledger_ι_VMState := fresh "Ledger_ι_VMState" in
                                    let Ledger_ι_LocalState := fresh "Ledger_ι_LocalState" in
                                    destruct l as
                                    ( Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ParticipantBase, 
                                  Ledger_ι_DePoolProxyContract, 
                                  Ledger_ι_RoundsBase, Ledger_ι_DePoolContract,  
                                  Ledger_ι_VMState, Ledger_ι_LocalState);
                                  destruct Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ParticipantBase, 
                                  Ledger_ι_DePoolProxyContract, 
                                  Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, 
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

Lemma DePoolContract_Ф_addVestingOrLock'_header_eq: DePoolContract_Ф_addVestingOrLock'_header = DePoolContract_Ф_addVestingOrLock'.
Proof.
        auto.
Qed.        

Opaque Z.eqb.

Opaque ParticipantBase_Ф_getOrCreateParticipant DePoolContract_Ф_addVestingOrLock'_tailer.

Lemma DePoolContract_Ф_addVestingOrLock'_header_exec : forall ( Л_stake : XInteger64 )
                                                ( Л_beneficiary : XAddress )
                                                ( Л_withdrawalPeriod : XInteger32 )
                                                ( Л_totalPeriod : XInteger32 )
                                                ( Л_isVesting : XBool )                                        
                                                ( l: Ledger ) , 

let if1 : bool := eval_state ( ↑12 ε DePoolContract_ι_m_poolClosed ) l in 
let if2 : bool := ((negb (isStdAddrWithoutAnyCast Л_beneficiary)) || (Л_beneficiary =? 0))%bool in 
let beneficiary := Л_beneficiary in
let msgSender := eval_state msg_sender l in
let if3 : bool := msgSender =? beneficiary in
let msgValue := eval_state  msg_value l in
let STAKE_FEE := DePool_ι_STAKE_FEE in 
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

exec_state (DePoolContract_Ф_addVestingOrLock'_header Л_stake Л_beneficiary Л_withdrawalPeriod Л_totalPeriod Л_isVesting ) l =

if if1 then exec_state ( ↓ ( DePoolContract_Ф__sendError DePool_ι_STATUS_DEPOOL_CLOSED  0 ) ) l else 
        if if2 then exec_state ( ↓ ( DePoolContract_Ф__sendError DePool_ι_STATUS_INVALID_ADDRESS 0 ) ) l else 
                if if3 then exec_state ( ↓ ( DePoolContract_Ф__sendError DePool_ι_STATUS_INVALID_BENEFICIARY 0 ) ) l else
                        if if4 then exec_state ( ↓ ( DePoolContract_Ф__sendError DePool_ι_STATUS_FEE_TOO_SMALL ) STAKE_FEE ) l else
                                if if5 then exec_state ( ↓ ( DePoolContract_Ф__sendError 
                                DePool_ι_STATUS_STAKE_TOO_SMALL  
                                ( 2 * ( eval_state ( ↑12 ε DePoolContract_ι_m_minStake ) l ) ) ) ) l else 
                                        if if6 then exec_state ( ↓ ( DePoolContract_Ф__sendError 
                                        DePool_ι_STATUS_WITHDRAWAL_PERIOD_GREATER_TOTAL_PERIOD 0 ) ) l else
        if if7 then exec_state ( ↓ ( DePoolContract_Ф__sendError 
        DePool_ι_STATUS_TOTAL_PERIOD_MORE_18YEARS  0 ) ) l else 
                if if8 then exec_state ( ↓ ( DePoolContract_Ф__sendError 
                DePool_ι_STATUS_WITHDRAWAL_PERIOD_IS_ZERO 0 ) ) l else
                        if if9 then exec_state ( ↓ ( DePoolContract_Ф__sendError 
                        DePool_ι_STATUS_TOTAL_PERIOD_IS_NOT_DIVISIBLE_BY_WITHDRAWAL_PERIOD 0 ) ) l else
                                    if (if10 && if11)%bool then exec_state ( ↓ ( DePoolContract_Ф__sendError 
                                    DePool_ι_STATUS_PARTICIPANT_ALREADY_HAS_VESTING  0 ) ) l_getcreate else
                                        if ((negb if10) && if12)%bool then exec_state ( ↓ ( DePoolContract_Ф__sendError 
                                        DePool_ι_STATUS_PARTICIPANT_ALREADY_HAS_LOCK  0 ) ) l_getcreate else 
         exec_state (DePoolContract_Ф_addVestingOrLock'_tailer Л_stake halfStake Л_withdrawalPeriod withdrawalValue Л_beneficiary Л_isVesting participant fee) l_getcreate .

Proof.
        intros.
        destructLedger l. 
        compute.

        Time repeat destructIf_solve. idtac.

        all: try destructFunction1 ParticipantBase_Ф_getOrCreateParticipant; auto. idtac. 
        all: time repeat destructIf_solve. idtac.
        all: try destructFunction8 DePoolContract_Ф_addVestingOrLock'_tailer; auto. 
Qed.  
 


Lemma DePoolContract_Ф_addVestingOrLock'_eval : forall ( Л_stake : XInteger64 )
                                                ( Л_beneficiary : XAddress )
                                                ( Л_withdrawalPeriod : XInteger32 )
                                                ( Л_totalPeriod : XInteger32 )
                                                ( Л_isVesting : XBool )
                                                ( l: Ledger ) , 
 
let if1 : bool := eval_state ( ↑12 ε DePoolContract_ι_m_poolClosed ) l in 
let if2 : bool := ((negb (isStdAddrWithoutAnyCast Л_beneficiary)) || (Л_beneficiary =? 0))%bool in 
let beneficiary := Л_beneficiary in
let msgSender := eval_state msg_sender l in
let if3 : bool := msgSender =? beneficiary in
let msgValue := eval_state  msg_value l in
let STAKE_FEE := DePool_ι_STAKE_FEE in 
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
(* let withdrawalValue :=  halfStake * Л_withdrawalPeriod / Л_totalPeriod  in
let if13 : bool := withdrawalValue =? 0  in *)

eval_state (DePoolContract_Ф_addVestingOrLock' Л_stake Л_beneficiary Л_withdrawalPeriod Л_totalPeriod Л_isVesting) l =

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
        destructLedger l. 
        compute.

        replace (0 =? 0) with true.
        replace (0 =? 1) with false.
        replace (1 =? 0) with false.
        replace (1 =? 1) with true.

        Time repeat destructIf_solve. idtac.

        all: try destructFunction1 ParticipantBase_Ф_getOrCreateParticipant; auto. idtac. 
        all: time repeat destructIf_solve. idtac.
        all: try destructFunction6 RoundsBase_Ф__addStakes; auto. idtac.
        all: try destructFunction6 RoundsBase_Ф__addStakes; auto. idtac.

        all: time repeat destructIf_solve. 
        
Qed.   

End DePoolContract_Ф_addVestingOrLock.