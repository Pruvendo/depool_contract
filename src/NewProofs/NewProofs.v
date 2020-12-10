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

(* Existing Instance embeddedLocalState.
 
Existing Instance monadStateT.
Existing Instance monadStateStateT. *)

(* Existing Instance embeddedLocalState.
Existing Instance embeddedMultisig. *)


Lemma RoundsBase_Ф_transferStakeInOneRound'_error : forall ( Л_round : RoundsBase_ι_Round ) 
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

( ( negb ( optSourceStake_hasValue ) ) || 
( optSourceStake_hasValue && bReturn2 ) )%bool = true 
  <-> exists e ,
eval_state ( RoundsBase_Ф_transferStakeInOneRound' Л_round Л_sourceParticipant Л_destinationParticipant 
                                                   Л_source Л_destination Л_amount  Л_minStake) l = Error e.
Proof.
Abort.

Lemma RoundsBase_Ф_withdrawStakeInPoolingRound'_error : forall (participant : DePoolLib_ι_Participant ) 
                                                               (participantAddress : XAddress)
                                                               (targetAmount : XInteger64)
                                                               (minStake : XInteger64) 
                                                               (l: Ledger) ,
let oldRound0 := eval_state RoundsBase_Ф_getRound0 l in                                                          
    let optsv := (oldRound0 ->> RoundsBase_ι_Round_ι_stakes) ->fetch participantAddress in 

 negb ( isSome optsv ) = true <-> exists e ,
eval_state ( RoundsBase_Ф_withdrawStakeInPoolingRound' participant participantAddress targetAmount minStake ) l = Error e.
Proof.
Abort.

(* Lemma RoundsBase_Ф_withdrawStakeInPoolingRound'_value_error : forall (participant : DePoolLib_ι_Participant ) 
                                                               (participantAddress : XAddress)
                                                               (targetAmount : XInteger64)
                                                               (minStake : XInteger64) 
                                                               (l: Ledger) ,
let oldRound0 := eval_state RoundsBase_Ф_getRound0 l in                                                          
    let optsv := (oldRound0 ->> RoundsBase_ι_Round_ι_stakes) ->fetch participantAddress in 

 ( isSome optsv ) = true <-> exists e ,
eval_state ( RoundsBase_Ф_withdrawStakeInPoolingRound' participant participantAddress targetAmount minStake ) l = Value (Error e).
Proof.
Abort. *)

Lemma DePoolContract_Ф__returnOrReinvestForParticipant_error : forall ( Л_round2 : RoundsBase_ι_Round )
                                                                ( Л_round0 : RoundsBase_ι_Round )
                                                                ( Л_addr : XAddress )
                                                                ( Л_stakes : RoundsBase_ι_StakeValue ) 
                                                                ( Л_isValidator : XBool ) 
                                                                (l: Ledger) ,
    let (stakeSum, l_sum) := run (↓ RoundsBase_Ф_stakeSum Л_stakes) l in
    let optParticipant := eval_state (↓ ParticipantBase_Ф_fetchParticipant Л_addr) l_sum in
    let isSomeParticipant : bool := isSome optParticipant in

 negb isSomeParticipant = true <-> exists e ,
eval_state ( DePoolContract_Ф__returnOrReinvestForParticipant 
                     Л_round2 Л_round0 Л_addr Л_stakes Л_isValidator ) l = Error e.
Proof.
Abort.

Lemma DePoolContract_Ф_addVestingOrLock'_error : forall ( Л_stake : XInteger64 )
                                                ( Л_beneficiary : XAddress )
                                                ( Л_withdrawalPeriod : XInteger32 )
                                                ( Л_totalPeriod : XInteger32 )
                                                ( Л_isVesting : XBool )
                                                (l: Ledger) ,
let if1 : bool := eval_state ( ↑12 ε DePoolContract_ι_m_poolClosed ) l in 
let if2 : bool := ((negb (isStdAddrWithoutAnyCast Л_beneficiary)) || (Л_beneficiary =? 0))%bool in 
let beneficiary := Л_beneficiary in
let msgSender := eval_state msg_sender l in
let if3 : bool := msgSender =? beneficiary in
let msgValue := eval_state  msg_value l in
let STAKE_FEE := DePool_ι_STAKE_FEE ) l in 
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

( if1 || if2 || if3 || if4 || if5 || if6 || if7 || if8 || if9 
                       || (if10 && if11) || ((negb if10) && if12) )%bool = true 
  <-> exists e ,
eval_state ( DePoolContract_Ф_addVestingOrLock' 
             Л_stake Л_beneficiary Л_withdrawalPeriod Л_totalPeriod Л_isVesting ) l = Error e.
Proof.
Abort.

Lemma DePoolContract_Ф_updateRounds_value_error : forall (l: Ledger) ,
let tmp := eval_state ( ↓ ConfigParamsBase_Ф_roundTimeParams ) l in
let ret1 : bool := errorValueIsError tmp in
let tmp' := errorMapDefault Datatypes.id tmp (0,0,0,0) in 
let ( a , b ) := tmp' in 
let ( c , d ) := a in 
let ( e , f ) := c in 
let electionsStartBefore : XInteger32 := f in
let tmp := eval_state ( ↓ ConfigParamsBase_Ф_getCurValidatorData ) l in
let ret2 : bool := errorValueIsError tmp in
let tmp' := errorMapDefault Datatypes.id tmp (0,0,0) in 
let ( a , validationEnd ) := tmp' in
let ( curValidatorHash , validationStart ) := a in  
let tmp := ( eval_state ( ↓  ConfigParamsBase_Ф_getPrevValidatorHash ) l ) in
let ret3 : bool := errorValueIsError tmp in
let prevValidatorHash :=  errorMapDefault Datatypes.id tmp 0 in 

let areElectionsStarted : bool := ( ( eval_state ( ↓ tvm_now ) l ) >=? ( validationEnd - electionsStartBefore ) ) in
let roundPre0 := eval_state ( ↓ RoundsBase_Ф_getRoundPre0 ) l in
let round0 := eval_state ( ↓ RoundsBase_Ф_getRound0 ) l in
let round1 := eval_state ( ↓ RoundsBase_Ф_getRound1 ) l in
let round2 := eval_state ( ↓ RoundsBase_Ф_getRound2 ) l in
let if1 : bool := ( ( eval_state ( ↑12 ε DePoolContract_ι_m_poolClosed ) l ) &&
                    ( eval_state ( ↓     DePoolContract_Ф_isEmptyRound round2 ) l ) && 
                    ( eval_state ( ↓     DePoolContract_Ф_isEmptyRound round1 ) l ) && 
                    ( eval_state ( ↓     DePoolContract_Ф_isEmptyRound round0 ) l ) && 
                    ( eval_state ( ↓     DePoolContract_Ф_isEmptyRound roundPre0 ) l ) )%bool in
let round2' := ( eval_state 
            ( ↓ DePoolContract_Ф_updateRound2 round2 prevValidatorHash curValidatorHash validationStart ) l ) in
let l_updateRound2 := exec_state ( ↓ DePoolContract_Ф_updateRound2 round2 prevValidatorHash curValidatorHash validationStart ) l in
let if2 : bool := ( ( eqb ( round1 ->> RoundsBase_ι_Round_ι_step ) 
                        RoundsBase_ι_RoundStepP_ι_WaitingValidationStart ) 
                   &&
                  ( ( round1 ->> RoundsBase_ι_Round_ι_vsetHashInElectionPhase ) =? 
                      prevValidatorHash ) )%bool in
let l' := if if2 then exec_state ( ↓ ProxyBase_Ф__recoverStake ( round1 ->> RoundsBase_ι_Round_ι_proxy )
                                                                 ( round1 ->> RoundsBase_ι_Round_ι_id )
                                                                 ( round1 ->> RoundsBase_ι_Round_ι_elector ) ) l_updateRound2
                 else l_updateRound2 in

let if2 : bool := ( ( eqb ( round1 ->> RoundsBase_ι_Round_ι_step ) RoundsBase_ι_RoundStepP_ι_WaitingValidationStart ) &&
          ( ( round1 ->> RoundsBase_ι_Round_ι_vsetHashInElectionPhase ) =? prevValidatorHash ) )%bool in
let if3 : bool := ( (areElectionsStarted && 
         ( negb ( ( round1 ->> RoundsBase_ι_Round_ι_vsetHashInElectionPhase ) =? curValidatorHash ) ) && 
         ( negb ( eqb ( round2 ->> RoundsBase_ι_Round_ι_step ) RoundsBase_ι_RoundStepP_ι_Completed ) ) )%bool ) in
let l'' := if if3 then
             {$ l' With RoundsBase_ι_m_rounds := 
               ( eval_state ( ↑11 ε RoundsBase_ι_m_rounds ) l' ) ->delete 
                        ( round2 ->> RoundsBase_ι_Round_ι_id ) $} 
           else l' in


let if4  : bool := ( negb ( eval_state (↑12 ε DePoolContract_ι_m_poolClosed) l'' ) ) in

let l''' := if if3 then exec_state ( ↓ DePoolContract_Ф_updateRound2
                                           round2'
                                           prevValidatorHash
                                           curValidatorHash
                                           validationStart ) l'' else l'' in
let ret4 : bool := ( if3 && if4 && ( let tmp1 := eval_state ( ↓ ConfigParamsBase_Ф_roundTimeParams ) l''' in
                           errorValueIsError tmp1 ) )%bool in

( 
( (negb if1) && (negb ret1) && (negb ret2) && (negb ret3) && if3 && if4 && ret4 ) ||
( (negb if1) && (negb ret1) && (negb ret2) && ret3 ) ||
( (negb if1) && (negb ret1) &&  ret2 ) ||
( (negb if1) &&  ret1 ) ||
        if1
 )%bool = true <-> exists e ,
eval_state ( DePoolContract_Ф_updateRounds ) l = Value (Error e).
Proof.
Abort.

Lemma DePoolContract_Ф_onSuccessToRecoverStake_error : forall ( Л_queryId : XInteger64 ) 
                                                              ( Л_elector : XAddress ) 
                                                              (l: Ledger) ,
let optRound := eval_state ( ↓ ( RoundsBase_Ф_fetchRound Л_queryId ) ) l in
let req1 : bool := isSome optRound in  
let round := maybeGet optRound in
let req2 : bool := eval_state msg_sender l =?  round ->> RoundsBase_ι_Round_ι_proxy  in
let req3 : bool := Л_elector =? round ->> RoundsBase_ι_Round_ι_elector in
let la :=  exec_state (↓ tvm_accept) l in         
let value := ( eval_state msg_value l) + DePoolLib_ι_PROXY_FEE in
let if1 : bool := eqb (round ->> RoundsBase_ι_Round_ι_step) RoundsBase_ι_RoundStepP_ι_WaitingIfValidatorWinElections in
let if2 : bool := value <? round ->> RoundsBase_ι_Round_ι_stake in
let if3 : bool := eqb ( round ->> RoundsBase_ι_Round_ι_step ) RoundsBase_ι_RoundStepP_ι_WaitingReward in
let if4 : bool := value >=? ( ( round ->> RoundsBase_ι_Round_ι_stake ) - 
                           ( round ->> RoundsBase_ι_Round_ι_unused ) ) in
( 
 ( req1 && req2 && req3 && (negb if3) ) ||
 ( req1 && req2 && (negb req3) ) ||
 ( req1 && (negb req2) ) ||
  (negb req1) 
)%bool = true <-> exists e ,
eval_state ( DePoolContract_Ф_onSuccessToRecoverStake Л_queryId Л_elector ) l = Error e.
Proof.
Abort.

Lemma DePoolContract_Ф_completeRound_error : forall ( Л_roundId : XInteger64 ) 
                                                    ( Л_participantQty : XInteger32 ) 
                                                    (l: Ledger) ,
let req : bool := ( negb ( ( eval_state ( ↓ msg_sender ) l ) =? ( eval_state ( ↓ tvm_address ) l ) ) ) in
let l_tvm_accept := ( exec_state ( ↓ tvm_accept ) l ) in
let req1 : bool := ( negb ( ( eval_state ( ↓ RoundsBase_Ф_isRound2 Л_roundId ) l_tvm_accept ) 
                    || ( eval_state ( ↑12 ε DePoolContract_ι_m_poolClosed ) l_tvm_accept ) )%bool ) in
let optRound := eval_state ( ↓ ( RoundsBase_Ф_fetchRound Л_roundId ) ) l_tvm_accept in
let req2 : bool := ( negb ( xMaybeIsSome optRound ) ) in

( ( req || req1 || req2 ) )%bool = true <-> exists e ,
eval_state ( DePoolContract_Ф_completeRound Л_roundId Л_participantQty ) l = Error e.
Proof.
Abort.












