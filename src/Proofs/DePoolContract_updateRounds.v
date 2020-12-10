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
(* Require Import depoolContract.Lib.CommonCommon. *)
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



(* function updateRounds() private {
        (, uint32 electionsStartBefore,,) = roundTimeParams();
        (uint256 curValidatorHash, uint32 validationStart, uint32 validationEnd) = getCurValidatorData();
        uint256 prevValidatorHash = getPrevValidatorHash();
        bool areElectionsStarted = now >= validationEnd - electionsStartBefore;
        Round roundPre0 = getRoundPre0(); // round is in pre-pooling phase
        Round round0    = getRound0(); // round is in pooling phase
        Round round1    = getRound1(); // round is in election or validation phase
        Round round2    = getRound2(); // round is in validation or investigation round
(*if1*)  if (m_poolClosed && isEmptyRound(round2) && isEmptyRound(round1) && isEmptyRound(round0) && isEmptyRound(roundPre0) ) {
            selfdestruct(m_validatorWallet);
            tvm.exit();
        }
        round2 = updateRound2(round2, prevValidatorHash, curValidatorHash, validationStart);
(*if2*) if (round1.step == RoundStep.WaitingValidationStart &&
            round1.vsetHashInElectionPhase == prevValidatorHash
        )
        {
            round1.step = RoundStep.WaitingIfValidatorWinElections;
            _recoverStake(round1.proxy, round1.id, round1.elector);
        }
(*if3*) if (areElectionsStarted && 
            round1.vsetHashInElectionPhase != curValidatorHash && 
            round2.step == RoundStep.Completed 
        ) {
            delete m_rounds[round2.id];
            round2 = round1;
            round1 = round0;
            round0 = roundPre0;
            roundPre0 = generateRound();
            round2 = updateRound2(round2, prevValidatorHash, curValidatorHash, validationStart);
(*if4*)     if (!m_poolClosed) {
                round1.supposedElectedAt = validationEnd;
                round1.elector = getElector();
                round1.vsetHashInElectionPhase = curValidatorHash;
                (, , ,uint32 stakeHeldFor) = roundTimeParams();
                round1.stakeHeldFor = stakeHeldFor;
                round1.validatorStake = stakeSum(round1.stakes[m_validatorWallet]);
                bool isValidatorStakeOk  = round1.validatorStake >= m_validatorAssurance;
(*if5*)         if (!isValidatorStakeOk) {
                    round1.step = RoundStep.WaitingUnfreeze;
                    round1.completionReason = CompletionReason.ValidatorStakeIsTooSmall;
                    round1.unfreeze = 0;
                } else {
                    round1.step = RoundStep.WaitingValidatorRequest;
                    emit StakeSigningRequested(round1.supposedElectedAt, round1.proxy);
                }
            }
(*if6*)     if (!m_poolClosed)
                round0.step = RoundStep.Pooling;
        }
        setRoundPre0(roundPre0);
        setRound0(round0);
        setRound1(round1);
        setRound2(round2);   }*)

Check 0.
Check ( DePoolContract_ι_m_poolClosed ).

Lemma DePoolContract_Ф_updateRounds_exec : forall (l: Ledger) , 
                           (* LedgerT (XErrorValue (XValueValue True) XInteger) *)
      (* (, uint32 electionsStartBefore,,) = roundTimeParams(); *)
let tmp := eval_state ( ↓ ConfigParamsBase_Ф_roundTimeParams ) l in
let ret1 : bool := errorValueIsError tmp in
let tmp' := errorMapDefault Datatypes.id tmp (0,0,0,0) in 
let ( a , b ) := tmp' in 
let ( c , d ) := a in 
let ( e , f ) := c in 
let electionsStartBefore : XInteger32 := f in
      (*(uint256 curValidatorHash, uint32 validationStart, uint32 validationEnd) = getCurValidatorData(); *)
let tmp := eval_state ( ↓ ConfigParamsBase_Ф_getCurValidatorData ) l in
let ret2 : bool := errorValueIsError tmp in
let tmp' := errorMapDefault Datatypes.id tmp (0,0,0) in 
let ( a , validationEnd ) := tmp' in
let ( curValidatorHash , validationStart ) := a in  
      (* uint256 prevValidatorHash = getPrevValidatorHash(); *)
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
            (* if (round1.step == RoundStep.WaitingValidationStart &&
                 round1.vsetHashInElectionPhase == prevValidatorHash *)
let if2 : bool := ( ( eqb ( round1 ->> RoundsBase_ι_Round_ι_step ) 
                        RoundsBase_ι_RoundStepP_ι_WaitingValidationStart ) 
                   &&
                  ( ( round1 ->> RoundsBase_ι_Round_ι_vsetHashInElectionPhase ) =? 
                      prevValidatorHash ) )%bool in
                  (* _recoverStake(round1.proxy, round1.id, round1.elector); *)
let l' := if if2 then exec_state ( ↓ ProxyBase_Ф__recoverStake ( round1 ->> RoundsBase_ι_Round_ι_proxy )
                                                                 ( round1 ->> RoundsBase_ι_Round_ι_id )
                                                                 ( round1 ->> RoundsBase_ι_Round_ι_elector ) ) l_updateRound2
                 else l_updateRound2 in

let if2 : bool := ( ( eqb ( round1 ->> RoundsBase_ι_Round_ι_step ) RoundsBase_ι_RoundStepP_ι_WaitingValidationStart ) &&
          ( ( round1 ->> RoundsBase_ι_Round_ι_vsetHashInElectionPhase ) =? prevValidatorHash ) )%bool in
let if3 : bool := ( (areElectionsStarted && 
         ( negb ( ( round1 ->> RoundsBase_ι_Round_ι_vsetHashInElectionPhase ) =? curValidatorHash ) ) && 
         ( negb ( eqb ( round2 ->> RoundsBase_ι_Round_ι_step ) RoundsBase_ι_RoundStepP_ι_Completed ) ) )%bool ) in
         (* delete m_rounds[round2.id]; *)
let l'' := if if3 then
             {$ l' With RoundsBase_ι_m_rounds := 
               ( eval_state ( ↑11 ε RoundsBase_ι_m_rounds ) l' ) ->delete 
                        ( round2 ->> RoundsBase_ι_Round_ι_id ) $} 
           else l' in


let if4  : bool := ( negb ( eval_state (↑12 ε DePoolContract_ι_m_poolClosed) l'' ) ) in

let round1' :=  if if2 then {$ round1 with ( RoundsBase_ι_Round_ι_step , 
                                            RoundsBase_ι_RoundStepP_ι_WaitingIfValidatorWinElections ) $}
                       else round1 in
            (* round2 = round1;
            round1 = round0;
            round0 = roundPre0;
            roundPre0 = generateRound();
            round2 = updateRound2(round2, prevValidatorHash, curValidatorHash, validationStart); *)
let round2' := if if3  then round1 else round2 in
let round1'' := if if3 then round0 else round1' in
let round0' := if if3  then roundPre0 else round0 in
let roundPre0' := if if3 then eval_state ( ↓ DePoolContract_Ф_generateRound ) l'' else roundPre0 in
let round2'' := if if3 then eval_state ( ↓ DePoolContract_Ф_updateRound2
                                           round2'
                                           prevValidatorHash
                                           curValidatorHash
                                           validationStart ) l' else round2' in
let l''' := if if3 then exec_state ( ↓ DePoolContract_Ф_updateRound2
                                           round2'
                                           prevValidatorHash
                                           curValidatorHash
                                           validationStart ) l'' else l'' in
                (* round1.supposedElectedAt = validationEnd;
                   round1.elector = getElector();
                   round1.vsetHashInElectionPhase = curValidatorHash;
                (, , ,uint32 stakeHeldFor) = roundTimeParams();
                   round1.stakeHeldFor = stakeHeldFor;
                   round1.validatorStake = stakeSum(round1.stakes[m_validatorWallet]); *)

let round1''' :=  {$ round1'' with 
                  ( RoundsBase_ι_Round_ι_supposedElectedAt , 
                    ( if ( if3 && if4 )%bool then validationEnd 
                    else ( round1'' ->> RoundsBase_ι_Round_ι_supposedElectedAt ) ) ) ;
                   ( RoundsBase_ι_Round_ι_elector , 
                     ( if ( if3 && if4 )%bool then 
    errorMapDefault Datatypes.id ( eval_state ( ↓ ConfigParamsBase_Ф_getElector ) l''' ) 0
                    else ( round1'' ->> RoundsBase_ι_Round_ι_elector ) ) ) ; 
                   ( RoundsBase_ι_Round_ι_vsetHashInElectionPhase , 
                     ( if ( if3 && if4 )%bool then curValidatorHash 
                     else ( round1'' ->> RoundsBase_ι_Round_ι_vsetHashInElectionPhase ) ) ) ;
                   ( RoundsBase_ι_Round_ι_stakeHeldFor ,
                     ( if ( if3 && if4 )%bool then 
                           (*  (, , ,uint32 stakeHeldFor) = roundTimeParams(); *)
                           let tmp1 := eval_state ( ↓ ConfigParamsBase_Ф_roundTimeParams ) l''' in
                           let tmp1' := errorMapDefault Datatypes.id tmp1 (0,0,0,0) in
                           let ( _ , stakeHeldFor ) := tmp1' in
                     stakeHeldFor
                    else ( round1'' ->> RoundsBase_ι_Round_ι_elector ) ) ) ; 
                  ( RoundsBase_ι_Round_ι_validatorStake , 
                    ( if ( if3 && if4 )%bool then eval_state ( ↓ RoundsBase_Ф_stakeSum 
                       ( ( round1'' ->> RoundsBase_ι_Round_ι_stakes ) 
                         [ ( eval_state ( ↑2 ε ValidatorBase_ι_m_validatorWallet ) l''' ) ] ) ) l'''
                    else ( round1'' ->> RoundsBase_ι_Round_ι_validatorStake ) ) )
                    $} in 
let ret4 : bool := ( if3 && if4 && ( let tmp1 := eval_state ( ↓ ConfigParamsBase_Ф_roundTimeParams ) l''' in
                           errorValueIsError tmp1 ) )%bool in
            (* bool isValidatorStakeOk  = round1.validatorStake >= m_validatorAssurance; *)
let isValidatorStakeOk : bool := ( ( round1''' ->> RoundsBase_ι_Round_ι_validatorStake )
                                   >=? ( eval_state (↑12 ε DePoolContract_ι_m_validatorAssurance ) l''' ) ) in
           (*  if (!isValidatorStakeOk) { *)
let if5 : bool := ( negb isValidatorStakeOk ) in
(*                  round1.step = RoundStep.WaitingUnfreeze;
                    round1.completionReason = CompletionReason.ValidatorStakeIsTooSmall;
                    round1.unfreeze = 0; *)
let round14 := {$ round1''' with 
                        (  RoundsBase_ι_Round_ι_step , 
                           ( if ( if3 && if4 && if5 )%bool then RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze 
                           else round1''' ->> RoundsBase_ι_Round_ι_step ) ) ;
                        ( RoundsBase_ι_Round_ι_completionReason , 
                          ( if if5 then RoundsBase_ι_CompletionReasonP_ι_ValidatorStakeIsTooSmall 
                           else round1''' ->> RoundsBase_ι_Round_ι_completionReason ) ) ;
                        ( RoundsBase_ι_Round_ι_unfreeze , 
                          ( if if5 then 0
                           else round1''' ->> RoundsBase_ι_Round_ι_unfreeze ) ) $} in
               (*  } else {
                    round1.step = RoundStep.WaitingValidatorRequest;
                    emit StakeSigningRequested(round1.supposedElectedAt, round1.proxy);
                } *)
let round15 := {$ round14 with 
                     ( RoundsBase_ι_Round_ι_step , 
                       ( if ( ( if3 && if4 && ( negb if5 ) )%bool ) 
                         then RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest 
                         else round14 ->> RoundsBase_ι_Round_ι_step ) ) $} in

let oldEvents := eval_state ( ↑16 ε VMState_ι_events ) l''' in
let newEvent  := ( StakeSigningRequested ( round15 ->> RoundsBase_ι_Round_ι_supposedElectedAt )
                                         ( round15 ->> RoundsBase_ι_Round_ι_proxy ) ) in 
let l3' := {$ l''' With VMState_ι_events := if ( if3 && if4 && ( negb if5 ) )%bool 
                                            then
                                           ( newEvent :: oldEvents ) 
                                            else oldEvents $} in
                  (* if (!m_poolClosed)
                    round0.step = RoundStep.Pooling; *)
let if6 : bool := ( negb ( eval_state ( ↑12 ε DePoolContract_ι_m_poolClosed ) l3' ) ) in
let round0'' := {$ round0' with ( RoundsBase_ι_Round_ι_step , 
                   if ( if3 && if6 )%bool then RoundsBase_ι_RoundStepP_ι_Pooling 
                   else round0' ->> RoundsBase_ι_Round_ι_step ) $} in
        (*setRoundPre0(roundPre0);
          setRound0(round0);
          setRound1(round1);
          setRound2(round2);   }*)
let l4 := exec_state ( ↓ RoundsBase_Ф_setRoundPre0 roundPre0' ) l3' in
let l5 := exec_state ( ↓ RoundsBase_Ф_setRound0 round0'' )      l4 in
let l6 := exec_state ( ↓ RoundsBase_Ф_setRound1 round15 )       l5 in
let l7 := exec_state ( ↓ RoundsBase_Ф_setRound2 round2'' )      l6 in 

exec_state ( ↓ DePoolContract_Ф_updateRounds ) l = if if1 then l 
                                                   else if ret1 then l
                                                   else if ret2 then l
                                                   else if ret3 then l
                                                   else if ( if3 && if4 && ret4 )%bool then l'''
                                                     else l7.
Proof.
Abort.

Lemma DePoolContract_Ф_updateRounds_eval : forall (l: Ledger) , 
                           (* LedgerT (XErrorValue (XValueValue True) XInteger) *)
      (* (, uint32 electionsStartBefore,,) = roundTimeParams(); *)
let tmp := eval_state ( ↓ ConfigParamsBase_Ф_roundTimeParams ) l in
let ret1 : bool := errorValueIsError tmp in
let tmp' := errorMapDefault Datatypes.id tmp (0,0,0,0) in 
let ( a , b ) := tmp' in 
let ( c , d ) := a in 
let ( e , f ) := c in 
let electionsStartBefore : XInteger32 := f in
      (*(uint256 curValidatorHash, uint32 validationStart, uint32 validationEnd) = getCurValidatorData(); *)
let tmp := eval_state ( ↓ ConfigParamsBase_Ф_getCurValidatorData ) l in
let ret2 : bool := errorValueIsError tmp in
let tmp' := errorMapDefault Datatypes.id tmp (0,0,0) in 
let ( a , validationEnd ) := tmp' in
let ( curValidatorHash , validationStart ) := a in  
      (* uint256 prevValidatorHash = getPrevValidatorHash(); *)
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
            (* if (round1.step == RoundStep.WaitingValidationStart &&
                 round1.vsetHashInElectionPhase == prevValidatorHash *)
let if2 : bool := ( ( eqb ( round1 ->> RoundsBase_ι_Round_ι_step ) 
                        RoundsBase_ι_RoundStepP_ι_WaitingValidationStart ) 
                   &&
                  ( ( round1 ->> RoundsBase_ι_Round_ι_vsetHashInElectionPhase ) =? 
                      prevValidatorHash ) )%bool in
                  (* _recoverStake(round1.proxy, round1.id, round1.elector); *)
let l' := if if2 then exec_state ( ↓ ProxyBase_Ф__recoverStake ( round1 ->> RoundsBase_ι_Round_ι_proxy )
                                                                 ( round1 ->> RoundsBase_ι_Round_ι_id )
                                                                 ( round1 ->> RoundsBase_ι_Round_ι_elector ) ) l_updateRound2
                 else l_updateRound2 in

let if2 : bool := ( ( eqb ( round1 ->> RoundsBase_ι_Round_ι_step ) RoundsBase_ι_RoundStepP_ι_WaitingValidationStart ) &&
          ( ( round1 ->> RoundsBase_ι_Round_ι_vsetHashInElectionPhase ) =? prevValidatorHash ) )%bool in
let if3 : bool := ( (areElectionsStarted && 
         ( negb ( ( round1 ->> RoundsBase_ι_Round_ι_vsetHashInElectionPhase ) =? curValidatorHash ) ) && 
         ( negb ( eqb ( round2 ->> RoundsBase_ι_Round_ι_step ) RoundsBase_ι_RoundStepP_ι_Completed ) ) )%bool ) in
         (* delete m_rounds[round2.id]; *)
let l'' := if if3 then
             {$ l' With RoundsBase_ι_m_rounds := 
               ( eval_state ( ↑11 ε RoundsBase_ι_m_rounds ) l' ) ->delete 
                        ( round2 ->> RoundsBase_ι_Round_ι_id ) $} 
           else l' in


let if4  : bool := ( negb ( eval_state (↑12 ε DePoolContract_ι_m_poolClosed) l'' ) ) in

let round1' :=  if if2 then {$ round1 with ( RoundsBase_ι_Round_ι_step , 
                                            RoundsBase_ι_RoundStepP_ι_WaitingIfValidatorWinElections ) $}
                       else round1 in
            (* round2 = round1;
            round1 = round0;
            round0 = roundPre0;
            roundPre0 = generateRound();
            round2 = updateRound2(round2, prevValidatorHash, curValidatorHash, validationStart); *)
let round2' := if if3  then round1 else round2 in
let round1'' := if if3 then round0 else round1' in
let round0' := if if3  then roundPre0 else round0 in
let roundPre0' := if if3 then eval_state ( ↓ DePoolContract_Ф_generateRound ) l'' else roundPre0 in
let round2'' := if if3 then eval_state ( ↓ DePoolContract_Ф_updateRound2
                                           round2'
                                           prevValidatorHash
                                           curValidatorHash
                                           validationStart ) l' else round2' in
let l''' := if if3 then exec_state ( ↓ DePoolContract_Ф_updateRound2
                                           round2'
                                           prevValidatorHash
                                           curValidatorHash
                                           validationStart ) l'' else l'' in
                (* round1.supposedElectedAt = validationEnd;
                   round1.elector = getElector();
                   round1.vsetHashInElectionPhase = curValidatorHash;
                (, , ,uint32 stakeHeldFor) = roundTimeParams();
                   round1.stakeHeldFor = stakeHeldFor;
                   round1.validatorStake = stakeSum(round1.stakes[m_validatorWallet]); *)

let round1''' :=  {$ round1'' with 
                  ( RoundsBase_ι_Round_ι_supposedElectedAt , 
                    ( if ( if3 && if4 )%bool then validationEnd 
                    else ( round1'' ->> RoundsBase_ι_Round_ι_supposedElectedAt ) ) ) ;
                   ( RoundsBase_ι_Round_ι_elector , 
                     ( if ( if3 && if4 )%bool then 
    errorMapDefault Datatypes.id ( eval_state ( ↓ ConfigParamsBase_Ф_getElector ) l''' ) 0
                    else ( round1'' ->> RoundsBase_ι_Round_ι_elector ) ) ) ; 
                   ( RoundsBase_ι_Round_ι_vsetHashInElectionPhase , 
                     ( if ( if3 && if4 )%bool then curValidatorHash 
                     else ( round1'' ->> RoundsBase_ι_Round_ι_vsetHashInElectionPhase ) ) ) ;
                   ( RoundsBase_ι_Round_ι_stakeHeldFor ,
                     ( if ( if3 && if4 )%bool then 
                           (*  (, , ,uint32 stakeHeldFor) = roundTimeParams(); *)
                           let tmp1 := eval_state ( ↓ ConfigParamsBase_Ф_roundTimeParams ) l''' in
                           let tmp1' := errorMapDefault Datatypes.id tmp1 (0,0,0,0) in
                           let ( _ , stakeHeldFor ) := tmp1' in
                     stakeHeldFor
                    else ( round1'' ->> RoundsBase_ι_Round_ι_elector ) ) ) ; 
                  ( RoundsBase_ι_Round_ι_validatorStake , 
                    ( if ( if3 && if4 )%bool then eval_state ( ↓ RoundsBase_Ф_stakeSum 
                       ( ( round1'' ->> RoundsBase_ι_Round_ι_stakes ) 
                         [ ( eval_state ( ↑2 ε ValidatorBase_ι_m_validatorWallet ) l''' ) ] ) ) l'''
                    else ( round1'' ->> RoundsBase_ι_Round_ι_validatorStake ) ) )
                    $} in 
let ret4 : bool := ( if3 && if4 && ( let tmp1 := eval_state ( ↓ ConfigParamsBase_Ф_roundTimeParams ) l''' in
                           errorValueIsError tmp1 ) )%bool in
            (* bool isValidatorStakeOk  = round1.validatorStake >= m_validatorAssurance; *)
let isValidatorStakeOk : bool := ( ( round1''' ->> RoundsBase_ι_Round_ι_validatorStake )
                                   >=? ( eval_state (↑12 ε DePoolContract_ι_m_validatorAssurance ) l''' ) ) in
           (*  if (!isValidatorStakeOk) { *)
let if5 : bool := ( negb isValidatorStakeOk ) in
(*                  round1.step = RoundStep.WaitingUnfreeze;
                    round1.completionReason = CompletionReason.ValidatorStakeIsTooSmall;
                    round1.unfreeze = 0; *)
let round14 := {$ round1''' with 
                        (  RoundsBase_ι_Round_ι_step , 
                           ( if ( if3 && if4 && if5 )%bool then RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze 
                           else round1''' ->> RoundsBase_ι_Round_ι_step ) ) ;
                        ( RoundsBase_ι_Round_ι_completionReason , 
                          ( if if5 then RoundsBase_ι_CompletionReasonP_ι_ValidatorStakeIsTooSmall 
                           else round1''' ->> RoundsBase_ι_Round_ι_completionReason ) ) ;
                        ( RoundsBase_ι_Round_ι_unfreeze , 
                          ( if if5 then 0
                           else round1''' ->> RoundsBase_ι_Round_ι_unfreeze ) ) $} in
               (*  } else {
                    round1.step = RoundStep.WaitingValidatorRequest;
                    emit StakeSigningRequested(round1.supposedElectedAt, round1.proxy);
                } *)
let round15 := {$ round14 with 
                     ( RoundsBase_ι_Round_ι_step , 
                       ( if ( ( if3 && if4 && ( negb if5 ) )%bool ) 
                         then RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest 
                         else round14 ->> RoundsBase_ι_Round_ι_step ) ) $} in

let oldEvents := eval_state ( ↑16 ε VMState_ι_events ) l''' in
let newEvent  := ( StakeSigningRequested ( round15 ->> RoundsBase_ι_Round_ι_supposedElectedAt )
                                         ( round15 ->> RoundsBase_ι_Round_ι_proxy ) ) in 
let l3' := {$ l''' With VMState_ι_events := if ( if3 && if4 && ( negb if5 ) )%bool 
                                            then
                                           ( newEvent :: oldEvents ) 
                                            else oldEvents $} in
                  (* if (!m_poolClosed)
                    round0.step = RoundStep.Pooling; *)
let if6 : bool := ( negb ( eval_state ( ↑12 ε DePoolContract_ι_m_poolClosed ) l3' ) ) in
let round0'' := {$ round0' with ( RoundsBase_ι_Round_ι_step , 
                   if ( if3 && if6 )%bool then RoundsBase_ι_RoundStepP_ι_Pooling 
                   else round0' ->> RoundsBase_ι_Round_ι_step ) $} in
        (*setRoundPre0(roundPre0);
          setRound0(round0);
          setRound1(round1);
          setRound2(round2);   }*)
let l4 := exec_state ( ↓ RoundsBase_Ф_setRoundPre0 roundPre0' ) l3' in
let l5 := exec_state ( ↓ RoundsBase_Ф_setRound0 round0'' )      l4 in
let l6 := exec_state ( ↓ RoundsBase_Ф_setRound1 round15 )       l5 in
let l7 := exec_state ( ↓ RoundsBase_Ф_setRound2 round2'' )      l6 in 

eval_state ( ↓ DePoolContract_Ф_updateRounds ) l = if if1 then Value ( Error I ) 
                                                   else if ret1 then Value ( Error I )
                                                   else if ret2 then Value ( Error I )
                                                   else if ret3 then Value ( Error I )
                                                   else if ( if3 && if4 && ret4 )%bool then Value ( Error I )
                                                     else Value ( Value I ).

Proof.
Abort.
(* 
 *)