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
Module DePoolContract_Ф_updateRounds (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.

Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair intInc hmapPush.
 
Opaque  DePoolContract_Ф_updateRound2 RoundsBase_Ф_stakeSum ProxyBase_Ф__recoverStake (* RoundsBase_Ф_setRound0 *).

(* Notation "'->selfdestruct' a" := (do a' ← a; ↓ selfdestruct a') (at level 20). *)

(* Import TVMModel.LedgerClass. *)

Definition DePoolContract_Ф_updateRounds_tailer (Л_areElectionsStarted: XBool) 
                                                (Л_curValidatorHash Л_prevValidatorHash: XInteger) 
                                                (Л_validationStart Л_validationEnd Л_validatorsElectedFor:  XInteger) 
                                                      : LedgerT (XErrorValue (XValueValue True) XInteger) := 
If! ( $ Л_areElectionsStarted !& 
	 (↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_vsetHashInElectionPhase ?!= $ Л_curValidatorHash) !& 
	 (↑17 D2! LocalState_ι_updateRounds_Л_round2 ^^ RoundsBase_ι_Round_ι_step ?== ξ$ RoundsBase_ι_RoundStepP_ι_Completed)) then { 

		(↑↑11 U2! delete RoundsBase_ι_m_rounds [[ ↑17 D2! LocalState_ι_updateRounds_Л_round2 ^^ RoundsBase_ι_Round_ι_id ]]) >> 
		(↑17 U1! LocalState_ι_updateRounds_Л_round2 := D2! LocalState_ι_updateRounds_Л_round1) >> 
		(↑17 U1! LocalState_ι_updateRounds_Л_round1 := D2! LocalState_ι_updateRounds_Л_round0) >> 
    (↑17 U1! LocalState_ι_updateRounds_Л_round0 := D2! LocalState_ι_updateRounds_Л_roundPre0) >>  
		(↑↑17 U2! LocalState_ι_updateRounds_Л_roundPre0 := DePoolContract_Ф_generateRound () ) >> 

		(↑↑17 U2! LocalState_ι_updateRounds_Л_round2 := DePoolContract_Ф_updateRound2 (! ↑17 D2! LocalState_ι_updateRounds_Л_round2 , 
																				  $ Л_prevValidatorHash , 
																				  $ Л_curValidatorHash , 
                                          $ Л_validationStart !) ) >> 
    If! ( !¬ (↑12 D2! DePoolContract_ι_m_poolClosed) ) then { 
      (↑17 U1! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_supposedElectedAt := $ 	Л_validationEnd) >> 
      (↑17 U1! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_validatorsElectedFor := $ Л_validatorsElectedFor ) >> 
      ↑↑17 U2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_elector ??:= ConfigParamsBase_Ф_getElector () ; 
      (↑17 U1! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_vsetHashInElectionPhase := $ Л_curValidatorHash) >> 
declareLocal {( _ :>: _ , _ :>: _ , _ :>: _ , Л_stakeHeldFor :>: XInteger32 )} ?:= ConfigParamsBase_Ф_roundTimeParams () ; 
      (↑17 U1! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_stakeHeldFor := $ Л_stakeHeldFor) >> 
      (↑↑17 U2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_validatorStake := 
          RoundsBase_Ф_stakeSum (! D1! (↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_stakes) [[ ↑2 D2! ValidatorBase_ι_m_validatorWallet ]] !)) >> 
      declareLocal Л_isValidatorStakeOk :>: XBool := (↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_validatorStake) ?>= 
                     (↑12 D2! DePoolContract_ι_m_validatorAssurance)	; 
      (If ( !¬ $ Л_isValidatorStakeOk ) then { 
        (↑17 U1! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_step := ξ$ RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze) >> 
        (↑17 U1! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_completionReason := ξ$ RoundsBase_ι_CompletionReasonP_ι_ValidatorStakeIsTooSmall) >> 
        (↑17 U1! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_unfreeze := $ xInt0) 
      } else { 
        (↑17 U1! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_step := ξ$ RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest) >> 
        (->emit StakeSigningRequested (!! ↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_supposedElectedAt , 
                        ↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_proxy  !!)) 
      }) }; 

      (If ( !¬ (↑12 D2! DePoolContract_ι_m_poolClosed) ) then { 
        (↑17 U1! LocalState_ι_updateRounds_Л_round0 ^^ RoundsBase_ι_Round_ι_step := ξ$ RoundsBase_ι_RoundStepP_ι_Pooling) 
      })  
      
      } ;        
      ( RoundsBase_Ф_setRoundPre0 (! ↑17 D2! LocalState_ι_updateRounds_Л_roundPre0 !) ) >> 
      ( RoundsBase_Ф_setRound0 (! ↑17 D2! LocalState_ι_updateRounds_Л_round0 !) ) >> 
      ( RoundsBase_Ф_setRound1 (! ↑17 D2! LocalState_ι_updateRounds_Л_round1 !) ) >> 
      ( RoundsBase_Ф_setRound2 (! ↑17 D2! LocalState_ι_updateRounds_Л_round2 !) ) >> 
return! (xValue I) . 
 


Definition DePoolContract_Ф_updateRounds_header  : LedgerT (XErrorValue (XValueValue True) XInteger) := 
declareLocal {( Л_validatorsElectedFor :>: XInteger32 , Л_electionsStartBefore :>: XInteger32 , _ :>: _ , _ :>: _ )} ??:= ConfigParamsBase_Ф_roundTimeParams () ; 
declareLocal {( Л_curValidatorHash :>: XInteger256 , Л_validationStart :>: XInteger32 , Л_validationEnd  :>: XInteger32 )} ??:= ConfigParamsBase_Ф_getCurValidatorData () ; 
declareLocal Л_prevValidatorHash  :>: XInteger256 ??:= ConfigParamsBase_Ф_getPrevValidatorHash () ; 
declareLocal Л_areElectionsStarted :>: XBool := ( tvm_now () ?>=  $ Л_validationEnd !- $ Л_electionsStartBefore ) ; 
( declareGlobal! LocalState_ι_updateRounds_Л_roundPre0 :>: RoundsBase_ι_Round := RoundsBase_Ф_getRoundPre0 () ) >> 
( declareGlobal! LocalState_ι_updateRounds_Л_round0 :>: RoundsBase_ι_Round := RoundsBase_Ф_getRound0 () ) >> 
( declareGlobal! LocalState_ι_updateRounds_Л_round1 :>: RoundsBase_ι_Round := RoundsBase_Ф_getRound1 () ) >> 
( declareGlobal! LocalState_ι_updateRounds_Л_round2 :>: RoundsBase_ι_Round := RoundsBase_Ф_getRound2 () ) >> 
If2!! ((↑ε12 DePoolContract_ι_m_poolClosed ) !& 
(DePoolContract_Ф_isEmptyRound (! ↑17 D2! LocalState_ι_updateRounds_Л_round2 !) ) !& 
(DePoolContract_Ф_isEmptyRound (! ↑17 D2! LocalState_ι_updateRounds_Л_round1 !) ) !& 
(DePoolContract_Ф_isEmptyRound (! ↑17 D2! LocalState_ι_updateRounds_Л_round0 !) ) !& 
(DePoolContract_Ф_isEmptyRound (! ↑17 D2! LocalState_ι_updateRounds_Л_roundPre0 !))) then { 
  (->selfdestruct ( ↑2 D2! ValidatorBase_ι_m_validatorWallet ) ) >> 
  tvm_exit () 
};          
(↑↑17 U2! LocalState_ι_updateRounds_Л_round2 := DePoolContract_Ф_updateRound2 (! ↑17 D2! LocalState_ι_updateRounds_Л_round2 , 
                                        $ Л_prevValidatorHash , 
                                        $ Л_curValidatorHash , 
                    $ Л_validationStart !) ) >> 
If!! ( (↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_step ?== ξ$ RoundsBase_ι_RoundStepP_ι_WaitingValidationStart) !& 
(↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_vsetHashInElectionPhase ?== $ Л_prevValidatorHash)) then { 

(↑17 U1! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_step := ξ$ RoundsBase_ι_RoundStepP_ι_WaitingIfValidatorWinElections) >> 
ProxyBase_Ф__recoverStake (! ↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_proxy , 
            ↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_id , 
            ↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_elector !) >> $ xValue I 
};  DePoolContract_Ф_updateRounds_tailer Л_areElectionsStarted Л_curValidatorHash Л_prevValidatorHash Л_validationStart Л_validationEnd Л_validatorsElectedFor.


Lemma DePoolContract_Ф_updateRounds_header_eq: DePoolContract_Ф_updateRounds_header = DePoolContract_Ф_updateRounds.
Proof.
  auto.
Qed.

Opaque DePoolContract_Ф_updateRounds_tailer.


Lemma DePoolContract_Ф_updateRounds_header_exec : forall (l: Ledger) ,                            
let ertp := eval_state ( ↓ ConfigParamsBase_Ф_roundTimeParams ) l in
let ret1 : bool := errorValueIsValue ertp in
let rtp := errorMapDefault Datatypes.id ertp (0,0,0,0) in 
let electionsStartBefore := snd (fst ( fst rtp )) in
let validatorsElectedFor := fst (fst ( fst rtp )) in

let ecvd := eval_state ( ↓ ConfigParamsBase_Ф_getCurValidatorData ) l in
let ret2 : bool := errorValueIsValue ecvd in
let cvd := errorMapDefault Datatypes.id ecvd (0,0,0) in 
let curValidatorHash := fst (fst cvd) in
let validationStart := snd (fst cvd) in
let validationEnd := snd cvd in

let epvh :=  eval_state ( ↓  ConfigParamsBase_Ф_getPrevValidatorHash ) l  in
let ret3 : bool := errorValueIsValue epvh in
let prevValidatorHash := errorMapDefault Datatypes.id epvh 0 in 

let areElectionsStarted : bool := ( ( eval_state ( ↓ tvm_now ) l ) >=? ( validationEnd - electionsStartBefore ) ) in
let roundPre0 := eval_state ( ↓ RoundsBase_Ф_getRoundPre0 ) l in
let round0 := eval_state ( ↓ RoundsBase_Ф_getRound0 ) l in
let round1 := eval_state ( ↓ RoundsBase_Ф_getRound1 ) l in
let round2 := eval_state ( ↓ RoundsBase_Ф_getRound2 ) l in
let if1 : bool := ( ( eval_state ( ↑12 ε DePoolContract_ι_m_poolClosed ) l ) &&
                    (( eval_state ( ↓     DePoolContract_Ф_isEmptyRound round2 ) l ) && 
                    (( eval_state ( ↓     DePoolContract_Ф_isEmptyRound round1 ) l ) && 
                    (( eval_state ( ↓     DePoolContract_Ф_isEmptyRound round0 ) l ) && 
                    ( eval_state ( ↓     DePoolContract_Ф_isEmptyRound roundPre0 ) l )))) )%bool in  
let m_validatorWallet := eval_state ( ↑2 ε ValidatorBase_ι_m_validatorWallet) l in                                       
let l' := {$ l With (LocalState_ι_updateRounds_Л_roundPre0, roundPre0) ;
                         (LocalState_ι_updateRounds_Л_round0, round0) ; 
                         (LocalState_ι_updateRounds_Л_round1, round1) ;
                         (LocalState_ι_updateRounds_Л_round2, round2) $} in

let (round2, newl) := run (↓ DePoolContract_Ф_updateRound2 round2 prevValidatorHash curValidatorHash validationStart) l'  in
let if2 : bool := ( ( eqb ( round1 ->> RoundsBase_ι_Round_ι_step ) RoundsBase_ι_RoundStepP_ι_WaitingValidationStart ) 
                   &&
                  ( ( round1 ->> RoundsBase_ι_Round_ι_vsetHashInElectionPhase ) =? prevValidatorHash ) )%bool in
let round1 := if if2 then 
              {$ round1 with (RoundsBase_ι_Round_ι_step, RoundsBase_ι_RoundStepP_ι_WaitingIfValidatorWinElections ) $} 
              else round1 in 
let newl' :=  {$ newl With (LocalState_ι_updateRounds_Л_round1, round1); (LocalState_ι_updateRounds_Л_round2, round2) $} in                   
let newl := if if2 then exec_state ( ↓ ProxyBase_Ф__recoverStake ( round1 ->> RoundsBase_ι_Round_ι_proxy )
                                                               ( round1 ->> RoundsBase_ι_Round_ι_id )
                                                               ( round1 ->> RoundsBase_ι_Round_ι_elector ) ) newl'
                 else newl' in

exec_state ( DePoolContract_Ф_updateRounds_header ) l = 
if ret1 then
  if ret2 then 
    if ret3 then 
      if if1 then exec_state (↓ selfdestruct m_validatorWallet) l'
      else exec_state (DePoolContract_Ф_updateRounds_tailer areElectionsStarted curValidatorHash prevValidatorHash validationStart validationEnd validatorsElectedFor) newl  
    else l
  else l
else l. 

Proof.
  intros.
  destructLedger l. 
  compute. idtac.

  case_eq DePoolContract_ι_m_poolClosed; intros. idtac.

  all: repeat destructIf_solve2. idtac.
  all: try destructFunction4 DePoolContract_Ф_updateRound2; auto. idtac.


  all: try destructFunction1 selfdestruct; auto. idtac.
        
  all: repeat destructIf_solve2. 

Qed.  


Lemma DePoolContract_Ф_updateRounds_header_eval : forall (l: Ledger) ,                            
let ertp := eval_state ( ↓ ConfigParamsBase_Ф_roundTimeParams ) l in
let ret1 : bool := errorValueIsValue ertp in
let rtp := errorMapDefault Datatypes.id ertp (0,0,0,0) in 
let electionsStartBefore := snd (fst ( fst rtp )) in
let validatorsElectedFor := fst (fst ( fst rtp )) in

let ecvd := eval_state ( ↓ ConfigParamsBase_Ф_getCurValidatorData ) l in
let ret2 : bool := errorValueIsValue ecvd in
let cvd := errorMapDefault Datatypes.id ecvd (0,0,0) in 
let curValidatorHash := fst (fst cvd) in
let validationStart := snd (fst cvd) in
let validationEnd := snd cvd in

let epvh :=  eval_state ( ↓  ConfigParamsBase_Ф_getPrevValidatorHash ) l  in
let ret3 : bool := errorValueIsValue epvh in
let prevValidatorHash := errorMapDefault Datatypes.id epvh 0 in 

let areElectionsStarted : bool := ( ( eval_state ( ↓ tvm_now ) l ) >=? ( validationEnd - electionsStartBefore ) ) in
let roundPre0 := eval_state ( ↓ RoundsBase_Ф_getRoundPre0 ) l in
let round0 := eval_state ( ↓ RoundsBase_Ф_getRound0 ) l in
let round1 := eval_state ( ↓ RoundsBase_Ф_getRound1 ) l in
let round2 := eval_state ( ↓ RoundsBase_Ф_getRound2 ) l in
let if1 : bool := ( ( eval_state ( ↑12 ε DePoolContract_ι_m_poolClosed ) l ) &&
                    (( eval_state ( ↓     DePoolContract_Ф_isEmptyRound round2 ) l ) && 
                    (( eval_state ( ↓     DePoolContract_Ф_isEmptyRound round1 ) l ) && 
                    (( eval_state ( ↓     DePoolContract_Ф_isEmptyRound round0 ) l ) && 
                    ( eval_state ( ↓     DePoolContract_Ф_isEmptyRound roundPre0 ) l )))) )%bool in  
let m_validatorWallet := eval_state ( ↑2 ε ValidatorBase_ι_m_validatorWallet) l in                                       
let l' := {$ l With (LocalState_ι_updateRounds_Л_roundPre0, roundPre0) ;
                         (LocalState_ι_updateRounds_Л_round0, round0) ; 
                         (LocalState_ι_updateRounds_Л_round1, round1) ;
                         (LocalState_ι_updateRounds_Л_round2, round2) $} in

let (round2, newl) := run (↓ DePoolContract_Ф_updateRound2 round2 prevValidatorHash curValidatorHash validationStart) l'  in
let if2 : bool := ( ( eqb ( round1 ->> RoundsBase_ι_Round_ι_step ) RoundsBase_ι_RoundStepP_ι_WaitingValidationStart ) 
                   &&
                  ( ( round1 ->> RoundsBase_ι_Round_ι_vsetHashInElectionPhase ) =? prevValidatorHash ) )%bool in
let round1 := if if2 then 
              {$ round1 with (RoundsBase_ι_Round_ι_step, RoundsBase_ι_RoundStepP_ι_WaitingIfValidatorWinElections ) $} 
              else round1 in 
let newl' :=  {$ newl With (LocalState_ι_updateRounds_Л_round1, round1); (LocalState_ι_updateRounds_Л_round2, round2) $} in                   
let newl := if if2 then exec_state ( ↓ ProxyBase_Ф__recoverStake ( round1 ->> RoundsBase_ι_Round_ι_proxy )
                                                               ( round1 ->> RoundsBase_ι_Round_ι_id )
                                                               ( round1 ->> RoundsBase_ι_Round_ι_elector ) ) newl'
                 else newl' in

eval_state ( DePoolContract_Ф_updateRounds_header  ) l = 
(* if ret1 then
  if ret2 then 
    if ret3 then  *)
      if if1 then Value (Error I)
      else eval_state (DePoolContract_Ф_updateRounds_tailer areElectionsStarted curValidatorHash prevValidatorHash validationStart validationEnd validatorsElectedFor) newl  .
(*     else l
  else l
else l *)

Proof.
  intros.
  destructLedger l. 
  compute. idtac.

  case_eq DePoolContract_ι_m_poolClosed; intros. idtac.

  all: repeat destructIf_solve2. idtac.
  all: try destructFunction4 DePoolContract_Ф_updateRound2; auto. idtac.
  all: try destructFunction1 selfdestruct; auto. idtac.
        
  all: repeat destructIf_solve2. 

Qed.  

Definition DePoolContract_Ф_updateRounds_tailer3 (Л_validationEnd Л_validatorsElectedFor Л_curValidatorHash: XInteger) : LedgerT (XErrorValue True XInteger):=
  (↑17 U1! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_supposedElectedAt := $ 	Л_validationEnd) >> 
  (↑17 U1! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_validatorsElectedFor := $ Л_validatorsElectedFor ) >> 
  ↑↑17 U2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_elector ??:= ConfigParamsBase_Ф_getElector () ; 
  (↑17 U1! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_vsetHashInElectionPhase := $ Л_curValidatorHash) >> 
declareLocal {( _ :>: _ , _ :>: _ , _ :>: _ , Л_stakeHeldFor :>: XInteger32 )} ?:= ConfigParamsBase_Ф_roundTimeParams () ; 
  (↑17 U1! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_stakeHeldFor := $ Л_stakeHeldFor) >> 
  (↑↑17 U2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_validatorStake := 
      RoundsBase_Ф_stakeSum (! D1! (↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_stakes) [[ ↑2 D2! ValidatorBase_ι_m_validatorWallet ]] !)) >> 
  declareLocal Л_isValidatorStakeOk :>: XBool := (↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_validatorStake) ?>= 
                 (↑12 D2! DePoolContract_ι_m_validatorAssurance)	; 
  (If ( !¬ $ Л_isValidatorStakeOk ) then { 
    (↑17 U1! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_step := ξ$ RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze) >> 
    (↑17 U1! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_completionReason := ξ$ RoundsBase_ι_CompletionReasonP_ι_ValidatorStakeIsTooSmall) >> 
    (↑17 U1! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_unfreeze := $ xInt0) 
  } else { 
    (↑17 U1! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_step := ξ$ RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest) >> 
    (->emit StakeSigningRequested (!! ↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_supposedElectedAt , 
                    ↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_proxy  !!)) 
  }).

Definition DePoolContract_Ф_updateRounds_tailer2 (Л_areElectionsStarted: XBool) 
                                                (Л_curValidatorHash Л_prevValidatorHash: XInteger) 
                                                (Л_validationStart Л_validationEnd Л_validatorsElectedFor: XInteger) 
                                              
                                                      : LedgerT (XErrorValue (XValueValue True) XInteger) := 
If! ( $ Л_areElectionsStarted !& 
	 (↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_vsetHashInElectionPhase ?!= $ Л_curValidatorHash) !& 
	 (↑17 D2! LocalState_ι_updateRounds_Л_round2 ^^ RoundsBase_ι_Round_ι_step ?== ξ$ RoundsBase_ι_RoundStepP_ι_Completed)) then { 

		(↑↑11 U2! delete RoundsBase_ι_m_rounds [[ ↑17 D2! LocalState_ι_updateRounds_Л_round2 ^^ RoundsBase_ι_Round_ι_id ]]) >> 
		(↑17 U1! LocalState_ι_updateRounds_Л_round2 := D2! LocalState_ι_updateRounds_Л_round1) >> 
		(↑17 U1! LocalState_ι_updateRounds_Л_round1 := D2! LocalState_ι_updateRounds_Л_round0) >> 
    (↑17 U1! LocalState_ι_updateRounds_Л_round0 := D2! LocalState_ι_updateRounds_Л_roundPre0) >>  
		(↑↑17 U2! LocalState_ι_updateRounds_Л_roundPre0 := DePoolContract_Ф_generateRound () ) >> 

		(↑↑17 U2! LocalState_ι_updateRounds_Л_round2 := DePoolContract_Ф_updateRound2 (! ↑17 D2! LocalState_ι_updateRounds_Л_round2 , 
																				  $ Л_prevValidatorHash , 
																				  $ Л_curValidatorHash , 
                                          $ Л_validationStart !) ) >> 
    If! ( !¬ (↑12 D2! DePoolContract_ι_m_poolClosed) ) then { 
      DePoolContract_Ф_updateRounds_tailer3 Л_validationEnd Л_validatorsElectedFor Л_curValidatorHash
       }; 

      (If ( !¬ (↑12 D2! DePoolContract_ι_m_poolClosed) ) then { 
        (↑17 U1! LocalState_ι_updateRounds_Л_round0 ^^ RoundsBase_ι_Round_ι_step := ξ$ RoundsBase_ι_RoundStepP_ι_Pooling) 
      })  
      
      } ;        
      ( RoundsBase_Ф_setRoundPre0 (! ↑17 D2! LocalState_ι_updateRounds_Л_roundPre0 !) ) >> 
      ( RoundsBase_Ф_setRound0 (! ↑17 D2! LocalState_ι_updateRounds_Л_round0 !) ) >> 
      ( RoundsBase_Ф_setRound1 (! ↑17 D2! LocalState_ι_updateRounds_Л_round1 !) ) >> 
      ( RoundsBase_Ф_setRound2 (! ↑17 D2! LocalState_ι_updateRounds_Л_round2 !) ) >> 
return! (xValue I) .




(* Transparent RoundsBase_Ф_stakeSum. *)

(* Transparent RoundsBase_Ф_setRound0. *)

Opaque DePoolContract_Ф_updateRounds_tailer3.

Lemma  DePoolContract_Ф_updateRounds_tailer2_exec  (areElectionsStarted: XBool) 
                                                  (curValidatorHash prevValidatorHash: XInteger) 
                                                  (validationStart validationEnd validatorsElectedFor:  XInteger)  (l: Ledger):
let _roundPre0 := eval_state ( ↑17 ε LocalState_ι_updateRounds_Л_roundPre0 ) l in
let _round0 := eval_state (  ↑17 ε LocalState_ι_updateRounds_Л_round0 ) l in
let _round1 := eval_state (  ↑17 ε LocalState_ι_updateRounds_Л_round1) l in
let _round2 := eval_state (  ↑17 ε LocalState_ι_updateRounds_Л_round2 ) l in

let if3 : bool :=  (areElectionsStarted && 
         (( negb ( ( _round1 ->> RoundsBase_ι_Round_ι_vsetHashInElectionPhase ) =? curValidatorHash ) ) && 
         (  ( eqb ( _round2 ->> RoundsBase_ι_Round_ι_step ) RoundsBase_ι_RoundStepP_ι_Completed ) )) )%bool in
        
let newl :=   {$ l With RoundsBase_ι_m_rounds := 
               ( eval_state ( ↑11 ε RoundsBase_ι_m_rounds ) l ) ->delete ( _round2 ->> RoundsBase_ι_Round_ι_id ) $}
               in  
let round2 := _round1 in
let round1 := _round0 in
let round0 := _roundPre0  in
let (roundPre0, newl) :=  run ( ↓ DePoolContract_Ф_generateRound ) newl in

let newl' := {$ newl With (LocalState_ι_updateRounds_Л_roundPre0, roundPre0) ;
                         (LocalState_ι_updateRounds_Л_round0, round0) ; 
                         (LocalState_ι_updateRounds_Л_round1, round1) ;
                         (LocalState_ι_updateRounds_Л_round2, round2) $} in

let (round2, newl) := run ( ↓ DePoolContract_Ф_updateRound2 round2 prevValidatorHash curValidatorHash validationStart ) newl' in
let newl := {$ newl With (LocalState_ι_updateRounds_Л_round2, round2) $} in

let l2 := newl in 

let if4  : bool := negb ( eval_state (↑12 ε DePoolContract_ι_m_poolClosed) newl )  in 

let (r, newl) := if if4 then run (DePoolContract_Ф_updateRounds_tailer3 validationEnd validatorsElectedFor curValidatorHash) newl else (Value I, newl) in
let ml := newl in

let roundPre0 := eval_state ( ↑17 ε LocalState_ι_updateRounds_Л_roundPre0 ) ml in
let round0 := eval_state (  ↑17 ε LocalState_ι_updateRounds_Л_round0 ) ml in
let round1 := eval_state (  ↑17 ε LocalState_ι_updateRounds_Л_round1) ml in
let round2 := eval_state (  ↑17 ε LocalState_ι_updateRounds_Л_round2 ) ml in

let if5 : bool := negb ( eval_state (↑12 ε DePoolContract_ι_m_poolClosed) newl )  in  
let round0 := if if5 then {$ round0 with ( RoundsBase_ι_Round_ι_step , RoundsBase_ι_RoundStepP_ι_Pooling  ) $} 
                     else round0 in   
let newl := {$ newl With (LocalState_ι_updateRounds_Л_round0, round0) $} in             

let lsetPre0 := exec_state ( ↓ RoundsBase_Ф_setRoundPre0 roundPre0 ) newl in
let lset0 := exec_state ( ↓ RoundsBase_Ф_setRound0 round0 ) lsetPre0 in
let lset1 := exec_state ( ↓ RoundsBase_Ф_setRound1 round1 ) lset0 in
let lset2 := exec_state ( ↓ RoundsBase_Ф_setRound2 round2 ) lset1 in 

let lsetPre0' := exec_state ( ↓ RoundsBase_Ф_setRoundPre0 _roundPre0 ) l in
let lset0' := exec_state ( ↓ RoundsBase_Ф_setRound0 _round0 ) lsetPre0' in
let lset1' := exec_state ( ↓ RoundsBase_Ф_setRound1 _round1 ) lset0' in
let lset2' := exec_state ( ↓ RoundsBase_Ф_setRound2 _round2 ) lset1' in 

exec_state ( DePoolContract_Ф_updateRounds_tailer2 areElectionsStarted curValidatorHash prevValidatorHash
                              validationStart validationEnd validatorsElectedFor ) l = 
(* if ret1 then
  if ret2 then 
    if ret3 then  *)
     if if3 then
        if if4 then  
            if (errorValueIsValue r) then lset2
            else ml
        else lset2
     else lset2'.

Proof.
  intros.
  destructLedger l. 
  compute. idtac.


  all: repeat destructIf_solve2. idtac.
  all: try destructFunction4 DePoolContract_Ф_updateRound2; auto. idtac.
  all: repeat destructIf_solve2. idtac.
  all: try destructFunction3 DePoolContract_Ф_updateRounds_tailer3; auto. idtac.
  case_eq x0; intros; auto. idtac.
  all: repeat destructIf_solve2. idtac.

  Require Import depoolContract.Lib.CommonStateProofs.
  apply ledgerEq; auto. idtac.
  simpl. idtac.
  destructLedger l0; auto. 
Qed. 



Lemma  DePoolContract_Ф_updateRounds_tailer2_eval  (areElectionsStarted: XBool) 
                                                  (curValidatorHash prevValidatorHash: XInteger) 
                                                  (validationStart validationEnd validatorsElectedFor:  XInteger) (l: Ledger):
let _roundPre0 := eval_state ( ↑17 ε LocalState_ι_updateRounds_Л_roundPre0 ) l in
let _round0 := eval_state (  ↑17 ε LocalState_ι_updateRounds_Л_round0 ) l in
let _round1 := eval_state (  ↑17 ε LocalState_ι_updateRounds_Л_round1) l in
let _round2 := eval_state (  ↑17 ε LocalState_ι_updateRounds_Л_round2 ) l in

let if3 : bool :=  (areElectionsStarted && 
         (( negb ( ( _round1 ->> RoundsBase_ι_Round_ι_vsetHashInElectionPhase ) =? curValidatorHash ) ) && 
         (  ( eqb ( _round2 ->> RoundsBase_ι_Round_ι_step ) RoundsBase_ι_RoundStepP_ι_Completed ) )) )%bool in
        
let newl :=   {$ l With RoundsBase_ι_m_rounds := 
               ( eval_state ( ↑11 ε RoundsBase_ι_m_rounds ) l ) ->delete ( _round2 ->> RoundsBase_ι_Round_ι_id ) $}
               in  
let round2 := _round1 in
let round1 := _round0 in
let round0 := _roundPre0  in
let (roundPre0, newl) :=  run ( ↓ DePoolContract_Ф_generateRound ) newl in

let newl' := {$ newl With (LocalState_ι_updateRounds_Л_roundPre0, roundPre0) ;
                         (LocalState_ι_updateRounds_Л_round0, round0) ; 
                         (LocalState_ι_updateRounds_Л_round1, round1) ;
                         (LocalState_ι_updateRounds_Л_round2, round2) $} in

let (round2, newl) := run ( ↓ DePoolContract_Ф_updateRound2 round2 prevValidatorHash curValidatorHash validationStart ) newl' in
let newl := {$ newl With (LocalState_ι_updateRounds_Л_round2, round2) $} in

let l2 := newl in 

let if4  : bool := negb ( eval_state (↑12 ε DePoolContract_ι_m_poolClosed) newl )  in 

let (r, newl) := if if4 then run (DePoolContract_Ф_updateRounds_tailer3 validationEnd validatorsElectedFor curValidatorHash) newl else (Value I, newl) in
let ml := newl in

let roundPre0 := eval_state ( ↑17 ε LocalState_ι_updateRounds_Л_roundPre0 ) ml in
let round0 := eval_state (  ↑17 ε LocalState_ι_updateRounds_Л_round0 ) ml in
let round1 := eval_state (  ↑17 ε LocalState_ι_updateRounds_Л_round1) ml in
let round2 := eval_state (  ↑17 ε LocalState_ι_updateRounds_Л_round2 ) ml in

let if5 : bool := negb ( eval_state (↑12 ε DePoolContract_ι_m_poolClosed) newl )  in  
let round0 := if if5 then {$ round0 with ( RoundsBase_ι_Round_ι_step , RoundsBase_ι_RoundStepP_ι_Pooling  ) $} 
                     else round0 in   
let newl := {$ newl With (LocalState_ι_updateRounds_Л_round0, round0) $} in             

let lsetPre0 := exec_state ( ↓ RoundsBase_Ф_setRoundPre0 roundPre0 ) newl in
let lset0 := exec_state ( ↓ RoundsBase_Ф_setRound0 round0 ) lsetPre0 in
let lset1 := exec_state ( ↓ RoundsBase_Ф_setRound1 round1 ) lset0 in
let lset2 := exec_state ( ↓ RoundsBase_Ф_setRound2 round2 ) lset1 in 

let lsetPre0' := exec_state ( ↓ RoundsBase_Ф_setRoundPre0 _roundPre0 ) l in
let lset0' := exec_state ( ↓ RoundsBase_Ф_setRound0 _round0 ) lsetPre0' in
let lset1' := exec_state ( ↓ RoundsBase_Ф_setRound1 _round1 ) lset0' in
let lset2' := exec_state ( ↓ RoundsBase_Ф_setRound2 _round2 ) lset1' in 

eval_state ( DePoolContract_Ф_updateRounds_tailer2 areElectionsStarted curValidatorHash prevValidatorHash
                              validationStart validationEnd validatorsElectedFor ) l = 
(* if ret1 then
  if ret2 then 
    if ret3 then  *)
     if if3 then
        if if4 then  
            if (errorValueIsValue r) then Value (Value I)
            else errorMapDefaultF (fun _ => Value (Value I)) r (fun e => Error e)
        else Value (Value I)
     else Value (Value I).

Proof.
  intros.
  destructLedger l. 
  compute. idtac.


  all: repeat destructIf_solve2. idtac.
  all: try destructFunction4 DePoolContract_Ф_updateRound2; auto. idtac.
  all: repeat destructIf_solve2. idtac.
  all: try destructFunction3 DePoolContract_Ф_updateRounds_tailer3; auto. idtac.
  case_eq x0; intros; auto. idtac.
  all: repeat destructIf_solve2. 
Qed.


Transparent DePoolContract_Ф_updateRounds_tailer3.

Lemma DePoolContract_Ф_updateRounds_tailer3_exec : forall (validationEnd validatorsElectedFor curValidatorHash: XInteger) (l: Ledger) ,                            

let round1 := eval_state (  ↑17 ε LocalState_ι_updateRounds_Л_round1) l in

let eelector := eval_state ( ↓ ConfigParamsBase_Ф_getElector ) l in 
let ret4 : bool := errorValueIsValue eelector in
let elector := errorMapDefault Datatypes.id eelector 0 in 

let ertp := eval_state ( ↓ ConfigParamsBase_Ф_roundTimeParams ) l in
let ret5 : bool := errorValueIsValue ertp in
let rtp := errorMapDefault Datatypes.id ertp (0,0,0,0) in 
let stakeHeldFor := snd rtp in 

let round1 :=  {$ round1 with ( RoundsBase_ι_Round_ι_supposedElectedAt , validationEnd) ;
                                   ( RoundsBase_ι_Round_ι_validatorsElectedFor , validatorsElectedFor ) ;
                                   ( RoundsBase_ι_Round_ι_elector , elector) ;
                                   ( RoundsBase_ι_Round_ι_vsetHashInElectionPhase , curValidatorHash) ;
                                   ( RoundsBase_ι_Round_ι_stakeHeldFor , stakeHeldFor) $} in

let newl := {$l With (LocalState_ι_updateRounds_Л_round1, round1) $} in
let m_validatorWallet := eval_state ( ↑2 ε ValidatorBase_ι_m_validatorWallet) newl in
let (stakeSum, newl) :=  run (↓ RoundsBase_Ф_stakeSum
               ( ( round1 ->> RoundsBase_ι_Round_ι_stakes ) [m_validatorWallet])) newl  in 
let round1 :=  {$ round1 with ( RoundsBase_ι_Round_ι_validatorStake , stakeSum) $} in

let m_validatorAssurance := eval_state ( ↑12 ε DePoolContract_ι_m_validatorAssurance) newl in
let isValidatorStakeOk := round1 ->> RoundsBase_ι_Round_ι_validatorStake  >=? m_validatorAssurance in


let round1 := if negb isValidatorStakeOk  then 
{$ round1 with  ( RoundsBase_ι_Round_ι_step , RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze  ) ;
                ( RoundsBase_ι_Round_ι_completionReason  , RoundsBase_ι_CompletionReasonP_ι_ValidatorStakeIsTooSmall) ;                 
                ( RoundsBase_ι_Round_ι_unfreeze , 0)  $}
                                   else
{$ round1 with ( RoundsBase_ι_Round_ι_step , RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest) $}  in

let oldEvents := eval_state ( ↑16 ε VMState_ι_events ) newl in 
let newEvent : LedgerEvent :=  StakeSigningRequested ( round1 ->> RoundsBase_ι_Round_ι_supposedElectedAt )
                                        ( round1 ->> RoundsBase_ι_Round_ι_proxy ) in
let newl := if negb isValidatorStakeOk  then newl else 
             {$ newl With VMState_ι_events := newEvent :: oldEvents  $} in

exec_state ( DePoolContract_Ф_updateRounds_tailer3 validationEnd validatorsElectedFor curValidatorHash) l =
       {$newl With (LocalState_ι_updateRounds_Л_round1, round1) $}.  
Proof.
  intros.
  destructLedger l. 
  compute. idtac.

  repeat destructIf_solve2. idtac.           
  destructFunction1 RoundsBase_Ф_stakeSum; auto. idtac.              
  repeat destructIf_solve2. 
  
Qed.  


Lemma DePoolContract_Ф_updateRounds_tailer3_eval : forall (validationEnd validatorsElectedFor curValidatorHash: XInteger) (l: Ledger) ,                            
eval_state ( DePoolContract_Ф_updateRounds_tailer3 validationEnd validatorsElectedFor curValidatorHash) l = Value I.
       
Proof.
  intros.
  destructLedger l. 
  compute. idtac.

  repeat destructIf_solve2. idtac.           
  destructFunction1 RoundsBase_Ф_stakeSum; auto. idtac.              
  repeat destructIf_solve2. 
  
Qed.  

Lemma DePoolContract_Ф_updateRounds_tailer_eq: DePoolContract_Ф_updateRounds_tailer = DePoolContract_Ф_updateRounds_tailer2.
Proof.
  auto.
Qed.


End DePoolContract_Ф_updateRounds.