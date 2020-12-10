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

Definition DePoolContract_Ф_addOrdinaryStake'_header ( Л_stake : XInteger64 ) (f: XInteger64 -> XInteger64 -> LedgerT True) : 
           LedgerT ( XErrorValue (XValueValue True) XInteger ) := 
    Require {{ msg_sender () ?!= $ xInt0 , ↑7 D2! Errors_ι_IS_EXT_MSG }} ;
    (*if (m_poolClosed) { return _sendError(STATUS_DEPOOL_CLOSED, 0); } *)
    If!! ( ↑12 D2! DePoolContract_ι_m_poolClosed ) then {  
        DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_DEPOOL_CLOSED , $ xInt0 !) >>=
        fun x => return! (xError x)  } ; 
    (* uint64 msgValue = uint64(msg.value); *)
    U0! Л_msgValue :=  msg_value () ; 
    (* if (msgValue < uint(stake) + STAKE_FEE) {return _sendError(STATUS_FEE_TOO_SMALL, STAKE_FEE);} *)
    If!! ( $ Л_msgValue ?< $ Л_stake !+ ↑12 D2! DePoolContract_ι_STAKE_FEE ) then { 
        DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_FEE_TOO_SMALL , ↑ε12 DePoolContract_ι_STAKE_FEE !) >>=
        fun x => return! (xError x)  } ; 
    
    (* uint64 fee = msgValue - stake; *)
    U0! Л_fee := $ Л_msgValue !- $ Л_stake ;
    (* if (stake < m_minStake) {return _sendError(STATUS_STAKE_TOO_SMALL, m_minStake);} *)
    If! ( $ Л_stake ?< ↑12 D2! DePoolContract_ι_m_minStake ) then { 
        DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_STAKE_TOO_SMALL , ↑ε12  DePoolContract_ι_m_minStake !) >>=
        fun x => return! (xError x) } ;

        f Л_stake Л_fee.

Definition DePoolContract_Ф_addOrdinaryStake'_tailer (Л_stake Л_fee: XInteger64) : LedgerT True :=    
    (*DePoolLib.Participant participant = getOrCreateParticipant(msg.sender);*)
    U0! Л_participant := ParticipantBase_Ф_getOrCreateParticipant (! msg_sender () !) ; 
    (* Round round = getRound0(); *)
    U0! Л_round := RoundsBase_Ф_getRound0 () ;
    (*optional(InvestParams) empty;*)
    U0! Л_empty := $default ; 
    (*(round, participant) = _addStakes(round, participant, msg.sender, stake, empty, empty);*)
    U0! {( Л_round , Л_participant )} :=  RoundsBase_Ф__addStakes (! $ Л_round , 
                                                                        $ Л_participant , 
                                                                        msg_sender () , 
                                                                        $ Л_stake , 
                                                                        $ Л_empty , 
                                                                        $ Л_empty !) ; 
    (*  setRound0(round); *)
    RoundsBase_Ф_setRound0 (! $ Л_round !) >>
    (* _setOrDeleteParticipant(msg.sender, participant); *)
    (ParticipantBase_Ф__setOrDeleteParticipant (! msg_sender () , $ Л_participant !)) >>
    (* sendAcceptAndReturnChange128(fee); *)
    (DePoolContract_Ф_sendAcceptAndReturnChange128 (! $ Л_fee !)) >> 
            return! I. 
    
(*     Definition DePoolContract_Ф_addOrdinaryStake ( Л_stake : XInteger64 ) : LedgerT ( XErrorValue True XInteger ) := 
    do r ← DePoolContract_Ф_addOrdinaryStake' Л_stake ;
    return! (xErrorMapDefaultF (xValue ∘ fromValueValue) r xError).  *)
       
(* 
    function addOrdinaryStake(uint64 stake) public onlyInternalMessage {
        if (m_poolClosed) {
            return _sendError(STATUS_DEPOOL_CLOSED, 0);
        }

        uint64 msgValue = uint64(msg.value);
        if (msgValue < uint(stake) + STAKE_FEE) {
            return _sendError(STATUS_FEE_TOO_SMALL, STAKE_FEE);
        }
        uint64 fee = msgValue - stake;
        if (stake < m_minStake) {
            return _sendError(STATUS_STAKE_TOO_SMALL, m_minStake);
        }

        DePoolLib.Participant participant = getOrCreateParticipant(msg.sender);
        Round round = getRound0();
        optional(InvestParams) empty;
        (round, participant) = _addStakes(round, participant, msg.sender, stake, empty, empty);
        setRound0(round);
        _setOrDeleteParticipant(msg.sender, participant);

        sendAcceptAndReturnChange128(fee);
    } *)

Opaque DePoolContract_Ф_sendAcceptAndReturnChange128 RoundsBase_Ф__addStakes. 


Lemma addOrdinaryStake'_tailer_exec: forall (Л_stake Л_fee: Z) (l: Ledger), 
exec_state (DePoolContract_Ф_addOrdinaryStake'_tailer Л_stake Л_fee) l = 

let sender := eval_state msg_sender l in 
let (participant, l_getcreate) := run (↓ ParticipantBase_Ф_getOrCreateParticipant sender) l in

let round := eval_state (↓ RoundsBase_Ф_getRound0 ) l_getcreate in
let (rp' , l_addStakes) := run (↓ RoundsBase_Ф__addStakes round participant sender Л_stake None None) l_getcreate in
let (round', participant') := rp' in
let l_setRound := exec_state (↓ RoundsBase_Ф_setRound0 round') l_addStakes in
let sender' := eval_state msg_sender l_setRound in  
let l_setParticipant := exec_state (↓ ParticipantBase_Ф__setOrDeleteParticipant sender' participant') l_setRound in
let l_sendAccept := exec_state (↓ DePoolContract_Ф_sendAcceptAndReturnChange128 Л_fee) l_setParticipant in
   l_sendAccept.

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
    
    
  Time  repeat (
      
      time match goal with
        | |- ?x =>
          match x with
            | context [hmapLookup Z.eqb ?n ?m] =>
                                 idtac "destruct" m;
                                 let p := fresh"p" in
                                 destruct (hmapLookup Z.eqb n m) as [p | ];
                                 [try destruct p | ]
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

      all: pr_numgoals.
Qed.

Lemma addOrdinaryStake'_header_exec: forall (Л_stake: Z) (l: Ledger) f, 
    exec_state (DePoolContract_Ф_addOrdinaryStake'_header Л_stake f) l = 
    
    let sender := eval_state msg_sender l in 
    let isExtMsg : bool := negb (sender =? 0) in 
    let isPoolClosed : bool := eval_state (↑12 ε DePoolContract_ι_m_poolClosed) l in 
    let minStake := eval_state (↑12 ε DePoolContract_ι_m_minStake) l in 
    let STAKE_FEE := eval_state (↑12 ε DePoolContract_ι_STAKE_FEE) l in
    let msg_value := eval_state msg_value l in 
    let feeSmall := msg_value <? Л_stake + STAKE_FEE in
    let fee := msg_value - Л_stake in
    let stakeSmall := Л_stake <? minStake in
    if isExtMsg then 
     if isPoolClosed then exec_state (DePoolContract_Ф__sendError (eval_state (↑ε12 DePoolContract_ι_STATUS_DEPOOL_CLOSED) l) 
                                                                   0) l
     else if feeSmall then exec_state (DePoolContract_Ф__sendError (eval_state (↑ε12 DePoolContract_ι_STATUS_FEE_TOO_SMALL) l) 
                                                                    (eval_state (↑ε12 DePoolContract_ι_STAKE_FEE) l) ) l
     else if stakeSmall then exec_state (DePoolContract_Ф__sendError (eval_state (↑ε12 DePoolContract_ι_STATUS_STAKE_TOO_SMALL) l) 
                                                                     (eval_state (↑ε12  DePoolContract_ι_m_minStake) l) ) l
     else exec_state (f Л_stake fee) l
    else l.
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
                                              case b ; (* use case_eq to see destruction results *)
                                              simpl (* ; intros *)   
            | context  [match f ?a ?b
                  with
                  | SimpleState s => s
                  end ?m] => idtac "found f ..." a b; 
                             let p := fresh"p" in
                             destruct (f a b) as (p);
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
Qed.



Lemma addOrdinaryStake_eval: forall (Л_stake: Z) (l: Ledger), 
eval_state (DePoolContract_Ф_addOrdinaryStake' Л_stake) l = 

let sender := eval_state msg_sender l in 
let isExtMsg : bool := negb (sender =? 0) in 
let isPoolClosed : bool := eval_state (↑12 ε DePoolContract_ι_m_poolClosed) l in 
let minStake := eval_state (↑12 ε DePoolContract_ι_m_minStake) l in 
let STAKE_FEE := eval_state (↑12 ε DePoolContract_ι_STAKE_FEE) l in
let msg_value := eval_state msg_value l in 
let feeSmall := msg_value <? Л_stake + STAKE_FEE in
let stakeSmall := Л_stake <? minStake in
if isExtMsg then 
 if isPoolClosed then Value (Error I) 
 else if feeSmall then Value (Error I)
 else if stakeSmall then Value (Error I)
 else Value (Value I)
else Error (eval_state (↑ε7 Errors_ι_IS_EXT_MSG) l).
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
                                            (* compute ; *)
                                            (* let rem := fresh "rem" in  *)
                                            (* set (rem:= b) ;  *)
                                          case b ; 
                                          simpl(* ; intros *)    
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



  
