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


Lemma letIf: forall X Y (b: bool) (f g: X*Ledger) (h: X -> Ledger -> Y), 
(let (x, t) := if b then f else g in h x t)=
if b then let (x, t) := f in h x t else
          let (x, t) := g in h x t .
Proof.
  intros.
  destruct b; auto.
Qed.

Lemma matchIf: forall X (b: bool) (f g: LedgerT X) (l: Ledger), 
(match (if b then f else g) with | SimpleState c => c end l)=
if b then match f with | SimpleState c => c end l else 
match g with | SimpleState c => c end l.
Proof.
  intros.
  destruct b; auto.
Qed.




Ltac pr_numgoals := let n := numgoals in idtac "There are" n "goals".
Ltac pr_hyp := repeat match goal with
               | H: ?x = true |- _ => idtac x " = true"
               | H: ?x = false |- _ => idtac x " = false"  
                end.



(*
onBounce(TvmSlice body) external {
        uint32 functionId = body.decode(uint32);
        bool isProcessNewStake = functionId == tvm.functionId(IProxy.process_new_stake);
        bool isRecoverStake = functionId == tvm.functionId(IProxy.recover_stake);
        if (isProcessNewStake || isRecoverStake) {
            uint64 roundId = body.decode(uint64);
            optional(Round) optRound = fetchRound(roundId);
            if (isProcessNewStake) {
                require(isRound1(roundId), InternalErrors.ERROR524);
                Round r1 = optRound.get();
                require(r1.step == RoundStep.WaitingIfStakeAccepted, InternalErrors.ERROR525);
                r1.step = RoundStep.WaitingValidatorRequest; // roll back step
                emit ProxyHasRejectedTheStake(r1.validatorRequest.queryId);
                optRound.set(r1);
            } else {
                if (isRound2(roundId)) {
                    Round r2 = optRound.get();
                    require(r2.step == RoundStep.WaitingReward, InternalErrors.ERROR526);
                    r2.step = RoundStep.WaitingUnfreeze; // roll back step
                    optRound.set(r2);
                } else if (isRound1(roundId)) {
                    Round r1 = optRound.get();
                    require(r1.step == RoundStep.WaitingIfValidatorWinElections, InternalErrors.ERROR527);
                    r1.step = RoundStep.WaitingValidationStart; // roll back step
                    optRound.set(r1);
                } else {
                    revert(InternalErrors.ERROR528);
                }
                emit ProxyHasRejectedRecoverRequest(roundId);
            }
            setRound(roundId, optRound.get());
        }
    }
*)


Import TVMModel.LedgerClass.
Opaque roundStepEqb. 

Lemma DePoolContract_Ф_onBounce_eval : forall (l : Ledger) (body : TvmSlice),

eval_state (DePoolContract_Ф_onBounce body) l = 


let (functionId, body') := decode_uint32 body in
let process_new_stake_id := tvm_functionId IProxy_И_process_new_stakeF in 
let recover_stake_id := tvm_functionId IProxy_И_recover_stakeF in 

let (roundId, _) := decode_uint64 body' in
let optRound := eval_state (↓ RoundsBase_Ф_fetchRound roundId) l in
let round := maybeGet optRound in
let roundFound : bool := isSome optRound in
let isRound1 : bool := eval_state (↓ RoundsBase_Ф_isRound1 roundId) l in
let isRound2 : bool := eval_state (↓ RoundsBase_Ф_isRound2 roundId) l in 
let step := RoundsBase_ι_Round_ι_step round in
let step_wsa : bool := roundStepEqb step RoundsBase_ι_RoundStepP_ι_WaitingIfStakeAccepted in
let step_wr : bool := roundStepEqb step RoundsBase_ι_RoundStepP_ι_WaitingReward in
let step_wwe : bool := roundStepEqb step RoundsBase_ι_RoundStepP_ι_WaitingIfValidatorWinElections in
(* emit ProxyHasRejectedRecoverRequest(roundId); *)
(* let oldEvents := eval_state ( ↑16 ε VMState_ι_events ) l in
let queryId := DePoolLib_ι_Request_ι_queryId (RoundsBase_ι_Round_ι_validatorRequest round) in
let l_emit1 := {$ l With VMState_ι_events := ProxyHasRejectedTheStake queryId :: oldEvents $} in
let l_emit2 := {$ l With VMState_ι_events := ProxyHasRejectedRecoverRequest roundId :: oldEvents $} in *)

let isProcessNewStake := eqb functionId  process_new_stake_id in
let isRecoverStake := eqb functionId  recover_stake_id in
(* let round_pns := 
    {$ round with (RoundsBase_ι_Round_ι_step , RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest) $} in
let round_recover_1 :=
    {$ round with (RoundsBase_ι_Round_ι_step , RoundsBase_ι_RoundStepP_ι_WaitingValidationStart) $} in
let round_recover_2 :=
    {$ round with (RoundsBase_ι_Round_ι_step , RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze) $} in  *)

if (isProcessNewStake || isRecoverStake)%bool then 
    if (isProcessNewStake) then 
        if isRound1 then 
            if roundFound then 
                if step_wsa then Value I 
                            else Error (eval_state (↑ε8 InternalErrors_ι_ERROR525) l)
            else Error (eval_state (↑ε8 InternalErrors_ι_ERROR519) l)
        else Error (eval_state (↑ε8 InternalErrors_ι_ERROR524) l)
    else 
        if isRound2 then 
            if roundFound then 
                if step_wr then Value I
                else Error (eval_state (↑ε8 InternalErrors_ι_ERROR526) l)
            else Error (eval_state (↑ε8 InternalErrors_ι_ERROR519) l)
        else if isRound1 then 
                if roundFound then
                    if step_wwe then Value I
                    else Error (eval_state (↑ε8 InternalErrors_ι_ERROR527) l)
                else Error (eval_state (↑ε8 InternalErrors_ι_ERROR519) l)
        else Error (eval_state (↑ε8 InternalErrors_ι_ERROR528) l)                                                 
else Value I.
Proof.
    intros.
    destruct l. 
    destruct Ledger_ι_DebugDePool, Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ConfigParamsBase, Ledger_ι_ParticipantBase, 
    Ledger_ι_DePoolHelper, Ledger_ι_Errors, Ledger_ι_InternalErrors, Ledger_ι_DePoolLib, Ledger_ι_DePoolProxyContract, 
    Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_DePool, Ledger_ι_Participant, Ledger_ι_TestElector, 
    Ledger_ι_VMState, Ledger_ι_LocalState.

    compute. idtac.
  
    Time  do 2 (
    
    time match goal with
      | |- ?x =>
        match x with
         | context [decode_uint32 ?b] => idtac "decode_uint32" b; destruct (decode_uint32 b)
         | context [decode_uint64 ?b] => idtac "decode_uint64" b; destruct (decode_uint64 b)
         | context [hmapLookup eqb ?n ?m] =>  idtac "destruct" m "[" n "]";
                                                let p := fresh"p" in
                                                destruct (hmapLookup Z.eqb n m) as [p | ];
                                                [try destruct p | ]
        | context [if ?b then _ else _] =>  idtac "if..." b; 
                                            repeat rewrite ifSimpleState ; 
                                            repeat rewrite ifFunApply ;
                                            case b ; 
                                            simpl (* ; intros  *)                        
        | _ =>  idtac "solving..." x; pr_hyp; tryif solve [auto] then idtac "solved" else idtac "not solved"
        end
    end) . 


    remember (hmapLookup Z.eqb x0 RoundsBase_ι_m_rounds ) as lookup.
    repeat setoid_rewrite <- Heqlookup.

    destruct lookup as [p | ];
    [try destruct p | ]; simpl.

    Time  do 3  (
    rewrite <- ?Heqlookup;

    time match goal with
  
      | |- ?x =>
        match x with
        | context [if ?b then _ else _] =>  idtac "if..." b; 
                                            repeat rewrite ifSimpleState ; 
                                            repeat rewrite ifFunApply ;
                                            case b ; 
                                            simpl(*  ; intros      *)                                                                                                          
        | _ =>  idtac "solving..." x; pr_hyp; tryif solve [auto] then idtac "solved" else idtac "not solved"
        end
  
   
    end) . idtac.


  all: try match goal with
    | |- ?x =>
      match x with
      | context [if ?x then _ else _] =>  idtac "if..." x; 
                                           let b:=fresh "b" in
                                           let Heqb:=fresh "Heqb" in 
                                           remember x as b eqn:Heqb;
                                           (* rewrite <- Heqb; *)
                                           repeat setoid_rewrite <- Heqlookup in Heqb ;
                                           rewrite Heqb 
      end
  end.    idtac. 

  all: try match goal with
    | |- ?x =>
      match x with
      | context [if ?x then _ else _] =>  idtac "if..." x; 
                                           let b:=fresh "b" in
                                           let Heqb:=fresh "Heqb" in 
                                           remember x as b eqn:Heqb;
                                           (* rewrite <- Heqb; *)
                                           repeat setoid_rewrite <- Heqlookup in Heqb ;
                                           rewrite Heqb 
      end
  end.    idtac. 

  clear Heqb0.

  Time  do 1  (

    time match goal with
  
      | |- ?x =>
        match x with
        | context [if ?b then _ else _] =>  idtac "if..." b; 
                                            repeat rewrite ifSimpleState ; 
                                            repeat rewrite ifFunApply ;
                                            case b ; 
                                            simpl (* ; intros     *)                                                                                                           
        | _ =>  idtac "solving..." x; pr_hyp; tryif solve [auto] then idtac "solved" else idtac "not solved"
        end
  
   
    end) . idtac.

    auto. auto. auto. idtac.

    clear Heqb0.

    Time  do 1  (

    time match goal with
  
      | |- ?x =>
        match x with
        | context [if ?b then _ else _] =>  idtac "if..." b; 
                                            repeat rewrite ifSimpleState ; 
                                            repeat rewrite ifFunApply ;
                                            case b ; 
                                            simpl (* ; intros    *)                                                                                                            
        | _ =>  idtac "solving..." x; pr_hyp; tryif solve [auto] then idtac "solved" else idtac "not solved"
        end
  
   
    end) . idtac.

    auto. auto. idtac.

    Time  do 1  (

    time match goal with
  
      | |- ?x =>
        match x with
        | context [if ?b then _ else _] =>  idtac "if..." b; 
                                            repeat rewrite ifSimpleState ; 
                                            repeat rewrite ifFunApply ;
                                            case b ; 
                                            simpl (* ; intros    *)                                                                                                            
        | _ =>  idtac "solving..." x; pr_hyp; tryif solve [auto] then idtac "solved" else idtac "not solved"
        end
  
   
    end) . idtac.

    match goal with
    | |- ?x =>
      match x with
      | context [if ?x then _ else _] =>  idtac "if..." x; 
                                           let b:=fresh "b" in
                                           let Heqb:=fresh "Heqb" in 
                                           remember x as b eqn:Heqb;
                                           (* rewrite <- Heqb; *)
                                           repeat setoid_rewrite <- Heqlookup in Heqb ;
                                           rewrite Heqb 
      end
  end.    idtac. 

  match goal with
  | |- ?x =>
    match x with
    | context [if ?x then _ else _] =>  idtac "if..." x; 
                                         let b:=fresh "b" in
                                         let Heqb:=fresh "Heqb" in 
                                         remember x as b eqn:Heqb;
                                         (* rewrite <- Heqb; *)
                                         repeat setoid_rewrite <- Heqlookup in Heqb ;
                                         rewrite Heqb 
    end
end.    idtac. 


  Time  repeat  (

    time match goal with
  
      | |- ?x =>
        match x with
        | context [if ?b then _ else _] =>  idtac "if..." b; 
                                            repeat rewrite ifSimpleState ; 
                                            repeat rewrite ifFunApply ;
                                            case b ; 
                                            simpl (* ; intros     *)                                                                                                           
        | _ =>  idtac "solving..." x; pr_hyp; tryif solve [auto] then idtac "solved" else idtac "not solved"
        end
  
   
    end) . idtac.

    auto.  idtac.

    Time  repeat  (

    time match goal with
  
      | |- ?x =>
        match x with
        | context [if ?b then _ else _] =>  idtac "if..." b; 
                                            repeat rewrite ifSimpleState ; 
                                            repeat rewrite ifFunApply ;
                                            case_eq b ; 
                                            simpl  ; intros                                                                                                           
        | _ =>  idtac "solving..." x; pr_hyp; tryif solve [auto] then idtac "solved" else idtac "not solved"
        end
  
   
    end) . idtac.

    setoid_rewrite <- Heqlookup in H2. idtac. discriminate.
    setoid_rewrite <- Heqlookup in H2. idtac. discriminate.
    setoid_rewrite <- Heqlookup in H2. idtac. discriminate.
    setoid_rewrite <- Heqlookup in H2. idtac. discriminate.
    setoid_rewrite <- Heqlookup in H3. idtac. discriminate.
    setoid_rewrite <- Heqlookup in H3. idtac. discriminate.

  
    all: pr_numgoals.
Qed.    


Lemma DePoolContract_Ф_onBounce_exec : forall (l : Ledger) (body : TvmSlice),

exec_state (↓ DePoolContract_Ф_onBounce body) l = 

let (functionId, body') := decode_uint32 body in
let process_new_stake_id := tvm_functionId IProxy_И_process_new_stakeF in 
let recover_stake_id := tvm_functionId IProxy_И_recover_stakeF in 

let (roundId, _) := decode_uint64 body' in
let optRound := eval_state (↓ RoundsBase_Ф_fetchRound roundId) l in
let round := maybeGet optRound in
let roundFound : bool := isSome optRound in
let isRound1 : bool := eval_state (↓ RoundsBase_Ф_isRound1 roundId) l in
let isRound2 : bool := eval_state (↓ RoundsBase_Ф_isRound2 roundId) l in 
let step := RoundsBase_ι_Round_ι_step round in
let step_wsa : bool := eqb step RoundsBase_ι_RoundStepP_ι_WaitingIfStakeAccepted in
let step_wr : bool := eqb step RoundsBase_ι_RoundStepP_ι_WaitingReward in
let step_wwe : bool := eqb step RoundsBase_ι_RoundStepP_ι_WaitingIfValidatorWinElections in

let oldEvents := eval_state ( ↑16 ε VMState_ι_events ) l in
let queryId := DePoolLib_ι_Request_ι_queryId (RoundsBase_ι_Round_ι_validatorRequest round) in
let l_emit1 := {$ l With VMState_ι_events := ProxyHasRejectedTheStake queryId :: oldEvents $} in
let l_emit2 := {$ l With VMState_ι_events := ProxyHasRejectedRecoverRequest roundId :: oldEvents $} in

let isProcessNewStake := functionId =? process_new_stake_id in
let isRecoverStake := functionId =? recover_stake_id in
let round_pns := 
    {$ round with (RoundsBase_ι_Round_ι_step , RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest) $} in
let round_recover_1 :=
    {$ round with (RoundsBase_ι_Round_ι_step , RoundsBase_ι_RoundStepP_ι_WaitingValidationStart) $} in
let round_recover_2 :=
    {$ round with (RoundsBase_ι_Round_ι_step , RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze) $} in 

if (isProcessNewStake || isRecoverStake)%bool then 
    if (isProcessNewStake) then 
        if isRound1 then 
            if roundFound then 
                if step_wsa then exec_state (↓ RoundsBase_Ф_setRound roundId round_pns) l_emit1 
                            else l
            else l
        else l
    else 
        if isRound2 then 
            if roundFound then 
                if step_wr then exec_state (↓ RoundsBase_Ф_setRound roundId round_recover_2) l_emit2
                else l
            else l
        else if isRound1 then 
                if roundFound then
                    if step_wwe then exec_state (↓ RoundsBase_Ф_setRound roundId round_recover_1) l_emit2
                    else l
                else l
        else injEmbed (VMState_ι_savedDePoolContracts (Ledger_ι_VMState l)) l    
else  l.

Proof.
    intros.
    destruct l. 
    destruct Ledger_ι_DebugDePool, Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ConfigParamsBase, Ledger_ι_ParticipantBase, 
    Ledger_ι_DePoolHelper, Ledger_ι_Errors, Ledger_ι_InternalErrors, Ledger_ι_DePoolLib, Ledger_ι_DePoolProxyContract, 
    Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_DePool, Ledger_ι_Participant, Ledger_ι_TestElector, 
    Ledger_ι_VMState, Ledger_ι_LocalState.
  
(*     Opaque eqb. *)
    compute. idtac.
  
    Time  do 2 (
    
    time match goal with
      | |- ?x =>
        match x with
         | context [decode_uint32 ?b] => idtac "decode_uint32" b; destruct (decode_uint32 b)
         | context [decode_uint64 ?b] => idtac "decode_uint64" b; destruct (decode_uint64 b)
        end 
    end) . 

    repeat rewrite matchIf.  idtac.
    repeat rewrite letIf.  idtac.
    repeat rewrite matchIf.  idtac.
    repeat rewrite letIf.  idtac.
    repeat rewrite matchIf.  idtac.
    repeat rewrite letIf.  idtac.


    Time  repeat (
    
    time match goal with
      | |- ?x =>
        match x with
        | context [if ?b then _ else _] =>  idtac "if..." b; 
                                            repeat rewrite ifSimpleState ; 
                                            repeat rewrite ifFunApply ;
                                            case_eq b ; 
                                            simpl  ; intros                      
        | _ =>  idtac "solving..." x; pr_hyp; tryif solve [auto] then idtac "solved" else idtac "not solved"
        end
    end) . idtac.
   
    setoid_rewrite H3 in H4. idtac. discriminate. idtac.
    setoid_rewrite H3 in H4. idtac. discriminate. idtac.
    setoid_rewrite H3 in H4. idtac. discriminate. idtac.
    setoid_rewrite H3 in H4. idtac. discriminate. idtac.
    setoid_rewrite H4 in H5. idtac. discriminate. idtac.
    setoid_rewrite H4 in H5. idtac. discriminate. 
    all: pr_numgoals.
Qed.    


