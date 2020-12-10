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

(* Check maybeGet.

Axiom isSome_false_default : forall (X : Type) (x : XMaybe X)`{XDefault X},
xMaybeIsSome x = xBoolFalse -> maybeGet x = default.

Lemma foo: forall (x: option Z), isSome x = false -> maybeGet x = 0.
Proof.
  intros.
  apply isSome_false_default.
  apply H.
Qed. *)


(* Existing Instance embeddedLocalState.
 
Existing Instance monadStateT.
Existing Instance monadStateStateT. *)

(* Existing Instance embeddedLocalState.
Existing Instance embeddedMultisig. *)


 (* function onStakeAccept(uint64 queryId, uint32 comment, address elector) public override {
        optional(Round) optRound = fetchRound(queryId);
        require(optRound.hasValue(), InternalErrors.ERROR513);
        Round round = optRound.get();
        require(msg.sender == round.proxy, Errors.IS_NOT_PROXY);
        require(elector == round.elector, Errors.IS_NOT_ELECTOR);
        require(round.id == queryId, Errors.INVALID_QUERY_ID);
        require(round.step == RoundStep.WaitingIfStakeAccepted, Errors.INVALID_ROUND_STEP);

        tvm.accept();
        round.step = RoundStep.WaitingValidationStart;
        round.completionReason = CompletionReason.Undefined;
        setRound(queryId, round);

        emit RoundStakeIsAccepted(round.validatorRequest.queryId, comment); *) 

Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair.

Lemma DePoolContract_Ф_onStakeAccept_exec : forall ( Л_queryId : XInteger64 ) 
                                                    ( Л_comment : XInteger32 ) 
                                                    ( Л_elector : XAddress ) 
                                                         (l: Ledger) , 
 exec_state ( ↓ ( DePoolContract_Ф_onStakeAccept Л_queryId Л_comment Л_elector ) ) l =
                  (* optional(Round) optRound = fetchRound(queryId); *)
let optRound := eval_state ( ↓ ( RoundsBase_Ф_fetchRound Л_queryId ) ) l in
                  (* require(optRound.hasValue(), InternalErrors.ERROR513); *)
let req1 : bool := isSome optRound in
                  (*  Round round = optRound.get(); *)
let round := maybeGet optRound in
                  (*require(msg.sender == round.proxy, Errors.IS_NOT_PROXY);*)
let req2 : bool := eval_state msg_sender l =? round ->> RoundsBase_ι_Round_ι_proxy  in
                  (* require(elector == round.elector, Errors.IS_NOT_ELECTOR); *)
let req3 : bool := Л_elector =? round ->> RoundsBase_ι_Round_ι_elector in
                  (* require(round.id == queryId, Errors.INVALID_QUERY_ID); *)
let req4 : bool := round ->> RoundsBase_ι_Round_ι_id =? Л_queryId in
                  (* require(round.step == RoundStep.WaitingIfStakeAccepted, Errors.INVALID_ROUND_STEP); *)
let req5 : bool := eqb ( round ->> RoundsBase_ι_Round_ι_step ) RoundsBase_ι_RoundStepP_ι_WaitingIfStakeAccepted in
                  (* round.step = RoundStep.WaitingValidationStart;
                     round.completionReason = CompletionReason.Undefined; *)
let la := exec_state (↓ tvm_accept) l in                     
let round' := {$ round with ( RoundsBase_ι_Round_ι_step , RoundsBase_ι_RoundStepP_ι_WaitingValidationStart ) ;
                            ( RoundsBase_ι_Round_ι_completionReason , RoundsBase_ι_CompletionReasonP_ι_Undefined ) $} in
                  (* setRound(queryId, round); *)
let l_setRound := exec_state ( ↓ ( RoundsBase_Ф_setRound Л_queryId round' ) ) la in

                  (* emit RoundStakeIsAccepted(round.validatorRequest.queryId, comment); *)
let oldEvents := eval_state ( ↑16 ε VMState_ι_events ) l in
let newEvent  := roundStakeIsAccepted ( ( round ->> RoundsBase_ι_Round_ι_validatorRequest ) ->> DePoolLib_ι_Request_ι_queryId )  Л_comment  in
let l' := {$ l_setRound With VMState_ι_events := newEvent :: oldEvents $} in
  
  if req1 then if req2 then if req3 then if req4 then if req5 then l'
                                                              else l
                                                 else l
                                    else l
                       else l
          else l.  
 Proof. 

   intros. 
   destruct l. 
   destruct Ledger_ι_VMState.
   compute. repeat destructIf; auto. 
Qed. 
 
Lemma DePoolContract_Ф_onStakeAccept_eval : forall ( Л_queryId : XInteger64 ) 
                                                    ( Л_comment : XInteger32 ) 
                                                    ( Л_elector : XAddress ) 
                                                         (l: Ledger) ,  
eval_state (  DePoolContract_Ф_onStakeAccept Л_queryId Л_comment Л_elector ) l = 

                  (* optional(Round) optRound = fetchRound(queryId); *)
let optRound := eval_state ( ↓ ( RoundsBase_Ф_fetchRound Л_queryId ) ) l in
                  (* require(optRound.hasValue(), InternalErrors.ERROR513); *)
let req1 : bool := isSome optRound in
                  (*  Round round = optRound.get(); *)
let round := maybeGet optRound in
                  (*require(msg.sender == round.proxy, Errors.IS_NOT_PROXY);*)
let req2 : bool := eval_state  msg_sender l =?  round ->> RoundsBase_ι_Round_ι_proxy in
let req3 : bool := Л_elector =? round ->> RoundsBase_ι_Round_ι_elector in
                  (* require(round.id == queryId, Errors.INVALID_QUERY_ID); *)
let req4 : bool := round ->> RoundsBase_ι_Round_ι_id =? Л_queryId in
                  (* require(round.step == RoundStep.WaitingIfStakeAccepted, Errors.INVALID_ROUND_STEP); *)
let req5 : bool := eqb ( round ->> RoundsBase_ι_Round_ι_step ) RoundsBase_ι_RoundStepP_ι_WaitingIfStakeAccepted in

if req1 then if req2 then if req3 then if req4 then if req5 then Value I
                                                            else Error ( eval_state ( ↑7 ε Errors_ι_INVALID_ROUND_STEP ) l )
                                               else Error ( eval_state ( ↑7 ε Errors_ι_INVALID_QUERY_ID ) l )
                                  else Error ( eval_state ( ↑7 ε Errors_ι_IS_NOT_ELECTOR ) l )
                     else Error ( eval_state ( ↑7 ε Errors_ι_IS_NOT_PROXY ) l )
          else Error ( eval_state ( ↑8 ε InternalErrors_ι_ERROR513 ) l ) .

Proof. 
  intros. 
  destruct l. 
  compute. repeat destructIf; auto. 
Qed. 
