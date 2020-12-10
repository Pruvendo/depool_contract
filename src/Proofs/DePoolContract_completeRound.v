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




(*function completeRound(uint64 roundId, uint32 participantQty) public selfCall {

req     require(msg.sender == address(this), Errors.IS_NOT_DEPOOL);
        tvm.accept();
req1    require(isRound2(roundId) || m_poolClosed, InternalErrors.ERROR522);
        optional(Round) optRound = fetchRound(roundId);
req2    require(optRound.hasValue(), InternalErrors.ERROR519);
        Round round = optRound.get();
req3    require(round.step == RoundStep.Completing, InternalErrors.ERROR518);

        this.completeRoundWithChunk{flag: 1, bounce: false}(roundId, 1);
        tvm.commit();
        tvm.accept();
if1     if (participantQty < MAX_MSGS_PER_TR) {
            round = _returnOrReinvest(round, MAX_MSGS_PER_TR);
            setRound(roundId, round);
        } else {
            uint outActionQty = (participantQty + MAX_MSGS_PER_TR - 1) / MAX_MSGS_PER_TR; 
if2         if (outActionQty > MAX_QTY_OF_OUT_ACTIONS) {
                uint32 restParticipant = participantQty;
for1            for (int msgQty = 0; restParticipant > 0; ++msgQty) {
                    uint32 curGroup =
                        (restParticipant < MAX_PARTICIPANTS || msgQty + 1 == MAX_QTY_OF_OUT_ACTIONS) ?
                        restParticipant :
                        MAX_PARTICIPANTS;
                    this.completeRound{flag: 1, bounce: false}(roundId, curGroup);
                    restParticipant -= curGroup;
                }
            } else {
                for (uint i = 0; i < participantQty; i += MAX_MSGS_PER_TR) {
                    this.completeRoundWithChunk{flag: 1, bounce: false}(roundId, MAX_MSGS_PER_TR);
                }
            }
        }
    }
*)
Check 0.
Lemma DePoolContract_Ф_completeRound_exec : forall ( Л_roundId : XInteger64 ) 
                                                   ( Л_participantQty : XInteger32 ) 
                                                   (l: Ledger) , 
                                           (* : LedgerT ( XErrorValue True XInteger ) : *)
        (* require(msg.sender == address(this), Errors.IS_NOT_DEPOOL); *)
let req : bool := ( negb ( ( eval_state ( ↓ msg_sender ) l ) =? ( eval_state ( ↓ tvm_address ) l ) ) ) in
        (* tvm.accept(); *) 
let l_tvm_accept := ( exec_state ( ↓ tvm_accept ) l ) in
        (* require(isRound2(roundId) || m_poolClosed, InternalErrors.ERROR522); *)
let req1 : bool := ( negb ( ( eval_state ( ↓ RoundsBase_Ф_isRound2 Л_roundId ) l_tvm_accept ) 
                    || ( eval_state ( ↑12 ε DePoolContract_ι_m_poolClosed ) l_tvm_accept ) )%bool ) in
        (* optional(Round) optRound = fetchRound(roundId); *)
let optRound := eval_state ( ↓ ( RoundsBase_Ф_fetchRound Л_roundId ) ) l_tvm_accept in
        (* require(optRound.hasValue(), InternalErrors.ERROR519); *)
let req2 : bool := ( negb ( xMaybeIsSome optRound ) ) in
        (* Round round = optRound.get(); *)
let round := ( maybeGet optRound ) in
        (* require(round.step == RoundStep.Completing, InternalErrors.ERROR518); *)
let if2 : bool := ( negb ( eqb ( round ->> RoundsBase_ι_Round_ι_step ) 
                  RoundsBase_ι_RoundStepP_ι_Completing ) ) in
        (* this.completeRoundWithChunk{flag: 1, bounce: false}(roundId, 1); *)
let oldMessages := VMState_ι_messages ( Ledger_ι_VMState l_tvm_accept ) in
let newMessage  := {| contractAddress :=  0 ;
                      contractFunction := DePoolContract_Ф_completeRoundWithChunkF Л_roundId 1 ;
                      contractMessage := {| messageValue := default ;
                                            messageFlag  := 1 ; 
                                            messageBounce := false
                                            |} |} in 
let l_message := {$ l_tvm_accept With ( VMState_ι_messages , newMessage :: oldMessages ) $} in
        (* tvm.commit(); *)
let l_tvm_commit := ( exec_state ( ↓ tvm_accept ) l_message ) in
        (* tvm.accept(); *)
let l_tvm_accept := ( exec_state ( ↓ tvm_accept ) l_tvm_commit ) in
        (* if (participantQty < MAX_MSGS_PER_TR) { *)
let if1 : bool := ( Л_participantQty <? ( eval_state (↑12 ε DePoolContract_ι_MAX_MSGS_PER_TR ) l_tvm_accept ) ) in
        (* uint outActionQty = (participantQty + MAX_MSGS_PER_TR - 1) / MAX_MSGS_PER_TR; *)
let outActionQty := ( ( Л_participantQty + 
                    ( eval_state ( ↑12 ε DePoolContract_ι_MAX_MSGS_PER_TR ) l_tvm_accept )
                     - 1 )  / ( eval_state ( ↑12 ε DePoolContract_ι_MAX_MSGS_PER_TR ) l_tvm_accept ) ) in
        (* if (outActionQty > MAX_QTY_OF_OUT_ACTIONS) { *)
let if2 : bool := ( outActionQty >? ( eval_state ( ↑12 ε DePoolContract_ι_MAX_QTY_OF_OUT_ACTIONS ) l_tvm_accept ) ) in
        (* uint32 restParticipant = participantQty; *)
let restParticipant := Л_participantQty in

let l' := if req then l else if req then l_tvm_accept else if req2 then l_tvm_accept else
          if if1 then 
            (* round = _returnOrReinvest(round, MAX_MSGS_PER_TR);
               setRound(roundId, round); *)
               ( exec_state ( ↓ RoundsBase_Ф_setRound Л_roundId round ) 
                 ( exec_state ( ↓ DePoolContract_Ф__returnOrReinvest round 
                                  ( eval_state ( ↑12 ε DePoolContract_ι_MAX_MSGS_PER_TR ) l_tvm_accept ) 
                        ) l_tvm_accept ) ) 
          else if ( restParticipant <? 0 ) then l_tvm_accept
               else (* here was the loops - I dont know ... *) l_tvm_accept in

 	 exec_state (  DePoolContract_Ф_completeRound Л_roundId Л_participantQty ) l = l' .  
 Proof. 
   intros. destructIf. auto. 
 Abort. 
 
 Lemma DePoolContract_Ф_completeRound_eval : forall ( Л_roundId : XInteger64 ) 
                                                   ( Л_participantQty : XInteger32 ) 
                                                   (l: Ledger) , 
                                           (* : LedgerT ( XErrorValue True XInteger ) : *) 	 
        (* require(msg.sender == address(this), Errors.IS_NOT_DEPOOL); *)
let req : bool := ( negb ( ( eval_state ( ↓ msg_sender ) l ) =? ( eval_state ( ↓ tvm_address ) l ) ) ) in
        (* tvm.accept(); *) 
let l_tvm_accept := ( exec_state ( ↓ tvm_accept ) l ) in
        (* require(isRound2(roundId) || m_poolClosed, InternalErrors.ERROR522); *)
let req1 : bool := ( negb ( ( eval_state ( ↓ RoundsBase_Ф_isRound2 Л_roundId ) l_tvm_accept ) 
                    || ( eval_state ( ↑12 ε DePoolContract_ι_m_poolClosed ) l_tvm_accept ) )%bool ) in
        (* optional(Round) optRound = fetchRound(roundId); *)
let optRound := eval_state ( ↓ ( RoundsBase_Ф_fetchRound Л_roundId ) ) l_tvm_accept in
        (* require(optRound.hasValue(), InternalErrors.ERROR519); *)
let req2 : bool := ( negb ( xMaybeIsSome optRound ) ) in
 
eval_state (  DePoolContract_Ф_completeRound Л_roundId Л_participantQty ) l = 
       if req then Error ( eval_state ( ↑7 ε Errors_ι_IS_NOT_DEPOOL ) l )
       else
       if req1 then Error ( eval_state ( ↑8 ε InternalErrors_ι_ERROR522 ) l_tvm_accept )
       else
       if req2 then Error ( eval_state ( ↑8 ε InternalErrors_ι_ERROR519 ) l_tvm_accept )
       else Value I. 
 Proof. 
   intros. destructIf. auto. 
 Abort. 