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

Require Import depoolContract.Lib.CommonStateProofs.

Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope solidity_scope.
Require Import Lists.List.
Import ListNotations.
Local Open Scope list_scope.

Require Import depoolContract.DePoolConsts.
Module DePoolContract_Ф_setValidatorRewardFraction (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.



Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair.

(* function setValidatorRewardFraction(uint8 fraction) public { 
     require(msg.pubkey() == tvm.pubkey(), Errors.IS_NOT_OWNER); 
     require(fraction < m_validatorRewardFraction, Errors.NEW_VALIDATOR_FRACTION_MUST_BE_GREATER_THAN_OLD); 
     require(fraction > 0, Errors.FRACTION_MUST_NOT_BE_ZERO); 
     tvm.accept(); 
 
     m_validatorRewardFraction = fraction; 
     m_participantRewardFraction = 100 - m_validatorRewardFraction; 
     emit RewardFractionsChanged(m_validatorRewardFraction, m_participantRewardFraction); 
  } *) 

Lemma DePoolContract_Ф_setValidatorRewardFraction_exec : forall ( Л_fraction : XInteger8 )
                                                                (l: Ledger) ,
let req1 : bool := eval_state msg_pubkey l =? eval_state tvm_pubkey l in
let req2 : bool := Л_fraction <? (eval_state ( ↑12 ε DePoolContract_ι_m_validatorRewardFraction ) l) in
let req3 : bool := Л_fraction >? 0 in
let l_tvm_accept := exec_state ( tvm_accept ) l in
let m_validatorRewardFraction := Л_fraction in
let m_participantRewardFraction := 100 - m_validatorRewardFraction in
let oldEvents := eval_state (↑16 ε VMState_ι_events) l in
let newEvent  := RewardFractionsChanged m_validatorRewardFraction m_participantRewardFraction in 

let l' := if req1 then
            if req2 then 
              if req3 then {$ l_tvm_accept With ( DePoolContract_ι_m_validatorRewardFraction , m_validatorRewardFraction ) ;
                                                ( DePoolContract_ι_m_participantRewardFraction , m_participantRewardFraction ) ;
                                                (VMState_ι_events ,  newEvent :: oldEvents ) $}
              else l
            else l
          else l  in
exec_state ( ↓ DePoolContract_Ф_setValidatorRewardFraction Л_fraction ) l = l' .
Proof.
  intros.
  destructLedger l. 
  compute. idtac.

  Time repeat destructIf_solve2. 
Qed. 
 
Lemma DePoolContract_Ф_setValidatorRewardFraction_eval : forall ( Л_fraction : XInteger8 )
                                                                (l: Ledger) ,
let req1 : bool := eval_state msg_pubkey l =? eval_state tvm_pubkey l in
let req2 : bool := Л_fraction <? (eval_state ( ↑12 ε DePoolContract_ι_m_validatorRewardFraction ) l) in
let req3 : bool := Л_fraction >? 0 in

let ret' := if req1 then
            if req2 then 
              if req3 then Value I
              else Error Errors_ι_FRACTION_MUST_NOT_BE_ZERO
            else Error Errors_ι_NEW_VALIDATOR_FRACTION_MUST_BE_GREATER_THAN_OLD
          else Error Errors_ι_IS_NOT_OWNER in 
eval_state ( ↓ DePoolContract_Ф_setValidatorRewardFraction Л_fraction ) l = ret' .
Proof.
  intros.
  destructLedger l. 
  compute. idtac.

  Time repeat destructIf_solve2. 
Qed. 


End DePoolContract_Ф_setValidatorRewardFraction.