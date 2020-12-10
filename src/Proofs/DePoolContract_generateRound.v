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

(* function generateRound() internal returns (Round) {
        Request req;
        Round r = Round({
            id: m_roundQty,
            supposedElectedAt: 0, 
            unfreeze: DePoolLib.MAX_TIME, 
            stakeHeldFor: 0,
            vsetHashInElectionPhase: 0, 
            step: RoundStep.PrePooling,
            completionReason: CompletionReason.Undefined,
            stake: 0,
            recoveredStake: 0,
            unused: 0,
            isValidatorStakeCompleted: false,
            grossReward: 0,
            rewards: 0,
            participantQty : 0,
            validatorStake: 0,
            validatorRemainingStake: 0,
            handledStakesAndRewards: 0,
            validatorRequest: req,
            elector: address(0), // set when round in elections phase
            proxy: getProxy(m_roundQty)
        });
        ++m_roundQty;
        return r;
    }
*) 

Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo.

Lemma DePoolContract_Ф_generateRound_exec : forall (l: Ledger) , 
exec_state ( ↓ DePoolContract_Ф_generateRound ) l = 

let m_roundQty1 := ( eval_state ( ↑11 ε RoundsBase_ι_m_roundQty ) l ) + 1 in

    {$ l With ( RoundsBase_ι_m_roundQty , m_roundQty1 ) $} .  
 Proof. 
   intros. destruct l. auto. 
 Qed. 
 
Lemma DePoolContract_Ф_generateRound_eval : forall (l: Ledger) , 
eval_state ( ↓ DePoolContract_Ф_generateRound ) l = 
let addr : XAddress := default in
let req (* : DePoolLib_ι_RequestP *) := default in
let r : RoundsBase_ι_Round := ( RoundsBase_ι_RoundC 
  ( eval_state ( ↑11 ε RoundsBase_ι_m_roundQty ) l )  
 	0  
 	( eval_state ( ↑9 ε DePoolLib_ι_MAX_TIME ) l )
  0 0
 	 RoundsBase_ι_RoundStepP_ι_PrePooling 
 	 RoundsBase_ι_CompletionReasonP_ι_Undefined  
 	 0 0 0 false  0 0 0 default 0 0 0 req default  
 	( eval_state ( ↓ ( ProxyBase_Ф_getProxy ( eval_state ( ↑11 ε RoundsBase_ι_m_roundQty ) l ) ) ) l )
	) in r . 
 Proof.  
   intros. destruct l. auto. 
Qed. 