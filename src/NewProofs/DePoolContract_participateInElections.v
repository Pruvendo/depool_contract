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
Module DePoolContract_Ф_participateInElections (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.

Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo.

Opaque DePoolContract_Ф_checkPureDePoolBalance (* ProxyBase_Ф__sendElectionRequest DePoolContract_Ф__returnChange *).

Lemma DePoolContract_Ф_participateInElections_exec : forall ( Л_queryId : XInteger64 ) 
                                                             ( Л_validatorKey : XInteger256 ) 
                                                             ( Л_stakeAt : XInteger32 ) 
                                                             ( Л_maxFactor : XInteger32 ) 
                                                             ( Л_adnlAddr : XInteger256 ) 
                                                             ( Л_signature : XList XInteger8 ) 
                                                             (l: Ledger), 
let req1 : bool  := ( eval_state ( ↓ msg_sender ) l =? eval_state ( ↑2 ε ValidatorBase_ι_m_validatorWallet ) l ) in
let req2 : bool  := negb ( eval_state ( ↑12 ε DePoolContract_ι_m_poolClosed ) l ) in
let l_tvmAccept  := exec_state ( ↓ tvm_accept ) l in
let (ifBalance, l_checkPureDePoolBalance)  :=  run ( ↓ DePoolContract_Ф_checkPureDePoolBalance ) l_tvmAccept  in
let round := eval_state ( ↓ RoundsBase_Ф_getRound1 ) l_checkPureDePoolBalance in 
let req3 : bool :=  eqb ( round ->> RoundsBase_ι_Round_ι_step )  RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest  in
let req4 : bool := Л_stakeAt =? ( round ->>  RoundsBase_ι_Round_ι_supposedElectedAt ) in  
let round1 := {$ round with ( RoundsBase_ι_Round_ι_validatorRequest ,
                      ( DePoolLib_ι_RequestC Л_queryId Л_validatorKey Л_stakeAt Л_maxFactor  Л_adnlAddr  Л_signature ) ) $} in  
let l__sendElectionRequest :=
                      exec_state ( ↓ ( ProxyBase_Ф__sendElectionRequest 
                                          ( round1 ->> RoundsBase_ι_Round_ι_proxy)
                                          ( round1 ->> RoundsBase_ι_Round_ι_id) 
                                          ( round1 ->> RoundsBase_ι_Round_ι_stake) 
                                          ( round1 ->> RoundsBase_ι_Round_ι_validatorRequest)
                                          ( round1 ->> RoundsBase_ι_Round_ι_elector) ) ) l_checkPureDePoolBalance in  
let round2 := {$ round1 with ( RoundsBase_ι_Round_ι_step ,  RoundsBase_ι_RoundStepP_ι_WaitingIfStakeAccepted ) $} in 

let l_setRound1 :=  exec_state ( ↓ RoundsBase_Ф_setRound1 round2 ) l__sendElectionRequest in 
                              
let l_returnChange := if ifBalance then exec_state ( ↓ DePoolContract_Ф__returnChange ) l_setRound1 
                                   else exec_state ( ↓ DePoolContract_Ф__returnChange ) l_checkPureDePoolBalance in
                                                          

exec_state (↓ DePoolContract_Ф_participateInElections Л_queryId Л_validatorKey Л_stakeAt Л_maxFactor Л_adnlAddr Л_signature ) l = 
if req1 then 
   (if req2 then 
    (if ifBalance then   
       (if req3 then 
            (if req4 then l_returnChange
                    else exec_state (DePoolContract_Ф__sendError DePool_ι_STATUS_INVALID_ELECTION_ID 0 ) l_checkPureDePoolBalance)
       else exec_state (DePoolContract_Ф__sendError DePool_ι_STATUS_NO_ELECTION_ROUND 0 ) l_checkPureDePoolBalance)
       else l_returnChange)
    else exec_state (DePoolContract_Ф__sendError DePool_ι_STATUS_DEPOOL_CLOSED 0 ) l)
else l. 
Proof. 

  intros.
  destructLedger l. 
  compute.

  Time repeat destructIf_solve. idtac.

  all: try destructFunction0 DePoolContract_Ф_checkPureDePoolBalance; auto. idtac.

  Time repeat destructIf_solve. idtac.

  all: try rewrite H3 in H2; try discriminate. idtac.
  all: try rewrite H5 in H3; try discriminate. idtac.
  all: try rewrite H4 in H2; try discriminate. 
Qed.  


Lemma DePoolContract_Ф_participateInElections'_eval : forall ( Л_queryId : XInteger64 ) 
                                                             ( Л_validatorKey : XInteger256 ) 
                                                             ( Л_stakeAt : XInteger32 ) 
                                                             ( Л_maxFactor : XInteger32 ) 
                                                             ( Л_adnlAddr : XInteger256 ) 
                                                             ( Л_signature : XList XInteger8 ) 
                                                             (l: Ledger), 
let req1 : bool  :=  ( eval_state ( ↓ msg_sender ) l =? eval_state ( ↑2 ε ValidatorBase_ι_m_validatorWallet ) l ) in
let req2 : bool  :=  negb ( eval_state ( ↑12 ε DePoolContract_ι_m_poolClosed ) l ) in
let l_tvmAccept := exec_state ( ↓ tvm_accept ) l in
let if1  : bool   := ( eval_state ( ↓ DePoolContract_Ф_checkPureDePoolBalance ) l_tvmAccept ) in 
let l_checkPureDePoolBalance := exec_state ( ↓ DePoolContract_Ф_checkPureDePoolBalance ) l_tvmAccept in
let round := ( eval_state ( ↓ RoundsBase_Ф_getRound1 ) l_checkPureDePoolBalance ) in 
let req3 : bool :=  ( eqb ( round ->> RoundsBase_ι_Round_ι_step )  
                             RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest  ) in
let req4 :=  ( Л_stakeAt  =?  ( round ->>  RoundsBase_ι_Round_ι_supposedElectedAt ) ) in  

eval_state ( ↓ DePoolContract_Ф_participateInElections' Л_queryId Л_validatorKey Л_stakeAt Л_maxFactor Л_adnlAddr Л_signature ) l = 
if req1 then 
   (if req2 then 
    (if if1 then   
       (if req3 then 
            (if req4 then Value (Value I)
                     else Value (Error I))
       else Value (Error I))
       else Value (Value I))
    else Value (Error I))
else Error Errors_ι_IS_NOT_VALIDATOR . 
 Proof. 

  intros.
  destructLedger l. 
  compute.

  Time repeat destructIf_solve. idtac.

  all: try destructFunction0 DePoolContract_Ф_checkPureDePoolBalance; auto. idtac.

  all: repeat destructIf_solve. idtac.

  all: try rewrite H2 in H5; try discriminate. idtac.
  all: try rewrite H3 in H6; try discriminate. idtac.
  all: try rewrite H2 in H4; try discriminate. idtac.
  all: try congruence.
 Qed.

Opaque DePoolContract_Ф_participateInElections'.

Lemma DePoolContract_Ф_participateInElections_eval : forall ( Л_queryId : XInteger64 ) 
                                                             ( Л_validatorKey : XInteger256 ) 
                                                             ( Л_stakeAt : XInteger32 ) 
                                                             ( Л_maxFactor : XInteger32 ) 
                                                             ( Л_adnlAddr : XInteger256 ) 
                                                             ( Л_signature : XList XInteger8 ) 
                                                             (l: Ledger), 
let req1 : bool  :=  ( eval_state ( ↓ msg_sender ) l =? eval_state ( ↑2 ε ValidatorBase_ι_m_validatorWallet ) l ) in
let req2 : bool  :=  negb ( eval_state ( ↑12 ε DePoolContract_ι_m_poolClosed ) l ) in
let l_tvmAccept := exec_state ( ↓ tvm_accept ) l in
let if1  : bool   := ( eval_state ( ↓ DePoolContract_Ф_checkPureDePoolBalance ) l_tvmAccept ) in 
let l_checkPureDePoolBalance := exec_state ( ↓ DePoolContract_Ф_checkPureDePoolBalance ) l_tvmAccept in
let round := ( eval_state ( ↓ RoundsBase_Ф_getRound1 ) l_checkPureDePoolBalance ) in 
let req3 : bool :=  ( eqb ( round ->> RoundsBase_ι_Round_ι_step )  
                             RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest  ) in
let req4 :=  ( Л_stakeAt  =?  ( round ->>  RoundsBase_ι_Round_ι_supposedElectedAt ) ) in  

eval_state ( ↓ DePoolContract_Ф_participateInElections Л_queryId Л_validatorKey Л_stakeAt Л_maxFactor Л_adnlAddr Л_signature ) l = 
if req1 then 
   if req2 then 
    if if1 then   
       if req3 then 
            if req4 then Value I
                     else Value I
       else Value I
       else Value I
    else Value I
else Error Errors_ι_IS_NOT_VALIDATOR .
Proof.
  intros.

  assert (eval_state (↓ DePoolContract_Ф_participateInElections Л_queryId Л_validatorKey Л_stakeAt Л_maxFactor Л_adnlAddr Л_signature) l = 
  xErrorMapDefaultF (xValue ∘ fromValueValue) (eval_state (↓ DePoolContract_Ф_participateInElections' Л_queryId Л_validatorKey Л_stakeAt Л_maxFactor Л_adnlAddr Л_signature) l) xError ).

  unfold DePoolContract_Ф_participateInElections.
  unfold callEmbeddedStateAdj.
  remember (DePoolContract_Ф_participateInElections' Л_queryId Л_validatorKey Л_stakeAt Л_maxFactor Л_adnlAddr Л_signature).
  setoid_rewrite runbind.
  setoid_rewrite eval_bind2.
  rewrite eval_get.
  rewrite exec_get.
  remember (run l0 (injEmbed (T:=LocalState) DePoolFuncs.DePoolSpec.LedgerClass.local0 l)).
  setoid_rewrite <- Heqp.
  destruct p.
  destruct x.
  auto. auto.

  (**********************)
  rewrite H.
  rewrite DePoolContract_Ф_participateInElections'_eval.
  compute.
  repeat destructIf; auto. 

Qed. 

End DePoolContract_Ф_participateInElections.