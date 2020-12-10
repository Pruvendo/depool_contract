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

Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo.

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

(* Parameter f g: bool*nat.
Parameter h : nat -> bool*nat. *)

(* Lemma foo: 
(let (x, _) := f in x) = true -> 

(let (x, t) := f in (if x then g else h t)) = g.
Proof.
  intros.

  match goal with  
  | |- ?x =>
    match x with
    | context [let (x, t) := ?f in @?g x t] => replace (let (x, t) := f in g x t) with (g (fst f) (snd f)) by (symmetry; apply fstsndImplies)
    end
  end.

  match goal with  
  | H : ?x |- _ =>
    match x with
    | context [let (x, t) := ?f in @?g x t] => replace (let (x, t) := f in g x t) with (g (fst f) (snd f)) in H by (symmetry; apply fstsndImplies)
    end
  end.


  rewrite H. auto.  
Qed. *)

(* Opaque default. *)

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
                                                          

exec_state ( DePoolContract_Ф_participateInElections Л_queryId Л_validatorKey Л_stakeAt Л_maxFactor Л_adnlAddr Л_signature ) l = 
if req1 then 
   (if req2 then 
    (if ifBalance then   
       (if req3 then 
            (if req4 then l_returnChange
                    else exec_state (DePoolContract_Ф__sendError (eval_state (↑ε12 DePoolContract_ι_STATUS_INVALID_ELECTION_ID) l_checkPureDePoolBalance) 0 ) l_checkPureDePoolBalance)
       else exec_state (DePoolContract_Ф__sendError (eval_state (↑ε12 DePoolContract_ι_STATUS_NO_ELECTION_ROUND) l_checkPureDePoolBalance) 0 ) l_checkPureDePoolBalance)
       else l_returnChange)
    else exec_state (DePoolContract_Ф__sendError (eval_state (↑ε12 DePoolContract_ι_STATUS_DEPOOL_CLOSED) l) 0 ) l)
else l. 
Proof. 
  intros.
  destruct l. 
  destruct Ledger_ι_DebugDePool, Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ConfigParamsBase, Ledger_ι_ParticipantBase, 
  Ledger_ι_DePoolHelper, Ledger_ι_Errors, Ledger_ι_InternalErrors, Ledger_ι_DePoolLib, Ledger_ι_DePoolProxyContract, 
  Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_DePool, Ledger_ι_Participant, Ledger_ι_TestElector, 
  Ledger_ι_VMState, Ledger_ι_LocalState.

  compute.

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
                                          case_eq b ; 
                                          simpl ; intros                                                                                        
      | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
      end
  end) .  

  match goal with 
| |- ?x  => match x with 
      | context [DePoolContract_Ф_checkPureDePoolBalance] => remember (DePoolContract_Ф_checkPureDePoolBalance)
      end
end. idtac.

destruct l. idtac.

match goal with 
| |- ?x  => match x with 
      | context [p ?a] => remember (p a)
      end
end.

destruct p0. auto.

match goal with 
| |- ?x  => match x with 
      | context [DePoolContract_Ф_checkPureDePoolBalance] => remember (DePoolContract_Ф_checkPureDePoolBalance)
      end
end. idtac.

destruct l. idtac.

match goal with 
| |- ?x  => match x with 
      | context [p ?a] => remember (p a)
      end
end.

destruct p0. auto.

- idtac.


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
                                          case_eq b ; 
                                          simpl ; intros                                                                                        
      | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
      end

 
  end) . 

  rewrite H3 in H2. idtac. discriminate.
  rewrite H3 in H2. idtac. discriminate.
  rewrite H4 in H2. idtac.
  rewrite H5 in H3. idtac. discriminate.
  rewrite H4 in H2. idtac. discriminate.
  rewrite H5 in H3. idtac. discriminate.
  rewrite H4 in H2. idtac. discriminate.
 
- idtac.  

match goal with 
| |- ?x  => match x with 
      | context [DePoolContract_Ф_checkPureDePoolBalance] => remember (DePoolContract_Ф_checkPureDePoolBalance)
      end
end. idtac.

destruct l. idtac.

match goal with 
| |- ?x  => match x with 
      | context [p ?a] => remember (p a)
      end
end.

destruct p0. auto.

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
eval_state (  DePoolContract_Ф_participateInElections' Л_queryId Л_validatorKey Л_stakeAt Л_maxFactor Л_adnlAddr Л_signature ) l = 

if req1 then 
   (if req2 then 
    (if if1 then   
       (if req3 then 
            (if req4 then Value (Value I)
                     else Value (Error I))
       else Value (Error I))
       else Value (Value I))
    else Value (Error I))
else Error ( eval_state ( ↑7 ε Errors_ι_IS_NOT_VALIDATOR ) l ). 
 Proof. 

  intros.
  destruct l. 
  destruct Ledger_ι_DebugDePool, Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ConfigParamsBase, Ledger_ι_ParticipantBase, 
  Ledger_ι_DePoolHelper, Ledger_ι_Errors, Ledger_ι_InternalErrors, Ledger_ι_DePoolLib, Ledger_ι_DePoolProxyContract, 
  Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_DePool, Ledger_ι_Participant, Ledger_ι_TestElector, 
  Ledger_ι_VMState, Ledger_ι_LocalState.

  compute.

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
                                          case_eq b ; 
                                          simpl ; intros                                                                                        
      | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
      end
  end) .  

  match goal with 
| |- ?x  => match x with 
      | context [DePoolContract_Ф_checkPureDePoolBalance] => remember (DePoolContract_Ф_checkPureDePoolBalance)
      end
end. idtac.

destruct l. idtac.

match goal with 
| |- ?x  => match x with 
      | context [p ?a] => remember (p a)
      end
end.

destruct p0. auto.

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
                                          case_eq b ; 
                                          simpl ; intros                                                                                        
      | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
      end
  end) .  idtac.

  rewrite H2 in H5. idtac. discriminate.
  rewrite H2 in H5. idtac.
  rewrite H3 in H6. idtac. discriminate.

  match goal with 
  | |- ?x  => match x with 
        | context [DePoolContract_Ф_checkPureDePoolBalance] => remember (DePoolContract_Ф_checkPureDePoolBalance)
        end
  end. idtac.
  
  destruct l. idtac.
  
  match goal with 
  | |- ?x  => match x with 
        | context [p ?a] => remember (p a)
        end
  end.
  
  destruct p0. auto.

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
                                            case_eq b ; 
                                            simpl ; intros                                                                                        
        | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
        end
    end) .  idtac.

    rewrite H3 in H6. idtac. discriminate.
    rewrite H1 in H4. idtac. discriminate.

    match goal with 
  | |- ?x  => match x with 
        | context [DePoolContract_Ф_checkPureDePoolBalance] => remember (DePoolContract_Ф_checkPureDePoolBalance)
        end
  end. idtac.
  
  destruct l. idtac.
  
  match goal with 
  | |- ?x  => match x with 
        | context [p ?a] => remember (p a)
        end
  end.
  
  destruct p0. auto.

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
                                            case_eq b ; 
                                            simpl ; intros                                                                                        
        | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
        end
    end) .  idtac.

    rewrite H2 in H4. idtac. discriminate.
    rewrite H1 in H3. idtac. discriminate.

    match goal with 
  | |- ?x  => match x with 
        | context [DePoolContract_Ф_checkPureDePoolBalance] => remember (DePoolContract_Ф_checkPureDePoolBalance)
        end
  end. idtac.
  
  destruct l. idtac.
  
  match goal with 
  | |- ?x  => match x with 
        | context [p ?a] => remember (p a)
        end
  end.
  
  destruct p0. auto.

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
                                            case_eq b ; 
                                            simpl ; intros                                                                                        
        | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
        end
    end) .  idtac.

    rewrite H1 in H2. discriminate.
    rewrite H1 in H2. discriminate.

 Qed.    