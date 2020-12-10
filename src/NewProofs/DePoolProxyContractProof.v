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
Module DePoolProxyContractProofs (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.

Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair.

(* DePoolProxyContract_Ф_Constructor5 *)

Lemma DePoolProxyContract_Ф_Constructor5_exec : forall (l: Ledger) ,
let b := default in 
let ok := false in
let b' := builder_store b ( eval_state ( msg_sender ) l )  0 in 
let publicKey := tvm_hash ( toCell b' ) in
let ok' := ( ok || ( ( eval_state ( tvm_pubkey ) l ) =? publicKey ) )%bool in 
let b'' := default in 
let b''' := builder_store b'' ( eval_state ( msg_sender ) l ) 1 in
let publicKey' := tvm_hash ( toCell b''' )  in
let ok'' := ( ok' || ( ( eval_state ( tvm_pubkey ) l ) =? publicKey' ) )%bool in
let req : bool := ( ok'' ) in

exec_state ( ↓ DePoolProxyContract_Ф_constructor5 ) l =
                 if req then {$ l With DePoolProxyContract_ι_m_dePool := eval_state msg_sender l $}
                        else l.
Proof.   
   intros. 
   destruct l. 
   destruct Ledger_ι_VMState.
   compute. destructIf; auto. 
Qed. 
 
Lemma DePoolProxyContract_Ф_Constructor5_eval : forall (l: Ledger) ,
                          
let b := default in 
let ok := false in
let b' := builder_store b ( eval_state msg_sender l ) 0 in 
let publicKey := tvm_hash ( toCell b' ) in
let ok' := ( ok || (eval_state tvm_pubkey l =? publicKey) )%bool in 
let b'' := default in 
let b''' := builder_store b'' ( eval_state msg_sender l ) 1 in
let publicKey' := tvm_hash ( toCell b''' )  in
let ok'' := ( ok' || ( eval_state tvm_pubkey l =? publicKey' ) )%bool in
let req : bool := ( ok'' ) in

eval_state (↓ DePoolProxyContract_Ф_constructor5 ) l =  
    if req then Value I
           else Error DePoolProxyContract_ι_ERROR_IS_NOT_DEPOOL . 
Proof. 
  intros. 
  destruct l.
  compute. destructIf; auto. 
Qed. 
 
(* DePoolProxyContract_Ф_process_new_stake *)

Lemma DePoolProxyContract_Ф_process_new_stake_exec : forall ( Л_queryId : XInteger64 ) 
                                                             ( Л_validatorKey : XInteger256 ) 
                                                             ( Л_stakeAt : XInteger32 ) 
                                                             ( Л_maxFactor : XInteger32 ) 
                                                             ( Л_adnlAddr : XInteger256 ) 
                                                             ( Л_signature :  XList XInteger8 ) 
                                                             ( Л_elector : XAddress ) 
                                                             (l: Ledger) ,
let msgSender := eval_state msg_sender l in
let dePoolAddress := eval_state (↑10 ε DePoolProxyContract_ι_m_dePool) l in
let msgValue := eval_state msg_value l in
let proxyFee := DePoolLib_ι_PROXY_FEE in  
let carry := msgValue - proxyFee in 
let oldMessages := eval_state (↑16 ε VMState_ι_messages) l in 
let newMessage :ContractsFunctionWithMessage  := {| contractAddress :=  Л_elector;
                      contractFunction := IElector_И_process_new_stakeF Л_queryId Л_validatorKey Л_stakeAt Л_maxFactor Л_adnlAddr  Л_signature ;
                      contractMessage :=  {| messageValue := carry;
                                            messageFlag := 0 ;
                                            messageBounce := false |} |} in 
let balance := eval_state ( tvm_balance ) l in
let minBalance := DePoolLib_ι_MIN_PROXY_BALANCE in
let req2 : bool := balance >=? carry + minBalance in

    exec_state ( ↓ DePoolProxyContract_Ф_process_new_stake Л_queryId Л_validatorKey Л_stakeAt Л_maxFactor Л_adnlAddr Л_signature Л_elector ) l =

    if ( msgSender =? dePoolAddress) then
      if req2 then  {$ l With VMState_ι_messages := newMessage :: oldMessages $} 
      else l 
    else l.  
 Proof. 
   intros. 
   destruct l. destruct Ledger_ι_VMState , Ledger_ι_DePoolProxyContract(* , Ledger_ι_DePoolLib *).
   compute. 
   repeat destructIf; auto. 
 Qed.

Lemma DePoolProxyContract_Ф_process_new_stake_eval : forall ( Л_queryId : XInteger64 ) 
                                                             ( Л_validatorKey : XInteger256 ) 
                                                             ( Л_stakeAt : XInteger32 ) 
                                                             ( Л_maxFactor : XInteger32 ) 
                                                             ( Л_adnlAddr : XInteger256 ) 
                                                             ( Л_signature : XList XInteger8 ) 
                                                             ( Л_elector : XAddress ) 
                                                             (l: Ledger) ,
let msgSender := eval_state msg_sender l in
let dePoolAddress := eval_state (↑10 D2! DePoolProxyContract_ι_m_dePool) l in
let error1 := DePoolProxyContract_ι_ERROR_IS_NOT_DEPOOL in
let error2 := DePoolProxyContract_ι_ERROR_BAD_BALANCE in
let msgValue := eval_state msg_value l in
let proxyFee := DePoolLib_ι_PROXY_FEE in 
let carry := msgValue - proxyFee in 
let balance := eval_state ( tvm_balance ) l in
let minBalance := DePoolLib_ι_MIN_PROXY_BALANCE in
let req2 : bool := balance >=? carry + minBalance in

    eval_state (↓ DePoolProxyContract_Ф_process_new_stake Л_queryId Л_validatorKey Л_stakeAt Л_maxFactor Л_adnlAddr Л_signature Л_elector ) l = 

    if (msgSender =? dePoolAddress) then 
      if req2 then Value I
              else Error error2
    else Error error1 . 
 Proof. 
  intros. 
  destruct l. destruct Ledger_ι_VMState , Ledger_ι_DePoolProxyContract (*, Ledger_ι_DePoolLib*).
  compute. 
  repeat destructIf; auto. 
 Qed. 
 

(* DePoolProxyContract_Ф_onStakeAccept *)

Lemma DePoolProxyContract_Ф_onStakeAccept_exec : forall ( Л_queryId : XInteger64 ) ( Л_comment : XInteger32 ) (l: Ledger) , 
let dePoolAddress := eval_state (↑10 D2! DePoolProxyContract_ι_m_dePool) l in
let msgValue := eval_state msg_value l in
let proxyFee := DePoolLib_ι_PROXY_FEE in
let value := msgValue - proxyFee in
let msgSender := eval_state msg_sender l in
let oldMessages := eval_state (↑16 D2! VMState_ι_messages) l in
let newMessage  := {| contractAddress  := dePoolAddress;
                      contractFunction := DePoolContract_Ф_onStakeAcceptF Л_queryId Л_comment msgSender ;
                      contractMessage  := {$ default with messageValue := value $} |} in 
                                                    
    exec_state (↓ DePoolProxyContract_Ф_onStakeAccept Л_queryId Л_comment ) l =  {$ l With VMState_ι_messages := newMessage :: oldMessages $}.  
Proof. 
  intros. auto. 
Qed. 
 
Lemma DePoolProxyContract_Ф_onStakeAccept_eval : forall ( Л_queryId : XInteger64 ) ( Л_comment : XInteger32 ) (l: Ledger) , 
 	 eval_state (↓ DePoolProxyContract_Ф_onStakeAccept Л_queryId Л_comment ) l = I . 
Proof. 
  intros. auto.  
Qed. 


(* DePoolProxyContract_Ф_onStakeReject *) 

Lemma DePoolProxyContract_Ф_onStakeReject_exec : forall ( Л_queryId : XInteger64 ) ( Л_comment : XInteger32 ) (l: Ledger) , 
let dePoolAddress := eval_state (↑10 D2! DePoolProxyContract_ι_m_dePool) l in
let msgValue := eval_state msg_value l in
let proxyFee := DePoolLib_ι_PROXY_FEE in
let value := msgValue - proxyFee in
let msgSender := eval_state msg_sender l in
let oldMessages := eval_state (↑16 D2! VMState_ι_messages) l in
let newMessage  := {| contractAddress  := dePoolAddress;
                      contractFunction := DePoolContract_Ф_onStakeRejectF Л_queryId Л_comment msgSender ;
                      contractMessage  := {$ default with messageValue := value $} |} in                                                  
      
    exec_state ( ↓ DePoolProxyContract_Ф_onStakeReject Л_queryId Л_comment ) l = {$ l With VMState_ι_messages := newMessage :: oldMessages $}. 
 Proof. 
   intros. auto. 
 Qed. 
 
 Lemma DePoolProxyContract_Ф_onStakeReject_eval : forall ( Л_queryId : XInteger64 ) 
                                                         ( Л_comment : XInteger32 ) 
                                                         (l: Ledger) , 
 	 eval_state ( ↓ DePoolProxyContract_Ф_onStakeReject Л_queryId Л_comment ) l = I . 
 Proof. 
   intros. auto. 
 Qed. 
 

(* DePoolProxyContract_Ф_recover_stake *) 
         
Lemma DePoolProxyContract_Ф_recover_stake_exec : forall ( Л_queryId : XInteger64 ) 
                                                        ( Л_elector : XAddress ) 
                                                        (l: Ledger) ,
let dePoolAddress := eval_state (↑10 ε DePoolProxyContract_ι_m_dePool) l in
let msgValue := eval_state msg_value l in
let proxyFee := DePoolLib_ι_PROXY_FEE in
let value := msgValue - proxyFee in
let msgSender := eval_state msg_sender l in
let oldMessages := eval_state (↑16 ε VMState_ι_messages) l in
let newMessage  := {| contractAddress  := Л_elector;
                      contractFunction := IElector_И_recover_stakeF Л_queryId ;
                      contractMessage  := {$ default with messageValue := value $} |} in  
let carry := msgValue - proxyFee in 
let balance := eval_state ( tvm_balance ) l in
let minBalance := DePoolLib_ι_MIN_PROXY_BALANCE in
let req2 : bool := balance >=? carry + minBalance in
    
    exec_state ( ↓ DePoolProxyContract_Ф_recover_stake Л_queryId Л_elector ) l = 
    if (msgSender =? dePoolAddress) 
        then if req2 
            then {$ l With VMState_ι_messages := newMessage :: oldMessages $} 
            else l
        else l.  
 Proof. 
  intros.
  destruct l. 
  compute; repeat destructIf; auto. 
 Qed. 
 
Lemma DePoolProxyContract_Ф_recover_stake_eval : forall ( Л_queryId : XInteger64 ) 
                                                        ( Л_elector : XAddress ) 
                                                        (l: Ledger),
let msgSender := eval_state msg_sender l in
let dePoolAddress := eval_state (↑10 D2! DePoolProxyContract_ι_m_dePool) l in
let error1 := DePoolProxyContract_ι_ERROR_IS_NOT_DEPOOL in 
let error2 := DePoolProxyContract_ι_ERROR_BAD_BALANCE in 
let proxyFee := DePoolLib_ι_PROXY_FEE in
let msgValue := eval_state msg_value l in
let carry := msgValue - proxyFee in 
let balance := eval_state ( tvm_balance ) l in
let minBalance := DePoolLib_ι_MIN_PROXY_BALANCE in
let req2 : bool := balance >=? carry + minBalance in
 
    eval_state (DePoolProxyContract_Ф_recover_stake Л_queryId Л_elector ) l = 
    if (msgSender =? dePoolAddress) then 
       if req2 then xValue I 
               else xError error2 
    else xError error1 . 
 Proof. 
  intros.
  destruct l. 
  compute; repeat destructIf; auto.
 Qed. 


(* DePoolProxyContract_Ф_onSuccessToRecoverStake *) 

Lemma DePoolProxyContract_Ф_onSuccessToRecoverStake_exec : forall ( Л_queryId : XInteger64 ) (l: Ledger) , 
let dePoolAddress := eval_state (↑10 D2! DePoolProxyContract_ι_m_dePool) l in
let msgValue := eval_state msg_value l in
let proxyFee := DePoolLib_ι_PROXY_FEE in
let value := msgValue - proxyFee in
let msgSender := eval_state msg_sender l in
let oldMessages := eval_state (↑16 D2! VMState_ι_messages) l in
let newMessage  := {| contractAddress  := dePoolAddress;
                      contractFunction := DePoolContract_Ф_onSuccessToRecoverStakeF Л_queryId msgSender ;
                      contractMessage  := {$ default with messageValue := value $} |} in 

    exec_state (DePoolProxyContract_Ф_onSuccessToRecoverStake Л_queryId) l =  
               {$ l With VMState_ι_messages := newMessage :: oldMessages $}.  
 Proof. 
  intros.  auto.
 Qed. 
 
 Lemma DePoolProxyContract_Ф_onSuccessToRecoverStake_eval : forall ( Л_queryId : XInteger64 ) (l: Ledger) , 
 	 eval_state (DePoolProxyContract_Ф_onSuccessToRecoverStake Л_queryId ) l = I . 
 Proof. 
   intros. auto. 
 Qed. 



(* DePoolProxyContract_Ф_getProxyInfo *) 


Lemma DePoolProxyContract_Ф_getProxyInfo_exec : forall (l: Ledger) , 
 	 exec_state ( ↓ DePoolProxyContract_Ф_getProxyInfo ) l = l .  
Proof. 
    intros. destruct l; compute; auto. 
Qed. 
 
Lemma DePoolProxyContract_Ф_getProxyInfo_eval : forall (l: Ledger) , 
                           (*  LedgerT ( XAddress # XInteger64 ) *)
let dePool := eval_state (↑10 ε DePoolProxyContract_ι_m_dePool) l in
let minBalance := DePoolLib_ι_MIN_PROXY_BALANCE in

    eval_state ( ↓ DePoolProxyContract_Ф_getProxyInfo ) l = (dePool, minBalance). 
Proof. 
  intros. destruct l ; compute ; auto. 
Qed. 
 
End DePoolProxyContractProofs.