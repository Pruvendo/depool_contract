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


Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope solidity_scope.
Require Import Lists.List.
Import ListNotations.
Local Open Scope list_scope.

 
 
 
 (* constructor() public {
        bool ok = false;
        for (uint8 i = 0; i < 2; ++i) {
            TvmBuilder b;
            b.store(address(msg.sender), i);
            uint256 publicKey = tvm.hash(b.toCell());
            ok = ok || tvm.pubkey() == publicKey;
        }
        require(ok, ERROR_IS_NOT_DEPOOL);
        m_dePool = msg.sender;
    }
*) 
    

Opaque Z.eqb.
Lemma DePoolProxyContract_Ф_Constructor5_exec : forall (l: Ledger) ,
                                      (*LedgerT ( XErrorValue True XInteger )*)
let b := default in 
              (* bool ok = false; *) 
let ok := false in
(*first time, i = 0*)
            (* TvmBuilder b;
               b.store(address(msg.sender), i); *)
let b' := builder_store b ( eval_state ( msg_sender ) l )  0 in 
            (* uint256 publicKey = tvm.hash(b.toCell()) *)
let publicKey := tvm_hash ( toCell b' ) in
            (* ok = ok || tvm.pubkey() == publicKey; *)
let ok' := ( ok || ( ( eval_state ( tvm_pubkey ) l ) =? publicKey ) )%bool in 

(*second time, i = 1*)
            (* TvmBuilder b;
               b.store(address(msg.sender), i); *)
let b'' := default in 
let b''' := builder_store b'' ( eval_state ( msg_sender ) l ) 1 in
            (* uint256 publicKey = tvm.hash(b.toCell()) *)
let publicKey' := tvm_hash ( toCell b''' )  in
            (* ok = ok || tvm.pubkey() == publicKey; *)
let ok'' := ( ok' || ( ( eval_state ( tvm_pubkey ) l ) =? publicKey' ) )%bool in
            (* require(ok, ERROR_IS_NOT_DEPOOL); *)
let req : bool := ( ok'' ) in

         exec_state ( ↓ DePoolProxyContract_Ф_constructor5 ) l =
                 if req then  
          {$ l With DePoolProxyContract_ι_m_dePool := ( eval_state ( msg_sender ) l ) $}
                 else l.
Proof.   
   intros. 
   destruct l. 
   destruct Ledger_ι_VMState.
   compute. destructIf; auto. 
Qed. 
 
Lemma DePoolProxyContract_Ф_Constructor5_eval : forall (l: Ledger) ,
                                      (*LedgerT ( XErrorValue True XInteger )*) 
let b := default in 
              (* bool ok = false; *) 
let ok := false in
(*first time, i = 0*)
            (* TvmBuilder b;
               b.store(address(msg.sender), i); *)
let b' := builder_store b ( eval_state ( msg_sender ) l )  0 in 
            (* uint256 publicKey = tvm.hash(b.toCell()) *)
let publicKey := tvm_hash ( toCell b' ) in
            (* ok = ok || tvm.pubkey() == publicKey; *)
let ok' := ( ok || ( ( eval_state ( tvm_pubkey ) l ) =? publicKey ) )%bool in 

(*second time, i = 1*)
            (* TvmBuilder b;
               b.store(address(msg.sender), i); *)
let b'' := default in 
let b''' := builder_store b'' ( eval_state ( msg_sender ) l ) 1 in
            (* uint256 publicKey = tvm.hash(b.toCell()) *)
let publicKey' := tvm_hash ( toCell b''' )  in
            (* ok = ok || tvm.pubkey() == publicKey; *)
let ok'' := ( ok' || ( ( eval_state ( tvm_pubkey ) l ) =? publicKey' ) )%bool in
            (* require(ok, ERROR_IS_NOT_DEPOOL); *)
let req : bool := ( ok'' ) in

    eval_state (↓ DePoolProxyContract_Ф_constructor5 ) l =  
    if req then Value I
           else Error (eval_state ( ↑10 ε DePoolProxyContract_ι_ERROR_IS_NOT_DEPOOL ) l ). 
Proof. 
  intros. 
  destruct l.  (* destruct Ledger_ι_VMState. *)
  compute. destructIf; auto. 
Qed. 
 
(* 
 (* function process_new_stake(
        uint64 queryId,
        uint256 validatorKey,
        uint32 stakeAt,
        uint32 maxFactor,
        uint256 adnlAddr,
        bytes signature,
        address elector
    ) external override  {
        require(msg.sender == m_dePool, ERROR_IS_NOT_DEPOOL);
        uint carry = msg.value - DePoolLib.PROXY_FEE;
        require(address(this).balance >= carry + DePoolLib.MIN_PROXY_BALANCE, ERROR_BAD_BALANCE);
        IElector(elector).process_new_stake{value: msg.value - DePoolLib.PROXY_FEE}(
            queryId, validatorKey, stakeAt, maxFactor, adnlAddr, signature
        );
    } *)
Definition DePoolProxyContract_Ф_process_new_stake  ( Л_queryId : XInteger64 )
                                                    ( Л_validatorKey : XInteger256 )
                                                    ( Л_stakeAt : XInteger32 )
                                                    ( Л_maxFactor : XInteger32 )
                                                    ( Л_adnlAddr : XInteger256 )
                                                    ( Л_signature : XList XInteger8 )
                                                    ( Л_elector : XAddress ) 
                                                : LedgerT ( XErrorValue True XInteger ) :=
 Require2 {{ msg_sender () ?== ↑ε10 DePoolProxyContract_ι_m_dePool , ↑ε10 DePoolProxyContract_ι_ERROR_IS_NOT_DEPOOL }} ; 
 U0! Л_carry :=  msg_value () !- ↑ε9 DePoolLib_ι_PROXY_FEE ;
 Require {{ tvm_balance () ?>=  $Л_carry !+ (↑ε9 DePoolLib_ι_MIN_PROXY_BALANCE) , ↑ε10 DePoolProxyContract_ι_ERROR_BAD_BALANCE }} ;
 sendMessage {| contractAddress := Л_elector;
				contractFunction := IElector_И_process_new_stakeF Л_queryId Л_validatorKey Л_stakeAt Л_maxFactor Л_adnlAddr  Л_signature;
				contractMessage := {$ default with  messageValue := Л_carry $} |}*) 
Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair.

Lemma DePoolProxyContract_Ф_process_new_stake_exec : forall ( Л_queryId : XInteger64 ) 
                                                             ( Л_validatorKey : XInteger256 ) 
                                                             ( Л_stakeAt : XInteger32 ) 
                                                             ( Л_maxFactor : XInteger32 ) 
                                                             ( Л_adnlAddr : XInteger256 ) 
                                                             ( Л_signature :  XList XInteger8 ) 
                                                             ( Л_elector : XAddress ) 
                                                             (l: Ledger) ,
    exec_state ( ↓ DePoolProxyContract_Ф_process_new_stake Л_queryId Л_validatorKey Л_stakeAt Л_maxFactor Л_adnlAddr Л_signature Л_elector ) l =

   let msgSender := eval_state msg_sender l in
   let dePoolAddress := eval_state (↑10 ε DePoolProxyContract_ι_m_dePool) l in
   let msgValue := eval_state msg_value l in
   let proxyFee := eval_state (↑9 ε DePoolLib_ι_PROXY_FEE) l in  
   let carry := msgValue - proxyFee in 
   let oldMessages := eval_state (↑16 ε VMState_ι_messages) l in 
   let newMessage :ContractsFunctionWithMessage  := {| contractAddress :=  Л_elector;
                         contractFunction := IElector_И_process_new_stakeF Л_queryId Л_validatorKey Л_stakeAt Л_maxFactor Л_adnlAddr  Л_signature ;
                         contractMessage :=  {| messageValue := carry;
                                               messageFlag := 0 ;
                                               messageBounce := false |} |} in 
    let balance := eval_state ( tvm_balance ) l in
    let minBalance := eval_state ( ↑9 ε DePoolLib_ι_MIN_PROXY_BALANCE ) l in
    let req2 : bool := balance >=? carry + minBalance in
    if ( msgSender =? dePoolAddress) then
      if req2 then 
          {$ l With VMState_ι_messages := newMessage :: oldMessages $} 
      else l 
    else l.  
 Proof. 
   intros. 
   destruct l. destruct Ledger_ι_VMState , Ledger_ι_DePoolProxyContract, Ledger_ι_DePoolLib.
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
    let error1 := eval_state (↑10 D2! DePoolProxyContract_ι_ERROR_IS_NOT_DEPOOL) l in
    let error2 := eval_state (↑10 D2! DePoolProxyContract_ι_ERROR_BAD_BALANCE) l in
   let msgValue := eval_state msg_value l in
   let proxyFee := eval_state (↑9 ε DePoolLib_ι_PROXY_FEE) l in 
   let carry := msgValue - proxyFee in 
    let balance := eval_state ( tvm_balance ) l in
    let minBalance := eval_state ( ↑9 ε DePoolLib_ι_MIN_PROXY_BALANCE ) l in
    let req2 : bool := balance >=? carry + minBalance in


    eval_state (DePoolProxyContract_Ф_process_new_stake Л_queryId Л_validatorKey Л_stakeAt Л_maxFactor Л_adnlAddr Л_signature Л_elector ) l = 
    if (msgSender =? dePoolAddress) 
    then if req2 then Value I
                 else Error error2
    else Error error1 . 
 Proof. 
  intros. 
   destruct l. destruct Ledger_ι_VMState , Ledger_ι_DePoolProxyContract, Ledger_ι_DePoolLib.
   compute. 
   repeat destructIf; auto. 
 Qed. 
 
 (* (* function onStakeAccept ( uint64 queryId , uint32 comment ) 
 	 	 public functionID ( 0xF374484C ) { IDePool ( m_dePool ) . onStakeAccept 
 	 	 { value : msg_value - DePoolLib . PROXY_FEE } ( queryId , comment 
       , msg_sender ) ; } *)
       
Definition DePoolProxyContract_Ф_onStakeAccept ( Л_queryId : XInteger64 )( Л_comment : XInteger32 ) : LedgerT True := 
	U0! Л_dePool := ↑ε10 DePoolProxyContract_ι_m_dePool ;
	U0! Л_value := msg_value () !- ↑ε9 DePoolLib_ι_PROXY_FEE ;
	U0! Л_sender := msg_sender ()  ;
    sendMessage {| contractAddress := Л_dePool;
				   contractFunction := DePoolContract_Ф_onStakeAcceptF Л_queryId Л_comment Л_sender ;
           contractMessage := {$ default with  messageValue := Л_value $} |} . 
           *) 
 Lemma DePoolProxyContract_Ф_onStakeAccept_exec : forall ( Л_queryId : XInteger64 ) ( Л_comment : XInteger32 ) (l: Ledger) , 
 let dePoolAddress := eval_state (↑10 D2! DePoolProxyContract_ι_m_dePool) l in
 let msgValue := eval_state msg_value l in
 let proxyFee := eval_state (↑9 D2! DePoolLib_ι_PROXY_FEE) l in
 let value := msgValue - proxyFee in
 let msgSender := eval_state msg_sender l in
 let oldMessages := eval_state (↑16 D2! VMState_ι_messages) l in
 let newMessage  := {| contractAddress  := dePoolAddress;
                       contractFunction := DePoolContract_Ф_onStakeAcceptF Л_queryId Л_comment msgSender ;
                       contractMessage  := {$ default with messageValue := value $} |} in 
                                                    
    exec_state (DePoolProxyContract_Ф_onStakeAccept Л_queryId Л_comment ) l =  
    {$ l With VMState_ι_messages := newMessage :: oldMessages $}.  
 Proof. 
   intros. auto. 
 Qed. 
 
 Lemma DePoolProxyContract_Ф_onStakeAccept_eval : forall ( Л_queryId : XInteger64 ) ( Л_comment : XInteger32 ) (l: Ledger) , 
 	 eval_state (DePoolProxyContract_Ф_onStakeAccept Л_queryId Л_comment ) l = I . 
 Proof. 
   intros. auto.  
 Qed. 
 
 (* (* function onStakeReject ( uint64 queryId , uint32 comment ) 
 	 	 public functionID ( 0xEE6F454C ) { IDePool ( m_dePool ) . onStakeReject 
 	 	 { value : msg_value - DePoolLib . PROXY_FEE } ( queryId , comment 
       , msg_sender ) ; } *)
       
Definition DePoolProxyContract_Ф_onStakeReject ( Л_queryId : XInteger64 )( Л_comment : XInteger32 ) : LedgerT True := 
	U0! Л_dePool := ↑ε10 DePoolProxyContract_ι_m_dePool ;
	U0! Л_value := msg_value () !- ↑ε9 DePoolLib_ι_PROXY_FEE ;
	U0! Л_sender := msg_sender ()  ;	
    sendMessage {| contractAddress := Л_dePool;
				   contractFunction := DePoolContract_Ф_onStakeRejectF Л_queryId Л_comment Л_sender ;
           contractMessage := {$ default with  messageValue := Л_value $} |} .
           *) 
 Lemma DePoolProxyContract_Ф_onStakeReject_exec : forall ( Л_queryId : XInteger64 ) ( Л_comment : XInteger32 ) (l: Ledger) , 
 let dePoolAddress := eval_state (↑10 D2! DePoolProxyContract_ι_m_dePool) l in
 let msgValue := eval_state msg_value l in
 let proxyFee := eval_state (↑9 D2! DePoolLib_ι_PROXY_FEE) l in
 let value := msgValue - proxyFee in
 let msgSender := eval_state msg_sender l in
 let oldMessages := eval_state (↑16 D2! VMState_ι_messages) l in
 let newMessage  := {| contractAddress  := dePoolAddress;
                       contractFunction := DePoolContract_Ф_onStakeRejectF Л_queryId Л_comment msgSender ;
                       contractMessage  := {$ default with messageValue := value $} |} in                                                  
      
    exec_state (  DePoolProxyContract_Ф_onStakeReject Л_queryId Л_comment ) l = 
    {$ l With VMState_ι_messages := newMessage :: oldMessages $}. 
 Proof. 
   intros. auto. 
 Qed. 
 
 Lemma DePoolProxyContract_Ф_onStakeReject_eval : forall ( Л_queryId : XInteger64 ) 
                                                         ( Л_comment : XInteger32 ) 
                                                         (l: Ledger) , 
 	 eval_state (  DePoolProxyContract_Ф_onStakeReject Л_queryId Л_comment ) l = I . 
 Proof. 
   intros. auto. 
 Qed. 
 
 (* function recover_stake(uint64 queryId, address elector) public override {
        require(msg.sender == m_dePool, ERROR_IS_NOT_DEPOOL);
        uint carry = msg.value - DePoolLib.PROXY_FEE;
        require(address(this).balance >= carry + DePoolLib.MIN_PROXY_BALANCE, ERROR_BAD_BALANCE);
        IElector(elector).recover_stake{value: msg.value - DePoolLib.PROXY_FEE}(queryId);
    } *)
(*
Definition DePoolProxyContract_Ф_recover_stake  ( Л_queryId : XInteger64 )
                                                ( Л_elector : XAddress ) 
                                           : LedgerT ( XErrorValue True XInteger ) := 
 Require2 {{ msg_sender () ?== ↑ε10 DePoolProxyContract_ι_m_dePool , ↑ε10 DePoolProxyContract_ι_ERROR_IS_NOT_DEPOOL }} ; 
 U0! Л_carry := msg_value () !- ↑ε9 DePoolLib_ι_PROXY_FEE ;
 Require {{ tvm_balance () ?>=  $Л_carry !+ (↑ε9 DePoolLib_ι_MIN_PROXY_BALANCE) , ↑ε10 DePoolProxyContract_ι_ERROR_BAD_BALANCE }} ;
 sendMessage {| contractAddress := Л_elector;
				contractFunction := IElector_И_recover_stakeF Л_queryId ;
				contractMessage := {$ default with  messageValue := Л_carry $} |} . *)
         
 Lemma DePoolProxyContract_Ф_recover_stake_exec : forall ( Л_queryId : XInteger64 ) ( Л_elector : XAddress ) (l: Ledger) ,
 let dePoolAddress := eval_state (↑10 ε DePoolProxyContract_ι_m_dePool) l in
 let msgValue := eval_state msg_value l in
 let proxyFee := eval_state (↑9 ε DePoolLib_ι_PROXY_FEE) l in
 let value := msgValue - proxyFee in
 let msgSender := eval_state msg_sender l in
 let oldMessages := eval_state (↑16 ε VMState_ι_messages) l in
 let newMessage  := {| contractAddress  := Л_elector;
                       contractFunction := IElector_И_recover_stakeF Л_queryId ;
                       contractMessage  := {$ default with messageValue := value $} |} in  
   let carry := msgValue - proxyFee in 
   let balance := eval_state ( tvm_balance ) l in
   let minBalance := eval_state ( ↑9 ε DePoolLib_ι_MIN_PROXY_BALANCE ) l in
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
 
 Lemma DePoolProxyContract_Ф_recover_stake_eval : forall ( Л_queryId : XInteger64 ) ( Л_elector : XAddress ) (l: Ledger) ,
 let msgSender := eval_state msg_sender l in
 let dePoolAddress := eval_state (↑10 D2! DePoolProxyContract_ι_m_dePool) l in
 let error1 := eval_state (↑10 ε DePoolProxyContract_ι_ERROR_IS_NOT_DEPOOL) l in 
 let error2 := eval_state (↑10 ε DePoolProxyContract_ι_ERROR_BAD_BALANCE) l in 
   let proxyFee := eval_state (↑9 ε DePoolLib_ι_PROXY_FEE) l in
   let msgValue := eval_state msg_value l in
   let carry := msgValue - proxyFee in 
   let balance := eval_state ( tvm_balance ) l in
   let minBalance := eval_state ( ↑9 ε DePoolLib_ι_MIN_PROXY_BALANCE ) l in
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
 
 (* (* function onSuccessToRecoverStake ( uint64 queryId ) public 
 	 	 functionID ( 0xF96F7324 ) { IDePool ( m_dePool ) . onSuccessToRecoverStake 
 	 	 { value : msg_value - DePoolLib . PROXY_FEE } ( queryId , msg_sender 
       ) ; } *)
       
Definition DePoolProxyContract_Ф_onSuccessToRecoverStake ( Л_queryId : XInteger64 ) : LedgerT True := 
	U0! Л_dePool := ↑ε10 DePoolProxyContract_ι_m_dePool ;
	U0! Л_value := msg_value () !- ↑ε9 DePoolLib_ι_PROXY_FEE ;
	U0! Л_sender := msg_sender ()  ;	
	sendMessage {| contractAddress := Л_dePool;
				   contractFunction := DePoolContract_Ф_onSuccessToRecoverStakeF Л_queryId Л_sender ;
           contractMessage := {$ default with  messageValue := Л_value $} |} .
            *) 

 Lemma DePoolProxyContract_Ф_onSuccessToRecoverStake_exec : forall ( Л_queryId : XInteger64 ) (l: Ledger) , 
 let dePoolAddress := eval_state (↑10 D2! DePoolProxyContract_ι_m_dePool) l in
 let msgValue := eval_state msg_value l in
 let proxyFee := eval_state (↑9 D2! DePoolLib_ι_PROXY_FEE) l in
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

 (*   
      function getProxyInfo() public view returns (address depool, uint64 minBalance) {
        depool = m_dePool;
        minBalance = DePoolLib.MIN_PROXY_BALANCE;
    }
Definition DePoolProxyContract_Ф_getProxyInfo : LedgerT ( XAddress # XInteger64 ) := 
 U0! Л_depool := ↑ε10 DePoolProxyContract_ι_m_dePool ; 
 U0! Л_minBalance := ↑ε9 DePoolLib_ι_MIN_PROXY_BALANCE ; 
	 return# ($ Л_depool, $ Л_minBalance) . 
 *) 

 Lemma DePoolProxyContract_Ф_getProxyInfo_exec : forall (l: Ledger) , 
 	 exec_state ( ↓ DePoolProxyContract_Ф_getProxyInfo ) l = l .  
 Proof. 
    intros. destruct l; compute; auto. 
 Qed. 
 
 Lemma DePoolProxyContract_Ф_getProxyInfo_eval : forall (l: Ledger) , 
                           (*  LedgerT ( XAddress # XInteger64 ) *)
    let dePool := eval_state (↑10 ε DePoolProxyContract_ι_m_dePool) l in
    let minBalance := eval_state (↑9 ε DePoolLib_ι_MIN_PROXY_BALANCE) l in
    eval_state ( ↓ DePoolProxyContract_Ф_getProxyInfo ) l = (dePool, minBalance). 
 Proof. 
   intros. destruct l ; compute ; auto. 
 Qed. 
 
