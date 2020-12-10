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


Require Import depoolContract.Lib.CommonModelProofs.
Module CommonModelProofs := CommonModelProofs StateMonadSig.
Import CommonModelProofs. 
Require Import depoolContract.Lib.Tactics.
Require Import depoolContract.Lib.ErrorValueProofs.
Require Import depoolContract.Lib.CommonCommon.
Require Import depoolContract.Lib.CommonStateProofs.
(* Require Import depoolContract.Lib.tvmFunctionsProofs. *)

Import DePoolSpec.LedgerClass.SolidityNotations. 

Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope solidity_scope.
Require Import Lists.List.
Import ListNotations.
Local Open Scope list_scope.

Set Typeclasses Iterative Deepening.
Set Typeclasses Depth 100.
 
 
 
(* function getProxy(uint64 roundId) internal view inline returns (address) {
        return m_proxies[roundId % 2];
    } *) 
(* Definition ProxyBase_Ф_getProxy ( Л_roundId : XInteger64 ) : LedgerT XAddress := 
        ↑3 D2! ProxyBase_ι_m_proxies [[  $ Л_roundId !% $xInt2 ]].

*)

 Lemma ProxyBase_Ф_getProxy_exec : forall ( Л_roundId : XInteger64 ) (l: Ledger) , 
 	 exec_state (ProxyBase_Ф_getProxy Л_roundId ) l = l .  
 Proof. 
   intros. unfold ProxyBase_Ф_getProxy.
   compute. destructIf; auto; destruct l ; auto.
Qed. 

Lemma ProxyBase_Ф_getProxy_eval : forall ( Л_roundId : XInteger64 ) (l: Ledger) , 
    eval_state (ProxyBase_Ф_getProxy Л_roundId) l = 
       ( eval_state ( ↑3 ε ProxyBase_ι_m_proxies ) l ) [ xIntMod Л_roundId 2 ] .
Proof. 
   intros. 
   compute; destructIf; auto.
Qed. 
 
 (* function ProxyBase._recoverStake ( address proxy ,  uint64 requestId ,  address elector )  internal  { 
        IProxy ( proxy )  . recover_stake { value :  DePoolLib . ELECTOR_FEE  +  DePoolLib . PROXY_FEE }  ( requestId ,  elector )  ; 
     } *) 
(* Definition ProxyBase_Ф__recoverStake ( Л_proxy : XAddress )( Л_requestId : XInteger64 )( Л_elector : XAddress ) : LedgerT True :=
U0! Л_value := ↑ε9 DePoolLib_ι_ELECTOR_FEE !+ ↑ε9 DePoolLib_ι_PROXY_FEE ;
sendMessage {| contractAddress :=  Л_proxy;
               contractFunction := DePoolProxyContract_Ф_recover_stakeF Л_requestId Л_elector ;
			   contractMessage := {$ default with  messageValue := Л_value $} |}  . 
*)

 Lemma ProxyBase_Ф__recoverStake_exec : forall ( Л_proxy : XAddress ) ( Л_requestId : XInteger64 ) ( Л_elector : XAddress ) (l: Ledger) , 
    let oldMessages := eval_state (↑16 D2! VMState_ι_messages) l in
    let value := eval_state (↑9 D2! DePoolLib_ι_ELECTOR_FEE) l + 
                 eval_state (↑9 D2! DePoolLib_ι_PROXY_FEE) l in 
    let newMessage  := {| contractAddress :=  Л_proxy;
                          contractFunction := DePoolProxyContract_Ф_recover_stakeF Л_requestId Л_elector ;
                          contractMessage := {$ default with messageValue := value $} |} in 
    exec_state (ProxyBase_Ф__recoverStake Л_proxy Л_requestId Л_elector ) l = 
    {$ l With VMState_ι_messages := newMessage :: oldMessages $} .  
 Proof. 
   intros. auto. 
 Qed. 
 
Lemma ProxyBase_Ф__recoverStake_eval : forall ( Л_proxy : XAddress ) ( Л_requestId : XInteger64 ) ( Л_elector : XAddress ) (l: Ledger) , 
 	 eval_state (  ProxyBase_Ф__recoverStake Л_proxy Л_requestId Л_elector ) l = I . 
 Proof. 
   intros.  auto. 
 Qed. 
 
 (* function ProxyBase._sendElectionRequest ( 
        address proxy , 
        uint64 requestId , 
        uint64 validatorStake , 
        DePoolLib . Request req , 
        address elector
     ) 
        internal
     { 
                        IProxy ( proxy )  . process_new_stake { value :  validatorStake  +  DePoolLib . ELECTOR_FEE  +  DePoolLib . PROXY_FEE }  ( 
            requestId , 
            req . validatorKey , 
            req . stakeAt , 
            req . maxFactor , 
            req . adnlAddr , 
            req . signature , 
            elector
         )  ; 
     } *) 
     
(*  Definition ProxyBase_Ф__sendElectionRequest ( Л_proxy : XAddress )
                                            ( Л_requestId : XInteger64 )
                                            ( Л_validatorStake : XInteger64 )
                                            ( Л_req : DePoolLib_ι_Request ) 
                                            (Л_elector: XAddress) 
: LedgerT True := 
	U0! Л_value := $ Л_validatorStake !+ ↑ε9 DePoolLib_ι_ELECTOR_FEE !+ ↑ε9 DePoolLib_ι_PROXY_FEE  ;
	sendMessage {| contractAddress := Л_proxy;
	               contractFunction := DePoolProxyContract_Ф_process_new_stakeF  Л_requestId (Л_req ->> DePoolLib_ι_Request_ι_validatorKey) (Л_req ->> DePoolLib_ι_Request_ι_stakeAt) (Л_req ->> DePoolLib_ι_Request_ι_maxFactor) (Л_req ->> DePoolLib_ι_Request_ι_adnlAddr) (Л_req ->> DePoolLib_ι_Request_ι_signature) Л_elector;
				   contractMessage := {$ default with  messageValue := Л_value $} |}.  *)   

      
 Lemma ProxyBase_Ф__sendElectionRequest_exec : forall ( Л_proxy : XAddress ) 
                                                      ( Л_requestId : XInteger64 ) 
                                                      ( Л_validatorStake : XInteger64 ) 
                                                      ( Л_req : DePoolLib_ι_Request ) 
                                                      ( Л_elector : XAddress ) (l: Ledger) , 
 let oldMessages := eval_state (↑16 D2! VMState_ι_messages) l in
 let value := Л_validatorStake + 
              eval_state (↑9 D2! DePoolLib_ι_ELECTOR_FEE) l + 
              eval_state (↑9 D2! DePoolLib_ι_PROXY_FEE) l in 
 let newMessage  := {| contractAddress :=  Л_proxy;
                       contractFunction := DePoolProxyContract_Ф_process_new_stakeF  Л_requestId 
                                                                                     (Л_req ->> DePoolLib_ι_Request_ι_validatorKey) 
                                                                                     (Л_req ->> DePoolLib_ι_Request_ι_stakeAt) 
                                                                                     (Л_req ->> DePoolLib_ι_Request_ι_maxFactor) 
                                                                                     (Л_req ->> DePoolLib_ι_Request_ι_adnlAddr) 
                                                                                     (Л_req ->> DePoolLib_ι_Request_ι_signature) 
                                                                                     Л_elector ;
                       contractMessage := {$ default with messageValue := value $} |} in 
    exec_state (ProxyBase_Ф__sendElectionRequest Л_proxy Л_requestId Л_validatorStake Л_req Л_elector) l = 
    {$ l With VMState_ι_messages := newMessage :: oldMessages $} .  
 Proof. 
   intros. auto. 
 Qed. 
 
 Lemma ProxyBase_Ф__sendElectionRequest_eval : forall ( Л_proxy : XAddress ) 
                                                      ( Л_requestId : XInteger64 ) 
                                                      ( Л_validatorStake : XInteger64 ) 
                                                      ( Л_req : DePoolLib_ι_Request ) 
                                                      ( Л_elector : XAddress ) (l: Ledger) , 
 	 eval_state (ProxyBase_Ф__sendElectionRequest Л_proxy Л_requestId Л_validatorStake Л_req Л_elector ) l = I . 
 Proof. 
   intros. auto. 
 Qed. 
 
