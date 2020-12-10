Require Import Coq.Program.Basics.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.
Require Import Coq.Unicode.Utf8.


Local Open Scope program_scope. 

Require Import FinProof.Common.
Require Import FinProof.ProgrammingWith.
Require Import FinProof.StateMonad2.

Local Open Scope record.


Require Import depoolContract.DePoolClass. 
Require Import depoolContract.SolidityNotations.
Require Import depoolContract.ProofEnvironment. 
Require Import depoolContract.DePoolSpec.

Module DePoolFuncs (xt: XTypesSig) (sm: StateMonadSig).

Module DePoolSpec := DePoolSpec xt sm.
Import DePoolSpec.
Import LedgerClass.
Import SolidityNotations.

Import xt. Import sm.

Set Typeclasses Iterative Deepening.
(*Set Typeclasses Depth 1.
Set Typeclasses Strict Resolution. *)
(* Set Typeclasses Debug.  *)
(* Set Typeclasses Unique Instances. 
Unset Typeclasses Unique Solutions. *)

(* Existing Instance monadStateT.
Existing Instance monadStateStateT. *)

Local Open Scope solidity_scope.
Local Open Scope string_scope.


Definition setEventList l r := {$ r with VMState_ι_events := l $}.
 
Definition sendLedgerEvent (e: LedgerEvent) : LedgerT True := 
	↑16 (modify (fun r => setEventList (xListCons e (VMState_ι_events r)) r) >> return! I ).
Notation "->emit e" := (e >>= sendLedgerEvent) (at level  30).

Definition setMessageList l r := {$ r with VMState_ι_messages := l $}.

Definition sendMessage (m: ContractsFunctionWithMessage) : LedgerT True := 
    ↑16 (modify (fun r => setMessageList (xListCons m (VMState_ι_messages r)) r) >> return! I ).	  

Notation "'->sendMessage' m" := (do m' ← m; sendMessage m')	(at level 30, right associativity, m at level 50).							  
    	  

Definition eventIn (e: LedgerEvent) : LedgerT XBool := ↑ε16 (fun r => xListIn eventEqb e (VMState_ι_events r)).

Definition getLastEvent : LedgerT (XMaybe LedgerEvent) := ↑ε16 (fun r => xListHead (VMState_ι_events r)).

Definition tvm_pubkey : LedgerT XInteger256 := ↑ε16 VMState_ι_pubkey.
Definition tvm_now : LedgerT XInteger64 := ↑ε16 VMState_ι_now.


Definition setTransactionList l r := {$ r with VMState_ι_transactions := l $}.
Definition tvm_transfer (dest: XAddress) (value: XInteger256) 
						(bounce: XBool) (flags: XInteger8) (payload: TvmCell) : LedgerT True := 
    ↑16 (modify (fun r => setTransactionList (xListCons (TransactionC dest value bounce flags payload) (VMState_ι_transactions r)) r) >> return! I ).
    
Notation " a '->transfer' '(!' b , c , d '!)' " := (do a' ← a ; do b' ← b ; do c' ← c ; do d' ← d ; 
    ( tvm_transfer a' b' c' d' default ) ) (at level 62, left associativity): solidity_scope.  
Notation " a '->transfer' '(!' b , c , d , e '!)' " := (do a' ← a ; do b' ← b ; do c' ← c ; do d' ← d ; do e' ← e ;
	( tvm_transfer a' b' c' d' e' ) ) (at level 62, left associativity): solidity_scope.	      

Definition msg_pubkey : LedgerT XInteger256 := ↑ε16 VMState_ι_msg_pubkey.
Definition msg_sender : LedgerT XAddress := ↑ε16 VMState_ι_msg_sender.	
Definition msg_value : LedgerT XInteger32 := ↑ε16 VMState_ι_msg_value.
Definition msg_data : LedgerT TvmCell := ↑ε16 VMState_ι_msg_data. 

(*TODO:*)
Definition tvm_accept : LedgerT True := return! I.
Definition tvm_transLT : LedgerT XInteger64 := ↑ε16 VMState_ι_ltime.


Definition tvm_setcode (newcode : TvmCell) : LedgerT True := 
	↑16 (U1! VMState_ι_code := $ newcode).

(*TODO:*)	
Definition tvm_setCurrentCode (newcode : TvmCell) : LedgerT True := return! I.

(* Definition tvm_tree_cell_size (slice: TvmSlice) : LedgerT (XInteger # XInteger) := return! [(xInt0, xInt0)].
Definition tvm_ctos (cell : TvmCell): LedgerT TvmSlice := return! xStrNull. 
Definition tvm_reset_storage: LedgerT True :=  <! Ledger_ι_DePoolContract <- default  !> >> return! I. *)

(*TODO*)
(* Definition tvm_hash (cellTree: TvmCell) : LedgerT XInteger256 := return! xInt0.  *)
Parameter tvm_hash : TvmCell -> XInteger256.

Definition tvm_rawConfigParam (x:XInteger) : LedgerT (TvmCell # XBool) := return! [(xStrNull, xBoolTrue)]. 
Definition tvm_configParam (x: XInteger): LedgerT (XInteger32 # XInteger32 # XInteger32 # XInteger32 # XBool) := 
	                       return! [(xInt0, xInt0, xInt0, xInt0, xBoolTrue)]. 

(*our stub: doesn't exists in TVM*)
(*actual call is uint128(address(this).balance);*)
(*TODO*)
Definition tvm_balance : LedgerT XInteger128 := ↑ε16 VMState_ι_balance. 
Definition tvm_address : LedgerT XAddress := ↑ε16 VMState_ι_address.

(*TODO*) 
Definition tvm_commit: LedgerT True :=
do l ← get;
put {$l with Ledger_ι_VMState := {$Ledger_ι_VMState l with VMState_ι_savedDePoolContracts := projEmbed l $}$};
void!.

Definition tvm_revert {X E} (e: E): LedgerT (XErrorValue X E) :=
do l ← get;
put (injEmbed (VMState_ι_savedDePoolContracts (Ledger_ι_VMState l)) l  ) >>
return! (xError e).

Definition callDePool {X E} (m: LedgerT (XErrorValue X E)) : LedgerT (XErrorValue X E) :=
tvm_commit >> 
m >>= fun ea => xErrorMapDefaultF (fun a => return! (xValue a)) ea tvm_revert.

(*********************************************************)



Definition intMin (a b: XInteger) := xBoolIfElse (xIntLeb a b) a b.
Notation "'math->min2' '(!' a , b '!)'" := (do a' ← a; do b' ← b; return! (intMin a' b')) (at level 30, right associativity).
Notation "'math->min3' '(!' a , b , c '!)'" := (do a' ← a; do b' ← b; do c' ← c; return! (intMin (intMin a' b') c')) (at level 30, right associativity).

Definition intMulDiv (a b c: XInteger) := xIntDiv (xIntMult a b) c.
Notation "'math->muldiv' '(!' a , b , c '!)'" := (do a' ← a; do b' ← b; do c' ← c; return! (intMulDiv a' b' c')) (at level 30, right associativity).

Definition intMax (a b: XInteger) := xBoolIfElse (xIntLeb a b) b a.
Notation "'math->max' '(!' a , b '!)'" := (do a' ← a; do b' ← b; return! (intMax a' b')) (at level 30, right associativity).


(*TODO*)
Parameter address_makeAddrStd : XInteger -> XInteger256 -> XAddress.
Notation " 'address->makeAddrStd' '(!' b ',' c '!)' " := (
												   do b' ← b; 
												   do c' ← c; 
												   return! (address_makeAddrStd b' c') )( at level 10, left associativity ): solidity_scope.		   

(*TODO*)
Parameter decode_uint8_uint32_uint32 : TvmSlice -> XInteger8 # XInteger32 # XInteger32 # TvmSlice.
Notation " 'U0!' d ':=' a '->decode(uint8,uint32,uint32)' ; t " := ( let dec := decode_uint8_uint32_uint32 a in let d := xProdFst dec in let a := xProdSnd dec in t)( at level 33, left associativity, t at level 50 ): solidity_scope.

Parameter toSlice: TvmCell -> TvmSlice.
Notation " a '->toSlice()' " := ( do a' ← a ; return! (toSlice a') )( at level 10, left associativity ): solidity_scope.

Parameter tvm_loadTons : TvmSlice -> TvmSlice.
(*TODO*)
Notation " a '->loadTons()' ; t " := ( let a := tvm_loadTons a in t )( at level 10, left associativity, t at level 50): solidity_scope.


Parameter decode_uint32 : TvmSlice -> XInteger32 # TvmSlice.
Notation " 'U0!' d ':=' a '->decode(uint32)' ; t " := ( let dec := decode_uint32 a in let d := xProdFst dec in let a := xProdSnd dec in t )( at level 33, left associativity , t at level 50): solidity_scope.

Parameter decode_uint256 : TvmSlice -> XInteger256 # TvmSlice.
Notation " 'U0!' d ':=' a '->decode(uint256)' ; t " := ( let dec := decode_uint256 a in let d := xProdFst dec in let a := xProdSnd dec in t )( at level 33, left associativity , t at level 50): solidity_scope.

Parameter isStdAddrWithoutAnyCast: XAddress -> XBool.
Notation " a '->isStdAddrWithoutAnyCast()' " := ( do a' ← a ; $ (isStdAddrWithoutAnyCast a') ) (at level 20, right associativity).

Parameter isStdZero :  XAddress -> XBool.
Notation " a '->isStdZero()' " := ( do a' ← a ; $ (isStdZero a') ) (at level 20, right associativity). 



Notation " f '()' " := ( ↓ f ) (at level 22, left associativity, only parsing): solidity_scope.
Notation " f '(!' a '!)' " := ( do a' ← a ; ↓ f a' ) (at level 22, left associativity, only parsing): solidity_scope.
Notation " f '(!' a ',' b '!)' " := (do a' ← a ; do b' ← b ; ↓ f a' b' ) (at level 22, left associativity, only parsing): solidity_scope.
Notation " f '(!' a ',' b ',' c '!)' " := (do a' ← a ; do b' ← b ; do c' ← c ; ↓ f a' b' c' ) (at level 22, left associativity, only parsing): solidity_scope.
Notation " f '(!' a ',' b ',' c ',' d '!)' " := (do a' ← a ; do b' ← b ; do c' ← c ; do d' ← d ; ↓ f a' b' c' d' ) (at level 22, left associativity, only parsing): solidity_scope.
Notation " f '(!' a ',' b ',' c ',' d ',' e '!)' " := (do a' ← a ; do b' ← b ; do c' ← c ; do d' ← d ; do e' ← e ; ↓ f a' b' c' d' e'  ) (at level 22, left associativity, only parsing): solidity_scope.
Notation " f '(!' a ',' b ',' c ',' d ',' e ',' i '!)' " := (do a' ← a ; do b' ← b ; do c' ← c ; do d' ← d ; do e' ← e ; do i' ← i ; ↓ f a' b' c' d' e' i'  ) (at level 22, left associativity, only parsing): solidity_scope.
Notation " f '(!' a ',' b ',' c ',' d ',' e ',' i ',' j '!)' " := (do a' ← a ; do b' ← b ; do c' ← c ; do d' ← d ; do e' ← e ; do i' ← i ; do j' ← j ; ↓ f a' b' c' d' e' i' j'  ) (at level 22, left associativity, only parsing): solidity_scope.




Set Typeclasses Iterative Deepening.
Set Typeclasses Depth 10.


(* constructor(address validatorWallet) internal {
        m_validatorWallet = validatorWallet;
    } *)
Definition ValidatorBase_Ф_Constructor2 ( Л_validatorWallet : XAddress ) : LedgerT True := 
 ↑2 U1! ValidatorBase_ι_m_validatorWallet := $ Л_validatorWallet.


(* 
function getProxy(uint64 roundId) internal view inline returns (address) {
        return m_proxies[roundId % 2];
    }
 *)
		   
Definition ProxyBase_Ф_getProxy ( Л_roundId : XInteger64 ) : LedgerT XAddress := 
↑3 D2! ProxyBase_ι_m_proxies [[  $ Л_roundId !% $xInt2 ]].


(* 
function _recoverStake(address proxy, uint64 requestId, address elector) internal {
        IProxy(proxy).recover_stake{value: DePoolLib.ELECTOR_FEE + DePoolLib.PROXY_FEE}(requestId, elector);
    }
 *)
Definition ProxyBase_Ф__recoverStake ( Л_proxy : XAddress )( Л_requestId : XInteger64 )( Л_elector : XAddress ) : LedgerT True :=
U0! Л_value := ↑ε9 DePoolLib_ι_ELECTOR_FEE !+ ↑ε9 DePoolLib_ι_PROXY_FEE ;
sendMessage {| contractAddress :=  Л_proxy;
               contractFunction := DePoolProxyContract_Ф_recover_stakeF Л_requestId Л_elector ;
			   contractMessage := {$ default with  messageValue := Л_value $} |}  .

(* 
function _sendElectionRequest(
        address proxy,
        uint64 requestId,
        uint64 validatorStake,
        DePoolLib.Request req,
        address elector
    )
        internal
    {
        // send stake + 1 ton  + 2 * 0.01 ton (proxy fee),
        // 1 ton will be used by Elector to return confirmation back to DePool contract.
        IProxy(proxy).process_new_stake{value: validatorStake + DePoolLib.ELECTOR_FEE + DePoolLib.PROXY_FEE}(
            requestId,
            req.validatorKey,
            req.stakeAt,
            req.maxFactor,
            req.adnlAddr,
            req.signature,
            elector
        );
    }
 *)
		   
Definition ProxyBase_Ф__sendElectionRequest ( Л_proxy : XAddress )
                                            ( Л_requestId : XInteger64 )
                                            ( Л_validatorStake : XInteger64 )
                                            ( Л_req : DePoolLib_ι_Request ) 
                                            (Л_elector: XAddress) 
                                                                  : LedgerT True := 
	U0! Л_value := $ Л_validatorStake !+ ↑ε9 DePoolLib_ι_ELECTOR_FEE !+ ↑ε9 DePoolLib_ι_PROXY_FEE  ;
	sendMessage {| contractAddress := Л_proxy;
	               contractFunction := DePoolProxyContract_Ф_process_new_stakeF  Л_requestId (Л_req ->> DePoolLib_ι_Request_ι_validatorKey) (Л_req ->> DePoolLib_ι_Request_ι_stakeAt) (Л_req ->> DePoolLib_ι_Request_ι_maxFactor) (Л_req ->> DePoolLib_ι_Request_ι_adnlAddr) (Л_req ->> DePoolLib_ι_Request_ι_signature) Л_elector;
				   contractMessage := {$ default with  messageValue := Л_value $} |}.


              
(*   
function getCurValidatorData() virtual internal returns (uint256 hash, uint32 utime_since, uint32 utime_until) {
        (TvmCell cell, bool ok) = tvm.rawConfigParam(34);
        require(ok, InternalErrors.ERROR508);
        hash = tvm.hash(cell);
        TvmSlice s = cell.toSlice();
        (, utime_since, utime_until) = s.decode(uint8, uint32, uint32);
    }
 *)   


Definition ConfigParamsBase_Ф_getCurValidatorData :  LedgerT ( XErrorValue ( XInteger256 # XInteger32 # XInteger32 ) XInteger ) :=  
	U0! {( Л_cell , Л_ok )} := tvm_rawConfigParam (! $ xInt34 !) ;
 	Require {{ $ Л_ok , ↑ε8 InternalErrors_ι_ERROR508 }} ; 
 	U0! Л_hash := tvm_hash (!! $ Л_cell !!) ; 
    U0! Л_s := ($ Л_cell) ->toSlice() ; 
    U0! Л_decoded := Л_s ->decode(uint8,uint32,uint32) ;
	U0! {( _ , Л_utime_since , Л_utime_until )} := $ Л_decoded ;  (* (uint8 , uint32 , uint32) *)
	return# ( $Л_hash, $Л_utime_since , $Л_utime_until ). 
 

(* 
function getPrevValidatorHash() virtual internal returns (uint) {
        (TvmCell cell, bool ok) = tvm.rawConfigParam(32);
        require(ok, InternalErrors.ERROR507);
        return tvm.hash(cell);
    }
 *) 
 	 	
Definition ConfigParamsBase_Ф_getPrevValidatorHash : LedgerT ( XErrorValue XInteger XInteger ) := 
	U0! {( Л_cell , Л_ok )} := tvm_rawConfigParam (! $ xInt32 !) ;
 	Require {{ $ Л_ok , ↑ε8 InternalErrors_ι_ERROR507 }} ; 
 	 tvm_hash (!! $ Л_cell !!). 
 


(*
function roundTimeParams() virtual internal returns (
        uint32 validatorsElectedFor,
        uint32 electionsStartBefore,
        uint32 electionsEndBefore,
        uint32 stakeHeldFor
    ) {
        bool ok;
        (validatorsElectedFor, electionsStartBefore, electionsEndBefore, stakeHeldFor, ok) = tvm.configParam(15);
        require(ok, InternalErrors.ERROR509);
    }

*)
Definition ConfigParamsBase_Ф_roundTimeParams  : LedgerT ( XErrorValue ( XInteger32 # XInteger32 # XInteger32 # XInteger32 ) XInteger )  := 
 U0! {( Л_validatorsElectedFor , Л_electionsStartBefore , Л_electionsEndBefore , Л_stakeHeldFor , Л_ok )} := tvm_configParam (! $ xInt15 !) ; 
 Require {{ $ Л_ok , ↑ε8 InternalErrors_ι_ERROR509 }} ; 
 return# ($Л_validatorsElectedFor, $Л_electionsStartBefore, $Л_electionsEndBefore, $Л_stakeHeldFor ). 
 


(* 
function getMaxStakeFactor() virtual pure internal returns (uint32) {
        (TvmCell cell, bool ok) = tvm.rawConfigParam(17);
        require(ok, InternalErrors.ERROR516);
        TvmSlice s = cell.toSlice();
        s.loadTons();
        s.loadTons();
        s.loadTons();
        return s.decode(uint32);
    }
 *)
Definition ConfigParamsBase_Ф_getMaxStakeFactor : LedgerT ( XErrorValue XInteger32 XInteger ) := 
	U0! {( Л_cell , Л_ok )} := tvm_rawConfigParam (! $ xInt17 !) ; 
 	Require {{ $ Л_ok , ↑ε8 InternalErrors_ι_ERROR516 }} ; 
 	U0! Л_s := ($ Л_cell) ->toSlice() ; 
 	Л_s ->loadTons() ;
 	Л_s ->loadTons() ; 
    Л_s ->loadTons() ;
    U0! Л_decoded := Л_s ->decode(uint32) ;
	   $ Л_decoded. 
	  
(* 
function getElector() virtual pure internal returns (address) {
        (TvmCell cell, bool ok) = tvm.rawConfigParam(1);
        require(ok, InternalErrors.ERROR517);
        TvmSlice s = cell.toSlice();
        uint256 value = s.decode(uint256);
        return address.makeAddrStd(-1, value);
    }
*)
Definition ConfigParamsBase_Ф_getElector : LedgerT ( XErrorValue XAddress XInteger ) := 
 U0! {( Л_cell , Л_ok )} := tvm_rawConfigParam (! $ xInt1 !) ; 
 Require {{ $ Л_ok , ↑ε8 InternalErrors_ι_ERROR517 }} ; 
 U0! Л_s := ($ Л_cell) ->toSlice() ; 
 U0! Л_value := Л_s ->decode(uint256) ; 
  address->makeAddrStd (! $xInt0 !- $ xInt1 , $ Л_value !) .
	


(* 
function _setOrDeleteParticipant(address addr, DePoolLib.Participant participant) internal {
        if (participant.roundQty == 0)
            delete m_participants[addr];
        else
            m_participants[addr] = participant;
    }
 *)
Definition ParticipantBase_Ф__setOrDeleteParticipant ( Л_addr : XAddress )
                                   ( Л_participant : DePoolLib_ι_Participant ) 
                                   : LedgerT True := 
 If ( $ (Л_participant ->> DePoolLib_ι_Participant_ι_roundQty) ?== $xInt0 ) then 
 {
	↑5 U1! delete ParticipantBase_ι_m_participants  [[ $ Л_addr ]] 
 } else 
 {
	↑5 U1! ParticipantBase_ι_m_participants [[ $ Л_addr ]] := $ Л_participant
 }.

(*  function getOrCreateParticipant(address addr) internal view returns (DePoolLib.Participant) {
    optional(DePoolLib.Participant) optParticipant = m_participants.fetch(addr);
    if (optParticipant.hasValue()) {
        return optParticipant.get();
    }
    DePoolLib.Participant newParticipant = DePoolLib.Participant({
        roundQty: 0,
        reward: 0,
        haveVesting: false,
        haveLock: false,
        reinvest: true,
        withdrawValue: 0
    });
    return newParticipant;
} *)

Definition ParticipantBase_Ф_getOrCreateParticipant' ( Л_addr : XAddress ) : LedgerT (XValueValue DePoolLib_ι_Participant)  :=
    U0! Л_optParticipant := ↑5 D1! (D2! ParticipantBase_ι_m_participants) ->fetch $ Л_addr ; 
    If! (($ Л_optParticipant) ->hasValue ) then {
        ($Л_optParticipant) ->get >>= fun x => return! (xError x)
    }; 
    U0! Л_newParticipant := {||
        DePoolLib_ι_Participant_ι_roundQty := $ xInt0 ,
        DePoolLib_ι_Participant_ι_reward := $ xInt0 ,
        DePoolLib_ι_Participant_ι_haveVesting := $ xBoolFalse ,
        DePoolLib_ι_Participant_ι_haveLock := $ xBoolFalse ,
        DePoolLib_ι_Participant_ι_reinvest := $ xBoolTrue ,
        DePoolLib_ι_Participant_ι_withdrawValue := $ xInt0 
    ||} ;
        return! Л_newParticipant.

Definition fromValueValue {V} (x: XValueValue V) : V := xErrorMapDefaultF Datatypes.id x Datatypes.id.


Definition ParticipantBase_Ф_getOrCreateParticipant ( Л_addr : XAddress ) : LedgerT  DePoolLib_ι_Participant :=
  do r ← ParticipantBase_Ф_getOrCreateParticipant' Л_addr;
  return! (fromValueValue r).



(* 
constructor(address pool) public {
require(msg.pubkey() == tvm.pubkey(), 101);
        tvm.accept();
        m_dePoolPool = pool;
    }
*)
Definition DePoolHelper_Ф_Constructor4 ( Л_pool : XAddress ) : LedgerT ( XErrorValue True XInteger ) := 
 Require {{ msg_pubkey () ?== tvm_pubkey () , $ xInt101 }} ; 
tvm_accept () >>
 ↑6 U1! DePoolHelper_ι_m_dePoolPool := $ Л_pool . 


(* 
function updateDePoolPoolAddress(address addr) public {
require(msg.pubkey() == tvm.pubkey(), 101);
        tvm.accept();
        m_poolHistory.push(m_dePoolPool);
        m_dePoolPool = addr;
    }
 *)
Definition DePoolHelper_Ф_updateDePoolPoolAddress ( Л_addr : XAddress ) : LedgerT ( XErrorValue True XInteger ) := 
 Require {{ msg_pubkey () ?== tvm_pubkey () , $ xInt101 }} ; 
tvm_accept () >>
 ↑6 DePoolHelper_ι_m_poolHistory ->push ( ε DePoolHelper_ι_m_dePoolPool ) >>
 ↑6 U1! DePoolHelper_ι_m_dePoolPool := $ Л_addr. 

  
 
(* 
function _settimer(address timer, uint period) private inline {
	    uint opex = period * _timerRate + _fwdFee * 8 + _epsilon;
        ITimer(timer).setTimer.value(opex)(period);
    }
 *)
Definition DePoolHelper_Ф__settimer ( Л_timer : XAddress )( Л_period : XInteger ) : LedgerT True := 
 U0! Л_opex := $ Л_period !* ↑ε6 DePoolHelper_ι__timerRate !+ ↑ε6 DePoolHelper_ι__fwdFee !* $ xInt8 !+ ↑ε6 DePoolHelper_ι__epsilon ; 
 sendMessage {| contractAddress := Л_timer;
 contractFunction := ITimer_И_setTimerF Л_period ;
 contractMessage := {$ default with  messageValue := Л_opex $} |} . 

(* 
function initTimer(address timer, uint period) public 
{
require(msg.pubkey() == tvm.pubkey(), 101);
        tvm.accept();
        m_timer = timer;
        m_timeout = period;
        _settimer(timer, period);
    }
 *)
Definition DePoolHelper_Ф_initTimer ( Л_timer : XAddress )
                                    ( Л_period : XInteger ) 
                             : LedgerT ( XErrorValue True XInteger ) := 
 Require {{ msg_pubkey () ?== tvm_pubkey () , $ xInt101 }} ; 
tvm_accept () >>
 ( ↑6 U1! DePoolHelper_ι_m_timer := $ Л_timer ) >> 
 ( ↑6 U1! DePoolHelper_ι_m_timeout := $ Л_period ) >> 
 	DePoolHelper_Ф__settimer (! $ Л_timer , $ Л_period !) .

(* 
function onTimer() public {
        address timer = m_timer;
        uint period = m_timeout;
        if (msg.sender == timer && period > 0) {
            IDePool(m_dePoolPool).ticktock.value(TICKTOCK_FEE)();
            _settimer(timer, period);
        }
    }
*)
Definition DePoolHelper_Ф_onTimer : LedgerT True := 
 U0! Л_timer := ↑ε6 DePoolHelper_ι_m_timer ; 
 U0! Л_period := ↑ε6 DePoolHelper_ι_m_timeout ; 
 U0! Л_dePoolPool := ↑ε6 DePoolHelper_ι_m_dePoolPool ;
 U0! Л_TICKTOCK_FEE := ↑ε6 DePoolHelper_ι_TICKTOCK_FEE ;
 	 
 If ( ( msg_sender () ?== $ Л_timer) !& ($ Л_period ?> $ xInt0) ) then { 
		sendMessage {| contractAddress := Л_dePoolPool;
					   contractFunction := DePoolContract_Ф_ticktockF ;
					   contractMessage := {$ default with messageValue := Л_TICKTOCK_FEE $} |} >>
		DePoolHelper_Ф__settimer (! $ Л_timer , $ Л_period !)  
	}.


(* 
function sendTicktock() public {
require(msg.pubkey() == tvm.pubkey(), 101);
        tvm.accept();
        IDePool(m_dePoolPool).ticktock.value(TICKTOCK_FEE)();
    }
*)
Definition DePoolHelper_Ф_sendTicktock : LedgerT ( XErrorValue True XInteger ) := 
 Require {{  msg_pubkey () ?== tvm_pubkey () , $ xInt101 }} ; 
tvm_accept () >>
 U0! Л_dePoolPool := ↑ε6 DePoolHelper_ι_m_dePoolPool ;
 U0! Л_TICKTOCK_FEE := ↑ε6 DePoolHelper_ι_TICKTOCK_FEE ;
 sendMessage {| contractAddress := Л_dePoolPool;
				contractFunction := DePoolContract_Ф_ticktockF ;
				contractMessage := {$ default with  messageValue := Л_TICKTOCK_FEE $} |}.
	 
 
(* 
function getDePoolPoolAddress() public view returns (address addr) {
        addr = m_dePoolPool;
    }
 *)
Definition DePoolHelper_Ф_getDePoolPoolAddress : LedgerT XAddress := 
 ↑ε6 DePoolHelper_ι_m_dePoolPool . 
 
(* 
function getHistory() public view returns (address[] list) {
        list = m_poolHistory;
    }
 *)
Definition DePoolHelper_Ф_getHistory : LedgerT (XHMap XInteger XAddress) := 
 ↑ε6 DePoolHelper_ι_m_poolHistory.


(* 
function onCodeUpgrade() private {}

 *)
Definition DePoolHelper_Ф_onCodeUpgrade : LedgerT True  :=  return! I .

(* 
function upgrade(TvmCell newcode) public require(msg.pubkey() == tvm.pubkey(), 101);
        tvm.accept(); 
        tvm.commit();
        tvm.setcode(newcode);
        tvm.setCurrentCode(newcode);
        onCodeUpgrade();
    }
 *)
Definition DePoolHelper_Ф_upgrade ( Л_newcode : TvmCell ) : LedgerT ( XErrorValue True XInteger ) := 
 Require {{ msg_pubkey () ?== tvm_pubkey () , $ xInt101 }} ; 
tvm_accept () >>
 	 tvm_commit () >> 
 	 tvm_setcode (! $ Л_newcode !) >> 
 	 tvm_setCurrentCode (! $ Л_newcode !) >> 
 	 DePoolHelper_Ф_onCodeUpgrade ()  . 
 
(* 
constructor() public {
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
(* Definition  builder_store  (b : TvmBuilder)  (a x: XInteger)  := b.  *)  
Parameter builder_store : TvmBuilder -> XInteger -> XInteger -> TvmBuilder.
Notation "U0! b '->store' x i ; t" := (do x'←x; do i'←i; let b := builder_store b x' i' in t) (at level 33, t at level 50).

(* Definition toCell (b : TvmBuilder) : TvmCell := xStrNull. *)
Parameter toCell : TvmBuilder -> TvmCell.
Notation "b '->toCell'" := (do b'←b; $ (toCell b')) (at level 62).


Definition DePoolProxyContract_Ф_constructor5 : LedgerT ( XErrorValue True XInteger ) :=
  (↑17 U1! LocalState_ι_constructor5_Л_ok := $ xBoolFalse) >>
  ( ForIndexed (xListCons xInt0 (xListCons xInt1 xListNil)) do (fun (i: XInteger) => 
    U0! Л_b := $ default ;
    U0! Л_b ->store msg_sender() $i;
    U0! Л_publicKey := tvm_hash (!! $Л_b ->toCell !!);
    (↑↑17 U2! LocalState_ι_constructor5_Л_ok := ((↑17 D2! LocalState_ι_constructor5_Л_ok) !| (tvm_pubkey () ?== $Л_publicKey)) )
  )) >> 
  Require {{ ↑17 D2! LocalState_ι_constructor5_Л_ok , ↑ε10 DePoolProxyContract_ι_ERROR_IS_NOT_DEPOOL }} ;
  (↑↑10 U2! DePoolProxyContract_ι_m_dePool := msg_sender ()).
 

(* 
function process_new_stake(
        uint64 queryId,
        uint256 validatorKey,
        uint32 stakeAt,
        uint32 maxFactor,
        uint256 adnlAddr,
        bytes signature,
        address elector
    ) external override { 
         require(msg.sender == m_dePool, ERROR_IS_NOT_DEPOOL);

        // this check is needed for correct work of proxy
        uint carry = msg.value - DePoolLib.PROXY_FEE;
        require(address(this).balance >= carry + DePoolLib.MIN_PROXY_BALANCE, ERROR_BAD_BALANCE);

        IElector(elector).process_new_stake{value: msg.value - DePoolLib.PROXY_FEE}(
            queryId, validatorKey, stakeAt, maxFactor, adnlAddr, signature
        );
    }
 *)
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
				contractMessage := {$ default with  messageValue := Л_carry $} |}. 
 

(* 
function onStakeAccept(uint64 queryId, uint32 comment) public functionID(0xF374484C) {
        // Elector contract always send 1GR
        IDePool(m_dePool).onStakeAccept{value: msg.value - DePoolLib.PROXY_FEE}(queryId, comment, msg.sender);
    }
 *)
Definition DePoolProxyContract_Ф_onStakeAccept ( Л_queryId : XInteger64 )( Л_comment : XInteger32 ) : LedgerT True := 
	U0! Л_dePool := ↑ε10 DePoolProxyContract_ι_m_dePool ;
	U0! Л_value := msg_value () !- ↑ε9 DePoolLib_ι_PROXY_FEE ;
	U0! Л_sender := msg_sender ()  ;
    sendMessage {| contractAddress := Л_dePool;
				   contractFunction := DePoolContract_Ф_onStakeAcceptF Л_queryId Л_comment Л_sender ;
				   contractMessage := {$ default with  messageValue := Л_value $} |} .


(* 
function onStakeReject(uint64 queryId, uint32 comment) public functionID(0xEE6F454C) {
        IDePool(m_dePool).onStakeReject{value: msg.value - DePoolLib.PROXY_FEE}(queryId, comment, msg.sender);
    }
 *)
Definition DePoolProxyContract_Ф_onStakeReject ( Л_queryId : XInteger64 )( Л_comment : XInteger32 ) : LedgerT True := 
	U0! Л_dePool := ↑ε10 DePoolProxyContract_ι_m_dePool ;
	U0! Л_value := msg_value () !- ↑ε9 DePoolLib_ι_PROXY_FEE ;
	U0! Л_sender := msg_sender ()  ;	
    sendMessage {| contractAddress := Л_dePool;
				   contractFunction := DePoolContract_Ф_onStakeRejectF Л_queryId Л_comment Л_sender ;
				   contractMessage := {$ default with  messageValue := Л_value $} |} .


(* 
function recover_stake(uint64 queryId, address elector) public override {
require(msg.sender == m_dePool, ERROR_IS_NOT_DEPOOL);

        // this check is needed for correct work of proxy
        uint carry = msg.value - DePoolLib.PROXY_FEE;
        require(address(this).balance >= carry + DePoolLib.MIN_PROXY_BALANCE, ERROR_BAD_BALANCE);

        IElector(elector).recover_stake{value: msg.value - DePoolLib.PROXY_FEE}(queryId);
    }
*)
Definition DePoolProxyContract_Ф_recover_stake  ( Л_queryId : XInteger64 )
                                                ( Л_elector : XAddress ) 
                                           : LedgerT ( XErrorValue True XInteger ) := 
 Require2 {{ msg_sender () ?== ↑ε10 DePoolProxyContract_ι_m_dePool , ↑ε10 DePoolProxyContract_ι_ERROR_IS_NOT_DEPOOL }} ; 
 U0! Л_carry := msg_value () !- ↑ε9 DePoolLib_ι_PROXY_FEE ;
 Require {{ tvm_balance () ?>=  $Л_carry !+ (↑ε9 DePoolLib_ι_MIN_PROXY_BALANCE) , ↑ε10 DePoolProxyContract_ι_ERROR_BAD_BALANCE }} ;
 sendMessage {| contractAddress := Л_elector;
				contractFunction := IElector_И_recover_stakeF Л_queryId ;
				contractMessage := {$ default with  messageValue := Л_carry $} |} . 

 
(* 
function onSuccessToRecoverStake(uint64 queryId) public functionID(0xF96F7324) {
        IDePool(m_dePool).onSuccessToRecoverStake{value: msg.value - DePoolLib.PROXY_FEE}(queryId, msg.sender);
    }
*)
Definition DePoolProxyContract_Ф_onSuccessToRecoverStake ( Л_queryId : XInteger64 ) : LedgerT True := 
	U0! Л_dePool := ↑ε10 DePoolProxyContract_ι_m_dePool ;
	U0! Л_value := msg_value () !- ↑ε9 DePoolLib_ι_PROXY_FEE ;
	U0! Л_sender := msg_sender ()  ;	
	sendMessage {| contractAddress := Л_dePool;
				   contractFunction := DePoolContract_Ф_onSuccessToRecoverStakeF Л_queryId Л_sender ;
				   contractMessage := {$ default with  messageValue := Л_value $} |} .



(* 
function getProxyInfo() public view returns (address depool, uint64 minBalance) {
        depool = m_dePool;
        minBalance = DePoolLib.MIN_PROXY_BALANCE;
    }
 *)
Definition DePoolProxyContract_Ф_getProxyInfo : LedgerT ( XAddress # XInteger64 ) := 
 U0! Л_depool := ↑ε10 DePoolProxyContract_ι_m_dePool ; 
 U0! Л_minBalance := ↑ε9 DePoolLib_ι_MIN_PROXY_BALANCE ; 
	 return# ($ Л_depool, $ Л_minBalance) . 
 

(* 
function _addStakes(
        Round round,
        DePoolLib.Participant participant,
        address participantAddress,
        uint64 stake,
        optional(InvestParams) vesting,
        optional(InvestParams) lock
    )
        internal inline returns (Round, DePoolLib.Participant)
    {
        if (stake == 0 && !vesting.hasValue() && !lock.hasValue()) {
            return (round, participant);
        }

        if (!round.stakes.exists(participantAddress)) {
            round.participantQty++;
            participant.roundQty++;
        }

        round.stake += stake;
        StakeValue sv = round.stakes[participantAddress];
        sv.ordinary += stake;

        if (vesting.hasValue()) {
            participant.haveVesting = true;
            round.stake += vesting.get().amount;
            sv.vesting = vesting;
        }

        if (lock.hasValue()) {
            participant.haveLock = true;
            round.stake += lock.get().amount;
            sv.lock = lock;
        }

        round.stakes[participantAddress] = sv;
        return (round, participant);
    }
*)

(* Check LocalState_ι__addStakes_Л_sv.

Check (↑17 U1! LocalState_ι__addStakes_Л_round ^^ RoundsBase_ι_Round_ι_stakes [[ $ xInt0 ]] := D2! LocalState_ι__addStakes_Л_sv ). *)

Definition RoundsBase_Ф__addStakes' (Л_round : RoundsBase_ι_Round )
								                     (Л_participant : DePoolLib_ι_Participant ) 
								                     (Л_participantAddress: XAddress) 
								                     (Л_stake: XInteger64) 
								                     (Л_vesting: XMaybe RoundsBase_ι_InvestParams) 
								                     (Л_lock: XMaybe RoundsBase_ι_InvestParams) 
                    : LedgerT  (XValueValue ( RoundsBase_ι_Round # DePoolLib_ι_Participant)) :=  							   
 (* initialize local variables *)						
 (↑17 U1! LocalState_ι__addStakes_Л_round := $ Л_round) >>
 (↑17 U1! LocalState_ι__addStakes_Л_participant := $ Л_participant) >> 

 (*
 if (stake == 0 && !vesting.hasValue() && !lock.hasValue()) {
            return (round, participant);
        }
 *)
 
  If! ( ( $ Л_stake ?== $ xInt0 ) !&  ( !¬ ($ Л_vesting ->hasValue) ) !& ( !¬ ($ Л_lock ->hasValue) ) ) then { 
    return! (xError (  [( Л_round , Л_participant )] ))  
  } ; 

		
					   
  (*
  if (!round.stakes.exists(participantAddress)) {
            round.participantQty++;
            participant.roundQty++;
        }
  *)
  ( If ( !¬ (D1! (↑17 D2! LocalState_ι__addStakes_Л_round ^^ RoundsBase_ι_Round_ι_stakes) ->exists $ Л_participantAddress) ) then  {
		(↑17 U1! LocalState_ι__addStakes_Л_round ^^ RoundsBase_ι_Round_ι_participantQty !++) >>
		(↑17 U1! LocalState_ι__addStakes_Л_participant ^^ DePoolLib_ι_Participant_ι_roundQty !++)
	} ) >>
						
  (*round.stake += stake;
        StakeValue sv = round.stakes[participantAddress];
		sv.ordinary += stake;*)			
  (↑17 U1! LocalState_ι__addStakes_Л_round ^^ RoundsBase_ι_Round_ι_stake !+= $ Л_stake) >> 			  
  (↑17 U1! LocalState_ι__addStakes_Л_sv := D1! (D2! LocalState_ι__addStakes_Л_round ^^ RoundsBase_ι_Round_ι_stakes) [[ $ Л_participantAddress ]] ) >> 
  (↑17 U1! LocalState_ι__addStakes_Л_sv ^^ RoundsBase_ι_StakeValue_ι_ordinary !+= $ Л_stake) >> 

  (*
  if (vesting.hasValue()) {
            participant.haveVesting = true;
          
                round.stake += vesting.get().amount;
           
            sv.vesting = vesting;
        }
  *)

  (If  ($ Л_vesting ->hasValue) then {
	  
	(↑17 U1! LocalState_ι__addStakes_Л_participant ^^ DePoolLib_ι_Participant_ι_haveVesting := $ xBoolTrue ) >>

	 (* (If  (D1! ($ Л_vesting ->get) ^^ RoundsBase_ι_InvestParams_ι_isActive) then { *)
		(↑17 U1! LocalState_ι__addStakes_Л_round ^^ RoundsBase_ι_Round_ι_stake !+= (D1! ($ Л_vesting ->get) ^^ RoundsBase_ι_InvestParams_ι_amount))
	  (* }) *) >>

	 (↑17 U1! LocalState_ι__addStakes_Л_sv ^^ RoundsBase_ι_StakeValue_ι_vesting := $ Л_vesting) 
  }) >> 

  (*

  if (lock.hasValue()) {
            participant.haveLock = true;
            
                round.stake += lock.get().amount;
           
            sv.lock = lock;
        }
  
  *)

  (If  ($ Л_lock ->hasValue) then {
	  
	(↑17 U1! LocalState_ι__addStakes_Л_participant ^^ DePoolLib_ι_Participant_ι_haveLock := $ xBoolTrue ) >>

	(*  (If (D1! ($ Л_lock ->get) ^^ RoundsBase_ι_InvestParams_ι_isActive) then { *)
		(↑17 U1! LocalState_ι__addStakes_Л_round ^^ RoundsBase_ι_Round_ι_stake !+= (D1! ($ Л_lock ->get) ^^ RoundsBase_ι_InvestParams_ι_amount))
	 (*  }) *) >>

	 (↑17 U1! LocalState_ι__addStakes_Л_sv ^^ RoundsBase_ι_StakeValue_ι_lock := $ Л_lock) 
  }) >>		

  (* round.stakes[participantAddress] = sv; *)
  (↑17 U1! LocalState_ι__addStakes_Л_round ^^ RoundsBase_ι_Round_ι_stakes [[ $ Л_participantAddress ]] := D2! LocalState_ι__addStakes_Л_sv ) >>

  return# ( ↑ε17 LocalState_ι__addStakes_Л_round , ↑ε17 LocalState_ι__addStakes_Л_participant).	
	 
Definition RoundsBase_Ф__addStakes (Л_round : RoundsBase_ι_Round )
                                  (Л_participant : DePoolLib_ι_Participant ) 
                                  (Л_participantAddress: XAddress) 
                                  (Л_stake: XInteger64) 
                                  (Л_vesting: XMaybe RoundsBase_ι_InvestParams) 
                                  (Л_lock: XMaybe RoundsBase_ι_InvestParams) 
                            : LedgerT  ( RoundsBase_ι_Round # DePoolLib_ι_Participant)   :=  							   
do r ← RoundsBase_Ф__addStakes' Л_round Л_participant Л_participantAddress Л_stake Л_vesting Л_lock;
  return! (fromValueValue r).



(* 

function stakeSum(StakeValue stakes) internal inline returns (uint64) {
    optional(InvestParams) v = stakes.vesting;
    optional(InvestParams) l = stakes.lock;
    return
        stakes.ordinary +
        (v.hasValue() ? v.get().amount : 0) +
        (l.hasValue() ? l.get().amount : 0);
}
 *)

 Definition RoundsBase_Ф_stakeSum ( Л_stakes : RoundsBase_ι_StakeValue ) : LedgerT XInteger64 := 
    U0! Л_v :=  D0! Л_stakes ^^ RoundsBase_ι_StakeValue_ι_vesting ;
    U0! Л_l :=  D0! Л_stakes ^^ RoundsBase_ι_StakeValue_ι_lock ; 
    
    D0! Л_stakes ^^ RoundsBase_ι_StakeValue_ι_ordinary !+
       ( (( $ Л_v ->hasValue ) ) ?  (  D1! ( $ Л_v ->get ) ^^ RoundsBase_ι_InvestParams_ι_amount ) ::: $ xInt0 ) !+
       ( (( $ Л_l ->hasValue ) ) ?  (  D1! ( $ Л_l ->get ) ^^ RoundsBase_ι_InvestParams_ι_amount ) ::: $ xInt0 ) .


(* 
function transferStakeInOneRound(
        Round round,
        DePoolLib.Participant sourceParticipant,
        DePoolLib.Participant destinationParticipant,
        address source,
        address destination,
        uint64 amount,
        uint64 minStake
    )
        internal inline
        returns (
            Round, // updated round
            uint64, // transferred value
            uint64, // prev ordinary stake of source
            DePoolLib.Participant, // updated source participant
            DePoolLib.Participant // updated destination participant
        )
    {
        optional(StakeValue) optSourceStake = round.stakes.fetch(source);
        if (!optSourceStake.hasValue())
            return (round, 0, 0, sourceParticipant, destinationParticipant);
        StakeValue sourceStake = optSourceStake.get();
        uint64 prevSourceStake = round.stakes[source].ordinary;
        uint64 newSourceStake;
        uint64 deltaDestinationStake;
        if (sourceStake.ordinary >= amount) {
            newSourceStake = sourceStake.ordinary - amount;
            deltaDestinationStake = amount;
        } else {
            newSourceStake = 0;
            deltaDestinationStake = sourceStake.ordinary;
        }


        uint64 newDestStake = round.stakes[destination].ordinary + deltaDestinationStake;
        if ((0 < newSourceStake && newSourceStake < minStake) ||
            (0 < newDestStake && newDestStake < minStake)) {
            return (round, 0, prevSourceStake, sourceParticipant, destinationParticipant);
        }

        sourceStake.ordinary = newSourceStake;
        if (stakeSum(sourceStake) == 0) {
            --round.participantQty;
            delete round.stakes[source];
            --sourceParticipant.roundQty;
        } else {
            round.stakes[source] = sourceStake;
        }

        if (!round.stakes.exists(destination)) {
            ++round.participantQty;
            ++destinationParticipant.roundQty;
        }
        round.stakes[destination].ordinary += deltaDestinationStake;

        return (round, deltaDestinationStake, prevSourceStake, sourceParticipant, destinationParticipant);
    }
*)

Definition RoundsBase_Ф_transferStakeInOneRound' ( Л_round : RoundsBase_ι_Round )
                                     (Л_sourceParticipant: DePoolLib_ι_Participant) (Л_destinationParticipant: DePoolLib_ι_Participant)
(Л_source : XAddress) (Л_destination: XAddress) (Л_amount: XInteger64) (Л_minStake : XInteger64)
 : LedgerT ( XValueValue ( RoundsBase_ι_Round # XInteger64 # XInteger64 # DePoolLib_ι_Participant # DePoolLib_ι_Participant) ) :=

		(*initialize pseudo locals*)
		(↑17 U1! LocalState_ι_transferStakeInOneRound_Л_round := ($ Л_round) ) >>
		(↑17 U1! LocalState_ι_transferStakeInOneRound_Л_sourceParticipant := ($ Л_sourceParticipant) ) >>
		(↑17 U1! LocalState_ι_transferStakeInOneRound_Л_destinationParticipant := ($ Л_destinationParticipant) ) >> 
		(* optional(StakeValue) optSourceStake = round.stakes.fetch(source); *)
		U0! Л_optSourceStake := D1! (D0! Л_round ^^ RoundsBase_ι_Round_ι_stakes) ->fetch ($ Л_source) ;  
        (* if (!optSourceStake.hasValue())
			return (round, 0, 0, sourceParticipant, destinationParticipant); *)
		If!! ( !¬ ($ Л_optSourceStake ->hasValue) ) then {
			 return! (xError ( [( Л_round, xInt0, xInt0, Л_sourceParticipant, Л_destinationParticipant )] ) )
		}  ; 				   
		(* StakeValue sourceStake = optSourceStake.get(); *)
		(↑17 U1! LocalState_ι_transferStakeInOneRound_Л_sourceStake := ($ Л_optSourceStake ->get) ) >> 
		(* uint64 prevSourceStake = round.stakes[source].ordinary; *)
		U0! Л_prevSourceStake := (D1! (D1! (D0! Л_round ^^ RoundsBase_ι_Round_ι_stakes) [[ $ Л_source ]] ) ^^ RoundsBase_ι_StakeValue_ι_ordinary ) ; 
		(* uint64 newSourceStake; *)
		(* uint64 deltaDestinationStake; *)
		
        (* if (sourceStake.ordinary >= amount) {
            newSourceStake = sourceStake.ordinary - amount;
            deltaDestinationStake = amount;
        } else {
            newSourceStake = 0;
            deltaDestinationStake = sourceStake.ordinary;
		} *)  
		(If ( ↑17 D2! LocalState_ι_transferStakeInOneRound_Л_sourceStake ^^ RoundsBase_ι_StakeValue_ι_ordinary ?>= $  Л_amount) then {

		   (↑17 U1! LocalState_ι_transferStakeInOneRound_Л_newSourceStake := (D2! LocalState_ι_transferStakeInOneRound_Л_sourceStake ^^ RoundsBase_ι_StakeValue_ι_ordinary) !- ($ Л_amount))  >>
	 	   (↑17 U1! LocalState_ι_transferStakeInOneRound_Л_deltaDestinationStake := ($ Л_amount)) 
		 
		} else { 
			
		(↑17 U1! LocalState_ι_transferStakeInOneRound_Л_newSourceStake := $ xInt0 )  >>
		(↑17 U1! LocalState_ι_transferStakeInOneRound_Л_deltaDestinationStake := D2! LocalState_ι_transferStakeInOneRound_Л_sourceStake ^^ RoundsBase_ι_StakeValue_ι_ordinary) 
 
		}) >> 
		(* uint64 newDestStake = round.stakes[destination].ordinary + deltaDestinationStake; *)
		U0! Л_newDestStake := (D1! (D1! ( ↑17 D2! LocalState_ι_transferStakeInOneRound_Л_round ^^ RoundsBase_ι_Round_ι_stakes) [[ $ Л_destination ]] ) ^^ RoundsBase_ι_StakeValue_ι_ordinary) 
		                      !+ ( ↑ε17 LocalState_ι_transferStakeInOneRound_Л_deltaDestinationStake  );


        (* if ((0 < newSourceStake && newSourceStake < minStake) ||
            (0 < newDestStake && newDestStake < minStake)) {
            return (round, 0, prevSourceStake, sourceParticipant, destinationParticipant);
		} *)
		If! ((($ xInt0 ?< (↑ε17 LocalState_ι_transferStakeInOneRound_Л_newSourceStake))!&
			((↑ε17 LocalState_ι_transferStakeInOneRound_Л_newSourceStake) ?< $ Л_minStake)) !| 
			 (($ xInt0 ?< $ Л_newDestStake) !& ($ Л_newDestStake ?< $ Л_minStake) )) then {
			return! (xError ( [( Л_round, xInt0, Л_prevSourceStake, Л_sourceParticipant, Л_destinationParticipant )] ))
		}; 

		(* sourceStake.ordinary = newSourceStake; *)
		(↑17 U1! LocalState_ι_transferStakeInOneRound_Л_sourceStake ^^ RoundsBase_ι_StakeValue_ι_ordinary := ε LocalState_ι_transferStakeInOneRound_Л_newSourceStake) >>
		
        (* if (stakeSum(sourceStake) == 0) {
            --round.participantQty;
            delete round.stakes[source];
            --sourceParticipant.roundQty;
        } else {
            round.stakes[source] = sourceStake;
		} *)
		
		( If (RoundsBase_Ф_stakeSum (! ↑ε17 LocalState_ι_transferStakeInOneRound_Л_sourceStake !) ?== $ xInt0) then 
		{ 
			(↑17 U1! LocalState_ι_transferStakeInOneRound_Л_round ^^ RoundsBase_ι_Round_ι_participantQty !--)   >> 
		 ( ↑17 U1! delete LocalState_ι_transferStakeInOneRound_Л_round ^^ RoundsBase_ι_Round_ι_stakes [[ $ Л_source ]] ) >>
			(↑17 U1! LocalState_ι_transferStakeInOneRound_Л_sourceParticipant ^^ DePoolLib_ι_Participant_ι_roundQty !--) 
		 } else {
			 (↑17 U1! LocalState_ι_transferStakeInOneRound_Л_round ^^ RoundsBase_ι_Round_ι_stakes [[ $ Л_source ]] := ε LocalState_ι_transferStakeInOneRound_Л_sourceStake)
		} ) >>

        (* if (!round.stakes.exists(destination)) {
            ++round.participantQty;
            ++destinationParticipant.roundQty;
		} *)

		(If ( !¬ (D1! (↑17 D2! LocalState_ι_transferStakeInOneRound_Л_round ^^ RoundsBase_ι_Round_ι_stakes) ->exists $ Л_destination ) ) then {
			(↑17 U1! LocalState_ι_transferStakeInOneRound_Л_round ^^ RoundsBase_ι_Round_ι_participantQty !++) >>
			(↑17 U1! LocalState_ι_transferStakeInOneRound_Л_destinationParticipant ^^ DePoolLib_ι_Participant_ι_roundQty !++)
		} ) >>
		
		(*round.stakes[destination].ordinary += deltaDestinationStake;*)
		(↑17 U1! LocalState_ι_transferStakeInOneRound_Л_round ^^ RoundsBase_ι_Round_ι_stakes [[ $ Л_destination ]] ^^ RoundsBase_ι_StakeValue_ι_ordinary !+= ε LocalState_ι_transferStakeInOneRound_Л_deltaDestinationStake) >>
		
		(*return (round, deltaDestinationStake, prevSourceStake, sourceParticipant, destinationParticipant);*)
		return# (↑ε17 LocalState_ι_transferStakeInOneRound_Л_round , 
				 ↑ε17 LocalState_ι_transferStakeInOneRound_Л_deltaDestinationStake, 
				 $ Л_prevSourceStake, 
				 ↑ε17 LocalState_ι_transferStakeInOneRound_Л_sourceParticipant, 
				 ↑ε17 LocalState_ι_transferStakeInOneRound_Л_destinationParticipant ).
		
Definition RoundsBase_Ф_transferStakeInOneRound ( Л_round : RoundsBase_ι_Round )
				                                        (Л_sourceParticipant: DePoolLib_ι_Participant) 
                                                (Л_destinationParticipant: DePoolLib_ι_Participant)
				                                        (Л_source : XAddress) 
                                                (Л_destination: XAddress) 
                                                (Л_amount: XInteger64) 
                                                (Л_minStake : XInteger64)
				  : LedgerT ( RoundsBase_ι_Round # XInteger64 # XInteger64 # DePoolLib_ι_Participant # DePoolLib_ι_Participant) :=
do r ← 	RoundsBase_Ф_transferStakeInOneRound' Л_round Л_sourceParticipant Л_destinationParticipant Л_source Л_destination Л_amount  Л_minStake ;
return! (fromValueValue r).


(* function isRoundPre0(uint64 id) internal inline returns (bool) { return id == m_roundQty - 1; } *)
Definition RoundsBase_Ф_isRoundPre0 (Л_id: XInteger64) : LedgerT XBool :=
    $ Л_id ?== (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt1.
(* function isRound0(uint64 id)    internal inline returns (bool) { return id == m_roundQty - 2; } *)
Definition RoundsBase_Ф_isRound0 (Л_id: XInteger64) : LedgerT XBool :=
    $ Л_id ?== (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt2.
(* function isRound1(uint64 id)    internal inline returns (bool) { return id == m_roundQty - 3; } *)
Definition RoundsBase_Ф_isRound1 (Л_id: XInteger64) : LedgerT XBool :=
    $ Л_id ?== (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt3.
(* function isRound2(uint64 id)    internal inline returns (bool) { return id == m_roundQty - 4; } *)
Definition RoundsBase_Ф_isRound2 (Л_id: XInteger64) : LedgerT XBool :=
    $ Л_id ?== (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt4.
(* function roundAt(uint64 id) internal returns (Round) {
    return m_rounds.fetch(id).get();
} *)
Definition RoundsBase_Ф_roundAt (Л_id: XInteger64) : LedgerT RoundsBase_ι_Round :=
     (D1! (↑11 D2! RoundsBase_ι_m_rounds) ->fetch $ Л_id) ->get.
(* function getRoundPre0() internal inline returns (Round) { return roundAt(m_roundQty - 1); } *)
Definition RoundsBase_Ф_getRoundPre0  : LedgerT RoundsBase_ι_Round :=
    RoundsBase_Ф_roundAt (!  (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt1 !).
(* function getRound0()    internal inline returns (Round) { return roundAt(m_roundQty - 2); } *)
Definition RoundsBase_Ф_getRound0 : LedgerT RoundsBase_ι_Round :=
    RoundsBase_Ф_roundAt (!  (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt2 !).
(* function getRound1()    internal inline returns (Round) { return roundAt(m_roundQty - 3); } *)
Definition RoundsBase_Ф_getRound1 : LedgerT RoundsBase_ι_Round :=
    RoundsBase_Ф_roundAt (!  (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt3 !).
(* function getRound2()    internal inline returns (Round) { return roundAt(m_roundQty - 4); } *)
Definition RoundsBase_Ф_getRound2 : LedgerT RoundsBase_ι_Round :=
    RoundsBase_Ф_roundAt (!  (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt4 !).

(* function setRound(uint64 id, Round round) internal {
    m_rounds[id] = round;
} *)
Definition RoundsBase_Ф_setRound (Л_id: XInteger) ( Л_round: RoundsBase_ι_Round) : LedgerT True :=
     ↑11 U1! RoundsBase_ι_m_rounds [[ $Л_id ]] := $Л_round.
(* function setRoundPre0(Round r) internal inline { setRound(m_roundQty - 1, r); } *)
Definition RoundsBase_Ф_setRoundPre0 ( Л_r: RoundsBase_ι_Round): LedgerT True :=
    RoundsBase_Ф_setRound (!  (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt1 , $Л_r  !).
(* function setRound0(Round r)    internal inline { setRound(m_roundQty - 2, r); } *)
Definition RoundsBase_Ф_setRound0 ( Л_r: RoundsBase_ι_Round): LedgerT True :=
    RoundsBase_Ф_setRound (!  (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt2 , $Л_r  !).
(* function setRound1(Round r)    internal inline { setRound(m_roundQty - 3, r); } *)
Definition RoundsBase_Ф_setRound1 ( Л_r: RoundsBase_ι_Round): LedgerT True :=
    RoundsBase_Ф_setRound (!  (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt3 , $Л_r  !).
(* function setRound2(Round r)    internal inline { setRound(m_roundQty - 4, r); } *)
Definition RoundsBase_Ф_setRound2 ( Л_r: RoundsBase_ι_Round): LedgerT True :=
    RoundsBase_Ф_setRound (!  (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt4 , $Л_r  !).

(* 
function fetchRound(uint64 id) internal returns (optional(Round)) {
    return m_rounds.fetch(id);
} *)
Definition RoundsBase_Ф_fetchRound (Л_id: XInteger64) : LedgerT (XMaybe RoundsBase_ι_Round) :=
     (D1! (↑11 D2! RoundsBase_ι_m_rounds) ->fetch $ Л_id) .

(*contract ParticipantBase {
    function fetchParticipant(address addr) internal view returns (optional(DePoolLib.Participant)) {
        return m_participants.fetch(addr);
    }*)

Definition ParticipantBase_Ф_fetchParticipant (Л_address: XAddress) : LedgerT (XMaybe DePoolLib_ι_Participant) :=
     (D1! (↑5 D2! ParticipantBase_ι_m_participants) ->fetch $ Л_address) .

(* function minRound() internal view returns(optional(uint64, Round)) {
    return m_rounds.min();
} *)

Definition RoundsBase_Ф_minRound : LedgerT (XMaybe (XInteger64 # RoundsBase_ι_Round)) :=
     (D1! (↑11 D2! RoundsBase_ι_m_rounds) ->min) .


(* function nextRound(uint64 id) internal view returns(optional(uint64, Round)) {
    return m_rounds.next(id);
} *)
Definition RoundsBase_Ф_nextRound (Л_id: XInteger64) : LedgerT (XMaybe (XInteger64 # RoundsBase_ι_Round)) :=
     (D1! (↑11 D2! RoundsBase_ι_m_rounds) ->next $ Л_id) .

			 
(* 
function withdrawStakeInPoolingRound(
        DePoolLib.Participant participant,
        address participantAddress,
        uint64 targetAmount,
        uint64 minStake
    )
        internal inline returns (uint64, DePoolLib.Participant)
    {
        Round round = getRound0();
        optional(StakeValue) optSv = round.stakes.fetch(participantAddress);
        if (!optSv.hasValue()) {
            return (0, participant);
        }
        StakeValue sv = optSv.get();
        targetAmount = math.min(targetAmount, sv.ordinary);
        sv.ordinary -= targetAmount;
        round.stake -= targetAmount;
        if (sv.ordinary < minStake) {
            round.stake -= sv.ordinary;
            targetAmount += sv.ordinary;
            sv.ordinary = 0;
        }

        if (stakeSum(sv) == 0) {
            --round.participantQty;
            delete round.stakes[participantAddress];
            --participant.roundQty;
        } else {
            round.stakes[participantAddress] = sv;
        }
        setRound0(round);
        return (targetAmount, participant);
    }

 *)

Definition RoundsBase_Ф_withdrawStakeInPoolingRound' (Л_participant : DePoolLib_ι_Participant ) 
													(Л_participantAddress : XAddress)
													(Л_targetAmount : XInteger64)
													(Л_minStake : XInteger64) : LedgerT ( XValueValue (XInteger64 # DePoolLib_ι_Participant) )  := 
(*initialize pseudo locals*)
(↑17 U1! LocalState_ι_withdrawStakeInPoolingRound_Л_targetAmount := $ Л_targetAmount) >>
(↑17 U1! LocalState_ι_withdrawStakeInPoolingRound_Л_participant := $ Л_participant)  >>

(* Round round = getRound0(); *)
(↑↑17 U2! LocalState_ι_withdrawStakeInPoolingRound_Л_round := RoundsBase_Ф_getRound0 () ) >>
(*optional(StakeValue) optSv = round.stakes.fetch(participantAddress);*)
U0! Л_optSv := (D1! (↑17 D2! LocalState_ι_withdrawStakeInPoolingRound_Л_round ^^ RoundsBase_ι_Round_ι_stakes) ->fetch $ Л_participantAddress) ;

(*if (!optSv.hasValue()) {
	return (0, participant);
}*) 
 If! ( !¬ ($ Л_optSv) ->hasValue ) then {
     return! (xError ( [( xInt0, Л_participant )] ) ) 
 } ;

(*StakeValue sv = optSv.get();*)
(↑17 U1! LocalState_ι_withdrawStakeInPoolingRound_Л_sv := ($ Л_optSv) ->get) >>
(*targetAmount = math.min(targetAmount, sv.ordinary);*)
(↑17 U1! LocalState_ι_withdrawStakeInPoolingRound_Л_targetAmount := math->min2 (! ε LocalState_ι_withdrawStakeInPoolingRound_Л_targetAmount ,
                                                                                 D2! LocalState_ι_withdrawStakeInPoolingRound_Л_sv ^^ RoundsBase_ι_StakeValue_ι_ordinary !) ) >>
(*sv.ordinary -= targetAmount;*)
(↑17 U1! LocalState_ι_withdrawStakeInPoolingRound_Л_sv ^^ RoundsBase_ι_StakeValue_ι_ordinary !-= ε LocalState_ι_withdrawStakeInPoolingRound_Л_targetAmount) >>
(*round.stake -= targetAmount;*)
(↑17 U1! LocalState_ι_withdrawStakeInPoolingRound_Л_round ^^ RoundsBase_ι_Round_ι_stake !-= ε LocalState_ι_withdrawStakeInPoolingRound_Л_targetAmount) >>
(*
if (sv.ordinary < minStake) {
	round.stake -= sv.ordinary;
	targetAmount += sv.ordinary;
	sv.ordinary = 0;
}
*)
(If (↑17 D2! LocalState_ι_withdrawStakeInPoolingRound_Л_sv ^^ RoundsBase_ι_StakeValue_ι_ordinary ?< $ Л_minStake ) then {
	(↑17 U1! LocalState_ι_withdrawStakeInPoolingRound_Л_round ^^ RoundsBase_ι_Round_ι_stake !-= D1! (ε LocalState_ι_withdrawStakeInPoolingRound_Л_sv) ^^  RoundsBase_ι_StakeValue_ι_ordinary) >>
	(↑17 U1! LocalState_ι_withdrawStakeInPoolingRound_Л_targetAmount !+= D1! (ε LocalState_ι_withdrawStakeInPoolingRound_Л_sv) ^^  RoundsBase_ι_StakeValue_ι_ordinary) >>
	(↑17 U1! LocalState_ι_withdrawStakeInPoolingRound_Л_sv ^^ RoundsBase_ι_StakeValue_ι_ordinary := $ xInt0 )
}) >>

(*
if (stakeSum(sv) == 0) {
	--round.participantQty;
	delete round.stakes[participantAddress];
	--participant.roundQty;
} else {
	round.stakes[participantAddress] = sv;
}
*)
(If (RoundsBase_Ф_stakeSum (! ↑ε17 LocalState_ι_withdrawStakeInPoolingRound_Л_sv  !) ?== $xInt0 ) then {
	(↑17 U1! LocalState_ι_withdrawStakeInPoolingRound_Л_round ^^ RoundsBase_ι_Round_ι_participantQty !--) >>
	(↑17 U1! delete LocalState_ι_withdrawStakeInPoolingRound_Л_round ^^ RoundsBase_ι_Round_ι_stakes [[ $ Л_participantAddress ]] ) >>
	(↑17 U1! LocalState_ι_withdrawStakeInPoolingRound_Л_participant ^^ DePoolLib_ι_Participant_ι_roundQty !--)
} else {
	(↑17 U1! LocalState_ι_withdrawStakeInPoolingRound_Л_round ^^ RoundsBase_ι_Round_ι_stakes [[ $ Л_participantAddress ]] := ε LocalState_ι_withdrawStakeInPoolingRound_Л_sv)
}) >>

(*setRound0(round);*)
(RoundsBase_Ф_setRound0 (! ↑17 D2! LocalState_ι_withdrawStakeInPoolingRound_Л_round !)) >>

(*return (targetAmount, participant);*)
return#  ( ↑ε17 LocalState_ι_withdrawStakeInPoolingRound_Л_targetAmount , ↑ε17 LocalState_ι_withdrawStakeInPoolingRound_Л_participant ).

Definition RoundsBase_Ф_withdrawStakeInPoolingRound (Л_participant : DePoolLib_ι_Participant ) 
													                          (Л_participantAddress : XAddress)
													                          (Л_targetAmount : XInteger64)
													                          (Л_minStake : XInteger64) 
                                         : LedgerT  (XInteger64 # DePoolLib_ι_Participant) := 
do r ← RoundsBase_Ф_withdrawStakeInPoolingRound' Л_participant Л_participantAddress Л_targetAmount 	Л_minStake	;
return! (fromValueValue r).											


(*
function toTruncatedRound(Round round) internal pure returns (TruncatedRound r) {
        return TruncatedRound({
            id: round.id,
            supposedElectedAt: round.supposedElectedAt,
            unfreeze: round.unfreeze,
            stakeHeldFor: round.stakeHeldFor,
            vsetHashInElectionPhase: round.vsetHashInElectionPhase,
            step: round.step,
            completionReason: round.completionReason,

            stake: round.stake,
            recoveredStake: round.recoveredStake,
            unused: round.unused,
            isValidatorStakeCompleted: round.isValidatorStakeCompleted,
            rewards: round.rewards,
            participantQty: round.participantQty,
            validatorStake: round.validatorStake,
            validatorRemainingStake: round.validatorRemainingStake,
            handledStakesAndRewards: round.handledStakesAndRewards
        }
*)

Definition RoundsBase_Ф_toTruncatedRound ( Л_round : RoundsBase_ι_Round ) : LedgerT RoundsBase_ι_TruncatedRound := 
  {|| RoundsBase_ι_TruncatedRound_ι_id := $ Л_round ->> RoundsBase_ι_Round_ι_id ,
      RoundsBase_ι_TruncatedRound_ι_supposedElectedAt := $ Л_round ->> RoundsBase_ι_Round_ι_supposedElectedAt,
      RoundsBase_ι_TruncatedRound_ι_unfreeze := $ Л_round ->> RoundsBase_ι_Round_ι_unfreeze , 
      RoundsBase_ι_TruncatedRound_ι_stakeHeldFor := $ Л_round ->> RoundsBase_ι_Round_ι_stakeHeldFor , 
      RoundsBase_ι_TruncatedRound_ι_vsetHashInElectionPhase := $ Л_round ->> RoundsBase_ι_Round_ι_vsetHashInElectionPhase ,
      RoundsBase_ι_TruncatedRound_ι_step := $ Л_round ->> RoundsBase_ι_Round_ι_step ,
      RoundsBase_ι_TruncatedRound_ι_completionReason := $ Л_round ->> RoundsBase_ι_Round_ι_completionReason ,
      RoundsBase_ι_TruncatedRound_ι_stake := $ Л_round ->> RoundsBase_ι_Round_ι_stake ,
      RoundsBase_ι_TruncatedRound_ι_recoveredStake := $ Л_round ->> RoundsBase_ι_Round_ι_recoveredStake ,
      RoundsBase_ι_TruncatedRound_ι_unused := $ Л_round ->> RoundsBase_ι_Round_ι_unused ,
      RoundsBase_ι_TruncatedRound_ι_isValidatorStakeCompleted := $ Л_round ->> RoundsBase_ι_Round_ι_isValidatorStakeCompleted ,
      RoundsBase_ι_TruncatedRound_ι_rewards := $ Л_round ->> RoundsBase_ι_Round_ι_rewards ,
      RoundsBase_ι_TruncatedRound_ι_participantQty := $ Л_round ->> RoundsBase_ι_Round_ι_participantQty ,
      RoundsBase_ι_TruncatedRound_ι_validatorStake := $ Л_round ->> RoundsBase_ι_Round_ι_validatorStake ,
      RoundsBase_ι_TruncatedRound_ι_validatorRemainingStake := $ Л_round ->> RoundsBase_ι_Round_ι_validatorRemainingStake ,
      RoundsBase_ι_TruncatedRound_ι_handledStakesAndRewards := $ Л_round ->> RoundsBase_ι_Round_ι_handledStakesAndRewards ||}.



(*  
function getRounds() external view returns (mapping(uint64 => TruncatedRound) rounds) {
        optional(uint64, Round) pair = minRound();
        while (pair.hasValue()) {
            (uint64 id, Round round) = pair.get();
            TruncatedRound r = toTruncatedRound(round);
            rounds[r.id] = r;
            pair = nextRound(id);
        }
        return rounds;
    }
 *)
    
Definition RoundsBase_Ф_getRounds : LedgerT (XHMap XInteger64 RoundsBase_ι_TruncatedRound) := 
	(↑17 U1! LocalState_ι_getRounds_Л_rounds := $default ) >>
	(*optional(uint64, Round) pair = m_rounds.min();*)
	(↑↑17 U2! LocalState_ι_getRounds_Л_pair := RoundsBase_Ф_minRound () ) >>
	(*while (pair.hasValue()) {
            (uint64 id, Round round) = pair.get();
            TruncatedRound r = toTruncatedRound(round);
            rounds[r.id] = r;
            pair = nextRound(id);
        }*)
	(While ((↑17 D2! LocalState_ι_getRounds_Л_pair) ->hasValue) do (
		U0! {( Л_id, Л_round )} := (↑17 D2! LocalState_ι_getRounds_Л_pair) ->get ;
		U0! Л_r := RoundsBase_Ф_toTruncatedRound (! $ Л_round !) ; 
		(↑17 U1! LocalState_ι_getRounds_Л_rounds [[ $ (Л_r ->> RoundsBase_ι_TruncatedRound_ι_id ) ]] := $ Л_r) >>
		(↑↑17 U2! LocalState_ι_getRounds_Л_pair := RoundsBase_Ф_nextRound (! $ Л_id !) ) >>
		continue! I
	)) >> 
	(*return rounds;*)
	↑17 D2! LocalState_ι_getRounds_Л_rounds.

(* 
function generateRound() internal returns (Round) {
        DePoolLib.Request req;
        Round r = Round({                      
            id: m_roundQty,
            supposedElectedAt: 0, // set when round in elections phase
            unfreeze: DePoolLib.MAX_TIME, // set when round in unfreeze phase
            stakeHeldFor: 0,                   
            vsetHashInElectionPhase: 0, // set when round in elections phase
            step: RoundStep.PrePooling,
            completionReason: CompletionReason.Undefined,

            stake: 0,
            recoveredStake: 0,                 
            unused: 0,
            isValidatorStakeCompleted: false,  
         (* TODO:new: *)grossReward: 0,
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

Definition DePoolContract_Ф_generateRound : LedgerT RoundsBase_ι_Round := 
	U0! Л_req := $ default;
	U0! Л_r :=  {||
				  (*id: m_roundQty,*)
				  RoundsBase_ι_Round_ι_id := ↑11 D2! RoundsBase_ι_m_roundQty ,
				  (*supposedElectedAt: 0*)
				  RoundsBase_ι_Round_ι_supposedElectedAt := $ xInt0 ,
				  (*unfreeze: DePoolLib.MAX_TIME*) 
				  RoundsBase_ι_Round_ι_unfreeze := ↑9 D2! DePoolLib_ι_MAX_TIME , 
                  (* stakeHeldFor: 0, *)                    
                  RoundsBase_ι_Round_ι_stakeHeldFor := $ xInt0 ,
				  (* vsetHashInElectionPhase: 0  *)
				  RoundsBase_ι_Round_ι_vsetHashInElectionPhase := $ xInt0 ,
				  (* step: RoundStep.Pooling, *)
				  RoundsBase_ι_Round_ι_step := $ RoundsBase_ι_RoundStepP_ι_PrePooling , 
				  (*completionReason: CompletionReason.Undefined*)
                  RoundsBase_ι_Round_ι_completionReason := $ RoundsBase_ι_CompletionReasonP_ι_Undefined , 
                  
				  (* stake: 0, *)
				  RoundsBase_ι_Round_ι_stake := $ xInt0 ,
                  (* recoveredStake: 0,  *)                
                  RoundsBase_ι_Round_ι_recoveredStake := $ xInt0 ,
				  (* unused: 0, *)
				  RoundsBase_ι_Round_ι_unused := $ xInt0 ,
                  (* isValidatorStakeCompleted: false, *) 
                  RoundsBase_ι_Round_ι_isValidatorStakeCompleted := $ xBoolFalse ,
                  (* grossReward: 0, *)
      RoundsBase_ι_Round_ι_grossReward := $ xInt0 ,
                  (* rewards: 0, *)
				  RoundsBase_ι_Round_ι_rewards := $ xInt0 ,
				  (* participantQty : 0, *)
				  RoundsBase_ι_Round_ι_participantQty := $ xInt0 ,				  
                  (*validatorStake: 0,               
                    validatorRemainingStake: 0,       
                    handledStakesAndRewards: 0,   *)   
                  RoundsBase_ι_Round_ι_validatorStake := $ xInt0 ,
                  RoundsBase_ι_Round_ι_validatorRemainingStake := $ xInt0 ,
                  RoundsBase_ι_Round_ι_handledStakesAndRewards := $ xInt0 ,
				  (* validatorRequest: req, *)
				  RoundsBase_ι_Round_ι_validatorRequest := $ Л_req ,				  
				  (* elector: address(0), *)
				  RoundsBase_ι_Round_ι_elector := $ xInt0 , 
				  (* proxy: getProxy(m_roundQty), *)
				  RoundsBase_ι_Round_ι_proxy := ProxyBase_Ф_getProxy (! ↑11 D2! RoundsBase_ι_m_roundQty !) 
	             ||}  ;
	(↑11 U1! RoundsBase_ι_m_roundQty !++) >> 

return! Л_r. 
	
(* 
constructor(                        
        uint64 minStake,
        uint64 validatorAssurance,
        TvmCell proxyCode,
        address validatorWallet,
    (*  TODO:delete   address association, *)
        uint8 participantRewardFraction,
    (*  TODO:delete   uint8 validatorRewardFraction, *)
        uint64 balanceThreshold
    )
        ValidatorBase(validatorWallet)
        public
    {
        require(address(this).wid == 0, Errors.NOT_WORKCHAIN0);
        require(msg.pubkey() == tvm.pubkey(), Errors.IS_NOT_OWNER);
        require(tvm.pubkey() != 0, Errors.CONSTRUCTOR_NO_PUBKEY);
        require(minStake >= 1 ton, Errors.BAD_STAKES);
        require(minStake <= validatorAssurance, Errors.BAD_STAKES);
        require(tvm.hash(proxyCode) == PROXY_CODE_HASH, Errors.BAD_PROXY_CODE);
        require(validatorWallet.isStdAddrWithoutAnyCast(), Errors.VALIDATOR_IS_NOT_STD);
      (*TODO:delete:  require(association.isStdAddrWithoutAnyCast(), Errors.ASSOCIATION_IS_NOT_STD);
        TODO:delete:  require(participantRewardFraction > 0, Errors.BAD_PART_REWARD);
        TODO:delete:  require(validatorRewardFraction > 0, Errors.BAD_VALID_REWARD);
        TODO:delete:  require(uint(participantRewardFraction) + validatorRewardFraction <= 100,
        TODO:delete:          Errors.PERCENT_NOT_EQ_100);
        TODO:delete:  uint8 associationRewardFraction = 100 - participantRewardFraction - validatorRewardFraction;
        TODO:delete:  bool isFractionZero = associationRewardFraction == 0;
        TODO:delete:  bool isAddressZero = association == address(0);
        TODO:delete:  require(isFractionZero == isAddressZero, Errors.BAD_ASSOCIATION_AND_PERCENT); // both are set or both are equal to zero *)      require(balanceThreshold >= CRITICAL_THRESHOLD, Errors.BAD_MINIMUM_BALANCE);
        (*TODO:new*) require(participantRewardFraction > 0 && participantRewardFraction < 100, Errors.BAD_PART_REWARD);
>       (*TODO:new*) uint8 validatorRewardFraction = 100 -  participantRewardFraction;
        require(balanceThreshold >= CRITICAL_THRESHOLD, Errors.BAD_MINIMUM_BALANCE);

        require(address(this).balance >=
                    balanceThreshold +
                    DePoolLib.DEPOOL_CONSTRUCTOR_FEE +
                    2 * (DePoolLib.MIN_PROXY_BALANCE + DePoolLib.PROXY_CONSTRUCTOR_FEE),
                Errors.BAD_MINIMUM_BALANCE);

        tvm.accept();


        for (uint8 i = 0; i < 2; ++i) {
            TvmBuilder b;
            b.store(address(this), i);
            uint256 publicKey = tvm.hash(b.toCell());
            TvmCell data = tvm.buildEmptyData(publicKey);
            TvmCell stateInit = tvm.buildStateInit(proxyCode, data);
            address proxy =
                new DePoolProxyContract{
                    wid: -1,
                    value: DePoolLib.MIN_PROXY_BALANCE + DePoolLib.PROXY_CONSTRUCTOR_FEE,
                    stateInit: stateInit
                }();
            m_proxies.push(proxy);
        }

        m_poolClosed = false;
        m_minStake = minStake;
        m_validatorAssurance = validatorAssurance;
        m_participantRewardFraction = participantRewardFraction;
        m_validatorRewardFraction = validatorRewardFraction;
        (* TODO:delete:  m_associationRewardFraction = associationRewardFraction;*)
        (* TODO:delete:  m_association = association;*)
        m_balanceThreshold = balanceThreshold;
        (, uint32 electionsStartBefore, ,) = roundTimeParams();
        (uint256 curValidatorHash, , uint32 validationEnd) = getCurValidatorData();
        uint256 prevValidatorHash = getPrevValidatorHash();
        bool areElectionsStarted = now >= validationEnd - electionsStartBefore;

        Round r2 = generateRound();
        Round r1 = generateRound();
        Round r0 = generateRound();
        r0.step = RoundStep.Pooling;
        Round preR0 = generateRound();
        (r2.step, r2.completionReason, r2.unfreeze) = (RoundStep.Completed, CompletionReason.FakeRound, 0);
        (r1.step, r1.completionReason, r1.unfreeze) = (RoundStep.WaitingUnfreeze, CompletionReason.FakeRound, 0);
        r1.vsetHashInElectionPhase = areElectionsStarted? curValidatorHash : prevValidatorHash;
        setRound(preR0.id, preR0);
        setRound(r0.id, r0);
        setRound(r1.id, r1);
        setRound(r2.id, r2);
    }


*)



(* Definition addressWid (a: XAddress) := xInt0. *)
Parameter addressWid : XAddress -> XInteger.

Notation "x ->wid" := (do x' ← x; $ (addressWid x')) (at level 20).



(* Definition tvm_buildEmptyData ( a : XInteger256) : LedgerT TvmCell := $xStrNull .
Definition tvm_buildStateInit (x: TvmCell) (c: TvmCell) : LedgerT TvmCell := $xStrNull . *)
Parameter tvm_buildEmptyData : XInteger256  -> TvmCell.
Parameter tvm_buildStateInit : TvmCell -> TvmCell -> TvmCell.


(* constructor(                         (*<<<< очень много изменений <<<<<*)
        uint64 minStake,
        uint64 validatorAssurance,
        TvmCell proxyCode,
        address validatorWallet,

        uint8 participantRewardFraction,

        uint64 minimumBalance
    )
        ValidatorBase(validatorWallet)
        public { *)
(* Check  ( ForIndexed (xListCons xInt1 (xListCons xInt2 xListNil)) do ( fun (i: XInteger) => 
U0! Л_b := $ default ; 
U0! Л_b ->store tvm_address $i;
U0! Л_publicKey := tvm_hash (!! ($ Л_b) ->toCell !!); 
U0! Л_data := tvm_buildEmptyData (!! $ Л_publicKey !!); 
U0! Л_stateInit := tvm_buildStateInit (!!  $xStrNull ,  $Л_data !!);    
U0! Л_proxy := $xInt0 ; 
(↑3 ProxyBase_ι_m_proxies ->push $Л_proxy )                                  
)). *)

Definition DePoolContract_Ф_Constructor6 ( Л_minStake : XInteger64 )
                                         ( Л_validatorAssurance : XInteger64 )   
										                     ( Л_proxyCode :  TvmCell )
                                         ( Л_validatorWallet : XAddress )
                                         ( Л_participantRewardFraction : XInteger8 )
                                         ( Л_balanceThreshold : XInteger64 )										                    
                                        : LedgerT ( XErrorValue True XInteger ) := 
ValidatorBase_Ф_Constructor2 (! $ Л_validatorWallet !) >> 
(* require(address(this).wid == 0, Errors.NOT_WORKCHAIN0); *)
Require2 {{ tvm_address ->wid ?== $ xInt0,  ↑ε7 Errors_ι_NOT_WORKCHAIN0 }} ; 
(*require(msg.pubkey() == tvm.pubkey(), Errors.IS_NOT_OWNER);*) 
Require2 {{ msg_pubkey () ?== tvm_pubkey () ,  ↑ε7 Errors_ι_IS_NOT_OWNER }} ;

(*require(tvm.pubkey() != 0, Errors.CONSTRUCTOR_NO_PUBKEY);*) 
Require2 {{ tvm_pubkey () ?!= $ xInt0 ,  ↑ε7 Errors_ι_CONSTRUCTOR_NO_PUBKEY }} ; 

(*require(minStake >= 1 ton, Errors.BAD_STAKES);*)
Require2 {{ $ Л_minStake ?>= $ x1_ton , ↑ε7 Errors_ι_BAD_STAKES }} ; 

(*require(minStake <= validatorAssurance, Errors.BAD_STAKES);*)
Require2 {{ $ Л_minStake ?<= $ Л_validatorAssurance , ↑ε7 Errors_ι_BAD_STAKES }} ; 
 
(* require(tvm.hash(proxyCode) == PROXY_CODE_HASH, Errors.BAD_PROXY_CODE); *)
Require2 {{ tvm_hash (!! $ Л_proxyCode !!) ?== ↑ε12 DePoolContract_ι_PROXY_CODE_HASH , ↑ε7 Errors_ι_BAD_PROXY_CODE }} ; 

(*require(validatorWallet.isStdAddrWithoutAnyCast(), Errors.VALIDATOR_IS_NOT_STD);*)
Require2 {{ ($ Л_validatorWallet) ->isStdAddrWithoutAnyCast() , ↑ε7 Errors_ι_VALIDATOR_IS_NOT_STD }} ;  

(*
Require2 {{ ($ Л_association) ->isStdAddrWithoutAnyCast() , ↑ε7 Errors_ι_ASSOCIATION_IS_NOT_STD }} ; 
Require2 {{ $ Л_participantRewardFraction ?> $xInt0, ↑ε7 Errors_ι_BAD_PART_REWARD }} ; 
Require2 {{ $ Л_validatorRewardFraction ?> $xInt0, ↑ε7 Errors_ι_BAD_VALID_REWARD }} ; 
Require2 {{ $ Л_participantRewardFraction !+ 
            $ Л_validatorRewardFraction ?<= $xInt100, ↑ε7 Errors_ι_PERCENT_NOT_EQ_100 }} ;
 U0! Л_associationRewardFraction := $xInt100 !- $ Л_participantRewardFraction !- $ Л_validatorRewardFraction ; 
 U0! Л_isFractionZero := $ Л_associationRewardFraction ?== $ xInt0 ; 
 U0! Л_isAddressZero := $ Л_association ?== $ xInt0 ;  
 Require2 {{ $Л_isFractionZero ?== $ Л_isAddressZero, ↑ε7 Errors_ι_BAD_ASSOCIATION_AND_PERCENT }} ; 
 *)

    (* require(participantRewardFraction > 0 && participantRewardFraction < 100, Errors.BAD_PART_REWARD);
       uint8 validatorRewardFraction = 100 -  participantRewardFraction; *)
Require2 {{ ( ( $ Л_participantRewardFraction ) ?> $ xInt0 ) !&  
            ( ( $ Л_participantRewardFraction ) ?< $ xInt100 ) , ↑ε7 Errors_ι_BAD_PART_REWARD }} ;
U0! Л_validatorRewardFraction := $ xInt100 !- $  Л_participantRewardFraction ; 

Require2 {{ $ Л_balanceThreshold ?>= ( ↑ε12 DePoolContract_ι_CRITICAL_THRESHOLD ) , ↑ε7 Errors_ι_BAD_MINIMUM_BALANCE }} ;

 (* require(address(this).balance >=
           balanceThreshold +
               DePoolLib.DEPOOL_CONSTRUCTOR_FEE +
                      2 * (DePoolLib.MIN_PROXY_BALANCE + DePoolLib.PROXY_CONSTRUCTOR_FEE), *)
Require2 {{ tvm_balance () ?>= $Л_balanceThreshold !+ 
                                $xInt2 !* (↑ε9 DePoolLib_ι_MIN_PROXY_BALANCE !+ ↑ε9 DePoolLib_ι_PROXY_CONSTRUCTOR_FEE) , 
                                ↑ε7 Errors_ι_BAD_MINIMUM_BALANCE }} ; 
 (*tvm.accept();*)
 tvm_accept () >> 

(*  for (uint8 i = 0; i < 2; ++i) {
    TvmBuilder b;
    b.store(address(this), i);
    uint256 publicKey = tvm.hash(b.toCell());
    TvmCell data = tvm.buildEmptyData(publicKey);
    TvmCell stateInit = tvm.buildStateInit(proxyCode, data);
    address proxy =
        new DePoolProxyContract{
            wid: -1,
            value: DePoolLib.MIN_PROXY_BALANCE + DePoolLib.PROXY_CONSTRUCTOR_FEE,
            stateInit: stateInit
        }();
    m_proxies.push(proxy);
} *)

( ForIndexed (xListCons xInt1 (xListCons xInt2 xListNil)) do ( fun (i: XInteger) => 
U0! Л_b := $ default ; 
U0! Л_b ->store tvm_address $i;
U0! Л_publicKey := tvm_hash (!! ($ Л_b) ->toCell !!); 
U0! Л_data := tvm_buildEmptyData (!! $ Л_publicKey !!); 
U0! Л_stateInit := tvm_buildStateInit (!!  $Л_proxyCode ,  $Л_data !!);  
U0! Л_proxy := $xInt0 ;  (* new DePoolProxyContract{
                                    wid: -1,
                                    value: DePoolLib.MIN_PROXY_BALANCE + DePoolLib.PROXY_CONSTRUCTOR_FEE,
                                    stateInit: stateInit  }() *)
(↑3 ProxyBase_ι_m_proxies ->push $Л_proxy )                                  
)) >>

(*m_poolClosed = false;*)
(↑12 U1! DePoolContract_ι_m_poolClosed := $ xBoolFalse) >> 

(* m_minStake = minStake; *)
(↑12 U1! DePoolContract_ι_m_minStake := $ Л_minStake) >>

(* m_validatorAssurance = validatorAssurance; *)
(↑12 U1! DePoolContract_ι_m_validatorAssurance := $ Л_validatorAssurance) >>

(* m_participantRewardFraction = participantRewardFraction; *)
(↑12 U1! DePoolContract_ι_m_participantRewardFraction := $ Л_participantRewardFraction) >>

(* m_validatorRewardFraction = validatorRewardFraction; *)
(↑12 U1! DePoolContract_ι_m_validatorRewardFraction := $ Л_validatorRewardFraction) >>

(* (↑12 U1! DePoolContract_ι_m_associationRewardFraction := $ Л_associationRewardFraction) >> *)
(* (↑12 U1! DePoolContract_ι_m_association := $ Л_association) >> *)

(*  m_minimumBalance = minimumBalance; *)
(↑12 U1! DePoolContract_ι_m_balanceThreshold := $ Л_balanceThreshold) >> 


(*(, uint32 electionsStartBefore, ,) = roundTimeParams();*)
U0! {( _ ,  Л_electionsStartBefore )} ??:= ConfigParamsBase_Ф_roundTimeParams  () ;

(*(uint256 curValidatorHash, , uint32 validationEnd) = getCurValidatorData();*)
U0! {( Л_curValidatorHash , _ , Л_validationEnd )} ??:= ConfigParamsBase_Ф_getCurValidatorData () ; 

(* uint256 prevValidatorHash = getPrevValidatorHash(); *)
U0! Л_prevValidatorHash ?:= ConfigParamsBase_Ф_getPrevValidatorHash () ; 

(*bool areElectionsStarted = now >= validationEnd - electionsStartBefore;*)
U0! Л_areElectionsStarted := tvm_now () ?>= $ Л_validationEnd !- $ Л_electionsStartBefore ; 

(*Round r2 = generateRound();*)	  
U0! Л_r2 := DePoolContract_Ф_generateRound () ;  
(*  Round r1 = generateRound(); *)
U0! Л_r1 := DePoolContract_Ф_generateRound () ; 
(* Round r0 = generateRound(); *)
U0! Л_r0 := DePoolContract_Ф_generateRound () ; 
(* r0.step = RoundStep.Pooling; *)
U0! Л_r0 ^^ RoundsBase_ι_Round_ι_step := $ RoundsBase_ι_RoundStepP_ι_Pooling ; 
(* Round preR0 = generateRound(); *)
U0! Л_preR0 := DePoolContract_Ф_generateRound () ; 


(*  (r2.step, r2.completionReason, r2.unfreeze) = (RoundStep.Completed, CompletionReason.FakeRound, 0);*)
U0! {( Л_r2 ^^ RoundsBase_ι_Round_ι_step , Л_r2 ^^ RoundsBase_ι_Round_ι_completionReason , Л_r2 ^^ RoundsBase_ι_Round_ι_unfreeze )} := 
    $ [( RoundsBase_ι_RoundStepP_ι_Completed, RoundsBase_ι_CompletionReasonP_ι_FakeRound, xInt0 )] ; 
(*  (r1.step, r1.completionReason, r1.unfreeze) = (RoundStep.WaitingUnfreeze, CompletionReason.FakeRound, 0); *) 
U0! {( Л_r1 ^^ RoundsBase_ι_Round_ι_step , Л_r1 ^^ RoundsBase_ι_Round_ι_completionReason , Л_r1 ^^ RoundsBase_ι_Round_ι_unfreeze )} := 
    $ [( RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze, RoundsBase_ι_CompletionReasonP_ι_FakeRound, xInt0 )] ; 
(*r1.vsetHashInElectionPhase = areElectionsStarted? curValidatorHash : prevValidatorHash;*)
U0! Л_r1 ^^ RoundsBase_ι_Round_ι_vsetHashInElectionPhase := $ Л_areElectionsStarted ? $ Л_curValidatorHash ::: $ Л_prevValidatorHash; 

(*  setRound(preR0.id, preR0); *)
RoundsBase_Ф_setRound (! $ (Л_preR0 ->> RoundsBase_ι_Round_ι_id) ,  $Л_preR0 !)  >>
(* setRound(r0.id, r0); *)
RoundsBase_Ф_setRound (! $ (Л_r0 ->> RoundsBase_ι_Round_ι_id) ,  $Л_r0 !) >>
(* setRound(r1.id, r1); *)
RoundsBase_Ф_setRound (! $ (Л_r1 ->> RoundsBase_ι_Round_ι_id) ,  $Л_r1 !) >>
(* setRound(r2.id, r2); *)
RoundsBase_Ф_setRound (! $ (Л_r2 ->> RoundsBase_ι_Round_ι_id) ,  $Л_r2 !) .


(* TODO: new function
function setLastRoundInfo(Round round) internal {
>         LastRoundInfo info = LastRoundInfo({
>             supposedElectedAt: round.supposedElectedAt,
>             participantRewardFraction: m_participantRewardFraction,
>             validatorRewardFraction: m_validatorRewardFraction,
>             participantQty: round.participantQty,
>             roundStake: round.stake,
>             validatorWallet: m_validatorWallet,
>             validatorPubkey: tvm.pubkey(),
>             validatorAssurance: m_validatorAssurance,
>             reward: round.grossReward,
>             reason: uint8(round.completionReason),
>             isDePoolClosed: m_poolClosed
>         });
>         lastRoundInfo[false] = info;
>     } *)

(* Parameter DePoolContract_Ф_setLastRoundInfo : RoundsBase_ι_Round -> LedgerT True. *)
Definition DePoolContract_Ф_setLastRoundInfo ( Л_round : RoundsBase_ι_Round ) :
                                                        LedgerT True :=
U0! Л_info := {|| 
     DePool_ι_LastRoundInfo_ι_supposedElectedAt :=         $ Л_round ->> RoundsBase_ι_Round_ι_supposedElectedAt ,
     DePool_ι_LastRoundInfo_ι_participantRewardFraction := ( ↑12 D2! DePoolContract_ι_m_participantRewardFraction ) ,
     DePool_ι_LastRoundInfo_ι_validatorRewardFraction :=   ( ↑12 D2! DePoolContract_ι_m_validatorRewardFraction )  ,
     DePool_ι_LastRoundInfo_ι_participantQty :=            $ Л_round ->> RoundsBase_ι_Round_ι_participantQty  ,
     DePool_ι_LastRoundInfo_ι_roundStake :=                $ Л_round ->> RoundsBase_ι_Round_ι_stake  ,
     DePool_ι_LastRoundInfo_ι_validatorWallet :=           ( ↑2 D2! ValidatorBase_ι_m_validatorWallet ) ,
     DePool_ι_LastRoundInfo_ι_validatorPubkey :=           tvm_pubkey () ,
     DePool_ι_LastRoundInfo_ι_validatorAssurance :=        ( ↑12 D2! DePoolContract_ι_m_validatorAssurance ) ,
     DePool_ι_LastRoundInfo_ι_reward :=                    $ Л_round ->> RoundsBase_ι_Round_ι_grossReward  ,
     DePool_ι_LastRoundInfo_ι_reason :=                    $ Л_round ->> RoundsBase_ι_Round_ι_completionReason ,
     DePool_ι_LastRoundInfo_ι_isDePoolClosed :=            ( ↑12 D2! DePoolContract_ι_m_poolClosed ) 
||} ; 
↑11 U1! RoundsBase_ι_lastRoundInfo [[ $ xBoolFalse ]] := $ Л_info .

(* ↑5 U1! ParticipantBase_ι_m_participants [[ $ Л_addr ]] := $ Л_participant *)
(* 
function _returnChange() private pure {
        msg.sender.transfer(0, false, 64);
    }
*) 
Definition DePoolContract_Ф__returnChange : LedgerT True := 
   ( ( msg_sender () ) ->transfer (! $ xInt0 ,  $ xBoolFalse ,  $ xInt64 !) ) >> 
   return! I.


(* 
function DePoolContract._sendError(uint32 errcode, uint64 comment) private {
        IParticipant(msg.sender).receiveAnswer{value:0, bounce: false, flag: 64}(errcode, comment); 
    } *)

Definition DePoolContract_Ф__sendError ( Л_errcode : XInteger32 )
                                       ( Л_comment : XInteger64 ) 
                                       : LedgerT True := 
U0! Л_addr := msg_sender () ;
sendMessage {| contractAddress  := Л_addr ;
				contractFunction := IParticipant_И_receiveAnswerF Л_errcode Л_comment ;
				contractMessage := {$ {$ {$ default with  messageValue := xInt0 $} 
													with  messageBounce := xBoolFalse $}
													with  messageFlag := xInt64 $}
			|} .



(*     
function startRoundCompleting(Round round, CompletionReason reason) private returns (Round) {
        round.completionReason = reason;
         round.handledStakesAndRewards = 0;
         round.validatorRemainingStake = 0;
         if (round.participantQty == 0) {
            round.step = RoundStep.Completed;
            this.ticktock{value: VALUE_FOR_SELF_CALL, bounce: false}();
         } else {
            round.step = RoundStep.Completing;
            this.completeRound{flag: 1, bounce: false, value: VALUE_FOR_SELF_CALL}(round.id, round.participantQty);
         }

        emit RoundCompleted(toTruncatedRound(round));
        setLastRoundInfo(round);

        return round; }	} *)

(* ↑17 D1! (D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2) ^^ RoundsBase_ι_Round_ι_id *)


Definition DePoolContract_Ф_startRoundCompleting ( Л_round : RoundsBase_ι_Round ) 
                                                 ( Л_reason : RoundsBase_ι_CompletionReason )  
                                                  : LedgerT RoundsBase_ι_Round := 
( ↑17 U1! LocalState_ι_startRoundCompleting_Л_round := $ Л_round ) >>
                (* round.completionReason = reason; *)
( ↑17 U1! LocalState_ι_startRoundCompleting_Л_round ^^ RoundsBase_ι_Round_ι_completionReason := $ Л_reason ) >>
            (* round.handledStakesAndRewards = 0; *)
( ↑17 U1! LocalState_ι_startRoundCompleting_Л_round ^^ RoundsBase_ι_Round_ι_handledStakesAndRewards := $ xInt0 ) >>
            (* round.validatorRemainingStake = 0; *)
( ↑17 U1! LocalState_ι_startRoundCompleting_Л_round ^^ RoundsBase_ι_Round_ι_validatorRemainingStake := $ xInt0 ) >>

( If ( ↑17 D2! LocalState_ι_startRoundCompleting_Л_round ^^ RoundsBase_ι_Round_ι_participantQty ?== $ xInt0 )
then {
                (* round.step = RoundStep.Completed; *)
  ( ↑17 U1! LocalState_ι_startRoundCompleting_Л_round ^^ RoundsBase_ι_Round_ι_step 
                        := $ RoundsBase_ι_RoundStepP_ι_Completed ) >> 
                (* this.ticktock{value: VALUE_FOR_SELF_CALL, bounce: false}(); *)
 ( ->sendMessage {||
contractFunction := $ DePoolContract_Ф_ticktockF ,
contractMessage := {||  messageValue := ↑ε12 DePoolContract_ι_VALUE_FOR_SELF_CALL ,
                        messageBounce := $ xBoolFalse ||} ||} )
}
else {
                (* round.step = RoundStep.Completing; *)
  ( ↑17 U1! LocalState_ι_startRoundCompleting_Л_round ^^ RoundsBase_ι_Round_ι_step 
                        := $ RoundsBase_ι_RoundStepP_ι_Completing ) >> 
                (* this.completeRound{flag: 1, bounce: false, value: VALUE_FOR_SELF_CALL}(round.id, round.participantQty); *)
 ( ->sendMessage {||
contractFunction := DePoolContract_Ф_completeRoundF (!! 
     ( ↑17 D1! ( D2! LocalState_ι_startRoundCompleting_Л_round ) ^^ RoundsBase_ι_Round_ι_id ) ,
     ( ↑17 D1! ( D2! LocalState_ι_startRoundCompleting_Л_round ) ^^ RoundsBase_ι_Round_ι_participantQty ) !!) ,
contractMessage := {||  messageValue := ↑ε12 DePoolContract_ι_VALUE_FOR_SELF_CALL ,
                        messageBounce := $ xBoolFalse ,
                        messageFlag   := $ xInt1 ||} ||} )
} ) >>
                (* emit RoundCompleted(toTruncatedRound(round)); *)
(->emit (RoundCompleted (!!  RoundsBase_Ф_toTruncatedRound (! ↑ε17 LocalState_ι_startRoundCompleting_Л_round !)  !!))) >>
          (* setLastRoundInfo(round); *)
      DePoolContract_Ф_setLastRoundInfo (! ↑ε17 LocalState_ι_startRoundCompleting_Л_round !) >> 
                (* return round; *)
   ↑ε17 LocalState_ι_startRoundCompleting_Л_round .

(*     


function cutWithdrawalValue(InvestParams p) private view returns (optional(InvestParams), uint64) {
        uint64 periodQty = (uint64(now) - p.lastWithdrawalTime) / p.withdrawalPeriod;
        uint64 withdrawal = math.min(periodQty * p.withdrawalValue, p.amount);
        p.amount -= withdrawal;
        if (p.amount < m_minStake) {
            withdrawal += p.amount;
            p.amount = 0;
        }
        p.lastWithdrawalTime += periodQty * p.withdrawalPeriod;
(*<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<*)
        optional(InvestParams) opt;
        opt.set(p);
        return (opt, withdrawal);
    }
*)

Unset Typeclasses Iterative Deepening.
Set Typeclasses Depth 10.


									 
Definition DePoolContract_Ф_cutWithdrawalValue ( Л_p : RoundsBase_ι_InvestParams ) 
                                               : LedgerT ( (XMaybe RoundsBase_ι_InvestParams) # XInteger64 ) := 
U0! Л_periodQty := ( tvm_now () !- ↑11 D0! Л_p ^^ RoundsBase_ι_InvestParams_ι_lastWithdrawalTime ) !/ ↑11 D0! Л_p ^^ RoundsBase_ι_InvestParams_ι_withdrawalPeriod ; 
U0! Л_withdrawal := math->min2 (! $ Л_periodQty !* ↑11 D0! Л_p ^^ RoundsBase_ι_InvestParams_ι_withdrawalValue , ↑11 D0! Л_p ^^ RoundsBase_ι_InvestParams_ι_amount !) ; 
U0! Л_amount := ↑11 D0! Л_p ^^ RoundsBase_ι_InvestParams_ι_amount !- $ Л_withdrawal ;  
U0! Л_p ^^ RoundsBase_ι_InvestParams_ι_amount := $ Л_amount ; 

( ↑17 U1! LocalState_ι_cutWithdrawalValueAndActivateStake_Л_withdrawal := $ Л_withdrawal ) >>
( ↑17 U1! LocalState_ι_cutWithdrawalValueAndActivateStake_Л_p := $ Л_p ) >> 

( If ( ( ↑11 D0! Л_p ^^ RoundsBase_ι_InvestParams_ι_amount ) ?< ( ↑ε12 DePoolContract_ι_m_minStake ) ) 
then { 
        ( ↑17 U1! LocalState_ι_cutWithdrawalValueAndActivateStake_Л_withdrawal !+= 
             D1! ( D2! LocalState_ι_cutWithdrawalValueAndActivateStake_Л_p) ^^ RoundsBase_ι_InvestParams_ι_amount ) >>
         ( ↑17 U1! LocalState_ι_cutWithdrawalValueAndActivateStake_Л_p ^^ RoundsBase_ι_InvestParams_ι_amount               
           := $ xInt0 ) 
} ) >>  

(* p.lastWithdrawalTime += periodQty * p.withdrawalPeriod; *)
   ( ↑17 U1! LocalState_ι_cutWithdrawalValueAndActivateStake_Л_p ^^ RoundsBase_ι_InvestParams_ι_lastWithdrawalTime 
       !+= $ Л_periodQty !* ( D2! LocalState_ι_cutWithdrawalValueAndActivateStake_Л_p  ^^ RoundsBase_ι_InvestParams_ι_withdrawalPeriod ) ) >> 
   (*  optional(InvestParams) opt;
        opt.set(p);
        return (opt, withdrawal); *)
   U0! Л_opt := $ default ;
   U0! Л_opt ->set (↑17 D2! LocalState_ι_cutWithdrawalValueAndActivateStake_Л_p ) ;
   U0! Л_withdrawal := ↑ε17 LocalState_ι_cutWithdrawalValueAndActivateStake_Л_withdrawal ;
		return! [( Л_opt, Л_withdrawal )].	

Set Typeclasses Iterative Deepening.		

(*    
function _returnOrReinvestForParticipant( 
        Round round2,
        Round round0,
        address addr,
        StakeValue stakes,
        bool isValidator
    ) private returns (Round, Round) {
        uint64 stakeSum = stakeSum(stakes);
        bool stakeIsLost = round2.completionReason == CompletionReason.ValidatorIsPunished;
        optional((* DePoolLib. *)Participant) optParticipant = fetchParticipant(addr); 
        require(optParticipant.hasValue(), InternalErrors.ERROR511);
        (* DePoolLib. *)Participant participant = optParticipant.get();
        --participant.roundQty;
        uint64 lostFunds = stakeIsLost? (round2.stake - round2.unused) - round2.recoveredStake : 0;

        // upd ordinary stake
        uint64 newStake;
        uint64 reward;
        if (stakeIsLost) {
            if (isValidator) {
                newStake = stakes.ordinary;
                uint64 delta = math.min(newStake, lostFunds);
                newStake -= delta;
                lostFunds -= delta;
                round2.validatorRemainingStake = newStake;
            } else {
                newStake = math.muldiv(
                    round2.unused + round2.recoveredStake - round2.validatorRemainingStake,
                    stakes.ordinary,
                    round2.stake - round2.validatorStake
                );
            }
        } else {
            reward = math.muldiv(stakeSum, round2.rewards, round2.stake);
            participant.reward += reward;
            newStake = stakes.ordinary + reward;
        }
        round2.handledStakesAndRewards += newStake;

        // upd vesting
        optional(InvestParams) newVesting = stakes.vesting;
        if (newVesting.hasValue()) {
            InvestParams params = newVesting.get();
            if (stakeIsLost) {
                InvestParams params = newVesting.get();
                if (isValidator) {
                    uint64 delta = math.min(params.amount, lostFunds);
                    params.amount -= delta;
                    lostFunds -= delta;
                    round2.validatorRemainingStake += params.amount;
                } else {
                    params.amount = math.muldiv(
                        round2.unused + round2.recoveredStake - round2.validatorRemainingStake,
                        params.amount,
                        round2.stake - round2.validatorStake
                    );
                }
               (*  newVesting.set(params); *)
            }
            round2.handledStakesAndRewards += params.amount;
            uint64 withdrawalVesting;
            (* (* (* (* (* (* (newVesting, withdrawalVesting) = cutWithdrawalValue(newVesting.get()); *) *) *) *) *) *)
(newVesting, withdrawalVesting) = cutWithdrawalValue(params);
            newStake += withdrawalVesting;
        }

        // pause stake and newStake
        uint64 attachedValue = 1;
        uint64 curPause = math.min(participant.withdrawValue, newStake);
        attachedValue += curPause;
        participant.withdrawValue -= curPause;
        newStake -= curPause;
        if (newStake < m_minStake) { // whole stake is transferred to the participant
            attachedValue += newStake;
            newStake = 0;
        }

        // upd lock
        optional(InvestParams) newLock = stakes.lock;
        if (newLock.hasValue()) {
            InvestParams params = newLock.get();
            if (stakeIsLost) {
                
                if (isValidator) {
                    uint64 delta = math.min(params.amount, lostFunds);
                    params.amount -= delta;
                    lostFunds -= delta;
                    round2.validatorRemainingStake += params.amount;
                } else {
                    params.amount = math.muldiv(
                        round2.unused + round2.recoveredStake - round2.validatorRemainingStake,
                        params.amount,
                        round2.stake - round2.validatorStake
                    );
                }
               (* (* (* (* (* (* (*  newLock.set(params); *) *) *) *) *) *) *)
            }
            round2.handledStakesAndRewards += newLock.get().amount;
            uint64 withdrawalLock;
            (newLock, withdrawalLock) = cutWithdrawalValue(params);
            if (withdrawalLock != 0) {
                (* newLock.get().owner.transfer(withdrawalLock, false, 1); *)
                params.owner.transfer(withdrawalLock, false, 1);
            }
        }

        if (m_poolClosed) {
            attachedValue += newStake;
            if (newVesting.hasValue()) {
                newVesting.get().owner.transfer(newVesting.get().amount, false, 1);
            }
            if (newLock.hasValue()) {
                newLock.get().owner.transfer(newLock.get().amount, false, 1);
            }
        } else {
            if (newVesting.hasValue() && newVesting.get().amount == 0) newVesting.reset();
            if (newLock.hasValue() && newLock.get().amount == 0) newLock.reset();

            if (!participant.reinvest) {
                attachedValue += newStake;
                newStake = 0;
            }
            (round0, participant) = _addStakes(round0, participant, addr, newStake, newVesting, newLock);
        }

        _setOrDeleteParticipant(addr, participant);
        IParticipant(addr).onRoundComplete{value: attachedValue, bounce: false}(
            round2.id,
            reward,
            stakes.ordinary,
            stakes.vesting.hasValue() ? stakes.vesting.get().amount : 0,
            stakes.lock.hasValue() ? stakes.lock.get().amount : 0,
            participant.reinvest,
            uint8(round2.completionReason)
        );

        return (round0, round2);
    }

*)


Definition DePoolContract_Ф__returnOrReinvestForParticipant ( Л_round2 : RoundsBase_ι_Round )
															                              ( Л_round0 : RoundsBase_ι_Round )
															                              ( Л_addr : XAddress )
															                              ( Л_stakes : RoundsBase_ι_StakeValue ) 
                                                            ( Л_isValidator : XBool )
                                                  : LedgerT ( XErrorValue ( RoundsBase_ι_Round # RoundsBase_ι_Round ) XInteger ) := 
(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round2 := $ Л_round2) >> 
(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round0 := $ Л_round0) >>
U0! Л_stakeSum := RoundsBase_Ф_stakeSum (! $ Л_stakes !) ;
U0! Л_stakeIsLost := ($ (Л_round2 ->> RoundsBase_ι_Round_ι_completionReason) ) ?== ($ RoundsBase_ι_CompletionReasonP_ι_ValidatorIsPunished) ; 		
U0! Л_optParticipant := ParticipantBase_Ф_fetchParticipant (! $ Л_addr !) ; 
Require {{ $ Л_optParticipant ->hasValue , ↑8 D2! InternalErrors_ι_ERROR511 }} ; 

(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_participant := $ Л_optParticipant ->get) >> 
(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_participant ^^ DePoolLib_ι_Participant_ι_roundQty !--) >>

( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds := $ Л_stakeIsLost ? 
   ( D1! (D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2) ^^ RoundsBase_ι_Round_ι_stake !- 
     D1! (D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2) ^^ RoundsBase_ι_Round_ι_unused ) !- 
     D1! (D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2) ^^ RoundsBase_ι_Round_ι_recoveredStake 
                              ::: $ xInt0 ) 
>> 
(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake := $default) >>
(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_reward := $default) >>

(
	If ($ Л_stakeIsLost) then {
   ( If ( $ Л_isValidator ) 
     then {
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake := $ ( Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary ) ) >>  
           U0! Л_delta := math->min2 (! ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake ,
                                         ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds !) ; 
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake !-= $ Л_delta ) >>  
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds !-= $ Л_delta ) >> 
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ^^ RoundsBase_ι_Round_ι_validatorRemainingStake
                       := D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake )
     } 
     else {
         (* round2.unused + round2.recoveredStake - round2.validatorRemainingStake, *)
		(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake := math->muldiv (! 
                D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_unused !+
                D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_recoveredStake !-
                D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_validatorRemainingStake, 
				$ Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary , 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_stake !-
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_validatorStake !))
} )
	} else {
        (* reward = math.muldiv(stakeSum, round2.rewards, round2.stake);
            participant.reward += reward;
            newStake = stakes.ordinary + reward; *)
    (↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_reward := math->muldiv (! $ Л_stakeSum , 
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_rewards ,
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_stake !) ) >>
		(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_participant ^^ DePoolLib_ι_Participant_ι_reward 
                           !+=  D2! LocalState_ι__returnOrReinvestForParticipant_Л_reward ) >>
		(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake := $ ( Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary ) !+ 
                                                                            (D2! LocalState_ι__returnOrReinvestForParticipant_Л_reward))
	}
) >> 
( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ^^  RoundsBase_ι_Round_ι_handledStakesAndRewards 
  !+= D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake ) >>
 
(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting := 
                 $ ( Л_stakes ->> RoundsBase_ι_StakeValue_ι_vesting ) ) >> (* $ [( default , default )]. *) 

( If ( ( ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting ) ->hasValue ) 
then
{ (
              (* InvestParams params = newVesting.get(); *)
  (↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_params := 
             ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting ) ->get ) >>
	If ($ Л_stakeIsLost) then {
  
   ( If ( $ Л_isValidator ) 
     then {
           U0! Л_delta := math->min2 (! ↑17 D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params ) ^^ RoundsBase_ι_InvestParams_ι_amount ,
                                         ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds !) ; 
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_params ^^ 
                                             RoundsBase_ι_InvestParams_ι_amount !-= $ Л_delta ) >>  
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds !-= $ Л_delta ) >> 
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ^^ RoundsBase_ι_Round_ι_validatorRemainingStake
                       !+= D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params )
                                            ^^ RoundsBase_ι_InvestParams_ι_amount )
     } 
     else {
		( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_params ^^ 
                                             RoundsBase_ι_InvestParams_ι_amount := math->muldiv (! 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_unused !+
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_recoveredStake !-
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_validatorRemainingStake
              , 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params )
                                            ^^ RoundsBase_ι_InvestParams_ι_amount , 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_stake !-
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_validatorStake !) )
} ) 
	}  ) >>
                       (* round2.handledStakesAndRewards += params.amount; *)
  ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ^^ RoundsBase_ι_Round_ι_handledStakesAndRewards  !+=
      ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params ^^ RoundsBase_ι_InvestParams_ι_amount ) ) >>
  U0! Л_withdrawalVesting := $ default ;
                       (*  (newVesting, withdrawalVesting) = cutWithdrawalValue(params); *)
  U0! {( Л_newVesting , Л_withdrawalVesting )} := DePoolContract_Ф_cutWithdrawalValue 
                              (! ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_params !) ;

  ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting := $ Л_newVesting ) >>
  ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake !+= $ Л_withdrawalVesting ) 
} )

>> (* $ [( default , default )]. *)

(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue := $ xInt1) >>
(* uint64 curPause = math.min(participant.withdrawValue, newStake); *)
U0! Л_curPause := math->min2 (! (D1! (↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_participant) ^^ DePoolLib_ι_Participant_ι_withdrawValue) ,
								(↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake) !) ;
(* attachedValue += curPause; *)
( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue !+= $Л_curPause ) >>
(* participant.withdrawValue -= curPause; *)
( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_participant ^^ DePoolLib_ι_Participant_ι_withdrawValue !-= 
                                 $Л_curPause ) >>
(* newStake -= curPause; *)
( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake !-= $Л_curPause ) >>
(* if (newStake < m_minStake) { // whole stake is transferred to unused
	attachedValue += newStake;
	newStake = 0;
} *)
( If ( ( ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake ) ?< 
                                          (↑12 D2! DePoolContract_ι_m_minStake ) ) then {
	( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue !+= 
                           D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake ) >>
	( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake := $xInt0 )
} ) >> (* $ [( default , default )]. *)


(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newLock := 
                 $ ( Л_stakes ->> RoundsBase_ι_StakeValue_ι_lock ) ) >> (* $ [( default , default )]. *) 

( If ( ( ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock ) ->hasValue )
then
{ (
                                   (* InvestParams params = newLock.get(); *)
  (↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_params := 
             ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock ) ->get ) >>
	If ($ Л_stakeIsLost) then {
  
   ( If ( $ Л_isValidator ) 
     then {
           U0! Л_delta := math->min2 (! ↑17 D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params ) ^^ RoundsBase_ι_InvestParams_ι_amount ,
                                         ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds !) ; 
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_params ^^ 
                                             RoundsBase_ι_InvestParams_ι_amount !-= $ Л_delta ) >>  
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds !-= $ Л_delta ) >> 
           ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ^^ RoundsBase_ι_Round_ι_validatorRemainingStake
                       !+= D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params )
                                            ^^ RoundsBase_ι_InvestParams_ι_amount )
     } 
     else {
		( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_params ^^ 
                                             RoundsBase_ι_InvestParams_ι_amount := math->muldiv (! 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_unused !+
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_recoveredStake !-
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_validatorRemainingStake
              , 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params )
                                            ^^ RoundsBase_ι_InvestParams_ι_amount , 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_stake !-
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^  RoundsBase_ι_Round_ι_validatorStake !) )
} ) 
	}  ) >>
                      (*********round2.handledStakesAndRewards += params.amount;************)
  ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ^^ RoundsBase_ι_Round_ι_handledStakesAndRewards !+=
  ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params ^^ RoundsBase_ι_InvestParams_ι_amount ) ) >>

  U0! Л_withdrawalLock := $ default ;
                      (* (newLock, withdrawalLock) = cutWithdrawalValue(params); *************)
  U0! {( Л_newLock , Л_withdrawalLock )} := DePoolContract_Ф_cutWithdrawalValue 
             (! ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_params !) ;
  ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newLock := $ Л_newLock ) >>
  (If  ( $ Л_withdrawalLock ?!= $xInt0 ) then {
                      (* params.owner.transfer(withdrawalLock, false, 1); *)
   ( D1! ( ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_params ) ^^ RoundsBase_ι_InvestParams_ι_owner ) ->transfer 
            (! $ Л_withdrawalLock  , $xBoolFalse, $ xInt1 !)
     } ) 
} )  >>
(* if (m_poolClosed) {
	attachedValue += newStake;
	if (newVesting.hasValue()) {
		newVesting.get().owner.transfer(newVesting.get().amount, false, 1);
	}
	if (newLock.hasValue()) {
		newLock.get().owner.transfer(newLock.get().amount, false, 1);
	}
} else {
	if (newVesting.hasValue() && newVesting.get().amount == 0) newVesting.reset();
	if (newLock.hasValue() && newLock.get().amount == 0) newLock.reset();

	if (!participant.reinvest) {
		attachedValue += newStake;
		newStake = 0;
	}
	(round0, participant) = _addStakes(round0, participant, addr, newStake, newVesting, newLock);
} *)

(If (↑12 D2! DePoolContract_ι_m_poolClosed) then { 
	(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue !+= D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake) >>
	(If ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting) ->hasValue) then { 
	(D1! ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting) ->get) ^^ RoundsBase_ι_InvestParams_ι_owner ) ->transfer 
                                (! D1! ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting) ->get) ^^ RoundsBase_ι_InvestParams_ι_amount , $xBoolFalse, $ xInt1 !)
	}) >>
	(If ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock) ->hasValue) then { 
	(D1! ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock) ->get) ^^ RoundsBase_ι_InvestParams_ι_owner ) ->transfer 
            (! D1! ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock) ->get) ^^ RoundsBase_ι_InvestParams_ι_amount , $xBoolFalse, $ xInt1 !)
    }) 
 } else { 
	(If ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting) ->hasValue) !& 
		(D1! ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting) ->get) ^^ RoundsBase_ι_InvestParams_ι_amount ?== $xInt0)
	then { 
		 ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting ->reset 
	}) >>
	(If ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock) ->hasValue) !& 
		(D1! ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock) ->get) ^^ RoundsBase_ι_InvestParams_ι_amount ?== $xInt0)
	then { 
		↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newLock ->reset 
	}) >>
	(If (D1! (↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_participant) ^^ DePoolLib_ι_Participant_ι_reinvest) then { 
		(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue !+= D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake) >>
		(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake := $xInt0)
	}) >>
	(↑↑17 U2! {( LocalState_ι__returnOrReinvestForParticipant_Л_round0, 
			    LocalState_ι__returnOrReinvestForParticipant_Л_participant )} := RoundsBase_Ф__addStakes (! (↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_round0) , 
				(↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_participant) ,
				$Л_addr ,
				(↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake) , 
				(↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting) ,
				(↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock)   !) )
 
 }) >>
 (* _setOrDeleteParticipant(addr, participant); *)
 ParticipantBase_Ф__setOrDeleteParticipant (! $Л_addr , (↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_participant)  !) >>
(* IParticipant(addr).onRoundComplete{value: attachedValue, bounce: false}(
	completedRound.id,
	reward,
	stakes.ordinary,
	stakes.vesting.hasValue() && stakes.vesting.get().isActive? stakes.vesting.get().amount : 0,
	stakes.lock.hasValue() && stakes.lock.get().isActive? stakes.lock.get().amount : 0,
	participant.reinvest,
	uint8(completedRound.completionReason)
); *)
 ( ->sendMessage {|| contractAddress := $ Л_addr ,
			   contractFunction :=  IParticipant_И_onRoundCompleteF (!! ↑17 D1! (D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2) ^^ RoundsBase_ι_Round_ι_id ,
																	   ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_reward ,
																	   $ Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary ,
																	   (($ Л_stakes ->> RoundsBase_ι_StakeValue_ι_vesting) ->hasValue ) ? 
																			  (D1! (($ Л_stakes ->> RoundsBase_ι_StakeValue_ι_vesting) ->get) ^^ RoundsBase_ι_InvestParams_ι_amount) ::: $xInt0, 
																	   (($ Л_stakes ->> RoundsBase_ι_StakeValue_ι_lock) ->hasValue ) ? 
																			  (D1! (($ Л_stakes ->> RoundsBase_ι_StakeValue_ι_lock) ->get) ^^ RoundsBase_ι_InvestParams_ι_amount) ::: $xInt0 ,
																	   D1! (↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_participant) ^^ DePoolLib_ι_Participant_ι_reinvest , 
																	   (completionReason2XInteger (!! ↑17 D1! (D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2) ^^ RoundsBase_ι_Round_ι_completionReason !!) ) 
			                                                          !!) ,
			   contractMessage := {|| messageValue := ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue , 
			                          messageBounce := $xBoolFalse ||} ||} ) >> 
(*  return (round0, round2); *)
 return# ( ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_round0 , 
           ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ).


(*     
function _returnOrReinvest(Round round2, uint8 chunkSize) private returns (Round) {
        tvm.accept();
                                     
        Round round0 = getRound0();
        uint startIndex = 0;
        if (!round2.isValidatorStakeCompleted) {
            round2.isValidatorStakeCompleted = true;
            optional(StakeValue) optStake = round2.stakes.fetch(m_validatorWallet);
            if (optStake.hasValue()) {
                StakeValue stake = optStake.get();
                startIndex = 1;
                delete round2.stakes[m_validatorWallet];
                (round0, round2) = _returnOrReinvestForParticipant(round2, round0, m_validatorWallet, stake, true);
            }
        }

        for (uint i = startIndex; i < chunkSize && !round2.stakes.empty(); ++i) {
            (*TODO:old: (address addr, StakeValue stake) = round2.stakes.delMin(); *)
            (*TODO:new*)(address addr, StakeValue stake) = round2.stakes.delMin().get();
            (round0, round2) = _returnOrReinvestForParticipant(round2, round0, addr, stake, false);
        }

        setRound0(round0);
        if (round2.stakes.empty()) {
            round2.step = RoundStep.Completed;
            this.ticktock{value: VALUE_FOR_SELF_CALL, bounce: false}();
        }
        return round2;
    }

 *)

(* Notation " 'U1!' 'delMin' m  ^^ p " := (do m' ← ε m; let kv := xProdFst (hmapMin (m' ->> p)) in modify (fun r => {$ r with m := {$ m' with p := (m'->>p) ->delete (xProdFst kv) $} $}) >> $ kv)
                                  (at level 33, right associativity, m at level 50): solidity_scope.
 *)


Definition DePoolContract_Ф__returnOrReinvest ( Л_round2 : RoundsBase_ι_Round )
                                              ( Л_chunkSize : XInteger8 ) 
                                              : LedgerT ( XErrorValue RoundsBase_ι_Round XInteger ) 
											  :=    
(*init*)
( ↑17 U1! LocalState_ι__returnOrReinvest_Л_round2     := $ Л_round2 ) >> 
( ↑17 U1! LocalState_ι__returnOrReinvest_Л_chunkSize := $ Л_chunkSize ) >> 
(*tvm.accept();*)
tvm_accept ()  >>  
        (* Round round0 = getRound0(); *)
( ↑↑17 U2!  LocalState_ι__returnOrReinvest_Л_round0     := RoundsBase_Ф_getRound0 () ) >>
(*        uint startIndex = 0;    *)
(↑↑17 U2! LocalState_ι__returnOrReinvest_Л_startIndex := $ xInt0 ) >>
          (*if (!round2.isValidatorStakeCompleted) {
                      round2.isValidatorStakeCompleted = true;
                      optional(StakeValue) optStake = round2.stakes.fetch(m_validatorWallet);
                      if (optStake.hasValue()) {
                          StakeValue stake = optStake.get();
                          startIndex = 1;
                          delete round2.stakes[m_validatorWallet]; 
                          (round0, round2) = _returnOrReinvestForParticipant(round2, round0, m_validatorWallet, stake, true);
                      } 
                  }*) 
 
(*         if (!round2.isValidatorStakeCompleted) { *) 
If!! ( !¬ ( ↑17 D1! ( D2! LocalState_ι__returnOrReinvest_Л_round2 ) ^^ RoundsBase_ι_Round_ι_isValidatorStakeCompleted ) )
then 
{ (*          round2.isValidatorStakeCompleted = true; optional(StakeValue) optStake = round2.stakes.fetch(m_validatorWallet); *)
    ( ↑17 U1!  LocalState_ι__returnOrReinvest_Л_round2 ^^ RoundsBase_ι_Round_ι_isValidatorStakeCompleted := $ xBoolTrue ) >>
    U0! Л_optStake := (D1! (↑17 D2! LocalState_ι__returnOrReinvest_Л_round2 ^^ RoundsBase_ι_Round_ι_stakes) 
                 ->fetch  ( ↑2 D2! ValidatorBase_ι_m_validatorWallet ) ) ; 
   (*         if (optStake.hasValue()) { *)
     If! ( ( $ Л_optStake ) ->hasValue ) 
     then   
     {
       (*     StakeValue stake = optStake.get(); *) 
       U0! Л_stake := ( $ Л_optStake ) ->get ; 
       (*     startIndex = 1; *)  
       ( ↑17 U1! LocalState_ι__returnOrReinvest_Л_startIndex := $ xInt1 ) >>
       (*     delete round2.stakes[m_validatorWallet]; *)
       ( ↑↑17 U2!  delete LocalState_ι__returnOrReinvest_Л_round2 ^^ 
                          RoundsBase_ι_Round_ι_stakes [[ ↑2 D2! ValidatorBase_ι_m_validatorWallet ]] ) >>
       (*     (round0, round2) = _returnOrReinvestForParticipant(round2, round0, m_validatorWallet, stake, true); *)
 U0! Л_rounds ?:=
               DePoolContract_Ф__returnOrReinvestForParticipant (!  
                 ↑17 D2! LocalState_ι__returnOrReinvest_Л_round2 ,
                 ↑17 D2! LocalState_ι__returnOrReinvest_Л_round0 , 
                 ↑2 D2! ValidatorBase_ι_m_validatorWallet ,
                 $ Л_stake ,
                 $ xBoolTrue !) ;
( ↑17 U1! {( LocalState_ι__returnOrReinvest_Л_round0 , LocalState_ι__returnOrReinvest_Л_round2 )} := $ Л_rounds )
     } ; $ I  
} ; (* $ (xValue default). *)
 
(* for (uint i = startIndex; i < chunkSize && !round2.stakes.empty(); ++i) {
            (address addr, StakeValue stake) = round2.stakes.delMin().get();
            (round0, round2) = _returnOrReinvestForParticipant(round2, round0, addr, stake, false);
        } *)

do _ ← ( WhileE ( ( ↑17 D2! LocalState_ι__returnOrReinvest_Л_startIndex ?< $ Л_chunkSize ) !& 
     ( !¬ ( ( ↑17 D2! LocalState_ι__returnOrReinvest_Л_round2  ^^ RoundsBase_ι_Round_ι_stakes) ->empty ) ) )
do 
( 
 U0! {( Л_addr , Л_stake)} :=  ↑17 U1! delMin LocalState_ι__returnOrReinvest_Л_round2 ^^ RoundsBase_ι_Round_ι_stakes ;
 (* TODO: need ->get *)  
 (* U0! {( Л_addr , Л_stake)} := ( ↑17 U1! delMin LocalState_ι__returnOrReinvest_Л_round2 ^^ RoundsBase_ι_Round_ι_stakes ) ->get ; *)

DePoolContract_Ф__returnOrReinvestForParticipant (!  
                 ↑17 D2! LocalState_ι__returnOrReinvest_Л_round2 ,
                 ↑17 D2! LocalState_ι__returnOrReinvest_Л_round0 , 
                 $ Л_addr ,
                 $ Л_stake ,
                 $ xBoolFalse !) >>=
fun ea => xErrorMapDefaultF (fun a => (↑17 U1! {( LocalState_ι__returnOrReinvest_Л_round0 , LocalState_ι__returnOrReinvest_Л_round2 )} := $ a ) >> continue! (xValue I)) 
                    ea (fun er => break! (xError er)))) >>= 
        fun r => return! (xProdSnd r) ?; 
 (* return! default.  *) 
 
        (* setRound0(round0); *)
 ( RoundsBase_Ф_setRound0 (! ↑17 D2! LocalState_ι__returnOrReinvest_Л_round0 !) ) >>
         (* if (round2.stakes.empty()) {
            round2.step = RoundStep.Completed;
            this.ticktock{value: VALUE_FOR_SELF_CALL, bounce: false}();   } *)
 ( If ( ( ↑17 D2! LocalState_ι__returnOrReinvest_Л_round2  ^^ RoundsBase_ι_Round_ι_stakes ) ->empty )
 then
{
	(↑17 U1! LocalState_ι__returnOrReinvest_Л_round2 ^^ RoundsBase_ι_Round_ι_step := 
                                             $ RoundsBase_ι_RoundStepP_ι_Completed )  >>

          ->sendMessage {|| 
               contractFunction := $ DePoolContract_Ф_ticktockF  ,
			   contractMessage := {||  messageValue := ↑12 D2!  DePoolContract_ι_VALUE_FOR_SELF_CALL , 
			   						   messageBounce := $ xBoolFalse||} ||}  
        } ) >> 
(*return round2;*)
( ↑17 D2! LocalState_ι__returnOrReinvest_Л_round2 ).


    
(*    function sendAcceptAndReturnChange128(uint64 fee) private {
        tvm.rawReserve(address(this).balance - fee, 0);
        IParticipant(msg.sender).receiveAnswer{value: 0, bounce: false, flag: 128}(STATUS_SUCCESS, 0);
    } *)


Parameter tvm_rawReserve : XInteger64 -> XInteger -> LedgerT True.    
Parameter xInt128 : XInteger.

Definition DePoolContract_Ф_sendAcceptAndReturnChange128 (Л_fee : XInteger64) : LedgerT True :=
    tvm_rawReserve (! tvm_balance () ,  $xInt0 !) >> 
    ->sendMessage {|| contractAddress  := msg_sender () ,
				      contractFunction := IParticipant_И_receiveAnswerF  (!!  ↑ε12 DePoolContract_ι_STATUS_SUCCESS , $xInt0 !!) ,
				      contractMessage := {|| messageValue := $ xInt0 ,
											 messageBounce := $ xBoolFalse ,
                                             messageFlag := $ xInt128 ||} ||}.
                                             
(* function sendAcceptAndReturnChange() private {
    IParticipant(msg.sender).receiveAnswer{value: 0, bounce: false, flag: 64}(STATUS_SUCCESS, 0);
} *)                                             


Definition DePoolContract_Ф_sendAcceptAndReturnChange : LedgerT True :=
    ->sendMessage {|| contractAddress  := msg_sender () ,
				      contractFunction := IParticipant_И_receiveAnswerF  (!!  ↑ε12 DePoolContract_ι_STATUS_SUCCESS , $xInt0 !!) ,
				      contractMessage := {|| messageValue := $ xInt0 ,
											 messageBounce := $ xBoolFalse ,
                                             messageFlag := $ xInt64 ||} ||}.

    
(* 
function addOrdinaryStake(uint64 stake) public  { 
        require(msg.sender != address(0), Errors.IS_EXT_MSG);
                                         (*<<<<<<<<<<<<<<< очень много изменений <<<<<<<<<*)
        if (m_poolClosed) {
            return _sendError(STATUS_DEPOOL_CLOSED, 0);
        }

        uint64 msgValue = uint64(msg.value);
        if (msgValue < uint(stake) + STAKE_FEE) {
            return _sendError(STATUS_FEE_TOO_SMALL, STAKE_FEE);
        }
        uint64 fee = msgValue - stake;
        if (stake < m_minStake) {
            return _sendError(STATUS_STAKE_TOO_SMALL, m_minStake);
        }

        DePoolLib.Participant participant = getOrCreateParticipant(msg.sender);
        Round round = getRound0();
        optional(InvestParams) empty;
        (round, participant) = _addStakes(round, participant, msg.sender, stake, empty, empty);
        setRound0(round);
        _setOrDeleteParticipant(msg.sender, participant);

        sendAcceptAndReturnChange128(fee);
    }

    } *)

Definition DePoolContract_Ф_addOrdinaryStake' ( Л_stake : XInteger64 ) : LedgerT ( XErrorValue (XValueValue True) XInteger ) := 
 Require {{ msg_sender () ?!= $ xInt0 , ↑7 D2! Errors_ι_IS_EXT_MSG }} ;
 (*if (m_poolClosed) { return _sendError(STATUS_DEPOOL_CLOSED, 0); } *)
 If!! ( ↑12 D2! DePoolContract_ι_m_poolClosed ) then {  
     DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_DEPOOL_CLOSED , $ xInt0 !) >>=
     fun x => return! (xError x)  } ; 
 (* uint64 msgValue = uint64(msg.value); *)
 U0! Л_msgValue :=  msg_value () ; 
 (* if (msgValue < uint(stake) + STAKE_FEE) {return _sendError(STATUS_FEE_TOO_SMALL, STAKE_FEE);} *)
 If!! ( $ Л_msgValue ?< $ Л_stake !+ ↑12 D2! DePoolContract_ι_STAKE_FEE ) then { 
     DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_FEE_TOO_SMALL , ↑ε12 DePoolContract_ι_STAKE_FEE !) >>=
     fun x => return! (xError x)  } ; 

 (* uint64 fee = msgValue - stake; *)
 U0! Л_fee := $ Л_msgValue !- $ Л_stake ;
 (* if (stake < m_minStake) {return _sendError(STATUS_STAKE_TOO_SMALL, m_minStake);} *)
 If! ( $ Л_stake ?< ↑12 D2! DePoolContract_ι_m_minStake ) then { 
     DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_STAKE_TOO_SMALL , ↑ε12  DePoolContract_ι_m_minStake !) >>=
     fun x => return! (xError x) } ;

 (*DePoolLib.Participant participant = getOrCreateParticipant(msg.sender);*)
 U0! Л_participant := ParticipantBase_Ф_getOrCreateParticipant (! msg_sender () !) ; 
 (* Round round = getRound0(); *)
 U0! Л_round := RoundsBase_Ф_getRound0 () ;
 (*optional(InvestParams) empty;*)
 U0! Л_empty := $default ; 
 (*(round, participant) = _addStakes(round, participant, msg.sender, stake, empty, empty);*)
 U0! {( Л_round , Л_participant )} :=  RoundsBase_Ф__addStakes (! $ Л_round , 
                                                                  $ Л_participant , 
                                                                    msg_sender () , 
                                                                  $ Л_stake , 
                                                                  $ Л_empty , 
										                          $ Л_empty !) ; 
 (*  setRound0(round); *)
 RoundsBase_Ф_setRound0 (! $ Л_round !) >>
 (* _setOrDeleteParticipant(msg.sender, participant); *)
 (ParticipantBase_Ф__setOrDeleteParticipant (! msg_sender () , $ Л_participant !)) >>
 (* sendAcceptAndReturnChange128(fee); *)
 (DePoolContract_Ф_sendAcceptAndReturnChange128 (! $ Л_fee !)) >>
        return! I.

Definition DePoolContract_Ф_addOrdinaryStake ( Л_stake : XInteger64 ) : LedgerT ( XErrorValue True XInteger ) := 
 do r ← DePoolContract_Ф_addOrdinaryStake' Л_stake ;
return! (xErrorMapDefaultF (xValue ∘ fromValueValue) r xError).

(* 
function addVestingOrLock(uint64 stake, 
                          address beneficiary, uint32 withdrawalPeriod, uint32 totalPeriod, bool isVesting) private {
        if (m_poolClosed) {  
            return _sendError(STATUS_DEPOOL_CLOSED, 0);
        }

        (* TODO: old: require(beneficiary.isStdAddrWithoutAnyCast(), Errors.INVALID_ADDRESS);
        if (beneficiary == address(0)) {
            beneficiary = msg.sender;
        } *)
        (* TODO: new: *)if (!beneficiary.isStdAddrWithoutAnyCast() || beneficiary == address(0))
>       (* TODO: new: *)return _sendError(STATUS_INVALID_ADDRESS, 0);
> 
>       (* TODO: new: *)if (msg.sender == beneficiary)
>       (* TODO: new: *)return _sendError(STATUS_INVALID_BENEFICIARY, 0);
        uint64 msgValue = uint64(msg.value);        

        if (msgValue < uint(stake) + STAKE_FEE) {
            return _sendError(STATUS_FEE_TOO_SMALL, STAKE_FEE);
        }
        uint64 fee = msgValue - stake;

        uint64 halfStake = stake / 2;
        if (halfStake < m_minStake) {
            return _sendError(STATUS_STAKE_TOO_SMALL, 2 * m_minStake);
        }

        if (withdrawalPeriod > totalPeriod) {
            return _sendError(STATUS_WITHDRAWAL_PERIOD_GREATER_TOTAL_PERIOD, 0);
        }

        if (totalPeriod >= 18 * (365 days)) { // ~18 years
            return _sendError(STATUS_TOTAL_PERIOD_MORE_18YEARS, 0);
        }

        if (withdrawalPeriod == 0) {
            return _sendError(STATUS_WITHDRAWAL_PERIOD_IS_ZERO, 0);
        }

        if (totalPeriod % withdrawalPeriod != 0) {
            return _sendError(STATUS_TOTAL_PERIOD_IS_NOT_DIVED_BY_WITHDRAWAL_PERIOD, 0);
        }

        DePoolLib.Participant participant = getOrCreateParticipant(beneficiary);
        if (isVesting) {
            if (participant.haveVesting) {
                return _sendError(STATUS_PARTICIPANT_HAVE_ALREADY_VESTING, 0);
            }
        } else {
            if (participant.haveLock) {
                return _sendError(STATUS_PARTICIPANT_HAVE_ALREADY_LOCK, 0);
            }
        }

        uint64 withdrawalValue = math.muldiv(halfStake, withdrawalPeriod, totalPeriod);
        if (withdrawalValue == 0) {
            return _sendError(STATUS_PERIOD_PAYMENT_IS_ZERO, 0);
        }

        (* TODO: old: InvestParams vestingOrLock = InvestParams({
            amount: halfStake,
            lastWithdrawalTime: uint64(now),
            withdrawalPeriod: withdrawalPeriod,
            withdrawalValue: withdrawalValue,
            owner: msg.sender
        }); *)
        (*TODO: new: *)for (uint i = 0; i < 2; ++i) {
>       (*TODO: new: *)bool isFirstPart = i == 0;
>       (*TODO: new: *)InvestParams vestingOrLock = InvestParams({
>       (*TODO: new: *)amount: isFirstPart? halfStake : stake - halfStake,
>        (*TODO: new: *)lastWithdrawalTime: uint64(now),
>        (*TODO: new: *)withdrawalPeriod: withdrawalPeriod,
>        (*TODO: new: *)withdrawalValue: withdrawalValue,
>        (*TODO: new: *)owner: msg.sender
>        (*TODO: new: *)});
> 
        optional(InvestParams) l;
        if (isVesting) {
            v.set(vestingOrLock);
        } else {
            l.set(vestingOrLock);
        } 
        (*TODO: new:*)Round round = isFirstPart ? getRoundPre0() : getRound0();
>       (*TODO: new:*)(round, participant) = _addStakes(round, participant, beneficiary, 0, v, l);
>       (*TODO: new:*)isFirstPart? setRoundPre0(round) : setRound0(round);
     }
        (* TODO: delete: Round round = getRoundPre0();
                         (round, participant) = _addStakes(round, participant, beneficiary, 0, v, l);
                         setRoundPre0(round);

                         round = getRound0();
                         (round, participant) = _addStakes(round, participant, beneficiary, 0, v, l);
                         setRound0(round); *)

        _setOrDeleteParticipant(beneficiary, participant);
        sendAcceptAndReturnChange128(fee);
    } *)
	
Unset Typeclasses Iterative Deepening.
Set Typeclasses Depth 10.


(*function addVestingOrLock(uint64 stake, 
                          address beneficiary, uint32 withdrawalPeriod, uint32 totalPeriod, bool isVesting) private {*)

(* Check ( DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_DEPOOL_CLOSED , $ xInt0  !) >>=
	fun x => return! ( xError x) ). *)
(* Parameter DePoolContract_Ф_addVestingOrLock' : XInteger64 -> XAddress -> XInteger32 -> XInteger32 -> XBool -> 
                                         LedgerT (XErrorValue (XValueValue True) XInteger). *)

Definition DePoolContract_Ф_addVestingOrLock' ( Л_stake : XInteger64 )
                                              ( Л_beneficiary : XAddress )
                                                ( Л_withdrawalPeriod : XInteger32 )
                                                ( Л_totalPeriod : XInteger32 )
                                                ( Л_isVesting : XBool ) : 
                                         LedgerT (XValueValue True) := 
(* if (m_poolClosed) {return _sendError(STATUS_DEPOOL_CLOSED, 0); } *)
If!! ( ↑ε12 DePoolContract_ι_m_poolClosed ) 
then {
   DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_DEPOOL_CLOSED , $ xInt0  !) >>=
	fun x => return! ( xError x) 
 } ; 
   (* if (!beneficiary.isStdAddrWithoutAnyCast() || beneficiary == address(0))
    return _sendError(STATUS_INVALID_ADDRESS, 0);   
   if (msg.sender == beneficiary)
    return _sendError(STATUS_INVALID_BENEFICIARY, 0); *)
If!! ( ( ( $ Л_beneficiary ) ->isStdAddrWithoutAnyCast() ) !| ( $ Л_beneficiary ?!= $ xInt0 ) ) 
then {  
   DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_INVALID_ADDRESS , $ xInt0  !) >>=
	fun x => return! ( xError x)
 } ; 
If!! ( ( msg_sender () ) ?!= $ Л_beneficiary ) 
then { 
   DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_INVALID_BENEFICIARY , $ xInt0  !) >>=
	fun x => return! ( xError x) 
 } ; 

(↑17 U1! LocalState_ι_addVestingOrLock_Л_beneficiary := $ Л_beneficiary) >> 
(If ($ Л_beneficiary ?== $ xInt0) then {
(↑↑17 U2! LocalState_ι_addVestingOrLock_Л_beneficiary := msg_sender () ) 
})		>>       
U0! Л_msgValue := msg_value () ; 
If!! ( $ Л_msgValue ?< ( $ Л_stake !+ ( ↑12 D2! DePoolContract_ι_STAKE_FEE ) ) ) 
then
{
DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_FEE_TOO_SMALL ,
        ↑ε12 DePoolContract_ι_STAKE_FEE !) >>=
fun x => return! ( xError x )
} ; 
U0! Л_fee := $ Л_msgValue !- $ Л_stake ;
U0! Л_halfStake := $ Л_stake !/ $ xInt2 ; 
If!! ( $ Л_halfStake ?< ↑12 D2! DePoolContract_ι_m_minStake )
then
{
DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_STAKE_TOO_SMALL ,
        $ xInt2 !* ( ↑12 D2! DePoolContract_ι_m_minStake ) !) >>=
fun x => return! ( xError x )
} ;  
If!! ( $ Л_withdrawalPeriod ?> $ Л_totalPeriod )
then
{
DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_WITHDRAWAL_PERIOD_GREATER_TOTAL_PERIOD ,
        $ xInt0 !) >>=
fun x => return! ( xError x )
} ;
If!! ( $ Л_totalPeriod ?>= $ xInt18 !* $ xInt365 !* $ x1_day )
then
{
DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_TOTAL_PERIOD_MORE_18YEARS ,
        $ xInt0 !) >>=
fun x => return! ( xError x )
} ; 
If!! ( $ Л_withdrawalPeriod ?== $ xInt0 )
then
{
DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_WITHDRAWAL_PERIOD_IS_ZERO ,
        $ xInt0 !) >>=
fun x => return! ( xError x )
} ; 
If!! ( $ Л_totalPeriod !% $ Л_withdrawalPeriod ?!= $ xInt0 )
then
{ 
DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_TOTAL_PERIOD_IS_NOT_DIVED_BY_WITHDRAWAL_PERIOD ,
        $ xInt0 !) >>=
fun x => return! ( xError x )
} ; 
U0! Л_participant := ParticipantBase_Ф_getOrCreateParticipant (! ↑ε17 LocalState_ι_addVestingOrLock_Л_beneficiary !) ;
If!! ( $ Л_isVesting )
then {
If! ( $ Л_participant ->> DePoolLib_ι_Participant_ι_haveVesting )
then {
DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_PARTICIPANT_HAVE_ALREADY_VESTING ,
        $ xInt0 !) >>=
fun x => return! ( xError x )
} ; $ I
}
else
{
If! ( $ Л_participant ->> DePoolLib_ι_Participant_ι_haveLock )
then {
DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_PARTICIPANT_HAVE_ALREADY_LOCK ,
        $ xInt0 !) >>=
fun x => return! ( xError x )
} ; $ I
} ; 


U0! Л_withdrawalValue := math->muldiv (! $ Л_halfStake , $ Л_withdrawalPeriod , $ Л_totalPeriod !) ; 
If! ( $ Л_withdrawalValue ?== $ xInt0 )
then
{
DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_PERIOD_PAYMENT_IS_ZERO ,
        $ xInt0 !) >>=
fun x => return! ( xError x )
} ; 
 
        (* for (uint i = 0; i < 2; ++i) {
>       bool isFirstPart = i == 0;
>       InvestParams vestingOrLock = InvestParams({
>       amount: isFirstPart? halfStake : stake - halfStake,
>       lastWithdrawalTime: uint64(now),
>       withdrawalPeriod: withdrawalPeriod,
>       withdrawalValue: withdrawalValue,
>       owner: msg.sender
>       }); *)

(* TODO: for (uint i = 0; i < 2; ++i) { *)
( 
ForIndexed (xListCons xInt0 (xListCons xInt1 xListNil)) do (fun (i: XInteger) => 
U0! Л_isFirstPart := ( $ i ?== $ xInt0 ) ;
U0! Л_vestingOrLock := {|| 
    RoundsBase_ι_InvestParams_ι_amount := $ Л_isFirstPart ? $ Л_halfStake ::: $Л_stake !- $Л_halfStake,
    RoundsBase_ι_InvestParams_ι_lastWithdrawalTime := tvm_now () ,
    RoundsBase_ι_InvestParams_ι_withdrawalPeriod := $ Л_withdrawalPeriod ,
    RoundsBase_ι_InvestParams_ι_withdrawalValue := $ Л_withdrawalValue ,
    RoundsBase_ι_InvestParams_ι_owner := msg_sender () ||} ;
(*         optional(InvestParams) v;
           optional(InvestParams) l; *)
       (* if (isVesting) {
            v.set(vestingOrLock);
        } else {
            l.set(vestingOrLock); } *)
( ↑17 U1! LocalState_ι_addVestingOrLock_Л_v := $ default ) >>
( ↑17 U1! LocalState_ι_addVestingOrLock_Л_l := $ default ) >>
If ( $ Л_isVesting )
then
{
  ↑17 U1! LocalState_ι_addVestingOrLock_Л_v ->set ( $ Л_vestingOrLock )
}
else
{
 ↑17 U1! LocalState_ι_addVestingOrLock_Л_l ->set ( $ Л_vestingOrLock )
} >> 
                  (* Round round = isFirstPart ? getRoundPre0() : getRound0(); *)
                  (* (round, participant) = _addStakes(round, participant, beneficiary, 0, v, l);
                     isFirstPart? setRoundPre0(round) : setRound0(round); *)
U0! Л_round := $Л_isFirstPart ? RoundsBase_Ф_getRoundPre0 () ::: RoundsBase_Ф_getRound0 ; 
U0!  {( Л_round, Л_participant )} := RoundsBase_Ф__addStakes (! ($ Л_round) , 
	                                   ( $ Л_participant ) ,
																		 ( ↑17 D2! LocalState_ι_addVestingOrLock_Л_beneficiary ) ,
																		 ( $ xInt0 ) , 
																		 ( ↑17 D2! LocalState_ι_addVestingOrLock_Л_v ),
																		 ( ↑17 D2! LocalState_ι_addVestingOrLock_Л_l )  !) ;
$ Л_isFirstPart ? 
 RoundsBase_Ф_setRoundPre0 (! $ Л_round !) ::: RoundsBase_Ф_setRound0 (! $ Л_round !) 
) ) >> 
(* TODO: End of LOOP *)

                (* _setOrDeleteParticipant(beneficiary, participant);
                        sendAcceptAndReturnChange128(fee); *)
ParticipantBase_Ф__setOrDeleteParticipant (! (↑17 D2! LocalState_ι_addVestingOrLock_Л_beneficiary) ,  
                                             ($ Л_participant)  !) >>
DePoolContract_Ф_sendAcceptAndReturnChange128 (! $ Л_fee !) .		

Definition DePoolContract_Ф_addVestingOrLock ( Л_stake : XInteger64 )
                                             ( Л_beneficiary : XAddress )
											 ( Л_withdrawalPeriod : XInteger32 )
											 ( Л_totalPeriod : XInteger32 )
											 ( Л_isVesting : XBool ) : LedgerT True  :=
do r ← DePoolContract_Ф_addVestingOrLock' Л_stake Л_beneficiary Л_withdrawalPeriod Л_totalPeriod Л_isVesting ;
return! ( fromValueValue r ).


(*function addVestingStake(uint64 stake, address beneficiary, uint32 withdrawalPeriod, uint32 totalPeriod) public {
        addVestingOrLock(beneficiary, withdrawalPeriod, totalPeriod, true);
    } *) 
Definition DePoolContract_Ф_addVestingStake ( Л_stake : XInteger64 )
                                            (Л_beneficiary: XAddress)
											                      (Л_withdrawalPeriod: XInteger32)
											                      (Л_totalPeriod: XInteger32)
                                        : LedgerT True  :=
DePoolContract_Ф_addVestingOrLock (! $ Л_stake , $ Л_beneficiary , $ Л_withdrawalPeriod , $ Л_totalPeriod , $ xBoolTrue !).

(* 
function addLockStake(uint64 stake, address beneficiary, uint32 withdrawalPeriod, uint32 totalPeriod) public {
        addVestingOrLock(stake, beneficiary, withdrawalPeriod, totalPeriod, false);} 
*)
Definition DePoolContract_Ф_addLockStake ( Л_stake : XInteger64 )
                                         (Л_beneficiary: XAddress)
										 (Л_withdrawalPeriod: XInteger32)
										 (Л_totalPeriod: XInteger32)
                                     : LedgerT True  :=
DePoolContract_Ф_addVestingOrLock (! $ Л_stake , $ Л_beneficiary , $ Л_withdrawalPeriod , $ Л_totalPeriod , $ xBoolFalse !).											
  

(* 
function withdrawPart (uint64 withdrawValue) public  { 
        require(msg.sender != address(0), Errors.IS_EXT_MSG);
        if (m_poolClosed) { 
            return _sendError(STATUS_DEPOOL_CLOSED, 0);
        }
        optional(DePoolLib.Participant) optParticipant = fetchParticipant(msg.sender);
        if (!optParticipant.hasValue()) {
            return _sendError(STATUS_NO_PARTICIPANT, 0);
        }
        DePoolLib.Participant participant = optParticipant.get();
        participant.withdrawValue = withdrawValue;
        _setOrDeleteParticipant(msg.sender, participant);
        sendAcceptAndReturnChange();                       
    }*) 

Definition DePoolContract_Ф_withdrawPart' ( Л_withdrawValue : XInteger64 ) 
                                          : LedgerT (XErrorValue (XValueValue True) XInteger) := 
(*onlyInternalMessage*)
Require {{ msg_sender () ?!= $ xInt0 , ↑ε7 Errors_ι_IS_EXT_MSG }} ; 

(* if (m_poolClosed) {return _sendError(STATUS_DEPOOL_CLOSED, 0); } *)
If!! ( ↑ε12 DePoolContract_ι_m_poolClosed ) 
then { 
   DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_DEPOOL_CLOSED , $ xInt0  !) >>=
	fun x => return! ( xError x) 
 } ; 
(* optional(DePoolLib.Participant) optParticipant = fetchParticipant(msg.sender);
 if (!optParticipant.hasValue()) {
	 return _sendError(STATUS_NO_PARTICIPANT, 0);
 }*)
U0! Л_optParticipant := ParticipantBase_Ф_fetchParticipant (! msg_sender () !) ;
If! ( !¬ ( $ Л_optParticipant ->hasValue ) ) 
then { 
   DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_NO_PARTICIPANT , $ xInt0  !) >>=
	fun x => return! ( xError x)													
 } ;  
(*DePoolLib.Participant participant = optParticipant.get();*) 
U0! Л_participant := $ Л_optParticipant ->get ; 
(*        participant.withdrawValue = withdrawValue;*)
U0! Л_participant ^^ DePoolLib_ι_Participant_ι_withdrawValue := $ Л_withdrawValue ; 
(*        
_setOrDeleteParticipant(msg.sender, participant);
sendAcceptAndReturnChange();   
*)
(ParticipantBase_Ф__setOrDeleteParticipant (! msg_sender () , $ Л_participant !)) >> 
(DePoolContract_Ф_sendAcceptAndReturnChange () ).

Definition DePoolContract_Ф_withdrawPart ( Л_withdrawValue : XInteger64 ) 
                                                      : LedgerT (XErrorValue True XInteger) :=
do r ← DePoolContract_Ф_withdrawPart' Л_withdrawValue  ;
	return! (xErrorMapDefaultF (xValue ∘ fromValueValue) r xError).	 
	
(* 
function withdrawAll()                  (*<<<<< имя и аргументы <<<<<<<*)
                      public  { 
        require(msg.sender != address(0), Errors.IS_EXT_MSG);

(*<<<<<<<< мнорго изменений <<<<<<<<<<<<*)

        if (m_poolClosed) {
            return _sendError(STATUS_DEPOOL_CLOSED, 0);
        }

        optional(DePoolLib.Participant) optParticipant = fetchParticipant(msg.sender);
        if (!optParticipant.hasValue()) {
            return _sendError(STATUS_NO_PARTICIPANT, 0);
        }
        DePoolLib.Participant participant = optParticipant.get();

        participant.reinvest = false;
        _setOrDeleteParticipant(msg.sender, participant);
        sendAcceptAndReturnChange();
    }
 *) 
	
Definition DePoolContract_Ф_withdrawAll'  : LedgerT (XErrorValue (XValueValue True) XInteger) :=
    (*require(msg.sender != address(0), Errors.IS_EXT_MSG);*)
Require {{ msg_sender () ?!= $ xInt0 , ↑ε7 Errors_ι_IS_EXT_MSG }} ; 
(* if (m_poolClosed) {
            return _sendError(STATUS_DEPOOL_CLOSED, 0);
        } *)
If!! ( ↑ε12 DePoolContract_ι_m_poolClosed ) 
then { 
   DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_DEPOOL_CLOSED , $ xInt0  !) >>=
	fun x => return! ( xError x) 
 } ; 
(* optional(DePoolLib.Participant) optParticipant = fetchParticipant(msg.sender);
        if (!optParticipant.hasValue()) {
            return _sendError(STATUS_NO_PARTICIPANT, 0);
        } *)
U0! Л_optParticipant := ParticipantBase_Ф_fetchParticipant (! msg_sender () !) ;
If! ( !¬ ( $ Л_optParticipant ->hasValue ) ) 
then { 
   DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_NO_PARTICIPANT , 
														$ xInt0  !) >>=
	fun x => return! ( xError x)													
 } ; 

(*         DePoolLib.Participant participant = optParticipant.get(); *)
U0! Л_participant := $ Л_optParticipant ->get ; 


(*   participant.reinvest = false; *)
U0! Л_participant ^^ DePoolLib_ι_Participant_ι_reinvest := $ xBoolFalse ; 
(*        
_setOrDeleteParticipant(msg.sender, participant);
sendAcceptAndReturnChange();   
*)
(ParticipantBase_Ф__setOrDeleteParticipant (! msg_sender () , $ Л_participant !)) >> 
(DePoolContract_Ф_sendAcceptAndReturnChange () ).


Definition DePoolContract_Ф_withdrawAll : LedgerT (XErrorValue True XInteger) :=
do r ← DePoolContract_Ф_withdrawAll'  ;
	return! (xErrorMapDefaultF (xValue ∘ fromValueValue) r xError).


(* function cancelWithdrawal() public 
{
require(msg.sender != address(0), Errors.IS_EXT_MSG);
        if (m_poolClosed) {
            return _sendError(STATUS_DEPOOL_CLOSED, 0);
        }

        optional(DePoolLib.Participant) optParticipant = fetchParticipant(msg.sender);
        if (!optParticipant.hasValue()) {
            return _sendError(STATUS_NO_PARTICIPANT, 0);
        }
        DePoolLib.Participant participant = optParticipant.get();

        participant.reinvest = true;
        participant.withdrawValue = 0;
        _setOrDeleteParticipant(msg.sender, participant);
        sendAcceptAndReturnChange();
    } *)

Definition DePoolContract_Ф_cancelWithdrawal' : LedgerT (XErrorValue (XValueValue True) XInteger) :=
    (*require(msg.sender != address(0), Errors.IS_EXT_MSG);*)
Require {{ msg_sender () ?!= $ xInt0 , ↑ε7 Errors_ι_IS_EXT_MSG }} ; 
(* if (m_poolClosed) {
            return _sendError(STATUS_DEPOOL_CLOSED, 0);
        } *)
If!! ( ↑ε12 DePoolContract_ι_m_poolClosed ) 
then { 
   DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_DEPOOL_CLOSED , $ xInt0  !) >>=
	fun x => return! ( xError x) 
 } ; 
(* optional(DePoolLib.Participant) optParticipant = fetchParticipant(msg.sender);
        if (!optParticipant.hasValue()) {
            return _sendError(STATUS_NO_PARTICIPANT, 0);
        } *)
U0! Л_optParticipant := ParticipantBase_Ф_fetchParticipant (! msg_sender () !) ;
If! ( !¬ ( $ Л_optParticipant ->hasValue ) ) 
then { 
   DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_NO_PARTICIPANT , 
														$ xInt0  !) >>=
	fun x => return! ( xError x)													
 } ; 

(*         DePoolLib.Participant participant = optParticipant.get(); *)
U0! Л_participant := $ Л_optParticipant ->get ; 
(*   participant.reinvest = false; *)
U0! Л_participant ^^ DePoolLib_ι_Participant_ι_reinvest := $ xBoolTrue ; 
U0! Л_participant ^^ DePoolLib_ι_Participant_ι_withdrawValue := $ xInt0 ; 

(*        
_setOrDeleteParticipant(msg.sender, participant);
sendAcceptAndReturnChange();   
*)
(ParticipantBase_Ф__setOrDeleteParticipant (! msg_sender () , $ Л_participant !)) >> 
(DePoolContract_Ф_sendAcceptAndReturnChange () ).

Definition DePoolContract_Ф_cancelWithdrawal : LedgerT (XErrorValue True XInteger) :=
do r ← DePoolContract_Ф_cancelWithdrawal'  ;
	return! (xErrorMapDefaultF (xValue ∘ fromValueValue) r xError).

(*  
    function transferStake(address dest, uint64 amount) public 
{ 
        require(msg.sender != address(0), Errors.IS_EXT_MSG);

        if (m_poolClosed) {
            return _sendError(STATUS_DEPOOL_CLOSED, 0);
        }

        // target address should be set.
        (* TODO: old: require(dest.isStdAddrWithoutAnyCast() && !dest.isStdZero(), Errors.INVALID_ADDRESS); *)
        (* TODO: new: *) if (!dest.isStdAddrWithoutAnyCast() || dest.isStdZero())
>       (* TODO: new: *) return _sendError(STATUS_INVALID_ADDRESS, 0);
        // check self transfer
        address src = msg.sender;
        if (src == dest)  {
            return _sendError(STATUS_TRANSFER_SELF, 0);
        }

        if (src == m_validatorWallet || dest == m_validatorWallet) {
            return _sendError(STATUS_TRANSFER_TO_OR_FROM_VALIDATOR, 0);
        }

        optional(DePoolLib.Participant) optSrcParticipant = fetchParticipant(src);
        if (!optSrcParticipant.hasValue()) {
            return _sendError(STATUS_NO_PARTICIPANT, 0);
        }
        DePoolLib.Participant srcParticipant = optSrcParticipant.get();

        if (amount == 0) {
            amount = DePoolLib.MAX_UINT64;
        }

        DePoolLib.Participant destParticipant = getOrCreateParticipant(dest);

        uint64 totalSrcStake;
        uint64 transferred;
        mapping(uint64 => Round) rounds = m_rounds;
        optional(uint64, Round) pair = rounds.min();
        while (pair.hasValue() && transferred < amount) {
            (uint64 roundId, Round round) = pair.get();
            uint64 currentTransferred;
            uint64 srcStake;
            (rounds[roundId], currentTransferred, srcStake, srcParticipant, destParticipant)
                = transferStakeInOneRound(
                    round,
                    srcParticipant,
                    destParticipant,
                    src,
                    dest,
                    amount - transferred,
                    m_minStake
                );
            transferred += currentTransferred;
            totalSrcStake += srcStake;
            pair = rounds.next(roundId);
        }

        if (amount != DePoolLib.MAX_UINT64) {
            if (totalSrcStake < amount) {
                return _sendError(STATUS_TRANSFER_AMOUNT_IS_TOO_BIG, 0);
            }

            if (transferred < amount) {
                return _sendError(STATUS_REMAINING_STAKE_LESS_THAN_MINIMAL, 0);
            }
        }

        m_rounds = rounds;

        _setOrDeleteParticipant(src, srcParticipant);
        _setOrDeleteParticipant(dest, destParticipant);

        IParticipant(dest).onTransfer{bounce: false}(src, amount);
        sendAcceptAndReturnChange();
    }     *)

Unset Typeclasses Iterative Deepening.
Set Typeclasses Depth 10.


                              
Notation "'do' a ← e '???;' c" := (e >>= fun ea => xErrorMapDefaultF (fun a => c) ea (fun er => return! (xValue (xError er)))) 
                                   (at level 60, right associativity): solidity_scope.
Notation " 'If2!!' g 'then' '{' y '}' ; c " := ( do g' ← g ; do _ ← ( xBoolIfElse g' y (return! (xValue I))) ???; c )(at level 21, g at level 22, y at level 22, c at level 60, right associativity): solidity_scope.

(* Parameter DePoolContract_Ф_transferStake' : XAddress -> XInteger64 -> LedgerT ( XErrorValue (XValueValue True) XInteger ). *)
Definition DePoolContract_Ф_transferStake' (Л_dest : XAddress ) (Л_amount : XInteger64 ) : 
                                           LedgerT ( XErrorValue (XValueValue True) XInteger ) := 
 (* require(msg.sender != address(0), Errors.IS_EXT_MSG); *)                                           
 Require {{ msg_sender () ?!= $xInt0 ,  ↑7 D2! Errors_ι_IS_EXT_MSG  }} ; 										   
 (*init*)
 (↑17 U1!  LocalState_ι_transferStake_Л_amount := $ Л_amount)	>>	
 
 (* if (m_poolClosed) { 
            return _sendError(STATUS_DEPOOL_CLOSED, 0);
        } *) 
If!! ( ↑ε12 DePoolContract_ι_m_poolClosed ) 
then { 
   DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_DEPOOL_CLOSED , $ xInt0  !) >>=
	fun x => return! (xError x)
 } ; 
 
 (* if (!dest.isStdAddrWithoutAnyCast() || dest.isStdZero())
         return _sendError(STATUS_INVALID_ADDRESS, 0);*)
If!! ( ( !¬ ( ( $ Л_dest ) ->isStdAddrWithoutAnyCast() ) )  !|  ( ( $ Л_dest ) ->isStdZero() ) )
 then { 
         DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_INVALID_ADDRESS , $ xInt0 !) >>=
	          fun x => return! (xError x) 
      } ; 
 (* // check self transfer
	 address src = msg.sender; *)
 U0! Л_src := msg_sender ()	 ;  

(*         if (src == dest)  {
            return _sendError(STATUS_TRANSFER_SELF, 0);
		} *)
 If!! ( $ Л_src ?== $ Л_dest ) then {
	(DePoolContract_Ф__sendError (! ↑ε12  DePoolContract_ι_STATUS_TRANSFER_SELF , $xInt0 !)) >>=
	fun x => return! (xError x)
  } ;

(* if (src == m_validatorWallet || dest == m_validatorWallet) { 
            return _sendError(STATUS_TRANSFER_TO_OR_FROM_VALIDATOR, 0);
        } *)

If!! (($Л_src ?== ↑ε2 ValidatorBase_ι_m_validatorWallet ) !| ($Л_dest ?== ↑ε2 ValidatorBase_ι_m_validatorWallet)) then {
	(DePoolContract_Ф__sendError (! ↑ε12  DePoolContract_ι_STATUS_TRANSFER_TO_OR_FROM_VALIDATOR , $xInt0 !)) >>=
	fun x => return! (xError x)
  } ; 
       

 (* optional(DePoolLib.Participant) optSrcParticipant = fetchParticipant(src); *)
 U0! Л_optSrcParticipant := ParticipantBase_Ф_fetchParticipant (! $Л_src !); 
 (* if (!optSrcParticipant.hasValue()) {
            return _sendError(STATUS_NO_PARTICIPANT, 0);
		} *)
 If!! ( !¬ $Л_optSrcParticipant ->hasValue )then {
	(DePoolContract_Ф__sendError (! ↑ε12  DePoolContract_ι_STATUS_NO_PARTICIPANT , $xInt0 !)) >>=
	fun x => return! (xError x)
 }	; 
 (* DePoolLib.Participant srcParticipant = optSrcParticipant.get(); *)
 (↑17 U1! LocalState_ι_transferStake_Л_srcParticipant := $Л_optSrcParticipant ->get) >>

(* if (amount == 0) {
            amount = DePoolLib.MAX_UINT64;
        }*)
 (If (↑17 D2! LocalState_ι_transferStake_Л_amount ?== $xInt0) then {
	↑↑17 U2! LocalState_ι_transferStake_Л_amount := ↑9 D2! DePoolLib_ι_MAX_UINT64
        }) >> 


 (*DePoolLib.Participant destParticipant = getOrCreateParticipant(dest);*)	
 (↑↑17 U2! LocalState_ι_transferStake_Л_destParticipant := ParticipantBase_Ф_getOrCreateParticipant (! $Л_dest !)) >>
  (*uint64 totalSrcStake;*)
  (↑17 U1! LocalState_ι_transferStake_Л_totalSrcStake := $default) >>
  (* uint64 transferred; *)
  (↑17 U1! LocalState_ι_transferStake_Л_transferred := $default) >>
  (* mapping(uint64 => Round) rounds = m_rounds; *)
  (↑↑17 U2! LocalState_ι_transferStake_Л_rounds := ↑11 D2! RoundsBase_ι_m_rounds) >>
  (* optional(uint64, Round) pair = rounds.min(); *) 
  (↑17 U1! LocalState_ι_transferStake_Л_pair :=  D1! (D2! LocalState_ι_transferStake_Л_rounds) ->min) >> 
  
(*         while (pair.hasValue() && transferred < amount) {
            (uint64 roundId, Round round) = pair.get();
            uint64 currentTransferred;
            uint64 srcStake;
            (rounds[roundId], currentTransferred, srcStake, srcParticipant, destParticipant)
                = transferStakeInOneRound(
                    round,
                    srcParticipant,
                    destParticipant,
                    src,
                    dest,
                    amount - transferred,
                    m_minStake
                );
            transferred += currentTransferred;
            totalSrcStake += srcStake;
            pair = rounds.next(roundId);
		} *)
	  ((While ( ((↑17 D2! LocalState_ι_transferStake_Л_pair) ->hasValue)   !&
		      ((↑17 D2! LocalState_ι_transferStake_Л_transferred) ?< (↑17 D2!  LocalState_ι_transferStake_Л_amount))  ) do 
		   (
			   U0! {( Л_roundId  , Л_round  )} := (↑17 D2! LocalState_ι_transferStake_Л_pair) ->get  ; 
			   U0! Л_currentTransferred := $ default ;
			   U0! Л_srcStake := $ default ;
			   U0! {( Л_rounds_roundId , Л_currentTransferred , Л_srcStake, Л_srcParticipant, Л_destParticipant )} :=
			   RoundsBase_Ф_transferStakeInOneRound (! $ Л_round , 
													   ↑17 D2! LocalState_ι_transferStake_Л_srcParticipant, 
													   ↑17 D2! LocalState_ι_transferStake_Л_destParticipant,
													   $ Л_src, 
													   $ Л_dest,
													   (↑17 D2! LocalState_ι_transferStake_Л_amount) !- (↑17 D2! LocalState_ι_transferStake_Л_transferred), 
													   (↑12 D2! DePoolContract_ι_m_minStake)
													 !) ;
			   (↑17 U1! LocalState_ι_transferStake_Л_rounds [[ $ Л_roundId ]] := $ Л_rounds_roundId)	>>
			   (↑17 U1! LocalState_ι_transferStake_Л_srcParticipant := $ Л_srcParticipant) >>
			   (↑17 U1! LocalState_ι_transferStake_Л_destParticipant := $ Л_destParticipant) >>
			   (↑17 U1! LocalState_ι_transferStake_Л_transferred !+= $Л_currentTransferred) >>
			   (↑17 U1! LocalState_ι_transferStake_Л_totalSrcStake !+= $Л_srcStake) >>
			   (↑17 U1! LocalState_ι_transferStake_Л_pair :=  D1! (D2! LocalState_ι_transferStake_Л_rounds) ->next $ Л_roundId) >>
 			   continue! I 
		   )))   >>  

        (* if (amount != DePoolLib.MAX_UINT64) {
            if (totalSrcStake < amount) {
                return _sendError(STATUS_TRANSFER_AMOUNT_IS_TOO_BIG, 0);
            }

            if (transferred < amount) {
                return _sendError(STATUS_REMAINING_STAKE_LESS_THAN_MINIMAL, 0);
            }
		} *)
		
		If! ((↑17 D2! LocalState_ι_transferStake_Л_amount) ?!= (↑9 D2! DePoolLib_ι_MAX_UINT64)) then {
			If!! ((↑17 D2! LocalState_ι_transferStake_Л_totalSrcStake) ?< (↑17 D2! LocalState_ι_transferStake_Л_amount)) then
			{
				(DePoolContract_Ф__sendError (! ↑ε12  DePoolContract_ι_STATUS_TRANSFER_AMOUNT_IS_TOO_BIG , ↑ε12 DePoolContract_ι_TRANSFER_STAKE_FEE !)) >>=
				fun x => return! (xError x)
			} ;
			If! ((↑17 D2! LocalState_ι_transferStake_Л_transferred) ?< (↑17 D2! LocalState_ι_transferStake_Л_amount)) then
			{
				(DePoolContract_Ф__sendError (! ↑ε12  DePoolContract_ι_STATUS_REMAINING_STAKE_LESS_THAN_MINIMAL , ↑ε12 DePoolContract_ι_TRANSFER_STAKE_FEE !)) >>=
				fun x => return! (xError x)
			} ; $ I 
        } ;  

		(* m_rounds = rounds; *)
		(↑↑11 U2! RoundsBase_ι_m_rounds := ↑17 D2! LocalState_ι_transferStake_Л_rounds) >>

		(* _setOrDeleteParticipant(src, srcParticipant); *)
		ParticipantBase_Ф__setOrDeleteParticipant (! $ Л_src ,  (↑17 D2! LocalState_ι_transferStake_Л_srcParticipant)  !) >> 
        (* _setOrDeleteParticipant(dest, destParticipant); *)
		ParticipantBase_Ф__setOrDeleteParticipant (! $ Л_dest ,  (↑17 D2! LocalState_ι_transferStake_Л_destParticipant)  !) >> 
		(* IParticipant(dest).onTransfer{bounce: false}(src, amount); *)
	    (->sendMessage {|| 
		       contractAddress := $ Л_dest ,
			   contractFunction := IParticipant_И_onTransferF (!!
																 $ Л_src , 
																 ↑17 D2! LocalState_ι_transferStake_Л_amount
			                                                   !!)  ,
			   contractMessage := {||  messageBounce := $ xBoolFalse||} ||} )  >> 

		(* sendAcceptAndReturnChange *)
		DePoolContract_Ф_sendAcceptAndReturnChange () .

Definition DePoolContract_Ф_transferStake (Л_dest : XAddress )
                                          ( Л_amount : XInteger64 ) : 
                                           LedgerT ( XErrorValue True XInteger ) :=  	 
do r ← DePoolContract_Ф_transferStake' Л_dest Л_amount ;
return! (xErrorMapDefaultF (xValue ∘ fromValueValue) r xError).                                   
                                           



(* function totalParticipantFunds(uint64 ingoreRoundId) private view returns (uint64) {
        uint64 stakes = 0;
        optional(uint64, Round) pair = minRound();
        while (pair.hasValue()) {
            (uint64 id, Round round) = pair.get();
            RoundStep step = round.step;
            if (id != ingoreRoundId && step != RoundStep.Completed) {
                if (step == RoundStep.Completing) {
                    if (round.completionReason == CompletionReason.ValidatorIsPunished)
                        stakes += (round.unused + round.recoveredStake) - round.handledStakesAndRewards;
                    else {
                        stakes += (round.stake + round.rewards) - round.handledStakesAndRewards;
                    }
                } else if (
                    step == RoundStep.PrePooling ||
                    step == RoundStep.Pooling ||
                    step == RoundStep.WaitingValidatorRequest ||
                    step == RoundStep.WaitingUnfreeze && round.completionReason != CompletionReason.Undefined
                ) {
                    stakes += round.stake;
                } else {
                    stakes += round.unused;
                }
            }
            pair = nextRound(id);
        }
        return stakes;
    } *)

Definition DePoolContract_Ф_totalParticipantFunds (Л_ingoreRoundId : XInteger64) : LedgerT XInteger64 :=
    (*  uint64 stakes = 0; *)
    (↑17 U1! LocalState_ι_totalParticipantFunds_Л_stakes := $xInt0) >>
    (*     optional(uint64, Round) pair = minRound(); *)
    (↑↑17 U2! LocalState_ι_totalParticipantFunds_Л_pair := RoundsBase_Ф_minRound ()) >>
    (*      while (pair.hasValue()) { *)
    (While ((↑17 D2! LocalState_ι_totalParticipantFunds_Л_pair) ->hasValue) do (
    (*         (uint64 id, Round round) = pair.get(); *)
    U0! {( Л_id,  Л_round )} := (↑17 D2! LocalState_ι_totalParticipantFunds_Л_pair) ->get ;
    (*        RoundStep step = round.step; *)
    U0! Л_step := $ (Л_round ->> RoundsBase_ι_Round_ι_step) ; 
    (*         if (id != ingoreRoundId && step != RoundStep.Completed) { *)
    (If (($Л_id ?!= $Л_ingoreRoundId) !& ($Л_step ?!= $RoundsBase_ι_RoundStepP_ι_Completed )) then { 
    (*             if (step == RoundStep.Completing) { *)
    If ($Л_step ?== $RoundsBase_ι_RoundStepP_ι_Completing) then {
    (*                 if (round.completionReason == CompletionReason.ValidatorIsPunished) *)
    If ($ (Л_round ->> RoundsBase_ι_Round_ι_completionReason) ?== $ RoundsBase_ι_CompletionReasonP_ι_ValidatorIsPunished) then { 
    (*                     stakes += (round.unused + round.recoveredStake) - round.handledStakesAndRewards; *)
        (↑17 U1! LocalState_ι_totalParticipantFunds_Л_stakes !+= ($ (Л_round ->> RoundsBase_ι_Round_ι_unused) !+
                                                                  $ (Л_round ->> RoundsBase_ι_Round_ι_recoveredStake)) !- $ (Л_round ->> RoundsBase_ι_Round_ι_handledStakesAndRewards))
    } 
    (*                 else { *)
    else { 
    (*                     stakes += (round.stake + round.rewards) - round.handledStakesAndRewards; *)
        (↑17 U1! LocalState_ι_totalParticipantFunds_Л_stakes !+= ($ (Л_round ->> RoundsBase_ι_Round_ι_stake) !+
            $ (Л_round ->> RoundsBase_ι_Round_ι_rewards)) !- $ (Л_round ->> RoundsBase_ι_Round_ι_handledStakesAndRewards))
    (*                 } *)
    }
    (*            } else if ( *)
    (*                step == RoundStep.PrePooling || *)
    (*                 step == RoundStep.Pooling || *)
    (*                 step == RoundStep.WaitingValidatorRequest || *)
    (*                 step == RoundStep.WaitingUnfreeze && round.completionReason != CompletionReason.Undefined *)
    (*             ) { *)
    } else { If ($Л_step ?== $RoundsBase_ι_RoundStepP_ι_PrePooling) !|
                ($Л_step ?== $RoundsBase_ι_RoundStepP_ι_Pooling) !| 
                ($Л_step ?== $RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest) !|
                (($Л_step ?== $RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze) !&
                ($ (Л_round ->> RoundsBase_ι_Round_ι_completionReason) ?== $ RoundsBase_ι_CompletionReasonP_ι_Undefined)) then { 
    (*                 stakes += round.stake; *)
        (↑17 U1! LocalState_ι_totalParticipantFunds_Л_stakes !+= $ (Л_round ->> RoundsBase_ι_Round_ι_stake))
    (*             } else { *)
    } else { 
    (*                stakes += round.unused; *)
        (↑17 U1! LocalState_ι_totalParticipantFunds_Л_stakes !+= $ (Л_round ->> RoundsBase_ι_Round_ι_unused))
    (*             } *)
    }
    (*         } *)
    }
    }) >>
    (*         pair = nextRound(id); *)
    (↑↑17 U2! LocalState_ι_totalParticipantFunds_Л_pair := RoundsBase_Ф_nextRound (! $Л_id !)) >>
    (*     } *)
    continue! I) ) >>
    (*     return stakes; *)
    (↑17 D2! LocalState_ι_totalParticipantFunds_Л_stakes).

 
Set Typeclasses Iterative Deepening.
Set Typeclasses Depth 10.

(*     function checkPureDePoolBalance() private returns (bool) {
        uint stakes = totalParticipantFunds(0);
        uint64 msgValue = uint64(msg.value);
        (* TODO: old: if (address(this).balance < CRITICAL_MIN_BALANCE + stakes + msgValue) {
          int replenishment = int(CRITICAL_MIN_BALANCE) + int(stakes) + int(msgValue) - int(address(this).balance); *)
        (* TODO: new:*)uint sum = CRITICAL_THRESHOLD + stakes + msgValue;
>       (* TODO: new:*)if (address(this).balance < sum) {
>       (* TODO: new:*)uint replenishment = sum - address(this).balance;
            emit TooLowDePoolBalance(replenishment);
            return false;
        }
        return true;
    } *)

(* function checkPureDePoolBalance() private returns (bool) {
        uint stakes = totalParticipantFunds(0);
        uint64 msgValue = uint64(msg.value);
        uint sum = CRITICAL_THRESHOLD + stakes + msgValue;
        if (address(this).balance < sum) {
            uint replenishment = sum - address(this).balance;
            emit TooLowDePoolBalance(replenishment);
            return false;
        }
        return true;
    } *)



Definition DePoolContract_Ф_checkPureDePoolBalance' : LedgerT (XValueValue XBool) := 
    U0! Л_stakes := DePoolContract_Ф_totalParticipantFunds (! $xInt0 !) ;
    U0! Л_msgValue := msg_value ;
    U0! Л_sum := ↑ε12 DePoolContract_ι_CRITICAL_THRESHOLD !+ $ Л_stakes !+ $ Л_msgValue;
    If! ( tvm_balance () ?< $ Л_sum ) then {
             (* sum - address(this).balance; *)
        U0! Л_replenishment := $ Л_sum !- tvm_balance ();
        (->emit  TooLowDePoolBalance (!! $ Л_replenishment !!)) >>
        $ (xError xBoolFalse)                  
    }; $ xBoolTrue.

Definition DePoolContract_Ф_checkPureDePoolBalance : LedgerT  XBool :=     
    do r ← DePoolContract_Ф_checkPureDePoolBalance' ;
  return! (fromValueValue r).



(* 
function participateInElections(
        uint64 queryId,
        uint256 validatorKey,
        uint32 stakeAt,
        uint32 maxFactor,
        uint256 adnlAddr,
        bytes signature
    ) public functionID(0x4E73744B) {
require(msg.sender == m_validatorWallet, Errors.IS_NOT_VALIDATOR);
        (* TODO: old: require(!m_poolClosed, Errors.DEPOOL_IS_CLOSED); *)
        (* TODO: new: *)if (m_poolClosed)
>       (* TODO: new: *)return _sendError(STATUS_DEPOOL_CLOSED, 0);
        tvm.accept();
        if (checkPureDePoolBalance()) { 
            Round round = getRound1();
            (* TODO: old: require(round.step == RoundStep.WaitingValidatorRequest, Errors.NO_ELECTION_ROUND);
            (* TODO: old: require(stakeAt == round.supposedElectedAt, Errors.INVALID_ELECTION_ID);*)
            (* TODO: new: *)if (round.step != RoundStep.WaitingValidatorRequest)
            (* TODO: new: *)    return _sendError(STATUS_NO_ELECTION_ROUND, 0);
            (* TODO: new: *)if (stakeAt != round.supposedElectedAt)
            (* TODO: new: *)    return _sendError(STATUS_INVALID_ELECTION_ID, 0);

            round.validatorRequest = DePoolLib.Request(queryId, validatorKey, stakeAt, maxFactor, adnlAddr, signature); *)
 

            _sendElectionRequest(round.proxy, round.id, round.stake, round.validatorRequest, round.elector);
            round.step = RoundStep.WaitingIfStakeAccepted;
            setRound1(round);
        }
        _returnChange();
    }
    *)

(* Check RoundsBase_ι_Round_ι_step.
Check RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest. *)
(* Parameter DePoolContract_Ф_participateInElections : XInteger64 -> XInteger256 -> XInteger32 ->
                                                    XInteger32 -> XInteger256 -> (XList XInteger8) ->
                                                    LedgerT ( XErrorValue True XInteger ). *)
Definition DePoolContract_Ф_participateInElections'  ( Л_queryId : XInteger64 )
													( Л_validatorKey : XInteger256 )
													( Л_stakeAt : XInteger32 )
													( Л_maxFactor : XInteger32 )
													( Л_adnlAddr : XInteger256 )
													( Л_signature : XList XInteger8 ) 
                         : LedgerT ( XErrorValue (XValueValue True) XInteger ) :=
(*require(msg.sender == m_validatorWallet, Errors.IS_NOT_VALIDATOR);*)
Require {{  msg_sender () ?== ↑2 D2! ValidatorBase_ι_m_validatorWallet , ↑7 D2! Errors_ι_IS_NOT_VALIDATOR }} ; 
(*if (m_poolClosed)
      return _sendError(STATUS_DEPOOL_CLOSED, 0);*)
If!! ( ↑12 D2! DePoolContract_ι_m_poolClosed )
then {
   DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_DEPOOL_CLOSED , $ xInt0  !) >>=
	fun x => return! ( xError x) 
} ; 
(* tvm.accept(); *)					
tvm_accept () >>
If! (DePoolContract_Ф_checkPureDePoolBalance ()) then {							
(*Round round = getRound1();*)
U0! Л_round := RoundsBase_Ф_getRound1 (); 
        (*if (round.step != RoundStep.WaitingValidatorRequest)
           return _sendError(STATUS_NO_ELECTION_ROUND, 0);*)
If!! ( $ Л_round ->> RoundsBase_ι_Round_ι_step ?!= $ RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest )
then {
   DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_NO_ELECTION_ROUND , $ xInt0  !) >>=
	fun x => return! ( xError x) 
} ;
      (*if (stakeAt != round.supposedElectedAt)
           return _sendError(STATUS_INVALID_ELECTION_ID, 0);*)
If! ( $ Л_stakeAt ?!=  $ (Л_round ->>  RoundsBase_ι_Round_ι_supposedElectedAt) )
then {
   DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_INVALID_ELECTION_ID , $ xInt0  !) >>=
	fun x => return! ( xError x) 
} ;
(*round.validatorRequest = DePoolLib.Request(queryId, validatorKey, stakeAt, maxFactor, adnlAddr, signature);*)
U0! Л_round ^^ RoundsBase_ι_Round_ι_validatorRequest := $ (DePoolLib_ι_RequestC Л_queryId Л_validatorKey Л_stakeAt Л_maxFactor Л_adnlAddr Л_signature) ; 
(*_sendElectionRequest(round.proxy, round.id, round.stake, round.validatorRequest, round.elector);*)
(ProxyBase_Ф__sendElectionRequest  (! $ (Л_round ->> RoundsBase_ι_Round_ι_proxy) ,
									  $ (Л_round ->> RoundsBase_ι_Round_ι_id) , 
									  $ (Л_round ->> RoundsBase_ι_Round_ι_stake) , 
									  $ (Л_round ->> RoundsBase_ι_Round_ι_validatorRequest) ,
									  $ (Л_round ->> RoundsBase_ι_Round_ι_elector)  !)) >> 
(*round.step = RoundStep.WaitingIfStakeAccepted;*)
U0! Л_round ^^ RoundsBase_ι_Round_ι_step := $ RoundsBase_ι_RoundStepP_ι_WaitingIfStakeAccepted ;
(*setRound1(round);*)	
(RoundsBase_Ф_setRound1 (! $ Л_round !) ) } ; 
(* _returnChange();*)
DePoolContract_Ф__returnChange (). 
(*00:11*)
(* = 17 minutes / 11 clauses = ~1,5 min / clause*)	  

Definition DePoolContract_Ф_participateInElections  ( Л_queryId : XInteger64 )
													( Л_validatorKey : XInteger256 )
													( Л_stakeAt : XInteger32 )
													( Л_maxFactor : XInteger32 )
													( Л_adnlAddr : XInteger256 )
													( Л_signature : XList XInteger8 ) 
                         : LedgerT ( XErrorValue  True XInteger ) :=
do r ← DePoolContract_Ф_participateInElections'  Л_queryId  Л_validatorKey Л_stakeAt  Л_maxFactor Л_adnlAddr  Л_signature;
return! (xErrorMapDefaultF (xValue ∘ fromValueValue) r xError).              

(* 
function updateRound2(
        Round round2,
        uint256 prevValidatorHash,
        uint256 curValidatorHash,
        uint32 validationStart

    )
        private returns (Round)
    {

        if (round2.step == RoundStep.WaitingValidatorRequest) {
            // Next validation is started. Round is expired because no request from validator or proxy
            // rejected request. See onBounce function.
            round2.step = RoundStep.WaitingUnfreeze;
            if (round2.completionReason == CompletionReason.Undefined) {
                round2.completionReason = CompletionReason.NoValidatorRequest;
            }
            round2.unfreeze = 0;
        } else if (round2.step == RoundStep.Completing) {
            this.completeRoundWithChunk{bounce: false}(round2.id, 1);
            // For situations when exist stake with value==V, but DePool balance == (V - epsilon)
            // In such situations some extra funds must be sent to DePool balance (See function 'receiveFunds')
        }
        // try to update unfreeze time
        if (round2.vsetHashInElectionPhase != curValidatorHash &&
            round2.vsetHashInElectionPhase != prevValidatorHash &&
            round2.unfreeze == DePoolLib.MAX_TIME
        )
        {
            // at least 1 validation period is skipped
            round2.unfreeze = validationStart + round2.stakeHeldFor;
        }

        // try to complete round
        if (now >= uint(round2.unfreeze) + DePoolLib.ELECTOR_UNFREEZE_LAG) {
            if (round2.step == RoundStep.WaitingUnfreeze &&
                round2.completionReason != CompletionReason.Undefined
            )
            {
                (* TODO:delete: if (round2.participantQty == 0) {
                   TODO:delete:  round2.step = RoundStep.Completed;
                   TODO:delete:  emit RoundCompleted(toTruncatedRound(round2));
                   TODO:delete:  } else {
                   TODO:delete:     // just complete round
                   TODO:delete:     round2 = startRoundCompleting(round2, round2.completionReason);
                   TODO:delete:  } *)
                   (*TODO:new:*)round2 = startRoundCompleting(round2, round2.completionReason);
            } else if (
                round2.step == RoundStep.WaitingValidationStart ||
                round2.step == RoundStep.WaitingUnfreeze
            )
            {
                // recover stake and complete round
                round2.step = RoundStep.WaitingReward;
                _recoverStake(round2.proxy, round2.id, round2.elector);
            }
        }
        return round2;
    }
 *)

 (*function updateRound2(
        Round round2,
        uint256 prevValidatorHash,
        uint256 curValidatorHash,
        uint32 validationStart,
        uint32 stakeHeldFor
    )
        private returns (Round)*)
Definition DePoolContract_Ф_updateRound2 ( Л_round2 : RoundsBase_ι_Round )
                                        ( Л_prevValidatorHash : XInteger256 )
                                        ( Л_curValidatorHash : XInteger256 )
                                        ( Л_validationStart : XInteger32 )
										                     
                                         : LedgerT RoundsBase_ι_Round :=
(*init*)
(↑17 U1! LocalState_ι_updateRound2_Л_round2 := $ Л_round2) >>						 
(* if (round2.step == RoundStep.WaitingValidatorRequest) { *)
( If ( (↑17 D2! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_step) ?==  $RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest ) then {
            (* // Next validation is started. Round is expired because no request from validator or proxy
            // rejected request. See onBounce function.
			round2.step = RoundStep.WaitingUnfreeze; *)
     (↑17 U1! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_step := $RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze	) >>
           (*  if (round2.completionReason == CompletionReason.Undefined) {
                round2.completionReason = CompletionReason.NoValidatorRequest;
			} *)
	 (If (↑17 D2! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_completionReason ?== $ RoundsBase_ι_CompletionReasonP_ι_Undefined) then {
		↑17 U1! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_completionReason := $RoundsBase_ι_CompletionReasonP_ι_NoValidatorRequest
	 })	>>	
		   (*  round2.unfreeze = 0; *)
	 (↑17 U1! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_unfreeze := $xInt0)	   
} 
		(* else if (round2.step == RoundStep.Completing) { *)
else {
	 If ((↑17 D2! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_step) ?==  $RoundsBase_ι_RoundStepP_ι_Completing ) then {
		->sendMessage {|| contractMessage := {|| messageBounce := $xBoolFalse ||}, 
						  contractFunction :=  DePoolContract_Ф_completeRoundWithChunkF (!! ↑17 D2! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_id , 
						  																	 $ xInt1 !!)  ||}
	} } ) >> 

(* if (round2.vsetHashInElectionPhase != curValidatorHash &&
            round2.vsetHashInElectionPhase != prevValidatorHash &&
			round2.unfreeze == DePoolLib.MAX_TIME) *)
			
(If ( ((↑17 D2! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_vsetHashInElectionPhase) ?!= $Л_curValidatorHash) !&
	  ((↑17 D2! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_vsetHashInElectionPhase) ?!= $Л_prevValidatorHash) !&
	  ((↑17 D2! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_unfreeze) ?== ↑9 D2! DePoolLib_ι_MAX_TIME)) then {
		  (* // try to update unfreeze time
         {
            // at least 1 validation period is skipped
            round2.unfreeze = validationStart + round2.stakeHeldFor;
        } *)
        (↑17 U1! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_unfreeze := 
                          $Л_validationStart !+ 
                          (D1! (D2! LocalState_ι_updateRound2_Л_round2) ^^ RoundsBase_ι_Round_ι_stakeHeldFor))
} ) >> 


(
	(* if (now >= uint(round2.unfreeze) + DePoolLib.ELECTOR_UNFREEZE_LAG) { *)
	If ( tvm_now () ?>=  ((↑17 D2! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_unfreeze) !+
						  (↑9  D2! DePoolLib_ι_ELECTOR_UNFREEZE_LAG))  ) then {
		(* if (round2.step == RoundStep.WaitingUnfreeze &&
                round2.completionReason != CompletionReason.Undefined
			) *)
		If ( ((↑17 D2! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_step) ?== $RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze )  !& 
		     ((↑17 D2! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_completionReason) ?!= $RoundsBase_ι_CompletionReasonP_ι_Undefined)) then {
                (* round2 = startRoundCompleting(round2, round2.completionReason); *)
           ↑↑17 U2! LocalState_ι_updateRound2_Л_round2	 := DePoolContract_Ф_startRoundCompleting (! 
                            ↑17 D2! LocalState_ι_updateRound2_Л_round2 , 
														↑17 D2! LocalState_ι_updateRound2_Л_round2 ^^  RoundsBase_ι_Round_ι_completionReason  !)
		}	else {
			(* if (
                round2.step == RoundStep.WaitingValidationStart ||
                round2.step == RoundStep.WaitingUnfreeze
			) *)
			If ( ((↑17 D2! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_step) ?== $RoundsBase_ι_RoundStepP_ι_WaitingValidationStart) !| 
				 ((↑17 D2! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_step) ?== $RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze) ) then {
				(*  {
                // recover stake and complete round
                round2.step = RoundStep.WaitingReward;
                _recoverStake(round2.proxy, round2.id, round2.elector);
			} *)
			(↑17 U1! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_step := $RoundsBase_ι_RoundStepP_ι_WaitingReward) >>
			(ProxyBase_Ф__recoverStake (! ↑17 D2! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_proxy , 
										  ↑17 D2! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_id , 
										  ↑17 D2! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_elector !))
			}
           
		}
	}
) >>

(* return round2;*)

(↑17 D2! LocalState_ι_updateRound2_Л_round2).


(* function isEmptyRound(Round round) private pure returns (bool) {
    return round.step == RoundStep.Completed || round.stake == 0;
} *)

Definition DePoolContract_Ф_isEmptyRound (Л_round: RoundsBase_ι_Round) : LedgerT XBool := 
    ($(Л_round ->> RoundsBase_ι_Round_ι_step) ?== $RoundsBase_ι_RoundStepP_ι_Completed !& 
     $(Л_round ->> RoundsBase_ι_Round_ι_stake) ?== $xInt0).



(* 
function updateRounds() private {

        (, uint32 electionsStartBefore,,) = roundTimeParams();
        (uint256 curValidatorHash, uint32 validationStart, uint32 validationEnd) = getCurValidatorData();
        uint256 prevValidatorHash = getPrevValidatorHash();
        bool areElectionsStarted = now >= validationEnd - electionsStartBefore;
        Round roundPre0 = getRoundPre0(); // round is in pre-pooling phase
        Round round0    = getRound0(); // round is in pooling phase
        Round round1    = getRound1(); // round is in election or validation phase
        Round round2    = getRound2(); // round is in validation or investigation round

        // Try return rest part of balance to validator and delete account
        if (m_poolClosed && isEmptyRound(round2) && isEmptyRound(round1) && isEmptyRound(round0) && isEmptyRound(roundPre0) ) {
            selfdestruct(m_validatorWallet);
            tvm.exit();
        }

        round2 = updateRound2(round2, prevValidatorHash, curValidatorHash, validationStart);

        // New validator set is set. Let's recover stake to know if we win the elections
        if (round1.step == RoundStep.WaitingValidationStart &&
            round1.vsetHashInElectionPhase == prevValidatorHash
        )
        {
            round1.step = RoundStep.WaitingIfValidatorWinElections;
            _recoverStake(round1.proxy, round1.id, round1.elector);
        }

        // try to switch rounds
        if (areElectionsStarted && // elections are started
            round1.vsetHashInElectionPhase != curValidatorHash && // and pooling round is not switch to election phase yet
            round2.step == RoundStep.Completed // and round2 completed (stakes are reinvested to pooling round)
        ) {
            // we need to rotate rounds
            delete m_rounds[round2.id];
            round2 = round1;
            round1 = round0;
            round0 = roundPre0;
            roundPre0 = generateRound();

            // upd round2
            round2 = updateRound2(round2, prevValidatorHash, curValidatorHash, validationStart);

            // upd round1
            if (!m_poolClosed) {
                round1.supposedElectedAt = validationEnd;
                round1.elector = getElector();
                round1.vsetHashInElectionPhase = curValidatorHash;
                (, , ,uint32 stakeHeldFor) = roundTimeParams();
                round1.stakeHeldFor = stakeHeldFor;
                // check that validator wallet made a necessary minimal stake in round
                round1.validatorStake = stakeSum(round1.stakes[m_validatorWallet]);
                bool isValidatorStakeOk  = round1.validatorStake >= m_validatorAssurance;
                if (!isValidatorStakeOk) {
                    round1.step = RoundStep.WaitingUnfreeze;
                    round1.completionReason = CompletionReason.ValidatorStakeIsTooSmall;
                    round1.unfreeze = 0;
                } else {
                    round1.step = RoundStep.WaitingValidatorRequest;
                    emit StakeSigningRequested(round1.supposedElectedAt, round1.proxy);
                }
            }

            // upd round0
            if (!m_poolClosed)
                round0.step = RoundStep.Pooling;
        }

        setRoundPre0(roundPre0);
        setRound0(round0);
        setRound1(round1);
        setRound2(round2);
    }


 *)

Check I.
Parameter selfdestruct : XAddress -> LedgerT True.
Definition tvm_exit : LedgerT ( XValueValue True) := return! (xError I).

Notation "'->selfdestruct' a" := (do a' ← a; selfdestruct a') (at level 20).

(* Notation "'do' a ← e '???;' c" := (e >>= fun ea => xErrorMapDefaultF (fun a => c) ea (fun er => return! (xValue (xError er)))) 
                                   (at level 60, right associativity): solidity_scope. *)
(* Notation " 'If2!!' g 'then' '{' y '}' ; c " := ( do g' ← g ; do _ ← ( xBoolIfElse g' y (return! (xValue I))) ???; c )(at level 21, g at level 22, y at level 22, c at level 60, right associativity): solidity_scope.
 *)

(*  Check If2!! ((↑ε12 DePoolContract_ι_m_poolClosed ) !& 
 (DePoolContract_Ф_isEmptyRound (! ↑17 D2! LocalState_ι_updateRounds_Л_round2  !) ) !& 
 (DePoolContract_Ф_isEmptyRound (! ↑17 D2! LocalState_ι_updateRounds_Л_round1  !) ) !& 
 (DePoolContract_Ф_isEmptyRound (! ↑17 D2! LocalState_ι_updateRounds_Л_round0  !) ) !& 
 (DePoolContract_Ф_isEmptyRound (! ↑17 D2! LocalState_ι_updateRounds_Л_roundPre0  !))) then {
     (->selfdestruct ( ↑2 D2! ValidatorBase_ι_m_validatorWallet )) >>
     tvm_exit
 }; $ (xError 2). *)


Definition DePoolContract_Ф_updateRounds : LedgerT (XErrorValue (XValueValue True) XInteger) := 
(* (, uint32 electionsStartBefore,,) = roundTimeParams(); *)
U0! {( _ ,  Л_electionsStartBefore  , _ , _ )} ??:= ConfigParamsBase_Ф_roundTimeParams () ;
(* (uint256 curValidatorHash, uint32 validationStart, uint32 validationEnd) = getCurValidatorData(); *)
U0! {( Л_curValidatorHash,  Л_validationStart , Л_validationEnd )} ??:= ConfigParamsBase_Ф_getCurValidatorData () ;
(*uint256 prevValidatorHash = getPrevValidatorHash();*)
U0! Л_prevValidatorHash ??:= ConfigParamsBase_Ф_getPrevValidatorHash () ;
(*bool areElectionsStarted = now >= validationEnd - electionsStartBefore;*)
U0! Л_areElectionsStarted := (tvm_now () ?>  $Л_validationEnd !- $Л_electionsStartBefore) ;

(*Round roundPre0 = getRoundPre0(); *)
(↑↑17 U2! LocalState_ι_updateRounds_Л_roundPre0 := RoundsBase_Ф_getRoundPre0 () ) >>
(*Round round0    = getRound0();*)
(↑↑17 U2! LocalState_ι_updateRounds_Л_round0 := RoundsBase_Ф_getRound0 () ) >>
(*Round round1    = getRound1();*)
(↑↑17 U2! LocalState_ι_updateRounds_Л_round1 := RoundsBase_Ф_getRound1 () ) >>
(* Round round2    = getRound2(); *)
(↑↑17 U2! LocalState_ι_updateRounds_Л_round2 := RoundsBase_Ф_getRound2 () ) >> 

(*         if (m_poolClosed && isEmptyRound(round2) && isEmptyRound(round1) && isEmptyRound(round0) && isEmptyRound(roundPre0) ) {
            selfdestruct(m_validatorWallet);
            tvm.exit();
        } *)
If2!! ((↑ε12 DePoolContract_ι_m_poolClosed ) !& 
    (DePoolContract_Ф_isEmptyRound (! ↑17 D2! LocalState_ι_updateRounds_Л_round2  !) ) !& 
    (DePoolContract_Ф_isEmptyRound (! ↑17 D2! LocalState_ι_updateRounds_Л_round1  !) ) !& 
    (DePoolContract_Ф_isEmptyRound (! ↑17 D2! LocalState_ι_updateRounds_Л_round0  !) ) !& 
    (DePoolContract_Ф_isEmptyRound (! ↑17 D2! LocalState_ι_updateRounds_Л_roundPre0  !))) then {
        (->selfdestruct ( ↑2 D2! ValidatorBase_ι_m_validatorWallet )) >>
        tvm_exit
    }; 

(*round2 = updateRound2(round2, prevValidatorHash, curValidatorHash, validationStart);*)
(↑↑17 U2! LocalState_ι_updateRounds_Л_round2 := DePoolContract_Ф_updateRound2 (! ↑17 D2! LocalState_ι_updateRounds_Л_round2 ,
																				  $ Л_prevValidatorHash , 
																				  $ Л_curValidatorHash , 
                                                                                  $ Л_validationStart  !)) >>

(*
// New validator set is set. Let's recover stake to know if we win the elections
if (round1.step == RoundStep.WaitingValidationStart &&
	round1.vsetHashInElectionPhase == prevValidatorHash
)
{
	round1.step = RoundStep.WaitingIfValidatorWinElections;
	_recoverStake(round1.proxy, round1.id, round1.elector);
}
*)

(If ( (↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_step  ?== $ RoundsBase_ι_RoundStepP_ι_WaitingValidationStart) !& 
(↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_vsetHashInElectionPhase ?== $ Л_prevValidatorHash)) then {

(↑17 U1! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_step := $ RoundsBase_ι_RoundStepP_ι_WaitingIfValidatorWinElections) >> 
ProxyBase_Ф__recoverStake (! ↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_proxy , 
                           ↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_id , 
                           ↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_elector  !)
}) >> 
                                                                                   
(*// try to switch rounds
if (areElectionsStarted && // elections are started
	round1.vsetHashInElectionPhase != curValidatorHash && // and pooling round is not switch to election phase yet
	round2.step == RoundStep.Completed // and round2 completed (stakes are reinvested to pooling round)
) {*)																				  
If! ($ Л_areElectionsStarted !&
	 (↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_vsetHashInElectionPhase ?!= $ Л_curValidatorHash) !&
	 (↑17 D2! LocalState_ι_updateRounds_Л_round2 ^^ RoundsBase_ι_Round_ι_step ?!= $ RoundsBase_ι_RoundStepP_ι_Completed)) then {
		(*delete m_rounds[round2.id];*)
		(↑↑11 U2! delete RoundsBase_ι_m_rounds [[ ↑17 D2! LocalState_ι_updateRounds_Л_round2 ^^ RoundsBase_ι_Round_ι_id  ]]) >>
		(*// we need to rotate rounds
		 round2 = round1;*)
		(↑17 U1! LocalState_ι_updateRounds_Л_round2 :=  D2! LocalState_ι_updateRounds_Л_round1) >>
		(*round1 = round0;*)
		(↑17 U1! LocalState_ι_updateRounds_Л_round1 :=  D2! LocalState_ι_updateRounds_Л_round0) >>
        (*round0 = roundPre0;*)
        (↑17 U1! LocalState_ι_updateRounds_Л_round0 :=  D2! LocalState_ι_updateRounds_Л_roundPre0) >>
        (*roundPre0 = generateRound();*)
		(↑↑17 U2! LocalState_ι_updateRounds_Л_roundPre0 := DePoolContract_Ф_generateRound () ) >>
        
        (*round2 = updateRound2(round2, prevValidatorHash, curValidatorHash, validationStart, stakeHeldFor);*)
		(↑↑17 U2! LocalState_ι_updateRounds_Л_round2 := DePoolContract_Ф_updateRound2 (! ↑17 D2! LocalState_ι_updateRounds_Л_round2 ,
																				  $ Л_prevValidatorHash , 
																				  $ Л_curValidatorHash , 
                                                                                  $ Л_validationStart  !) ) >> 

        If! ( !¬ (↑12 D2! DePoolContract_ι_m_poolClosed) ) then {                                                                              
            (*round1.supposedElectedAt = validationEnd;*)
            (↑17 U1! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_supposedElectedAt := $ 	Л_validationEnd) >> 
            (*round1.elector = getElector();*)
            ↑↑17 U2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_elector ??:= ConfigParamsBase_Ф_getElector ()  ;
            (*round1.vsetHashInElectionPhase = curValidatorHash;*)
            (↑17 U1! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_vsetHashInElectionPhase := $ Л_curValidatorHash) >>
            (*(, , ,uint32 stakeHeldFor) = roundTimeParams();*)
            U0! {( _ ,  _  , _ , Л_stakeHeldFor )} ?:= ConfigParamsBase_Ф_roundTimeParams () ; 
            (* round1.stakeHeldFor = stakeHeldFor; *)
            (↑17 U1! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_stakeHeldFor := $Л_stakeHeldFor) >>

            (* // check that validator wallet made a necessary minimal stake in round
                    round1.validatorStake = stakeSum(round1.stakes[m_validatorWallet]);
                    bool isValidatorStakeOk  = round1.validatorStake >= m_validatorAssurance; *)
            (↑↑17 U2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_validatorStake := 
                    RoundsBase_Ф_stakeSum  (!  D1! (↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_stakes) [[ ↑2 D2! ValidatorBase_ι_m_validatorWallet  ]] !)) >>
            U0! Л_isValidatorStakeOk :=  (↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_validatorStake) ?>= 
                                         (↑12 D2! DePoolContract_ι_m_validatorAssurance)	; 
            (*if (!isValidatorStakeOk) {
            round1.step = RoundStep.WaitingUnfreeze;
            round1.completionReason = CompletionReason.ValidatorStakeIsTooSmall;
            round1.unfreeze = 0;
        } else {
            round1.step = RoundStep.WaitingValidatorRequest;
            emit stakeSigningRequested(round1.supposedElectedAt, round1.proxy);
        }*)
            (If ( !¬ $ Л_isValidatorStakeOk ) then  {
                (↑17 U1! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_step := $ RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze) >> 
                (↑17 U1! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_completionReason := $ RoundsBase_ι_CompletionReasonP_ι_ValidatorStakeIsTooSmall) >> 
                (↑17 U1! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_unfreeze := $xInt0)
            } else {
                (↑17 U1! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_step := $ RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest) >> 
                (->emit StakeSigningRequested (!! ↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_supposedElectedAt , 
                                                ↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_proxy   !!))
            })  }; 
            (* if (!m_poolClosed)
                round0.step = RoundStep.Pooling; *)

            (If ( !¬ (↑12 D2! DePoolContract_ι_m_poolClosed) ) then {
                (↑17 U1! LocalState_ι_updateRounds_Л_round0 ^^ RoundsBase_ι_Round_ι_step := $ RoundsBase_ι_RoundStepP_ι_Pooling)
            })    
            
            }  ; 
            
            (*         setRoundPre0(roundPre0);
                        setRound0(round0);
                        setRound1(round1);
                        setRound2(round2); *)
           ( RoundsBase_Ф_setRoundPre0 (! ↑17 D2! LocalState_ι_updateRounds_Л_roundPre0  !) ) >>
           ( RoundsBase_Ф_setRound0 (! ↑17 D2! LocalState_ι_updateRounds_Л_round0  !) ) >>
           ( RoundsBase_Ф_setRound1 (! ↑17 D2! LocalState_ι_updateRounds_Л_round1  !) ) >>
           ( RoundsBase_Ф_setRound2 (! ↑17 D2! LocalState_ι_updateRounds_Л_round2  !) )  >>
           $ (xValue I) .	

(* 
function ticktock() public override  { 
        require(msg.sender != address(0), Errors.IS_EXT_MSG);

        if (checkPureDePoolBalance()) (*<<<<<<<<<<<<<<<<<<<<<<<<<<<<*)
        {
            updateRounds();
        }
        if (msg.sender != address(this))
            _returnChange();
    }
*)
    
Definition DePoolContract_Ф_ticktock :  LedgerT ( XErrorValue True XInteger ) :=
 Require2 {{ msg_sender () ?!= $xInt0, ↑7 D2! Errors_ι_IS_EXT_MSG }} ;  
 If! (DePoolContract_Ф_checkPureDePoolBalance () ) then 
 { U0! _ ?:= DePoolContract_Ф_updateRounds  ; $I } ;
 (If (msg_sender () ?!= tvm_address () ) then {
    DePoolContract_Ф__returnChange ()
 }).
      


(*  function cutDePoolReward(uint64 reward, Round round2) private view returns (uint64) {
        uint64 balance = uint64(address(this).balance);
        // round2 in state WaitingRoundReward but reward is received
        uint64 roundStakes = round2.stake + totalParticipantFunds(round2.id);

        // if after sending rewards DePool balance (without round stakes) become less m_minimumBalance
        (*TODO: old:  if (balance < m_minimumBalance + roundStakes + reward) {
            uint64 dePoolReward = math.min(reward, m_minimumBalance, m_minimumBalance + roundStakes + reward - balance); *)            reward -= dePoolReward;
        (*TODO: new: *)if (balance < m_balanceThreshold + roundStakes + reward) {
>       (*TODO: new: *)uint64 dePoolReward = math.min(reward, m_balanceThreshold + roundStakes + reward - balance);
        }
        return reward;
    } *)

Definition DePoolContract_Ф_cutDePoolReward (Л_reward : XInteger64) (Л_round2 : RoundsBase_ι_Round) : LedgerT XInteger64 := 
    (↑17 U1! LocalState_ι_cutDePoolReward_Л_reward := $ Л_reward) >>

    U0! Л_balance := tvm_balance () ;
    U0! Л_roundStakes := $ (Л_round2 ->> RoundsBase_ι_Round_ι_stake) !+ 
                         DePoolContract_Ф_totalParticipantFunds (! $ (Л_round2 ->> RoundsBase_ι_Round_ι_id) !) ; 
    (If ( $ Л_balance ?< (↑ε12 DePoolContract_ι_m_balanceThreshold) !+ $ Л_roundStakes !+ (↑17 D2! LocalState_ι_cutDePoolReward_Л_reward) ) then {
        U0! Л_dePoolReward := math->min2 (! (↑17 D2! LocalState_ι_cutDePoolReward_Л_reward) , 
                    (↑ε12 DePoolContract_ι_m_balanceThreshold) !+ $ Л_roundStakes !+ (↑17 D2! LocalState_ι_cutDePoolReward_Л_reward) !- $Л_balance  !) ;
        (↑17 U1! LocalState_ι_cutDePoolReward_Л_reward !-= $ Л_dePoolReward)
        
    } ) >> (↑17 D2! LocalState_ι_cutDePoolReward_Л_reward)  .
    
 

 (*     
function acceptRewardAndStartRoundCompleting(Round round2, uint64 value) private returns (Round) {
        uint64 effectiveStake = round2.stake - round2.unused;
        uint64 reward = value - effectiveStake;

        (*TODO:new:*)round2.grossReward = reward;

        reward = cutDePoolReward(reward, round2);
        round2.rewards = math.muldiv(reward, m_participantRewardFraction, 100);
        round2.rewards -= math.min(round2.rewards, round2.participantQty * RET_OR_REINV_FEE);
        uint64 validatorReward = math.muldiv(reward, m_validatorRewardFraction, 100);
        if (validatorReward != 0)
            m_validatorWallet.transfer(validatorReward, false, 1);

        uint64 associationReward = math.muldiv(reward, m_associationRewardFraction, 100);
        if (associationReward != 0)
            m_association.transfer(associationReward, false, 1);

        round2 = startRoundCompleting(round2, CompletionReason.RewardIsReceived);
        return round2;
    }
 *)
    

Definition DePoolContract_Ф_acceptRewardAndStartRoundCompleting ( Л_round2 : RoundsBase_ι_Round )( Л_value : XInteger64 ) : LedgerT RoundsBase_ι_Round := 
(* uint64 effectiveStake = round2.stake - round2.unused; *)
U0! Л_effectiveStake := $ (Л_round2 ->> RoundsBase_ι_Round_ι_stake) !- $ (Л_round2 ->> RoundsBase_ι_Round_ι_unused) ; 
(* uint64 reward = value - effectiveStake; *)
U0! Л_reward := $ Л_value !- $ Л_effectiveStake; 
             (* round2.grossReward = reward; *)
U0! Л_round2 ^^ RoundsBase_ι_Round_ι_grossReward := $ Л_reward ;
(* reward = cutDePoolReward(reward, round2);*)
U0! Л_reward := DePoolContract_Ф_cutDePoolReward (! $Л_reward, $Л_round2 !) ;
(* round2.rewards = math.muldiv(reward, m_participantRewardFraction, 100); *)
U0! Л_round2 ^^ RoundsBase_ι_Round_ι_rewards := math->muldiv (! $ Л_reward, 
                                                ↑12 D2! DePoolContract_ι_m_participantRewardFraction , 
                                                $xInt100 !) ;
(* round2.rewards -= math.min(round2.rewards, round2.participantQty * RET_OR_REINV_FEE); *)  
U0! Л_round2 ^^ RoundsBase_ι_Round_ι_rewards !-= math->min2 (! $ (Л_round2 ->> RoundsBase_ι_Round_ι_rewards) ,
                                                              ($ (Л_round2 ->> RoundsBase_ι_Round_ι_participantQty)) !* (↑12 D2! DePoolContract_ι_RET_OR_REINV_FEE)  !) ;  

(* uint64 validatorReward = math.muldiv(reward, m_validatorRewardFraction, 100); *)
U0! Л_validatorReward := math->muldiv (! $ Л_reward, ↑12 D2! DePoolContract_ι_m_validatorRewardFraction , $xInt100 !) ; 
(* if (validatorReward != 0)
            m_validatorWallet.transfer(validatorReward, false, 1); *)
(If ($ Л_validatorReward ?!= $xInt0 ) then { 
    (↑2 D2! ValidatorBase_ι_m_validatorWallet) ->transfer (! $ Л_validatorReward,  $ xBoolFalse , $ xInt1 !)
    } ) >> 
(* round2 = startRoundCompleting(round2, CompletionReason.RewardIsReceived); *)
U0! Л_round2 := DePoolContract_Ф_startRoundCompleting (! $Л_round2 , $ RoundsBase_ι_CompletionReasonP_ι_RewardIsReceived !);
(* return round2; *)
$ Л_round2.


 
(* 
function onSuccessToRecoverStake(uint64 queryId, address elector) public override {
        optional(Round) optRound = fetchRound(queryId);
        require(optRound.hasValue(), InternalErrors.ERROR513);
        Round round = optRound.get();
        require(msg.sender == round.proxy, Errors.IS_NOT_PROXY);
        require(elector == round.elector, Errors.IS_NOT_ELECTOR);
        tvm.accept();
        uint64 value = uint64(msg.value) + DePoolLib.PROXY_FEE;
        if (round.step == RoundStep.WaitingIfValidatorWinElections) {
            if (value < round.stake) {
                // only part of round stake is returned - we won the election,
                // but round stake is cut-off by elector,
                // optimize a minimum round stake
                round.step = RoundStep.WaitingUnfreeze;
                round.unused = value;
            } else {
                // value +/- epsilon == round.stake, so elections are lost
                round.step = RoundStep.WaitingUnfreeze;
                round.completionReason = CompletionReason.ElectionsAreLost;
            }
        } else if (round.step == RoundStep.WaitingReward) {
            round.recoveredStake = value; (*<<<<<<<<<<<<<<<<<<<<<*)
            if (value >= round.stake - round.unused) {
                round = acceptRewardAndStartRoundCompleting(round, value);
            } else {
                round = startRoundCompleting(round, CompletionReason.ValidatorIsPunished);
               (*<<<<<<<<<<<<<<<<<<<<<<<<<*)
            }
        } else {
            revert(InternalErrors.ERROR521);
        }

        setRound(queryId, round); (*<<<<<<<<<<<<<<<<<<<<<*)
    }

*)

Definition DePoolContract_Ф_onSuccessToRecoverStake ( Л_queryId : XInteger64 ) ( Л_elector : XAddress ) : LedgerT ( XErrorValue True XInteger ) := 
(*optional(Round) optRound = fetchRound(queryId);*)	
U0! Л_optRound :=  RoundsBase_Ф_fetchRound (! $Л_queryId !) ;
(* require(optRound.hasValue(), InternalErrors.ERROR513);*)
Require2 {{ $ Л_optRound ->hasValue , ↑8 D2! InternalErrors_ι_ERROR513 }} ; 
(* Round round = optRound.get();*)
U0! Л_round := ($ Л_optRound) ->get ;
(*require(msg.sender == round.proxy, Errors.IS_NOT_PROXY);*)
Require2 {{ msg_sender () ?== $ Л_round ->> RoundsBase_ι_Round_ι_proxy , ↑7 D2! Errors_ι_IS_NOT_PROXY }} ; 
(*require(elector == round.elector, Errors.IS_NOT_ELECTOR);*)
Require2 {{ $ Л_elector ?== $ Л_round ->> RoundsBase_ι_Round_ι_elector , ↑7 D2! Errors_ι_IS_NOT_ELECTOR }} ; 

(tvm_accept ()) >>

(*init*)
(↑17 U1! LocalState_ι_onSuccessToRecoverStake_Л_round := $ Л_round) >>
(* uint64 value = uint64(msg.value) + DePoolLib.PROXY_FEE;*)
U0! Л_value := msg_value () !+ ↑9 D2! DePoolLib_ι_PROXY_FEE ;

(*if (round.step == RoundStep.WaitingIfValidatorWinElections) { *)
If! (↑17 D2! LocalState_ι_onSuccessToRecoverStake_Л_round ^^ RoundsBase_ι_Round_ι_step ?== $ RoundsBase_ι_RoundStepP_ι_WaitingIfValidatorWinElections) then { 
(*if (value < round.stake) {*)
(If ($Л_value ?< (↑17 D2! LocalState_ι_onSuccessToRecoverStake_Л_round ^^ RoundsBase_ι_Round_ι_stake )) then  {
(* // only part of round stake is returned - we won the election,
// but round stake is cut-off by elector,
// optimize a minimum round stake
round.step = RoundStep.WaitingUnfreeze;
round.unused = value; *)
(↑17 U1! LocalState_ι_onSuccessToRecoverStake_Л_round ^^ RoundsBase_ι_Round_ι_step := $ RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze )	>>
(↑17 U1! LocalState_ι_onSuccessToRecoverStake_Л_round ^^ RoundsBase_ι_Round_ι_unused := $ Л_value)
} else {
(*// value +/- epsilon == round.stake, so elections are lost
round.step = RoundStep.WaitingUnfreeze;
round.completionReason = CompletionReason.ElectionsAreLost;*)
(↑17 U1! LocalState_ι_onSuccessToRecoverStake_Л_round ^^ RoundsBase_ι_Round_ι_step := $ RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze )	>>
(↑17 U1! LocalState_ι_onSuccessToRecoverStake_Л_round ^^ RoundsBase_ι_Round_ι_completionReason := $ RoundsBase_ι_CompletionReasonP_ι_ElectionsAreLost)
}) >> $ (xValue I)
} 
(*} else if (round.step == RoundStep.WaitingReward) {*)		
else {     
If (↑17 D2! LocalState_ι_onSuccessToRecoverStake_Л_round ^^ RoundsBase_ι_Round_ι_step ?== $ RoundsBase_ι_RoundStepP_ι_WaitingReward) then  {
(* round.recoveredStake = value; *)
(↑17 U1! LocalState_ι_onSuccessToRecoverStake_Л_round ^^ RoundsBase_ι_Round_ι_recoveredStake := $ Л_value) >>
(* if (value >= round.stake - round.unused) { *)	
(If ($ Л_value ?>= (↑17 D2! LocalState_ι_onSuccessToRecoverStake_Л_round ^^ RoundsBase_ι_Round_ι_stake) !- (↑17 D2! LocalState_ι_onSuccessToRecoverStake_Л_round ^^ RoundsBase_ι_Round_ι_unused) ) then  {
(*round = acceptRewardAndStartRoundCompleting(round, value);*)
↑↑17 U2! LocalState_ι_onSuccessToRecoverStake_Л_round := DePoolContract_Ф_acceptRewardAndStartRoundCompleting(! ↑17 D2! LocalState_ι_onSuccessToRecoverStake_Л_round , 
                                                                            $ Л_value !)

} else {
(*round = startRoundCompleting(round, CompletionReason.ValidatorIsPunished);*)
↑↑17 U2! LocalState_ι_onSuccessToRecoverStake_Л_round := DePoolContract_Ф_startRoundCompleting(! ↑17 D2! LocalState_ι_onSuccessToRecoverStake_Л_round , 
                                                                  $ RoundsBase_ι_CompletionReasonP_ι_ValidatorIsPunished !) 
}) >> $ (xValue I)
} else {
(*revert(InternalErrors.ERROR521);*)
tvm_revert (! ↑8 D2! InternalErrors_ι_ERROR521  !)
} } ;

(* setRound(queryId, round); *)
(RoundsBase_Ф_setRound (! $Л_queryId , ↑17 D2! LocalState_ι_onSuccessToRecoverStake_Л_round  !) ). 



(* 
function onFailToRecoverStake(uint64 queryId, address elector) public override {
        optional(Round) optRound = 
                                   fetchRound(queryId); (*<<<<<<<<<<<<<<<<<<<<<*)
        require(optRound.hasValue(), InternalErrors.ERROR513);
        Round round = optRound.get();
        require(msg.sender == round.proxy, Errors.IS_NOT_PROXY);
        require(elector == round.elector, Errors.IS_NOT_ELECTOR);
        tvm.accept();                                     (*<<<<<<<<<<<<<<<<<<<*)
        if (round.step == RoundStep.WaitingIfValidatorWinElections) {
            // DePool win elections and our stake is locked by elector.
             round.step = RoundStep.WaitingUnfreeze;
        } else if (round.step == RoundStep.WaitingReward) {
            // Validator is banned! Cry.
            round = startRoundCompleting(round, CompletionReason.ValidatorIsPunished);
        } else {
            revert(InternalErrors.ERROR521);
        }
        setRound(queryId, round);              (* <<<<<<<<<<<<<<<<<<<<<<<<< *)
    }

function onFailToRecoverStake(uint64 queryId, address elector) public override {
        optional(Round) optRound = m_rounds.fetch(queryId);
        require(optRound.hasValue(), InternalErrors.ERROR513);
        Round round = optRound.get();
        require(msg.sender == round.proxy, Errors.IS_NOT_PROXY);
        require(elector == round.elector, Errors.IS_NOT_ELECTOR);
        if (round.step == RoundStep.WaitingIfValidatorWinElections) {
            // DePool win elections and our stake is locked by elector.
             round.step = RoundStep.WaitingUnfreeze;
        } else if (round.step == RoundStep.WaitingReward) {
            // Validator is banned! Cry.
            round = startRoundCompleting(round, CompletionReason.ValidatorIsPunished);
        } else {
            revert(InternalErrors.ERROR521);
        }
        m_rounds[queryId] = round;
	} *)
    
Definition DePoolContract_Ф_onFailToRecoverStake ( Л_queryId : XInteger64 ) ( Л_elector : XAddress ) : LedgerT ( XErrorValue True XInteger ) := 
(*optional(Round) optRound = fetchRound(queryId);*)	
U0! Л_optRound :=  RoundsBase_Ф_fetchRound (! $Л_queryId !) ;
(* require(optRound.hasValue(), InternalErrors.ERROR513);*)
Require2 {{ $ Л_optRound ->hasValue , ↑8 D2! InternalErrors_ι_ERROR513 }} ; 
(* Round round = optRound.get();*)
U0! Л_round := ($ Л_optRound) ->get ;
(*require(msg.sender == round.proxy, Errors.IS_NOT_PROXY);*)
Require2 {{ msg_sender () ?== $ Л_round ->> RoundsBase_ι_Round_ι_proxy , ↑7 D2! Errors_ι_IS_NOT_PROXY }} ; 
(*require(elector == round.elector, Errors.IS_NOT_ELECTOR);*)
Require2 {{ $ Л_elector ?== $ Л_round ->> RoundsBase_ι_Round_ι_elector , ↑7 D2! Errors_ι_IS_NOT_ELECTOR }} ; 
tvm_accept () >>
(*init*)
(↑17 U1! LocalState_ι_onFailToRecoverStake_Л_round := $ Л_round) >> 
(*
if (round.step == RoundStep.WaitingIfValidatorWinElections) {
// DePool win elections and our stake is locked by elector.
round.step = RoundStep.WaitingUnfreeze;
} else if (round.step == RoundStep.WaitingReward) {
// Validator is banned! Cry.
round = startRoundCompleting(round, CompletionReason.ValidatorIsPunished);
} else {
revert(InternalErrors.ERROR521);
}
*)
If! (↑17 D2! LocalState_ι_onFailToRecoverStake_Л_round ^^ RoundsBase_ι_Round_ι_step ?== $ RoundsBase_ι_RoundStepP_ι_WaitingIfValidatorWinElections) then {
(↑17 U1! LocalState_ι_onFailToRecoverStake_Л_round ^^ RoundsBase_ι_Round_ι_step := $ RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze ) >>
$ (xValue I)
} else { If (↑17 D2! LocalState_ι_onFailToRecoverStake_Л_round ^^ RoundsBase_ι_Round_ι_step ?== $ RoundsBase_ι_RoundStepP_ι_WaitingReward) then  {
↑↑17 U2! LocalState_ι_onFailToRecoverStake_Л_round := DePoolContract_Ф_startRoundCompleting(! ↑17 D2! LocalState_ι_onFailToRecoverStake_Л_round , 
                                                             $ RoundsBase_ι_CompletionReasonP_ι_ValidatorIsPunished !) >> 
$ (xValue I)
} else {
tvm_revert (! ↑8 D2! InternalErrors_ι_ERROR521  !)
} } ;

(* setRound(queryId, round); *)
( RoundsBase_Ф_setRound (! $Л_queryId ,  ↑17 D2! LocalState_ι_onFailToRecoverStake_Л_round !) ). 


   (* interface DePoolInfoGetter {
         function receiveDePoolInfo(LastRoundInfo lastRoundInfo) external; } *)
   (* function getLastRoundInfo() public view {
        if (lastRoundInfo.empty()) {
            LastRoundInfo info;
            IDePoolInfoGetter(msg.sender).receiveDePoolInfo(info);
        } else {
            IDePoolInfoGetter(msg.sender).receiveDePoolInfo(lastRoundInfo[false]);
        }
    } *)

(* 
function terminator() public {
        require(msg.pubkey() == tvm.pubkey() || msg.sender == address(this), Errors.IS_NOT_OWNER_OR_SELF_CALL);
        require(!m_poolClosed, Errors.DEPOOL_IS_CLOSED);
        m_poolClosed = true;
        tvm.commit();
        tvm.accept();
(* Далее множество изменений *)
        Round roundPre0 = getRoundPre0();
        Round round0 = getRound0();
        Round round1 = getRound1();

        roundPre0 = startRoundCompleting(roundPre0, CompletionReason.PoolClosed);
        round0 = startRoundCompleting(round0, CompletionReason.PoolClosed);
        if (round1.step == RoundStep.WaitingValidatorRequest) {
            round1 = startRoundCompleting(round1, CompletionReason.PoolClosed);
        }
        emit DePoolClosed();
        setRoundPre0(roundPre0);
        setRound0(round0);
        setRound1(round1);
    }

 *)
Definition DePoolContract_Ф_terminator : LedgerT ( XErrorValue True XInteger ) := 
(*require(msg.pubkey() == tvm.pubkey() || msg.sender == address(this), Errors.IS_NOT_OWNER_OR_SELF_CALL);*)	
Require2 {{ msg_pubkey () ?== tvm_pubkey () !| msg_sender () ?== tvm_address () , ↑7 D2!  Errors_ι_IS_NOT_OWNER_OR_SELF_CALL }} ; 
(*require(!m_poolClosed, Errors.DEPOOL_IS_CLOSED);*)
Require {{ !¬ ↑12 D2! DePoolContract_ι_m_poolClosed , ↑7 D2! Errors_ι_DEPOOL_IS_CLOSED }} ; 
(* m_poolClosed = true; *)
(↑12 U1! DePoolContract_ι_m_poolClosed := $xBoolTrue) >>
(* tvm.commit(); *)
tvm_commit () >>
(* tvm.accept(); *)
tvm_accept () >>


(* Round roundPre0 = getRoundPre0(); *)
U0! Л_roundPre0 := RoundsBase_Ф_getRoundPre0 ();
(* Round round0 = getRound0(); *)
U0! Л_round0 := RoundsBase_Ф_getRound0 ();
(*Round round1 = getRound1();*)
(↑↑17 U2! LocalState_ι_terminator_Л_round1 := RoundsBase_Ф_getRound1 () ) >>

(* roundPre0 = startRoundCompleting(roundPre0, CompletionReason.PoolClosed); *)
U0! Л_roundPre0 := DePoolContract_Ф_startRoundCompleting  (! $ Л_roundPre0 , 
														$ RoundsBase_ι_CompletionReasonP_ι_PoolClosed !) ;
(*round0 = startRoundCompleting(round0, CompletionReason.PoolClosed);*)
U0! Л_round0 := DePoolContract_Ф_startRoundCompleting  (! $ Л_round0 , 
														$ RoundsBase_ι_CompletionReasonP_ι_PoolClosed !) ;
(* if (round1.step == RoundStep.WaitingValidatorRequest) {
	round1 = startRoundCompleting(round1, CompletionReason.PoolClosed);
} *)
(If (↑17 D2! LocalState_ι_terminator_Л_round1 ^^ RoundsBase_ι_Round_ι_step ?== $ RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest) then {
	↑↑17 U2! LocalState_ι_terminator_Л_round1 := DePoolContract_Ф_startRoundCompleting (! ↑17 D2! LocalState_ι_terminator_Л_round1 , 
																						  $ RoundsBase_ι_CompletionReasonP_ι_PoolClosed !) 
}) >>
(* emit DePoolClosed(); *)
->emit $ DePoolClosed >>
(* setRoundPre0(roundPre0); *)
(RoundsBase_Ф_setRoundPre0 (! $ Л_roundPre0 !) ) >>
(*  setRound0(round0);  *)
(RoundsBase_Ф_setRound0 (! $ Л_round0 !)  ) >>
(* setRound1(round1); *)
(RoundsBase_Ф_setRound1 (! ↑17 D2! LocalState_ι_terminator_Л_round1 !) ) .

(* onBounce(TvmSlice body) external {
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
    } *)

Inductive ContractFunctionWithId  :=
     
    | IProxy_И_recover_stakeF : ContractFunctionWithId
    | IProxy_И_process_new_stakeF : ContractFunctionWithId.
    

Parameter tvm_functionId : ContractFunctionWithId ->  XInteger32.

Parameter decode_uint64 : TvmSlice -> XInteger64 # TvmSlice.

(* Notation " a '->decode(uint64)' " := ( do a' ← a ; return! xInt0 )( at level 10, left associativity ): solidity_scope. *)
Notation " 'U0!' d ':=' a '->decode(uint64)' ; t " := ( let dec := decode_uint64 a in let d := xProdFst dec in let a := xProdSnd dec in t )( at level 33, left associativity , t at level 50): solidity_scope.


Definition DePoolContract_Ф_onBounce (Л_body: TvmSlice) : LedgerT (XErrorValue True XInteger) :=
    (* uint32 functionId = body.decode(uint32); *)
    U0! Л_functionId := Л_body ->decode(uint32) ; 
    (* bool isProcessNewStake = functionId == tvm.functionId(IProxy.process_new_stake); *)
    U0! Л_isProcessNewStake := ($ Л_functionId) ?== $ (tvm_functionId IProxy_И_process_new_stakeF) ;
    (* bool isRecoverStake = functionId == tvm.functionId(IProxy.recover_stake); *)
    U0! Л_isRecoverStake := ($ Л_functionId) ?== $ (tvm_functionId IProxy_И_recover_stakeF) ;
    (* if (isProcessNewStake || isRecoverStake) { *)
    If! (($Л_isProcessNewStake) !| ($Л_isRecoverStake) ) then {
     (*    uint64 roundId = body.decode(uint64); *)
     U0! Л_roundId := Л_body ->decode(uint64) ; 
     (*    optional(Round) optRound = fetchRound(roundId); *)
     (↑↑17 U2! LocalState_ι_onBounce_Л_optRound := RoundsBase_Ф_fetchRound (! $ Л_roundId !) ) >>  
     (*    if (isProcessNewStake) { *)
     If!! ($Л_isProcessNewStake) then {
     (*        require(isRound1(roundId), InternalErrors.ERROR524); *)
     ( Require2 {{ RoundsBase_Ф_isRound1 (! $ Л_roundId !)  , ↑8 D2! InternalErrors_ι_ERROR524  }} ; 
     (*        Round r1 = optRound.get(); *)
      Require2 {{ (↑17 D2! LocalState_ι_onBounce_Л_optRound) ->hasValue,  ↑8 D2! InternalErrors_ι_ERROR519 }} ; 
      U0! Л_r1 := (↑17 D2! LocalState_ι_onBounce_Л_optRound) ->get ;  
     (*        require(r1.step == RoundStep.WaitingIfStakeAccepted, InternalErrors.ERROR525); *)
      Require {{  $(Л_r1 ->> RoundsBase_ι_Round_ι_step) ?==  $RoundsBase_ι_RoundStepP_ι_WaitingIfStakeAccepted , ↑8 D2! InternalErrors_ι_ERROR525 }} ;
     (*        r1.step = RoundStep.WaitingValidatorRequest; // roll back step *)
      U0! Л_r1 ^^ RoundsBase_ι_Round_ι_step := $RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest ;
     (*        emit ProxyHasRejectedTheStake(r1.validatorRequest.queryId); *)
      (->emit (ProxyHasRejectedTheStake (!! $((Л_r1 ->> RoundsBase_ι_Round_ι_validatorRequest) ->> DePoolLib_ι_Request_ι_queryId) !!) )) >>
     (*        optRound.set(r1); *)
      (↑17 U1! LocalState_ι_onBounce_Л_optRound ->set $ Л_r1)  )
     (*    } else { *) }
     else { 
     (*        if (isRound2(roundId)) { *)
     If! (RoundsBase_Ф_isRound2 (! $ Л_roundId !)) then { 
     (*            Round r2 = optRound.get(); *)
        ( Require2 {{ (↑17 D2! LocalState_ι_onBounce_Л_optRound) ->hasValue ,  ↑8 D2! InternalErrors_ι_ERROR519 }} ; 
        U0! Л_r2 := (↑17 D2! LocalState_ι_onBounce_Л_optRound) ->get ; 
     (*            require(r2.step == RoundStep.WaitingReward, InternalErrors.ERROR526); *)
        Require {{  $(Л_r2 ->> RoundsBase_ι_Round_ι_step) ?==  $RoundsBase_ι_RoundStepP_ι_WaitingReward , ↑8 D2! InternalErrors_ι_ERROR526 }} ;
     (*            r2.step = RoundStep.WaitingUnfreeze; // roll back step *)
        U0! Л_r2 ^^ RoundsBase_ι_Round_ι_step := $RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze ;
     (*            optRound.set(r2); *)
       (↑17 U1! LocalState_ι_onBounce_Л_optRound ->set $ Л_r2)  )
     (*       } else if (isRound1(roundId)) { *)
     } else { If! (RoundsBase_Ф_isRound1 (! $ Л_roundId !)) then { 
     (*            Round r1 = optRound.get(); *)
     ( Require2 {{ (↑17 D2! LocalState_ι_onBounce_Л_optRound) ->hasValue ,  ↑8 D2! InternalErrors_ι_ERROR519 }} ; 
     U0! Л_r1 := (↑17 D2! LocalState_ι_onBounce_Л_optRound) ->get ;  
     (*            require(r1.step == RoundStep.WaitingIfValidatorWinElections, InternalErrors.ERROR527); *)
     Require {{  $(Л_r1 ->> RoundsBase_ι_Round_ι_step) ?==  $RoundsBase_ι_RoundStepP_ι_WaitingIfValidatorWinElections , ↑8 D2! InternalErrors_ι_ERROR527 }} ;
     (*            r1.step = RoundStep.WaitingValidationStart; // roll back step *)
     U0! Л_r1 ^^ RoundsBase_ι_Round_ι_step := $RoundsBase_ι_RoundStepP_ι_WaitingValidationStart ;
     (*            optRound.set(r1); *)
     (↑17 U1! LocalState_ι_onBounce_Л_optRound ->set $ Л_r1) ) }
     (*        } else { *)
              else { 
     (*           revert(InternalErrors.ERROR528); *)
     tvm_revert (! ↑8 D2! InternalErrors_ι_ERROR528  !)
     (*        } *)
     }  ; $I }; 
     (*        emit ProxyHasRejectedRecoverRequest(roundId); *)
     ->emit ProxyHasRejectedRecoverRequest (!! $ Л_roundId !!)
     (*    } *)
     } ; 
     (*    setRound(roundId, optRound.get()); *)
     Require {{ (↑17 D2! LocalState_ι_onBounce_Л_optRound) ->hasValue,  ↑8 D2! InternalErrors_ι_ERROR519 }} ; 
     RoundsBase_Ф_setRound (! $ Л_roundId, (↑17 D2! LocalState_ι_onBounce_Л_optRound) ->get !)
    }; $I.

(* Lemma or_and_neg: forall (a b: bool), orb a (andb (negb a) b) = orb a b. 
Proof.
	intros.
	destruct a,b; simpl; auto.
Qed. *)


(* 
function completeRoundWithChunk(uint64 roundId, uint8 chunkSize) public { 
        require(msg.sender == address(this), Errors.IS_NOT_DEPOOL);
        tvm.accept();
        if (!(isRound2(roundId) || m_poolClosed)) (*<<<<<<<<<<<*)
            return;
        optional(Round) optRound = fetchRound(roundId);
        require(optRound.hasValue(), InternalErrors.ERROR519);
        Round round = optRound.get();
        if (round.step != RoundStep.Completing) (*<<<<<<<<<<<<<<*)
            return;

        round = _returnOrReinvest(round, chunkSize);

(* Этот Иф едентuчный нижнему *)
        if (chunkSize < MAX_MSGS_PER_TR && !round.stakes.empty()) {
            uint8 doubleChunkSize = 2 * chunkSize;
            this.completeRoundWithChunk{flag: 1, bounce: false}(
                roundId,
                doubleChunkSize < MAX_MSGS_PER_TR? doubleChunkSize : chunkSize
            );
            this.completeRoundWithChunk{flag: 1, bounce: false}(roundId, chunkSize);
        }

        setRound(roundId, round);
    }	} *)

(* Notation "'do' a ← e '????;' c" := (e >>= fun ea => xErrorMapDefaultF (fun a => c) ea (fun er => return! (xValue (xError er)))) 
                                   (at level 60, right associativity): solidity_scope.
Notation " 'If2!' g 'then' '{' y '}' ; c " := ( do g' ← g ; do _ ← ( xBoolIfElse g' y (return! (xValue (xValue I)))) ????; c )(at level 21, g at level 22, y at level 22, c at level 60, right associativity): solidity_scope.
 *)
Definition DePoolContract_Ф_completeRoundWithChunk ( Л_roundId : XInteger64 )
                                                   ( Л_chunkSize : XInteger8 ) 
                                       : LedgerT (XErrorValue ( XValueValue True ) XInteger ) :=
Require2 {{ msg_sender () ?== tvm_address (),  ↑7 D2! Errors_ι_IS_NOT_DEPOOL }} ; 
(* tvm.accept();*)  
tvm_accept () >>  
        (* if (!(isRound2(roundId) || m_poolClosed)) 
            return; *)
If2!! ( !¬ ( ( RoundsBase_Ф_isRound2 (! $ Л_roundId !) ) !| ( ↑12 D2! DePoolContract_ι_m_poolClosed ) ) )
then
{   
  return! ( xError I )
} ;
                    (* optional(Round) optRound = fetchRound(roundId); *)
U0! Л_optRound := ( RoundsBase_Ф_fetchRound (! $ Л_roundId !) ) ; 
                    (* require(optRound.hasValue(), InternalErrors.ERROR519); *)
Require2 {{ ( $ Л_optRound ) ->hasValue , ↑8 D2! InternalErrors_ι_ERROR519 }} ;   
                    (* Round round = optRound.get(); *)
U0! Л_round := ( $ Л_optRound ) ->get ; 
                    (* if (round.step != RoundStep.Completing) 
                        return; *)
If2!! ( ↑11 D0! Л_round ^^ RoundsBase_ι_Round_ι_step ?!= $ RoundsBase_ι_RoundStepP_ι_Completing )
then
{
  return! ( xError I )
} ; 
                    (* round = _returnOrReinvest(round, chunkSize); *)
U0! Л_round ?:= DePoolContract_Ф__returnOrReinvest (! $ Л_round , $ Л_chunkSize !) ;

(If ( ($ Л_chunkSize ?< (↑12 D2! DePoolContract_ι_MAX_MSGS_PER_TR ))  !&
      ( !¬ ( ($ (Л_round ->> RoundsBase_ι_Round_ι_stakes)) ->empty ) ) ) 
then  
{
	(*uint8 doubleChunkSize = 2 * chunkSize;*)
	U0! Л_doubleChunkSize := $xInt2 !*  $ Л_chunkSize;
	(* this.completeRoundWithChunk{flag: 1, bounce: false}(
                roundId,
                doubleChunkSize < MAX_MSGS_PER_TR? doubleChunkSize : chunkSize
			); *)
	(->sendMessage {||
	                contractMessage := {|| messageBounce := $xBoolFalse , messageFlag := $xInt1 ||} , 
					contractFunction := DePoolContract_Ф_completeRoundWithChunkF (!! $ Л_roundId ,
																	                 ($Л_doubleChunkSize ?< ↑12 D2! DePoolContract_ι_MAX_MSGS_PER_TR) ? $ Л_doubleChunkSize ::: $ Л_chunkSize !!)
					||} )	 >>	
	 (*this.completeRoundWithChunk{flag: 1, bounce: false}(roundId, chunkSize);*)
	 ->sendMessage {||
	                contractMessage := {|| messageBounce := $xBoolFalse , messageFlag := $xInt1 ||} , 
					contractFunction := DePoolContract_Ф_completeRoundWithChunkF (!! $Л_roundId , $ Л_chunkSize !!)
					||}					
} ) >> 
                      (* setRound(roundId, round); *)
 RoundsBase_Ф_setRound (! $ Л_roundId , $ Л_round !) >>
 $ (xValue I).

(* 
function completeRound(uint64 roundId, uint32 participantQty) public 
selfCall { 
        tvm.accept();
        require(isRound2(roundId) || m_poolClosed, InternalErrors.ERROR522);
        optional(Round) optRound = fetchRound(roundId);
        require(optRound.hasValue(), InternalErrors.ERROR519);
        Round round = optRound.get();
        require(round.step == RoundStep.Completing, InternalErrors.ERROR518);

        this.completeRoundWithChunk{flag: 1, bounce: false}(roundId, 1);
        tvm.commit();
      
        (* TODO: new *) uint outActionQty = (participantQty + MAX_MSGS_PER_TR - 1) / MAX_MSGS_PER_TR;
   (* TODO: new *) if (outActionQty > MAX_QTY_OF_OUT_ACTIONS) {
        (* TODO: new *) uint32 maxQty = uint32(MAX_QTY_OF_OUT_ACTIONS) * MAX_MSGS_PER_TR;
            uint32 restParticipant = participantQty;
            for (int msgQty = 0; restParticipant > 0; ++msgQty) {
                uint32 curGroup =
                    (restParticipant < maxQty || msgQty + 1 == MAX_QTY_OF_OUT_ACTIONS) ?
                    restParticipant :
                    maxQty;
                this.completeRound{flag: 1, bounce: false}(roundId, curGroup);
                restParticipant -= curGroup;
            }
        } else {
            for (uint i = 0; i < participantQty; i += MAX_MSGS_PER_TR) {
                this.completeRoundWithChunk{flag: 1, bounce: false}(roundId, MAX_MSGS_PER_TR);
            }
        }
    }
*)

(*function completeRound(uint64 roundId, uint32 participantQty)*)
Definition DePoolContract_Ф_completeRound ( Л_roundId : XInteger64 )
                                    ( Л_participantQty : XInteger32 ) 
                                    : LedgerT ( XErrorValue True XInteger ) := 
(*selfCall*) 
Require2 {{ msg_sender () ?== tvm_address (),  ↑7 D2! Errors_ι_IS_NOT_DEPOOL }} ; 
(* tvm.accept();*)
tvm_accept () >> 
(*require(isRound2(roundId) || m_poolClosed, InternalErrors.ERROR522);*)
Require2 {{ RoundsBase_Ф_isRound2 (! $ Л_roundId !) !| ↑12 D2! DePoolContract_ι_m_poolClosed , ↑8 D2! InternalErrors_ι_ERROR522 }} ; 
(*optional(Round) optRound = m_rounds.fetch(roundId);*)
U0! Л_optRound := RoundsBase_Ф_fetchRound (! $ Л_roundId !) ; 
(*require(optRound.hasValue(), InternalErrors.ERROR519);*)
Require2 {{ ($ Л_optRound) ->hasValue,  ↑8 D2! InternalErrors_ι_ERROR519 }} ; 
(* Round round = optRound.get(); *)
U0! Л_round := ($ Л_optRound) ->get ; 
(*require(round.step == RoundStep.Completing, InternalErrors.ERROR518);*)
Require2 {{ ( ( $ Л_round ->> RoundsBase_ι_Round_ι_step ) ?== ( $ RoundsBase_ι_RoundStepP_ι_Completing ) ) , ↑8 D2! InternalErrors_ι_ERROR518 }} ; 
(* this.completeRoundWithChunk{flag: 1, bounce: false}(roundId, 1); *) 
( ->sendMessage {||
	                contractMessage := {|| messageBounce := $xBoolFalse , messageFlag := $xInt1 ||} , 
					contractFunction := DePoolContract_Ф_completeRoundWithChunkF (!! $Л_roundId , $ xInt1 !!)
					||}	) >> 
       (*tvm.commit();*)					
tvm_commit () >> 
        (* uint outActionQty = (participantQty + MAX_MSGS_PER_TR - 1) / MAX_MSGS_PER_TR; *)
U0! Л_outActionQty := ( ( $ Л_participantQty !+ ( ↑12 D2! DePoolContract_ι_MAX_MSGS_PER_TR ) !- $ xInt1 ) !/
                             (↑12 D2! DePoolContract_ι_MAX_MSGS_PER_TR ) ) ; 

        (* if (outActionQty > MAX_QTY_OF_OUT_ACTIONS) { {*)
( If ( $ Л_outActionQty ?> ( ↑12 D2! DePoolContract_ι_MAX_QTY_OF_OUT_ACTIONS ) ) then  {
	      (* uint32 maxQty = uint32(MAX_QTY_OF_OUT_ACTIONS) * MAX_MSGS_PER_TR;*)
	U0! Л_maxQty := (↑12 D2! DePoolContract_ι_MAX_QTY_OF_OUT_ACTIONS ) !* 
                   (↑12 D2! DePoolContract_ι_MAX_MSGS_PER_TR ) ; 
	      (* uint32 restParticipant = participantQty;  *)
	(↑17 U1! LocalState_ι_completeRound_Л_restParticipant := $ Л_participantQty) >> 

          (* for (int msgQty = 0; restParticipant > 0; ++msgQty) {
                uint32 curGroup =
                    (restParticipant < maxQty || msgQty + 1 == MAX_QTY_OF_OUT_ACTIONS) ?
                    restParticipant :
                    maxQty;
                this.completeRound{flag: 1, bounce: false}(roundId, curGroup);
                restParticipant -= curGroup;
            } *)
		( ↑17 U1! LocalState_ι_completeRound_Л_msgQty := $ xInt0 ) >>
	( While  ( ↑17 D2! LocalState_ι_completeRound_Л_restParticipant ?> $ xInt0 ) do (
			U0! Л_curGroup := ( ( ↑17 D2! LocalState_ι_completeRound_Л_restParticipant ) ?< ( $ Л_maxQty ) !|
			                   ( ( (↑17 D2! LocalState_ι_completeRound_Л_msgQty) !+ $ xInt1 ) ?== ↑12 D2! DePoolContract_ι_MAX_QTY_OF_OUT_ACTIONS ) ) ? 
                     ( ↑17 D2! LocalState_ι_completeRound_Л_restParticipant ) :::  
                         ( $ Л_maxQty ) ;		
			(* this.completeRound{flag: 1, bounce: false}(roundId, curGroup); *)
			( ->sendMessage {||
	                contractMessage := {|| messageBounce := $xBoolFalse , messageFlag := $xInt1 ||} , 
					contractFunction := DePoolContract_Ф_completeRoundF (!! $Л_roundId , $ Л_curGroup !!)
					||}	)  >>
			(* restParticipant -= curGroup; *)
			( ↑17 U1! LocalState_ι_completeRound_Л_restParticipant !-= $ Л_curGroup ) >>
			continue! I
		) ) >> $ I
} else {
          (* else {
            for (uint i = 0; i < participantQty; i += MAX_MSGS_PER_TR) {
                this.completeRoundWithChunk{flag: 1, bounce: false}(roundId, MAX_MSGS_PER_TR);
            } } *)
			( ↑17 U1! LocalState_ι_completeRound_Л_i := $ xInt0 ) >>
		( While  ( ↑17 D2! LocalState_ι_completeRound_Л_i ?< $ Л_participantQty ) do (
			    ( ->sendMessage {||
	                contractMessage := {|| messageBounce := $xBoolFalse , messageFlag := $ xInt1 ||} , 
					contractFunction := DePoolContract_Ф_completeRoundWithChunkF (!! $Л_roundId , ↑12 D2! DePoolContract_ι_MAX_MSGS_PER_TR !!)
					||}	)  >>
				continue! I		
			) ) >>  $I		
	} ) >> 
	$ (xValue I) .
	 

(* 
function onStakeAccept(uint64 queryId, uint32 comment, address elector) public override {
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

        emit RoundStakeIsAccepted(round.validatorRequest.queryId, comment);  } *)
Definition DePoolContract_Ф_onStakeAccept ( Л_queryId : XInteger64 )
                                          ( Л_comment : XInteger32 )
  (* Полностью переписана - Bуква *)      ( Л_elector : XAddress ) 
                                          : LedgerT ( XErrorValue True XInteger ) :=
                    (*optional(Round) optRound = fetchRound(queryId);*)	
U0! Л_optRound :=  RoundsBase_Ф_fetchRound (! $ Л_queryId !) ;  
(* require(optRound.hasValue(), InternalErrors.ERROR513);*)
Require2 {{ $ Л_optRound ->hasValue , ↑8 D2! InternalErrors_ι_ERROR513 }} ; 
(* Round round = optRound.get();*)
U0! Л_round := ($ Л_optRound) ->get ;
(*require(msg.sender == round.proxy, Errors.IS_NOT_PROXY);*)
Require2 {{ msg_sender () ?== $ Л_round ->> RoundsBase_ι_Round_ι_proxy , ↑7 D2! Errors_ι_IS_NOT_PROXY }} ; 
(*require(elector == round.elector, Errors.IS_NOT_ELECTOR);*)
Require2 {{ $ Л_elector ?== $ Л_round ->> RoundsBase_ι_Round_ι_elector , ↑7 D2! Errors_ι_IS_NOT_ELECTOR }} ; 
(*require(round.id == queryId, Errors.INVALID_QUERY_ID);*)
Require2 {{ $ Л_round ->> RoundsBase_ι_Round_ι_id ?== $ Л_queryId ,  ↑7 D2! Errors_ι_INVALID_QUERY_ID }} ; 
(*require(round.step == RoundStep.WaitingIfStakeAccepted, Errors.INVALID_ROUND_STEP);*)
Require {{ $ Л_round ->> RoundsBase_ι_Round_ι_step ?== $ RoundsBase_ι_RoundStepP_ι_WaitingIfStakeAccepted , ↑7 D2!  Errors_ι_INVALID_ROUND_STEP }} ;
(*tvm.accept();*)
tvm_accept() >> 
(*round.step = RoundStep.WaitingValidationStart;*)
U0! Л_round ^^ RoundsBase_ι_Round_ι_step := $ RoundsBase_ι_RoundStepP_ι_WaitingValidationStart ; 
(* round.completionReason = CompletionReason.Undefined; *)
U0! Л_round ^^ RoundsBase_ι_Round_ι_completionReason := $ RoundsBase_ι_CompletionReasonP_ι_Undefined ; 
                       (* setRound(queryId, round); *)
RoundsBase_Ф_setRound (! $ Л_queryId , $Л_round !) >>
(*emit roundStakeIsAccepted(round.validatorRequest.queryId, comment); *)
->emit roundStakeIsAccepted (!! $  (Л_round ->> RoundsBase_ι_Round_ι_validatorRequest) ->> DePoolLib_ι_Request_ι_queryId , 
								$  Л_comment !!).
 	
(* 
function onStakeReject(uint64 queryId, uint32 comment, address elector) public override {
        // The return value is for logging, to catch outbound external message
        // and print queryId and comment.
        optional(Round) optRound = 
                           fetchRound(queryId);                   (*<<<<<<<<<<<<<<<<<<<<<*)
        require(optRound.hasValue(), InternalErrors.ERROR513);
        Round round = optRound.get();
        require(msg.sender == round.proxy, Errors.IS_NOT_PROXY);
        require(elector == round.elector, Errors.IS_NOT_ELECTOR);
        require(round.id == queryId, Errors.INVALID_QUERY_ID);
        require(round.step == RoundStep.WaitingIfStakeAccepted, Errors.INVALID_ROUND_STEP);

        tvm.accept();                                      (*<<<<<<<<<<<<<<<<<<<<<<<<<<*)
        round.step = RoundStep.WaitingValidatorRequest;
        round.completionReason = CompletionReason.StakeIsRejectedByElector;
        setRound(queryId, round);                           (*<<<<<<<<<<<<<<<<<<<<<<<<<<*)

        emit RoundStakeIsRejected(round.validatorRequest.queryId, comment);
    } *)
Definition DePoolContract_Ф_onStakeReject ( Л_queryId : XInteger64 )
                                          ( Л_comment : XInteger32 )
    (* Полностью переписана *)            ( Л_elector : XAddress ) 
                                          : LedgerT ( XErrorValue True XInteger ) := 
(*optional(Round) optRound = m_rounds.fetch(queryId);*)	
U0! Л_optRound :=  RoundsBase_Ф_fetchRound (! $ Л_queryId !) ; 
(* require(optRound.hasValue(), InternalErrors.ERROR513);*)
Require2 {{ $ Л_optRound ->hasValue , ↑8 D2! InternalErrors_ι_ERROR513 }} ; 
(* Round round = optRound.get();*)
U0! Л_round := ($ Л_optRound) ->get ;
(*require(msg.sender == round.proxy, Errors.IS_NOT_PROXY);*)
Require2 {{ msg_sender () ?== $ Л_round ->> RoundsBase_ι_Round_ι_proxy , ↑7 D2! Errors_ι_IS_NOT_PROXY }} ; 
(*require(elector == round.elector, Errors.IS_NOT_ELECTOR);*)
Require2 {{ $ Л_elector ?== $ Л_round ->> RoundsBase_ι_Round_ι_elector , ↑7 D2! Errors_ι_IS_NOT_ELECTOR }} ; 
(*require(round.id == queryId, Errors.INVALID_QUERY_ID);*)
Require2 {{ $ Л_round ->> RoundsBase_ι_Round_ι_id ?== $ Л_queryId ,  ↑7 D2! Errors_ι_INVALID_QUERY_ID }} ; 
(*require(round.step == RoundStep.WaitingIfStakeAccepted, Errors.INVALID_ROUND_STEP);*)
Require {{ $ Л_round ->> RoundsBase_ι_Round_ι_step ?== $ RoundsBase_ι_RoundStepP_ι_WaitingIfStakeAccepted , ↑7 D2!  Errors_ι_INVALID_ROUND_STEP }} ;
tvm_accept() >> 
(*round.step = RoundStep.WaitingValidatorRequest*)
U0! Л_round ^^ RoundsBase_ι_Round_ι_step := $ RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest ; 
(* round.completionReason = CompletionReason.Undefined; *)
U0! Л_round ^^ RoundsBase_ι_Round_ι_completionReason := $ RoundsBase_ι_CompletionReasonP_ι_StakeIsRejectedByElector ; 
                         (* setRound(queryId, round); *)
RoundsBase_Ф_setRound (! $ Л_queryId , $Л_round !) >>
(*emit roundStakeIsRejected(round.validatorRequest.queryId, comment); *)
->emit roundStakeIsRejected (!! $  (Л_round ->> RoundsBase_ι_Round_ι_validatorRequest) ->> DePoolLib_ι_Request_ι_queryId , 
								$  Л_comment !!).
 
 

(* 
function receiveFunds() public pure { } *)
Definition DePoolContract_Ф_receiveFunds : LedgerT True 
 	 := 
 return! I .

(* 
function getParticipantInfo(address addr) public view
        returns (
            uint64 total,
            uint64 withdrawValue,
            bool reinvest,
            uint64 reward,
            mapping (uint64 => uint64) stakes,
            mapping (uint64 => InvestParams) vestings,
            mapping (uint64 => InvestParams) locks
        )
    {
        optional(DePoolLib.Participant) optParticipant = 
                                                 fetchParticipant(addr); (*<<<<<<<<<<<<<<<*)
        require(optParticipant.hasValue(), Errors.NO_SUCH_PARTICIPANT);
        DePoolLib.Participant participant = optParticipant.get();

        reinvest = participant.reinvest;
        reward = participant.reward;
        withdrawValue = participant.withdrawValue;

        optional(uint64, Round) pair = 
                                      minRound();      (*<<<<<<<<<<<<<<*)
        while (pair.hasValue()) {
            (uint64 id, Round round) = pair.get();
            optional(StakeValue) optSv = round.stakes.fetch(addr);
            if (optSv.hasValue()) {
                StakeValue sv = optSv.get();
                if (sv.ordinary != 0) {
                    stakes[round.id] = sv.ordinary;
                    total += sv.ordinary;
                }
                if (sv.vesting.hasValue()) {
                    vestings[round.id] = sv.vesting.get();
                    total += sv.vesting.get().amount;
                }
                if (sv.lock.hasValue()) {
                    locks[round.id] = sv.lock.get();
                    total += sv.lock.get().amount;
                }
            }
            pair = nextRound(id); (*<<<<<<<<<<<<<<<<<<<<<<<<<*)
        }
    }


function getParticipantInfo(address addr) public view
        returns (
            uint64 total,
            uint64 withdrawValue,
            bool reinvest,
            uint64 reward,
            mapping (uint64 => uint64) stakes,
            mapping (uint64 => InvestParams) vestings,
            mapping (uint64 => InvestParams) locks
        )
    {
        optional(DePoolLib.Participant) optParticipant = m_participants.fetch(addr);
        require(optParticipant.hasValue(), Errors.NO_SUCH_PARTICIPANT);
        DePoolLib.Participant participant = optParticipant.get();

        reinvest = participant.reinvest;
        reward = participant.reward;
        withdrawValue = participant.withdrawValue;

        optional(uint64, Round) pair = m_rounds.min();
        while (pair.hasValue()) {
            (uint64 id, Round round) = pair.get();
            optional(StakeValue) optSv = round.stakes.fetch(addr);
            if (optSv.hasValue()) {
                StakeValue sv = optSv.get();
                if (sv.ordinary != 0) {
                    stakes[round.id] = sv.ordinary;
                    total += sv.ordinary;
                }
                if (sv.vesting.hasValue()) {
                    vestings[round.id] = sv.vesting.get();
                    total += sv.vesting.get().amount;
                }
                if (sv.lock.hasValue()) {
                    locks[round.id] = sv.lock.get();
                    total += sv.lock.get().amount;
                }
            }
            pair = m_rounds.next(id);
        }
	} *)
	
(*function getParticipantInfo(address addr) public view
        returns (
            uint64 total,
            uint64 withdrawValue,
            bool reinvest,
            uint64 reward,
            mapping (uint64 => uint64) stakes,
            mapping (uint64 => InvestParams) vestings,
            mapping (uint64 => InvestParams) locks*)	
Definition DePool_Ф_getParticipantInfo ( Л_addr : XAddress ) 
		   : LedgerT (XErrorValue ( XInteger64 # XInteger64 # XBool # XInteger64 # (XHMap XInteger64 XInteger64) # (XHMap XInteger64 RoundsBase_ι_InvestParams) # (XHMap XInteger64 RoundsBase_ι_InvestParams) ) XInteger)
		   := return! (xValue default).

(* 
function getDePoolInfo() public view returns ( (* очень большие отличия *)
        bool poolClosed,
        uint64 minStake,
        uint64 validatorAssurance,
        uint8 participantRewardFraction,
        uint8 validatorRewardFraction,
        uint64 balanceThreshold,

        address validatorWallet,
        address[] proxies,

        uint64 stakeFee,
        uint64 retOrReinvFee,
        uint64 proxyFee
    )
    {
        poolClosed = m_poolClosed;
        minStake = m_minStake;
        validatorAssurance = m_validatorAssurance;
        participantRewardFraction = m_participantRewardFraction;
        validatorRewardFraction = m_validatorRewardFraction;
        balanceThreshold = m_balanceThreshold;
        validatorWallet = m_validatorWallet;
        proxies = m_proxies;

        addStakeFee = ADD_STAKE_FEE;
        addVestingOrLockFee = ADD_VESTING_OR_LOCK_FEE;
        removeOrdinaryStakeFee = REMOVE_ORDINARY_STAKE_FEE;
        withdrawPartAfterCompletingFee = WITHDRAW_PART_AFTER_COMPLETING_FEE;
        withdrawAllAfterCompletingFee = WITHDRAW_ALL_AFTER_COMPLETING_FEE;
        transferStakeFee = TRANSFER_STAKE_FEE;
        retOrReinvFee = RET_OR_REINV_FEE;
        answerMsgFee = ANSWER_MSG_FEE;
        proxyFee = DePoolLib.PROXY_FEE;
    }


function getDePoolInfo() public view returns (
        uint64 minStake,
        uint64 minRoundStake,
        uint64 minValidatorStake,
        address validatorWallet,
        address proxy0,
        address proxy1,
        bool poolClosed,

        uint64 interest,

        uint64 addStakeFee,
        uint64 addVestingOrLockFee,
        uint64 removeOrdinaryStakeFee,
        uint64 withdrawPartAfterCompletingFee,
        uint64 withdrawAllAfterCompletingFee,
        uint64 transferStakeFee,
        uint64 retOrReinvFee,
        uint64 answerMsgFee,
        uint64 proxyFee,

        uint64 participantFraction,
        uint64 validatorFraction,
        uint64 validatorWalletMinStake
    )
    {
        minStake = m_minStake;
        minRoundStake = m_minRoundStake;
        minValidatorStake = (m_minRoundStake * VALIDATOR_WALLET_MIN_STAKE) / 100;
        validatorWallet = m_validatorWallet;
        proxy0 = m_proxy0;
        proxy1 = m_proxy1;
        poolClosed = m_poolClosed;

        interest = m_lastRoundInterest;

        addStakeFee = ADD_STAKE_FEE;
        addVestingOrLockFee = ADD_VESTING_OR_LOCK_FEE;
        removeOrdinaryStakeFee = REMOVE_ORDINARY_STAKE_FEE;
        withdrawPartAfterCompletingFee = WITHDRAW_PART_AFTER_COMPLETING_FEE;
        withdrawAllAfterCompletingFee = WITHDRAW_ALL_AFTER_COMPLETING_FEE;
        transferStakeFee = TRANSFER_STAKE_FEE;
        retOrReinvFee = RET_OR_REINV_FEE;
        answerMsgFee = ANSWER_MSG_FEE;
        proxyFee = DePoolLib.PROXY_FEE;

        participantFraction = PART_FRACTION;
        validatorFraction = VALIDATOR_FRACTION;
        validatorWalletMinStake = VALIDATOR_WALLET_MIN_STAKE;
    }
*)


(* 		   function getDePoolInfo() public view returns (
			uint64 minStake,
			uint64 minRoundStake,
			uint64 minValidatorStake,
			address validatorWallet,
			address proxy0,
			address proxy1,
			bool poolClosed,
	
			uint64 interest, //8
	
			uint64 addStakeFee,
			uint64 addVestingOrLockFee,
			uint64 removeOrdinaryStakeFee,
			uint64 withdrawPartAfterCompletingFee,
			uint64 withdrawAllAfterCompletingFee,
			uint64 transferStakeFee,
			uint64 retOrReinvFee,
			uint64 answerMsgFee,
			uint64 proxyFee, //9
	
			uint64 participantFraction,
			uint64 validatorFraction,
			uint64 validatorWalletMinStake //3
		)	 *)	   
Set Typeclasses Depth 100.
Definition DePool_Ф_getDePoolInfo 
		   : LedgerT ( XInteger64 # XInteger64 # XInteger64 # XAddress # XAddress # XAddress # XBool # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 ) := return! default.
Set Typeclasses Depth 10. 

 

(* 
function getParticipants() external view returns (address[] participants) {
        mapping(address => bool) used;
        optional(address, DePoolLib.Participant) pair = m_participants.min();
        while (pair.hasValue()) {
            (address p, ) = pair.get();
            if (!used.exists(p)) {
                used[p] = true;
                participants.push(p);
            }
            pair = m_participants.next(p);
        }
    } *)
Definition DePool_Ф_getParticipants : LedgerT (XArray XAddress) := $ default.

(*function withdrawFromPoolingRound(uint64 withdrawValue) public 
{
require(msg.sender != address(0), Errors.IS_EXT_MSG);
        if (m_poolClosed) {
            return _sendError(STATUS_DEPOOL_CLOSED, 0);
        }

        optional(DePoolLib.Participant) optParticipant = fetchParticipant(msg.sender);
        if (!optParticipant.hasValue()) {
            return _sendError(STATUS_NO_PARTICIPANT, 0);
        }
        DePoolLib.Participant participant = optParticipant.get();

        uint64 removedPoolingStake;
        (removedPoolingStake, participant) = withdrawStakeInPoolingRound(participant, msg.sender, withdrawValue, m_minStake);
        _setOrDeleteParticipant(msg.sender, participant);
        msg.sender.transfer(removedPoolingStake, false, 64); }*)
(* Check I.  *)
Definition DePoolContract_Ф_withdrawFromPoolingRound' ( Л_withdrawValue : XInteger64 )  
                                  : LedgerT (XErrorValue (XValueValue True) XInteger) :=
    (*require(msg.sender != address(0), Errors.IS_EXT_MSG);*)
Require {{ msg_sender () ?!= $ xInt0 , ↑ε7 Errors_ι_IS_EXT_MSG }} ; 
(* if (m_poolClosed) {
            return _sendError(STATUS_DEPOOL_CLOSED, 0);
        } *)
If!! ( ↑ε12 DePoolContract_ι_m_poolClosed ) 
then { 
   DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_DEPOOL_CLOSED , $ xInt0  !) >>=
	fun x => return! ( xError x) 
 } ; 
(* optional(DePoolLib.Participant) optParticipant = fetchParticipant(msg.sender);
        if (!optParticipant.hasValue()) {
            return _sendError(STATUS_NO_PARTICIPANT, 0);
        } *)
U0! Л_optParticipant := ParticipantBase_Ф_fetchParticipant (! msg_sender () !) ;
If! ( !¬ ( $ Л_optParticipant ->hasValue ) ) 
then { 
   DePoolContract_Ф__sendError (! ↑ε12 DePoolContract_ι_STATUS_NO_PARTICIPANT , 
														$ xInt0  !) >>=
	fun x => return! ( xError x)													
 } ; 

(*         DePoolLib.Participant participant = optParticipant.get(); *)
U0! Л_participant := $ Л_optParticipant ->get ; 

(* (removedPoolingStake, participant) = withdrawStakeInPoolingRound(participant, msg.sender, withdrawValue, m_minStake); *)
U0! {( Л_removedPoolingStake , Л_participant )} := RoundsBase_Ф_withdrawStakeInPoolingRound
                   (! $ Л_participant , msg_sender () , $ Л_withdrawValue , ↑12 D2! DePoolContract_ι_m_minStake !) ;

(*        
_setOrDeleteParticipant(msg.sender, participant);
msg.sender.transfer(removedPoolingStake, false, 64);   
*)
(ParticipantBase_Ф__setOrDeleteParticipant (! msg_sender () , $ Л_participant !)) >> 
( ( msg_sender () ) ->transfer (! $Л_removedPoolingStake ,  $ xBoolFalse ,  $ xInt64 !) ) .


Definition DePoolContract_Ф_withdrawFromPoolingRound ( Л_withdrawValue : XInteger64 )
                                     : LedgerT (XErrorValue True XInteger) :=
do r ← DePoolContract_Ф_withdrawFromPoolingRound'  Л_withdrawValue ;
	return! (xErrorMapDefaultF (xValue ∘ fromValueValue) r xError).






(* 
function onRoundComplete(
        uint64 roundId,
        uint64 reward,
        uint64 ordinaryStake,
        uint64 vestingStake,
        uint64 lockStake,
        bool reinvest,                   Такая функция внешняя и её прототип описан в IParticipant
        uint8 reason) external override
*)
(* Definition *_Ф_onRoundComplete ( Л_roundId : XInteger64 )
										                     ( Л_reward : XInteger64 )
										                     ( Л_ordinaryStake : XInteger64 )
										                     ( Л_vestingStake : XInteger64 )
										                     ( Л_lockStake : XInteger64 )
										                     ( Л_reinvest : XBool )
										                     ( Л_reason : XInteger8 ) : LedgerT True  := 
 return! I . *)



(* 
function receiveAnswer ( uint32 errcode , uint64 comment )  Такая функция внешняя и её прототип описан в IParticipant
 	 	 external override { } *)
(* Definition *_Ф_receiveAnswer ( Л_errcode : XInteger32 )
                                       ( Л_comment : XInteger64 ) 
                                       : LedgerT True 
 	 := 
 return! I . *)


(* 
function onTransfer ( address source , uint128 amount ) external  
                                  Такая функция внешняя и её прототип описан в IParticipant
 	 	 override { } *)
(* Definition *_Ф_onTransfer ( Л_source : XAddress )
                                    ( Л_amount : XInteger128 ) 
                                        : LedgerT True 
 	 := 
 return! I . *)


(*
Функуии, отсутствующие в старом контракте


contract DePoolProxyContract is IProxy {
    fallback() external {
        TvmSlice payload = msg.data;
        (uint32 functionId, uint64 queryId) = payload.decode(uint32, uint64);
        if (functionId == 0xfffffffe) {
            IDePool(m_dePool).onFailToRecoverStake{value: msg.value - DePoolLib.PROXY_FEE}(queryId, msg.sender);
        }
    }
}





}


*)













(*BELOW  IS code for TestElector*)	  

(* 
constructor(uint32 offset) public {
        electAt = now + offset;
    }
function Constructor8 ( uint32 offset ) public { electAt = now 
 	 	 + offset ; } *)
(* Definition TestElector_Ф_Constructor8 ( Л_offset : XInteger32 ) : LedgerT True := 
 d1! TestElector_ι_electAt := tvm_now !+ $ Л_offset ; 
 	 
 } >> 
 
 return! I . *)
(* 
function getElectionId() public view returns (uint32) {
        return electAt;
    }

function getElectionId ( ) public view returns ( uint32 ) { return 
 	 	 electAt ; } *)
(* Definition TestElector_Ф_getElectionId : LedgerT XInteger32 := 
 return! ↑9 TestElector_ι_electAt ; .  *)
 

(* 
function process_new_stake(
        uint64 queryId,
        uint256 validatorKey,
        uint32 stakeAt,
        uint32 maxFactor,
        uint256 adnlAddr,
        bytes signature
    ) public functionID(0x4e73744b)
    {
        require(msg.sender != address(0), 101);
        uint32 nowtime = now;
        if (nowtime >= electAt) {
            electAt += ((nowtime - electAt) / ELECTED_FOR + 1) * ELECTED_FOR;
        }
        require(nowtime >= (electAt - ELECTIONS_BEGIN_BEFORE), 103);
        require(nowtime < (electAt - ELECTIONS_END_BEFORE), 103);
        require(electAt == stakeAt, 102);
        require(msg.value >= 100000000000, 104);

        (, uint256 addr) = msg.sender.unpack();
        elections[addr] = Validator(
            uint64(msg.value) - 1e9, validatorKey, 10000000000, queryId, maxFactor, adnlAddr, signature
        );
        IDePool(msg.sender).onStakeAccept.value(1000000000)(queryId, 0);
    }


function process_new_stake ( uint64 queryId , uint256 validatorKey 
 	 	 , uint32 stakeAt , uint32 maxFactor , uint256 adnlAddr , bytes 
 	 	 signature ) public functionID ( 0x4e73744b ) { require ( msg_sender 
 	 	 ! = address ( 0 ) , 101 ) ; uint32 nowtime = now ; if ( nowtime >= electAt 
 	 	 ) { electAt + = ( ( nowtime - electAt ) / ELECTED_FOR + 1 ) * ELECTED_FOR 
 	 	 ; } require ( nowtime >= ( electAt - ELECTIONS_BEGIN_BEFORE ) , 
 	 	 103 ) ; require ( nowtime < ( electAt - ELECTIONS_END_BEFORE ) , 
 	 	 103 ) ; require ( electAt == stakeAt , 102 ) ; require ( msg_value 
 	 	 >= 100000000000 , 104 ) ; ( , uint256 addr ) = msg_sender . unpack 
 	 	 ( ) ; elections [ addr ] = Validator ( uint64 ( msg_value ) - 1e9 , validatorKey 
 	 	 , 10000000000 , queryId , maxFactor , adnlAddr , signature ) ; IDePool 
 	 	 ( msg_sender ) . onStakeAccept . value ( 1000000000 ) ( queryId 
 	 	 , 0 ) ; } *)
(* Definition TestElector_Ф_process_new_stake ( msg_value : XInteger ) ( msg_sender : XInteger ) ( Л_queryId : XInteger64 )( Л_validatorKey : XInteger256 )( Л_stakeAt : XInteger32 )( Л_maxFactor : XInteger32 )( Л_adnlAddr : XInteger256 )( Л_signature : XInteger8 ) : LedgerT ( XErrorValue True XInteger ) := 
 Require {{ $ msg_sender ?!= xInt0 , $ xInt101 }} ; 
 	 d0! Л_nowtime := tvm_now ; 
 	 
 Ift ( $ Л_nowtime ?>= ↑9 TestElector_ι_electAt ) { d1! TestElector_ι_electAt += ( ( $ Л_nowtime !- ↑9 TestElector_ι_electAt ) !/ ↑9 TestElector_ι_ELECTED_FOR !+ $ xInt1 ) { !* { ↑9 TestElector_ι_ELECTED_FOR } >> 
 Require {{ $ Л_nowtime ?>= ( ↑9 TestElector_ι_electAt !- ↑9 TestElector_ι_ELECTIONS_BEGIN_BEFORE ) , $ xInt103 }} ; 
 	 Require {{ $ Л_nowtime ?< ( ↑9 TestElector_ι_electAt !- ↑9 TestElector_ι_ELECTIONS_END_BEFORE ) , $ xInt103 }} ; 
 	 Require {{ ↑9 TestElector_ι_electAt ?== $ Л_stakeAt , $ xInt102 }} ; 
 	 Require {{ $ msg_value ?>= $ xInt100000000000 , $ xInt104 }} ; 
 	 ( , $ Л_addr $ msg_sender ^^ unpack ( ) >> 
 	 d4! TestElector_ι_elections [ Л_addr ] := ↑9 TestElector_ι_Validator ( $ msg_value !- 1e9 , $ Л_validatorKey , $ xInt10000000000 , $ Л_queryId , $ Л_maxFactor , $ Л_adnlAddr , $ Л_signature ) >> 
 	 (* IDePool ( $ msg_sender ) ^^ DePoolProxyContract_Ф_onStakeAccept *) . value ( $ xInt1000000000 ) {( $ Л_queryId , xInt0 ) 
 	 } >> .  *)
 

(* 
function recover_stake(uint64 queryId, address elector) public override onlyDePoolAndCheckBalance {
        IElector(elector).recover_stake{value: msg.value - DePoolLib.PROXY_FEE}(queryId);
    } *)

(* 
function TestElector.recover_stake(uint64 queryId) public functionID(0x47657424) {
        (, uint256 addr) = msg.sender.unpack();
        optional(Validator) optValidator = elections.fetch(addr);
        require(optValidator.hasValue(), Errors.IS_NOT_ELECTOR);
        Validator validator = optValidator.get();
        uint32 time = now;
        if ((time > electAt) && time < (electAt + ELECTED_FOR + STAKE_HELD_FOR)) {
            IDePool(msg.sender).sendError.value(1000000000)(queryId, 0x47657424);
        } else {
            IDePool(msg.sender).acceptRecoveredStake.value(validator.stake + validator.reward)(queryId);
            delete elections[addr];
        }
    }
*) 
(* Module DePoolFunSpec <: DePoolSpecSig.

Definition DePool_Ф_getDePoolInfo := DePool_Ф_getDePoolInfo.
Definition DePool_Ф_getParticipants := DePool_Ф_getParticipants.
Definition DePool_Ф_getParticipantInfo := DePool_Ф_getParticipantInfo.
(* Definition DePool_Ф_Constructor7 := DePool_Ф_Constructor7. *)

Definition DePoolContract_Ф__returnChange := DePoolContract_Ф__returnChange.
Definition DePoolContract_Ф__sendError := DePoolContract_Ф__sendError.
(* Definition DePoolContract_Ф__sendAccept := DePoolContract_Ф__sendAccept.
Definition DePoolContract_Ф_cutWithdrawalValueAndActivateStake := DePoolContract_Ф_cutWithdrawalValueAndActivateStake.
 *)Definition DePoolContract_Ф_onStakeAccept := DePoolContract_Ф_onStakeAccept.
Definition DePoolContract_Ф_onStakeReject := DePoolContract_Ф_onStakeReject.
Definition DePoolContract_Ф_Constructor6 := DePoolContract_Ф_Constructor6.
Definition DePoolContract_Ф_onSuccessToRecoverStake := DePoolContract_Ф_onSuccessToRecoverStake.
Definition DePoolContract_Ф_onFailToRecoverStake := DePoolContract_Ф_onFailToRecoverStake.
Definition DePoolContract_Ф_ticktock := DePoolContract_Ф_ticktock.
Definition DePoolContract_Ф__returnOrReinvestForParticipant := DePoolContract_Ф__returnOrReinvestForParticipant.
Definition DePoolContract_Ф__returnOrReinvest := DePoolContract_Ф__returnOrReinvest.
(* Definition DePoolContract_Ф_calculateStakeWithAssert := DePoolContract_Ф_calculateStakeWithAssert. *)
Definition DePoolContract_Ф_addOrdinaryStake := DePoolContract_Ф_addOrdinaryStake.
(* Definition DePoolContract_Ф_removeOrdinaryStake := DePoolContract_Ф_removeOrdinaryStake. *)
Definition DePoolContract_Ф_addVestingOrLock := DePoolContract_Ф_addVestingOrLock.
(* Definition DePoolContract_Ф_withdrawPartAfterCompleting := DePoolContract_Ф_withdrawPartAfterCompleting.
Definition DePoolContract_Ф_withdrawAllAfterCompleting := DePoolContract_Ф_withdrawAllAfterCompleting.
*)Definition DePoolContract_Ф_transferStake := DePoolContract_Ф_transferStake.
Definition DePoolContract_Ф_participateInElections := DePoolContract_Ф_participateInElections.
Definition DePoolContract_Ф_updateRound2 := DePoolContract_Ф_updateRound2.
Definition DePoolContract_Ф_updateRounds := DePoolContract_Ф_updateRounds.
Definition DePoolContract_Ф_completeRoundWithChunk := DePoolContract_Ф_completeRoundWithChunk.
Definition DePoolContract_Ф_completeRound := DePoolContract_Ф_completeRound.
Definition DePoolContract_Ф_acceptRewardAndStartRoundCompleting := DePoolContract_Ф_acceptRewardAndStartRoundCompleting.
Definition DePoolContract_Ф_terminator := DePoolContract_Ф_terminator.
Definition DePoolContract_Ф_receiveFunds := DePoolContract_Ф_receiveFunds.
Definition DePoolContract_Ф_startRoundCompleting := DePoolContract_Ф_startRoundCompleting.
Definition DePoolContract_Ф_addVestingStake := DePoolContract_Ф_addVestingStake.
Definition DePoolContract_Ф_addLockStake := DePoolContract_Ф_addLockStake.
Definition DePoolContract_Ф_generateRound := DePoolContract_Ф_generateRound.

Definition ConfigParamsBase_Ф_getCurValidatorData := ConfigParamsBase_Ф_getCurValidatorData.
Definition ConfigParamsBase_Ф_getPrevValidatorHash := ConfigParamsBase_Ф_getPrevValidatorHash.
Definition ConfigParamsBase_Ф_roundTimeParams := ConfigParamsBase_Ф_roundTimeParams.
Definition ConfigParamsBase_Ф_getMaxStakeFactor := ConfigParamsBase_Ф_getMaxStakeFactor.
Definition ConfigParamsBase_Ф_getElector := ConfigParamsBase_Ф_getElector.

Definition ValidatorBase_Ф_Constructor2 := ValidatorBase_Ф_Constructor2.

(* Definition ProxyBase_Ф_Constructor3 := ProxyBase_Ф_Constructor3. *)
Definition ProxyBase_Ф_getProxy := ProxyBase_Ф_getProxy.
Definition ProxyBase_Ф__recoverStake := ProxyBase_Ф__recoverStake.
Definition ProxyBase_Ф__sendElectionRequest := ProxyBase_Ф__sendElectionRequest.

(* Definition DePoolProxyContract_Ф_Constructor5 := DePoolProxyContract_Ф_Constructor5. *)
Definition DePoolProxyContract_Ф_process_new_stake := DePoolProxyContract_Ф_process_new_stake.
Definition DePoolProxyContract_Ф_recover_stake := DePoolProxyContract_Ф_recover_stake.
Definition DePoolProxyContract_Ф_getProxyInfo := DePoolProxyContract_Ф_getProxyInfo.

Definition DePoolHelper_Ф_Constructor4 := DePoolHelper_Ф_Constructor4.
Definition DePoolHelper_Ф_updateDePoolPoolAddress := DePoolHelper_Ф_updateDePoolPoolAddress.
Definition DePoolHelper_Ф__settimer := DePoolHelper_Ф__settimer.
Definition DePoolHelper_Ф_sendTicktock := DePoolHelper_Ф_sendTicktock.
Definition DePoolHelper_Ф_getDePoolPoolAddress := DePoolHelper_Ф_getDePoolPoolAddress.
Definition DePoolHelper_Ф_getHistory := DePoolHelper_Ф_getHistory.
Definition DePoolHelper_Ф_onCodeUpgrade := DePoolHelper_Ф_onCodeUpgrade.
Definition DePoolHelper_Ф_onTimer := DePoolHelper_Ф_onTimer.
Definition DePoolHelper_Ф_initTimer := DePoolHelper_Ф_initTimer.
Definition DePoolHelper_Ф_upgrade := DePoolHelper_Ф_upgrade.

Definition RoundsBase_Ф__addStakes := RoundsBase_Ф__addStakes.
Definition RoundsBase_Ф_activeAndNotStakeSum := RoundsBase_Ф_activeAndNotStakeSum.
Definition RoundsBase_Ф_activeStakeSum := RoundsBase_Ф_activeStakeSum.
Definition RoundsBase_Ф_toTruncatedRound := RoundsBase_Ф_toTruncatedRound.
Definition RoundsBase_Ф_getRounds := RoundsBase_Ф_getRounds.
Definition RoundsBase_Ф_transferStakeInOneRound := RoundsBase_Ф_transferStakeInOneRound.
Definition RoundsBase_Ф_withdrawStakeInPoolingRound := RoundsBase_Ф_withdrawStakeInPoolingRound.

Definition ParticipantBase_Ф__setOrDeleteParticipant := ParticipantBase_Ф__setOrDeleteParticipant.

Definition Participant_Ф_onRoundComplete := Participant_Ф_onRoundComplete.
Definition Participant_Ф_receiveAnswer := Participant_Ф_receiveAnswer.
Definition Participant_Ф_onTransfer := Participant_Ф_onTransfer.
Definition Participant_Ф_sendTransaction := Participant_Ф_sendTransaction.


Definition DebugDePool_Ф_getCurValidatorData2 := DebugDePool_Ф_getCurValidatorData2.
Definition DebugDePool_Ф_getPrevValidatorHash2 := DebugDePool_Ф_getPrevValidatorHash2.
Definition DebugDePool_Ф_Constructor1 := DebugDePool_Ф_Constructor1.


End  DePoolFunSpec.
 *)

End DePoolFuncs.
