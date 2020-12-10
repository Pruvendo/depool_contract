

(* 
These lines need to place into 'SolidityNotation.v':

Parameters  xInt228_000_000
xInt1_000_000_000 xInt3 xInt65536 xInt0 xInt1 xInt34 xInt32 xInt15 xInt17
xInt101 xInt8 xInt64 xInt100 xInt2 xInt18 xInt4 xInt103 xInt102
xInt100000000000 xInt104 xInt10000000000 xInt1000000000 : XInteger .

and these - into 'ProofEnvironment.v':

Definition xInt1000000000 := 1000000000%Z.
Definition xInt10000000000 := 10000000000%Z.
Definition xInt104 := 104%Z.
Definition xInt100000000000 := 100000000000%Z.
Definition xInt102 := 102%Z.
Definition xInt103 := 103%Z.
Definition xInt4 := 4%Z.
Definition xInt18 := 18%Z.
Definition xInt2 := 2%Z.
Definition xInt100 := 100%Z.
Definition xInt64 := 64%Z.
Definition xInt8 := 8%Z.
Definition xInt101 := 101%Z.
Definition xInt17 := 17%Z.
Definition xInt15 := 15%Z.
Definition xInt32 := 32%Z.
Definition xInt34 := 34%Z.
Definition xInt1 := 1%Z.
Definition xInt0 := 0%Z.
Definition xInt65536 := 65536%Z.
Definition xInt3 := 3%Z.
Definition xInt1_000_000_000 := 1000000000%Z.
Definition xInt228_000_000 := 228000000%Z.

*)


Require Import Coq.Program.Basics.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.
Require Import FinProof.ProgrammingWith.

Local Open Scope record.
Local Open Scope program_scope. 

Require Import FinProof.Common.
Require Import FinProof.StateMonad2.


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


(* 

UNCOMMENT THIS BLOCK AFTER VMState WOULD BE ADDED TO Ledger: *)

Definition setEventList l r := {$ r with VMState_ι_events := l $}.
(* Check setEventList. *)

Definition sendLedgerEvent (e: LedgerEventP) : LedgerT True :=
liftEmbeddedState ( T := T13 ) (modify (fun r => setEventList (xListCons e (VMState_ι_events r)) r) >> 
	  return! I ).
	  
Definition eventEqb (e1 e2: LedgerEvent): XBool := xBoolFalse.	  

Definition eventIn (e: LedgerEvent) : LedgerT XBool :=
↑  (embed_fun (fun r => xListIn eventEqb e (VMState_ι_events r))).

Definition getLastEvent : LedgerT (XMaybe LedgerEvent) :=
↑  (embed_fun (fun r => xListHead (VMState_ι_events r))).

Definition tvm_pubkey : LedgerT XInteger256 :=
  ↑returnε VMState_ι_pubkey.

Definition tvm_now : LedgerT XInteger64 :=
  ↑returnε VMState_ι_now.

Definition tvm_transfer (dest: XAddress) (value: XInteger256) 
  (bounce: XBool) (flags: XInteger8) 
  (payload: TvmCell) : LedgerT True := return! I.

Definition msg_pubkey : LedgerT XInteger256 :=
	↑returnε VMState_ι_msg_pubkey.

  (* sendLedgerEvent (TransactionSent 
(Transaction_ι_Transaction xInt0 xInt0 xInt0 xInt0 xInt0 xInt0 dest value flags payload bounce)) *)

(* Notation " tx '->transfer' " := (sendLedgerEvent (TransactionSent tx) >> 
		   tvm_transfer (tx ->> dest_ι_Transaction) (tx ->> value_ι_Transaction)
						(tx ->> bounce_ι_Transaction) (tx ->> sendFlags_ι_Transaction)
						(tx ->> payload_ι_Transaction)) (at level 60, tx constr, right associativity): solidity_scope.
 *)
Definition tvm_accept : LedgerT True := return! I.
Definition tvm_transLT : LedgerT XInteger64 := ↑returnε VMState_ι_ltime.

Definition tvm_setcode (newcode : TvmCell) : LedgerT True := (↑ <! VMState_ι_code <- newcode  !>) >> return! I.
Definition tvm_setCurrentCode (newcode : TvmCell) : LedgerT True :=  return! I.

(* Definition tvm_ignore_integer_overflow: LedgerT True := return! I. *)
Definition tvm_tree_cell_size (slice: TvmSlice) : LedgerT (XInteger # XInteger) := return! [(xInt0, xInt0)].
Definition tvm_ctos (cell : TvmCell): LedgerT TvmSlice := return! xStrNull. 
Definition tvm_reset_storage: LedgerT True :=  <! Ledger_ι_DePoolContract <- default  !> >> return! I.
Definition tvm_hash (cellTree: TvmCell) : LedgerT XInteger256 := return! xInt0. 
Definition tvm_rawConfigParam (x:XInteger) : LedgerT (XInteger # XInteger) := return! [(xInt0, xInt0)]. 

(*our stub: doesn't exists in TVM*)
(*actual call is uint128(address(this).balance);*)
Definition tvm_get_balance : LedgerT XInteger128 := ↑returnε VMState_ι_balance. 

Definition tvm_commit: LedgerT True :=
do l ← get;
put {$l with Ledger_ι_VMState := {$Ledger_ι_VMState l with VMState_ι_savedDePoolContract := Ledger_ι_DePoolContract l $}$};
void!.

Definition tvm_restore: LedgerT True :=
do l ← get;
put {$l with Ledger_ι_DePoolContract := VMState_ι_savedDePoolContract (Ledger_ι_VMState l) $};
void!.

Definition callDePool {X E} (m: LedgerT (XErrorValue X E)) : LedgerT (XErrorValue X E) :=
tvm_commit >> 
m >>= fun ea => xErrorMapDefaultF (fun a => return! (xValue a)) ea (fun er => tvm_restore >> return! (xError er)).


(* These functions doesn't need proof *)
(*DELETE THIS AFTER  PREVIOUS BLOCK WOULD BE UNCOMMENTED*)
(* Definition msg_pubkey : XInteger := xInt0.
Definition tvm_pubkey : XInteger := xInt0.
Definition tvm_pubkey1 ( x : XInteger ) : XInteger := xInt0.
Definition tvm_accept : LedgerT True := return! I.
Definition tvm_commit : LedgerT True := return! I.
Definition tvm_setcode ( x : TvmCell ) : LedgerT True := return! I.
Definition tvm_setCurrentCode ( x : TvmCell ) : LedgerT True := return! I. *)
(*********************************************************)


Set Typeclasses Iterative Deepening.
Set Typeclasses Depth 10.


(* function Constructor1 ( uint64 minRoundStake , address proxy0 
 	 	 , address proxy1 , address validatorWallet , uint64 minStake 
 	 	 ) DePool ( minRoundStake , proxy0 , proxy1 , validatorWallet , 
 	 	 minStake ) public { } *)
Definition DebugDePool_Ф_Constructor1 ( Л_minRoundStake : XInteger64 )( Л_proxy0 : XAddress )( Л_proxy1 : XAddress )( Л_validatorWallet : XAddress )( Л_minStake : XInteger64 ) : LedgerT ( XErrorValue True XInteger ) 
 	 := return! I .
(* function getCurValidatorData ( ) override internal returns 
 	 	 ( uint256 hash , uint32 utime_since , uint32 utime_until ) { int 
 	 	 t = int ( now ) - 228_000_000 - elections_start_before ; int start 
 	 	 = 228_000_000 + elections_start_before + t / validators_elected_for 
 	 	 * validators_elected_for ; return ( uint256 ( start + 1_000_000_000 
 	 	 ) , uint32 ( start ) , uint32 ( start + validators_elected_for ) 
 	 	 ) ; } *)
Definition DebugDePool_Ф_getCurValidatorData : LedgerT ( XErrorValue ( XInteger256 # XInteger32 # XInteger32 ) XInteger ) := 
 d0! Л_t := tvm_now !- $ xInt228_000_000 !- ↑1 DebugDePool_ι_elections_start_before ; 
 	 d0! Л_start := $ xInt228_000_000 !+ ↑1 DebugDePool_ι_elections_start_before !+ $ Л_t !/ ↑1 DebugDePool_ι_validators_elected_for !* ↑1 DebugDePool_ι_validators_elected_for ; 
 	 return# ( $ Л_start !+ $ xInt1_000_000_000 , $ Л_start , $ Л_start !+ ↑1 DebugDePool_ι_validators_elected_for ) .
(* function getPrevValidatorHash ( ) override internal returns 
 	 	 ( uint ) { int t = int ( now ) - 228_000_000 - elections_start_before 
 	 	 - validators_elected_for ; int start = 228_000_000 + elections_start_before 
 	 	 + t / validators_elected_for * validators_elected_for ; return 
 	 	 uint256 ( start + 1_000_000_000 ) ; } *)
Definition DebugDePool_Ф_getPrevValidatorHash : LedgerT ( XErrorValue XInteger XInteger ) := 
 d0! Л_t := tvm_now !- $ xInt228_000_000 !- ↑1 DebugDePool_ι_elections_start_before !- ↑1 DebugDePool_ι_validators_elected_for ; 
 	 d0! Л_start := $ xInt228_000_000 !+ ↑1 DebugDePool_ι_elections_start_before !+ $ Л_t !/ ↑1 DebugDePool_ι_validators_elected_for !* ↑1 DebugDePool_ι_validators_elected_for ; 
 	 $ Л_start !+ $ xInt1_000_000_000 .
(* function roundTimeParams ( ) override internal returns ( uint32 
 	 	 , uint32 , uint32 , uint32 ) { return ( validators_elected_for 
 	 	 , elections_start_before , elections_end_before , stake_held_for 
 	 	 ) ; } *)
Definition DebugDePool_Ф_roundTimeParams : LedgerT ( XErrorValue ( XInteger32 # XInteger32 # XInteger32 # XInteger32 ) XInteger ) := 
 return# ( ↑1 DebugDePool_ι_validators_elected_for , ↑1 DebugDePool_ι_elections_start_before , ↑1 DebugDePool_ι_elections_end_before , ↑1 DebugDePool_ι_stake_held_for ) .
(* function getMaxStakeFactor ( ) override pure internal returns 
 	 	 ( uint32 ) { return 3 * 65536 ; } *)
Definition DebugDePool_Ф_getMaxStakeFactor : LedgerT ( XErrorValue XInteger32 XInteger ) := 
 $ xInt3 !* $ xInt65536 .
(* function getElector ( ) override pure internal returns ( address 
 	 	 ) { return address . makeAddrStd ( 0 , 0x4444444444444444444444444444444444444444444444444444444444444444 
 	 	 ) ; } *)
Definition DebugDePool_Ф_getElector : LedgerT ( XErrorValue XAddress XInteger ) := 
 return! address ->makeAddrStd (! $ xInt0 , Ox4444444444444444444444444444444444444444444444444444444444444444 !) .
(* function getCurValidatorData2 ( ) external returns ( uint256 
 	 	 curValidatorHash , uint32 validationStart , uint32 validationEnd 
 	 	 ) { return getCurValidatorData ( ) ; } *)
Definition DebugDePool_Ф_getCurValidatorData2 : LedgerT ( XErrorValue ( XInteger256 # XInteger32 # XInteger32 ) XInteger ) := 
 DebugDePool_Ф_getCurValidatorData () .
(* function getPrevValidatorHash2 ( ) external returns ( uint 
 	 	 prevValidatorHash ) { return getPrevValidatorHash ( ) ; } *)
Definition DebugDePool_Ф_getPrevValidatorHash2 : LedgerT ( XErrorValue XInteger XInteger ) := 
 DebugDePool_Ф_getPrevValidatorHash () .
(* function Constructor2 ( uint64 minStake , uint64 minRoundStake 
 	 	 ) { require ( msg_pubkey ( ) == tvm_pubkey ( ) , Errors . IS_NOT_OWNER 
 	 	 ) ; require ( tvm_pubkey ( ) ! = 0 , STATUS_CONSTRUCTOR_NO_PUBKEY 
 	 	 ) ; require ( 1 <= minStake && minStake <= minRoundStake , STATUS_CONSTRUCTOR_WRONG_PARAMS 
 	 	 ) ; tvm_accept ( ) ; } *)
Definition CheckAndAcceptBase_Ф_Constructor2 ( Л_minStake : XInteger64 )( Л_minRoundStake : XInteger64 ) : LedgerT ( XErrorValue True XInteger ) := 
 Require {{ $ msg_pubkey () ?== tvm_pubkey () ,  Errors_ι_IS_NOT_OWNER }} ; 
 	 Require {{ tvm_pubkey () ?!= $ xInt0 , ↑2 CheckAndAcceptBase_ι_STATUS_CONSTRUCTOR_NO_PUBKEY }} ; 
 	 Require {{ $ xInt1 ?<= $ Л_minStake && $ Л_minStake ?<= $ Л_minRoundStake , ↑2 CheckAndAcceptBase_ι_STATUS_CONSTRUCTOR_WRONG_PARAMS }} ; 
 	 tvm_accept () >> . 
 

(* function Constructor3 ( address validatorWallet ) internal 
 	 	 { m_validatorWallet = validatorWallet ; } *)
Definition ValidatorBase_Ф_Constructor3 ( Л_validatorWallet : XAddress ) : LedgerT ( XErrorValue True XInteger ) := 
 d1! ValidatorBase_ι_m_validatorWallet := $ Л_validatorWallet ; . 
 

(* function Constructor4 ( address proxy0 , address proxy1 ) internal 
 	 	 { m_proxies = [ proxy0 , proxy1 ] ; } *)
Definition ProxyBase_Ф_Constructor4 ( Л_proxy0 : XAddress )( Л_proxy1 : XAddress ) : LedgerT ( XErrorValue True XInteger ) := 
 d1! ProxyBase_ι_m_proxies := [ $ Л_proxy0 , $ Л_proxy1 ] ; . 
 

(* function getProxy ( uint64 roundId ) internal view inline returns 
 	 	 ( address ) { return m_proxies [ roundId % 2 ] ; } *)
Definition ProxyBase_Ф_getProxy ( Л_roundId : XInteger64 ) : LedgerT ( XErrorValue XAddress XInteger ) := 
 return! ↑4 ProxyBase_ι_m_proxies [ $ Л_roundId $ Л_% $ Л_2 ] ; . 
 

(* function _recoverStake ( address proxy , uint64 requestId 
 	 	 , address elector ) internal { IProxy ( proxy ) . recover_stake 
 	 	 { value : DePoolLib . ELECTOR_FEE + DePoolLib . PROXY_FEE } ( requestId 
 	 	 , elector ) ; } *)
Definition ProxyBase_Ф__recoverStake ( Л_proxy : XAddress )( Л_requestId : XInteger64 )( Л_elector : XAddress ) : LedgerT ( XErrorValue True XInteger ) := 
 (* IProxy ( $ Л_proxy ) ^^ DePoolProxyContract_Ф_recover_stake { value : DePoolLib_ι_ELECTOR_FEE !+  DePoolLib_ι_PROXY_FEE 
 } 
 ( $ Л_requestId , $ Л_elector ) *) . 
 

(* function _sendElectionRequest ( address proxy , uint64 requestId 
 	 	 , uint64 validatorStake , DePoolLib . Request req , address elector 
 	 	 ) internal { IProxy ( proxy ) . process_new_stake { value : validatorStake 
 	 	 + DePoolLib . ELECTOR_FEE + DePoolLib . PROXY_FEE } ( requestId 
 	 	 , req . validatorKey , req . stakeAt , req . maxFactor , req . adnlAddr 
 	 	 , req . signature , elector ) ; } *)
Definition ProxyBase_Ф__sendElectionRequest ( Л_proxy : XAddress )( Л_requestId : XInteger64 )( Л_validatorStake : XInteger64 )( Л_Request : DePoolLib ) : LedgerT ( XErrorValue True XInteger ) := 
 (* IProxy ( $ Л_proxy ) ^^ DePoolProxyContract_Ф_process_new_stake { value : $ Л_validatorStake !+  DePoolLib_ι_ELECTOR_FEE !+  DePoolLib_ι_PROXY_FEE 
 } 
 ( $ Л_requestId , req ^^ validatorKey , req ^^ stakeAt , req ^^ maxFactor , req ^^ adnlAddr , req ^^ TestElector_ι_Validator_ι_signature , ↑8 RoundsBase_ι_Round_ι_elector ) *) . 
 

(* function getCurValidatorData ( ) virtual internal returns 
 	 	 ( uint256 hash , uint32 utime_since , uint32 utime_until ) { ( TvmCell 
 	 	 cell , bool ok ) = tvm_rawConfigParam ( 34 ) ; require ( ok , InternalErrors 
 	 	 . ERROR508 ) ; hash = tvm_hash ( cell ) ; TvmSlice s = cell . toSlice 
 	 	 ( ) ; ( , utime_since , utime_until ) = s . decode ( uint8 , uint32 , 
 	 	 uint32 ) ; } *)
Definition ConfigParamsBase_Ф_getCurValidatorData : LedgerT ( XErrorValue ( XInteger256 # XInteger32 # XInteger32 ) XInteger ) := 
 {( $ Л_cell , Л_ok )} := tvm_rawConfigParam (! $ xInt34 !) >> 
 	 Require {{ $ Л_ok ,  InternalErrors_ι_ERROR508 }} ; 
 	 tvm_hash (! $ Л_cell !) >> 
 	 d0! Л_s := Л_cell ->toSlice () >> 
 	 ( , utime_since , utime_until $ Л_s ^^ decode ( uint8 , uint32 , uint32 ) >> . 
 

(* function getPrevValidatorHash ( ) virtual internal returns 
 	 	 ( uint ) { ( TvmCell cell , bool ok ) = tvm_rawConfigParam ( 32 ) ; require 
 	 	 ( ok , InternalErrors . ERROR507 ) ; return tvm_hash ( cell ) ; } *) 
 	 	
Definition ConfigParamsBase_Ф_getPrevValidatorHash : LedgerT ( XErrorValue XInteger XInteger ) := 
 {( $ Л_cell , Л_ok )} := tvm_rawConfigParam (! $ xInt32 !) >> 
 	 Require {{ $ Л_ok ,  InternalErrors_ι_ERROR507 }} ; 
 	 return! tvm_hash (! $ Л_cell !) >> . 
 

(* function roundTimeParams ( ) virtual internal returns ( uint32 
 	 	 validatorsElectedFor , uint32 electionsStartBefore , uint32 
 	 	 electionsEndBefore , uint32 stakeHeldFor ) { bool ok ; ( validatorsElectedFor 
 	 	 , electionsStartBefore , electionsEndBefore , stakeHeldFor 
 	 	 , ok ) = tvm_configParam ( 15 ) ; require ( ok , InternalErrors . ERROR509 
 	 	 ) ; } *)
Definition ConfigParamsBase_Ф_roundTimeParams : LedgerT ( XErrorValue ( XInteger32 # XInteger32 # XInteger32 # XInteger32 ) XInteger ) := 
 ( validatorsElectedFor , electionsStartBefore , electionsEndBefore , stakeHeldFor , $ Л_ok tvm_configParam (! $ xInt15 !) >> 
 	 Require {{ $ Л_ok ,  InternalErrors_ι_ERROR509 }} ; . 
 

(* function getMaxStakeFactor ( ) virtual pure internal returns 
 	 	 ( uint32 ) { ( TvmCell cell , bool ok ) = tvm_rawConfigParam ( 17 ) 
 	 	 ; require ( ok , InternalErrors . ERROR516 ) ; TvmSlice s = cell . 
 	 	 toSlice ( ) ; s . loadTons ( ) ; s . loadTons ( ) ; s . loadTons ( ) ; return 
 	 	 s . decode ( uint32 ) ; } *)
Definition ConfigParamsBase_Ф_getMaxStakeFactor : LedgerT ( XErrorValue XInteger32 XInteger ) := 
 {( $ Л_cell , Л_ok )} := tvm_rawConfigParam (! $ xInt17 !) >> 
 	 Require {{ $ Л_ok ,  InternalErrors_ι_ERROR516 }} ; 
 	 d0! Л_s := Л_cell ->toSlice () >> 
 	 $ Л_s ^^ loadTons ( ) >> 
 	 $ Л_s ^^ loadTons ( ) >> 
 	 $ Л_s ^^ loadTons ( ) >> 
 	 $ Л_s ^^ decode ( uint32 ) .
(* function getElector ( ) virtual pure internal returns ( address 
 	 	 ) { ( TvmCell cell , bool ok ) = tvm_rawConfigParam ( 1 ) ; require 
 	 	 ( ok , InternalErrors . ERROR517 ) ; TvmSlice s = cell . toSlice ( 
 	 	 ) ; uint256 value = s . decode ( uint256 ) ; return address . makeAddrStd 
 	 	 ( - 1 , value ) ; } *)
Definition ConfigParamsBase_Ф_getElector : LedgerT ( XErrorValue XAddress XInteger ) := 
 {( $ Л_cell , Л_ok )} := tvm_rawConfigParam (! $ xInt1 !) >> 
 	 Require {{ $ Л_ok ,  InternalErrors_ι_ERROR517 }} ; 
 	 d0! Л_s := Л_cell ->toSlice () >> 
 	 d0! Л_value := $ Л_s ^^ decode ( uint256 ) >> 
 	 return! address ->makeAddrStd (! !- $ xInt1 , $ Л_value !) .
(* function _setOrDeleteParticipant ( address addr , DePoolLib 
 	 	 . Participant participant ) internal inline { if ( participant 
 	 	 . roundQty == 0 ) delete m_participants [ addr ] ; else m_participants 
 	 	 [ addr ] = participant ; } *)
Definition ParticipantBase_Ф__setOrDeleteParticipant ( Л_addr : XAddress )( Л_Participant : DePoolLib ) : LedgerT ( XErrorValue True XInteger ) := 
 
 Ift ( participant . roundQty ?== $ xInt0 ) delete  [ $ Л_addr ] ; else d4!  [ Л_addr ] := participant ; } >> . 
 

(* function Constructor5 ( address pool ) { require ( msg_pubkey 
 	 	 ( ) == tvm_pubkey ( ) , 101 ) ; m_dePoolPool = pool ; } *)
Definition DePoolHelper_Ф_Constructor5 ( Л_pool : XAddress ) : LedgerT ( XErrorValue True XInteger ) := 
 Require {{ $ msg_pubkey () ?== tvm_pubkey () , $ xInt101 }} ; 
 	 d1! DePoolHelper_ι_m_dePoolPool := $ Л_pool ; . 
 

(* function updateDePoolPoolAddress ( address addr ) { require 
 	 	 ( msg_pubkey ( ) == tvm_pubkey ( ) , 101 ) ; m_poolHistory . push ( 
 	 	 m_dePoolPool ) ; m_dePoolPool = addr ; } *)
Definition DePoolHelper_Ф_updateDePoolPoolAddress ( Л_addr : XAddress ) : LedgerT ( XErrorValue True XInteger ) := 
 Require {{ $ msg_pubkey () ?== tvm_pubkey () , $ xInt101 }} ; 
 	 push ( ↑6 DePoolHelper_ι_m_dePoolPool ) >> 
 	 d1! DePoolHelper_ι_m_dePoolPool := $ Л_addr ; . 
 

(* function initTimer ( address timer , uint period ) { require 
 	 	 ( msg_pubkey ( ) == tvm_pubkey ( ) , 101 ) ; m_timer = timer ; m_timeout 
 	 	 = period ; _settimer ( timer , period ) ; } *)
Definition DePoolHelper_Ф_initTimer ( Л_timer : XAddress )( Л_period : XInteger ) : LedgerT ( XErrorValue True XInteger ) := 
 Require {{ $ msg_pubkey () ?== tvm_pubkey () , $ xInt101 }} ; 
 	 d1! DePoolHelper_ι_m_timer := $ Л_timer ; 
 	 d1! DePoolHelper_ι_m_timeout := $ Л_period ; 
 	 DePoolHelper_Ф__settimer (! $ Л_timer , $ Л_period !) ; . 
 

(* function _settimer ( address timer , uint period ) private inline 
 	 	 { uint opex = period * _timerRate + _fwdFee * 8 + _epsilon ; ITimer 
 	 	 ( timer ) . setTimer . value ( opex ) ( period ) ; } *)
Definition DePoolHelper_Ф__settimer ( Л_timer : XAddress )( Л_period : XInteger ) : LedgerT ( XErrorValue True XInteger ) := 
 d0! Л_opex := $ Л_period !* ↑6 DePoolHelper_ι__timerRate !+ ↑6 DePoolHelper_ι__fwdFee !* $ xInt8 !+ ↑6 DePoolHelper_ι__epsilon ; 
 	 (* ITimer ( $ Л_timer ) ^^ ParticipantBase_Ф_setTimer *) . value ( $ Л_opex ) ( $ Л_period ) >> . 
 

(* function onTimer ( ) public { address timer = m_timer ; uint period 
 	 	 = m_timeout ; if ( msg_sender == timer && period > 0 ) { IDePool ( m_dePoolPool 
 	 	 ) . ticktock . value ( TICKTOCK_FEE ) ( ) ; _settimer ( timer , period 
 	 	 ) ; } } *)
Definition DePoolHelper_Ф_onTimer ( msg_sender : XInteger ) : LedgerT ( XErrorValue True XInteger ) := 
 d0! Л_timer := ↑6 DePoolHelper_ι_m_timer ; 
 	 d0! Л_period := ↑6 DePoolHelper_ι_m_timeout ; 
 	 
 Ift ( $ msg_sender ?== $ Л_timer && $ Л_period ?> $ xInt0 ) { (* IDePool ( ↑6 DePoolHelper_ι_m_dePoolPool ) { *) . { DePoolContract_Ф_ticktock { . { value { ( { ↑6 DePoolHelper_ι_TICKTOCK_FEE { ) { ( { ) } >> DePoolHelper_Ф__settimer (! $ Л_timer , $ Л_period !) ; . 
 

(* function sendTicktock ( ) { require ( msg_pubkey ( ) == tvm_pubkey 
 	 	 ( ) , 101 ) ; IDePool ( m_dePoolPool ) . ticktock . value ( TICKTOCK_FEE 
 	 	 ) ( ) ; } *)
Definition DePoolHelper_Ф_sendTicktock : LedgerT ( XErrorValue True XInteger ) := 
 Require {{ $ msg_pubkey () ?== tvm_pubkey () , $ xInt101 }} ; 
 	 (* IDePool ( ↑6 DePoolHelper_ι_m_dePoolPool ) ^^ DePoolContract_Ф_ticktock *) . value ( ↑6 DePoolHelper_ι_TICKTOCK_FEE ) () >> . 
 

(* function getDePoolPoolAddress ( ) public view returns ( address 
 	 	 addr ) { addr = m_dePoolPool ; } *)
Definition DePoolHelper_Ф_getDePoolPoolAddress : LedgerT ( XErrorValue XAddress XInteger ) := 
 ↑6 DePoolHelper_ι_m_dePoolPool ; . 
 

(* function getHistory ( ) public view returns ( mapping ( int => 
 	 	 address ) list ) { list = m_poolHistory ; } *)
Definition DePoolHelper_Ф_getHistory : LedgerT ( XErrorValue True XInteger ) := 
 ↑6 DePoolHelper_ι_m_poolHistory ; . 
 

(* function upgrade ( TvmCell newcode ) { require ( msg_pubkey 
 	 	 ( ) == tvm_pubkey ( ) , 101 ) ; tvm_commit ( ) ; tvm_setcode ( newcode 
 	 	 ) ; tvm_setCurrentCode ( newcode ) ; onCodeUpgrade ( ) ; } *)
Definition DePoolHelper_Ф_upgrade ( Л_newcode : TvmCell ) : LedgerT ( XErrorValue True XInteger ) := 
 Require {{ $ msg_pubkey () ?== tvm_pubkey () , $ xInt101 }} ; 
 	 tvm_commit () >> 
 	 tvm_setcode (! $ Л_newcode !) >> 
 	 tvm_setCurrentCode (! $ Л_newcode !) >> 
 	 DePoolHelper_Ф_onCodeUpgrade () ; . 
 

(* function onCodeUpgrade ( ) private { } *)
Definition DePoolHelper_Ф_onCodeUpgrade : LedgerT ( XErrorValue True XInteger ) 
 	 := return! I .
(* function Constructor6 ( address depool ) public { require ( 
 	 	 msg_pubkey ( ) == tvm_pubkey ( ) , ERROR_IS_NOT_OWNER ) ; tvm_accept 
 	 	 ( ) ; m_dePool = depool ; } *)
Definition DePoolProxyContract_Ф_Constructor6 ( Л_depool : XAddress ) : LedgerT ( XErrorValue True XInteger ) := 
 Require {{ $ msg_pubkey () ?== tvm_pubkey () , ↑7 DePoolProxyContract_ι_ERROR_IS_NOT_OWNER }} ; 
 	 tvm_accept () >> 
 	 d1! DePoolProxyContract_ι_m_dePool := $ Л_depool ; . 
 

(* function process_new_stake ( uint64 queryId , uint256 validatorKey 
 	 	 , uint32 stakeAt , uint32 maxFactor , uint256 adnlAddr , bytes 
 	 	 signature , address elector ) external { require ( msg_sender 
 	 	 == m_dePool , ERROR_IS_NOT_DEPOOL ) ; IElector ( elector ) . process_new_stake 
 	 	 { value : msg_value - DePoolLib . PROXY_FEE } ( queryId , validatorKey 
 	 	 , stakeAt , maxFactor , adnlAddr , signature ) ; } *)
Definition DePoolProxyContract_Ф_process_new_stake ( msg_value : XInteger ) ( msg_sender : XInteger ) ( Л_queryId : XInteger64 )( Л_validatorKey : XInteger256 )( Л_stakeAt : XInteger32 )( Л_maxFactor : XInteger32 )( Л_adnlAddr : XInteger256 )( Л_signature : XInteger8 )( Л_elector : XAddress ) : LedgerT ( XErrorValue True XInteger ) := 
 Require {{ $ msg_sender ?== ↑7 DePoolProxyContract_ι_m_dePool , ↑7 DePoolProxyContract_ι_ERROR_IS_NOT_DEPOOL }} ; 
 	 (* IElector ( $ Л_elector ) ^^ DePoolProxyContract_Ф_process_new_stake { value : $ msg_value !-  DePoolLib_ι_PROXY_FEE 
 } 
 ( $ Л_queryId , $ Л_validatorKey , $ Л_stakeAt , $ Л_maxFactor , $ Л_adnlAddr , $ Л_signature ) *) . 
 

(* function onStakeAccept ( uint64 queryId , uint32 comment ) 
 	 	 public functionID ( 0xF374484C ) { IDePool ( m_dePool ) . onStakeAccept 
 	 	 { value : msg_value - DePoolLib . PROXY_FEE } ( queryId , comment 
 	 	 , msg_sender ) ; } *)
Definition DePoolProxyContract_Ф_onStakeAccept ( msg_value : XInteger ) ( msg_sender : XInteger ) ( Л_queryId : XInteger64 )( Л_comment : XInteger32 ) : LedgerT ( XErrorValue True XInteger ) := 
 (* IDePool ( ↑7 DePoolProxyContract_ι_m_dePool ) ^^ DePoolProxyContract_Ф_onStakeAccept { value : $ msg_value !-  DePoolLib_ι_PROXY_FEE 
 } 
 ( $ Л_queryId , $ Л_comment , $ msg_sender ) *) . 
 

(* function onStakeReject ( uint64 queryId , uint32 comment ) 
 	 	 public functionID ( 0xEE6F454C ) { IDePool ( m_dePool ) . onStakeReject 
 	 	 { value : msg_value - DePoolLib . PROXY_FEE } ( queryId , comment 
 	 	 , msg_sender ) ; } *)
Definition DePoolProxyContract_Ф_onStakeReject ( msg_value : XInteger ) ( msg_sender : XInteger ) ( Л_queryId : XInteger64 )( Л_comment : XInteger32 ) : LedgerT ( XErrorValue True XInteger ) := 
 (* IDePool ( ↑7 DePoolProxyContract_ι_m_dePool ) ^^ DePoolProxyContract_Ф_onStakeReject { value : $ msg_value !-  DePoolLib_ι_PROXY_FEE 
 } 
 ( $ Л_queryId , $ Л_comment , $ msg_sender ) *) . 
 

(* function recover_stake ( uint64 queryId , address elector 
 	 	 ) public { require ( msg_sender == m_dePool , ERROR_IS_NOT_DEPOOL 
 	 	 ) ; IElector ( elector ) . recover_stake { value : msg_value - DePoolLib 
 	 	 . PROXY_FEE } ( queryId ) ; } *)
Definition DePoolProxyContract_Ф_recover_stake ( msg_value : XInteger ) ( msg_sender : XInteger ) ( Л_queryId : XInteger64 )( Л_elector : XAddress ) : LedgerT ( XErrorValue True XInteger ) := 
 Require {{ $ msg_sender ?== ↑7 DePoolProxyContract_ι_m_dePool , ↑7 DePoolProxyContract_ι_ERROR_IS_NOT_DEPOOL }} ; 
 	 (* IElector ( $ Л_elector ) ^^ DePoolProxyContract_Ф_recover_stake { value : $ msg_value !-  DePoolLib_ι_PROXY_FEE 
 } 
 ( $ Л_queryId ) *) . 
 

(* function onSuccessToRecoverStake ( uint64 queryId ) public 
 	 	 functionID ( 0xF96F7324 ) { IDePool ( m_dePool ) . onSuccessToRecoverStake 
 	 	 { value : msg_value - DePoolLib . PROXY_FEE } ( queryId , msg_sender 
 	 	 ) ; } *)
Definition DePoolProxyContract_Ф_onSuccessToRecoverStake ( msg_value : XInteger ) ( msg_sender : XInteger ) ( Л_queryId : XInteger64 ) : LedgerT ( XErrorValue True XInteger ) := 
 (* IDePool ( ↑7 DePoolProxyContract_ι_m_dePool ) ^^ DePoolProxyContract_Ф_onSuccessToRecoverStake { value : $ msg_value !-  DePoolLib_ι_PROXY_FEE 
 } 
 ( $ Л_queryId , $ msg_sender ) *) . 
 

(* function getProxyInfo ( ) public view returns ( address depool 
 	 	 , uint64 minBalance ) { depool = m_dePool ; minBalance = MIN_BALANCE 
 	 	 ; } *)
Definition DePoolProxyContract_Ф_getProxyInfo : LedgerT ( XErrorValue ( XAddress # XInteger64 ) XInteger ) := 
 ↑7 DePoolProxyContract_ι_m_dePool ; 
 	 ↑7 DePoolProxyContract_ι_MIN_BALANCE ; . 
 

(* function _addStakes ( Round round , DePoolLib . Participant 
 	 	 participant , address participantAddress , uint64 stake , optional 
 	 	 ( InvestParams ) vesting , optional ( InvestParams ) lock ) internal 
 	 	 inline returns ( Round , DePoolLib . Participant ) { if ( stake == 
 	 	 0 && ! vesting . hasValue ( ) && ! lock . hasValue ( ) ) { return ( round 
 	 	 , participant ) ; } if ( ! round . stakes . exists ( participantAddress 
 	 	 ) ) { round . participantQty + + ; participant . roundQty + + ; } round 
 	 	 . stake + = stake ; StakeValue sv = round . stakes [ participantAddress 
 	 	 ] ; sv . ordinary + = stake ; if ( vesting . hasValue ( ) ) { participant 
 	 	 . haveVesting = true ; if ( vesting . get ( ) . isActive ) { round . stake 
 	 	 + = vesting . get ( ) . amount ; } sv . vesting = vesting ; } if ( lock . 
 	 	 hasValue ( ) ) { participant . haveLock = true ; if ( lock . get ( ) . 
 	 	 isActive ) { round . stake + = lock . get ( ) . amount ; } sv . lock = lock 
 	 	 ; } round . stakes [ participantAddress ] = sv ; return ( round , participant 
 	 	 ) ; } *)
Definition RoundsBase_Ф__addStakes ( Л_round : RoundsBase_ι_Round )( Л_Participant : DePoolLib ) : LedgerT ( XErrorValue ( RoundsBase_ι_Round # := 
 
 Ift ( ↑8 RoundsBase_ι_Round_ι_stake ?== $ xInt0 && ! vesting . hasValue () XInteger ) { && { ! { lock { . { hasValue { ( { ) { ) { return# ( $ Л_round , participant ) . 
 	 
 
 Ift ( ! $ Л_round . ↑8 RoundsBase_ι_Round_ι_stakes . exists ( participantAddress ) { ) { $ Л_round ^^ RoundsBase_ι_Round_ι_participantQty ++ ; 
 	 participant ^^ roundQty ++ ; 
 	 
 d2! Л_round ^^ RoundsBase_ι_Round_ι_stake += ↑8 RoundsBase_ι_Round_ι_stake ; 
 	 d0! Л_sv := $ Л_round ^^ RoundsBase_ι_Round_ι_stakes [ participantAddress ] ; 
 	 d2! Л_sv ^^ RoundsBase_ι_StakeValue_ι_ordinary += ↑8 RoundsBase_ι_Round_ι_stake ; 
 	 
 Ift ( vesting . hasValue () { ) { d2! participant ^^ haveVesting := $ xBoolTrue ; 
 	 
 Ift ( vesting . get () { . { ↑8 RoundsBase_ι_InvestParams_ι_isActive { ) { d2! Л_round ^^ RoundsBase_ι_Round_ι_stake += vesting ^^ get ( ) ^^ RoundsBase_ι_InvestParams_ι_amount ; 
 	 
 d2! Л_sv ^^ vesting := vesting ; 
 	 
 
 Ift ( lock . hasValue () { ) { d2! participant ^^ haveLock := $ xBoolTrue ; 
 	 
 Ift ( lock . get () { . { ↑8 RoundsBase_ι_InvestParams_ι_isActive { ) { d2! Л_round ^^ RoundsBase_ι_Round_ι_stake += lock ^^ get ( ) ^^ RoundsBase_ι_InvestParams_ι_amount ; 
 	 
 d2! Л_sv ^^ lock := lock ; 
 	 
 d3! Л_round ^^ RoundsBase_ι_Round_ι_stakes [ participantAddress ] := $ Л_sv ; 
 	 return# ( $ Л_round , participant ) .
(* function transferStakeInOneRound ( Round round , DePoolLib 
 	 	 . Participant sourceParticipant , DePoolLib . Participant destinationParticipant 
 	 	 , address source , address destination , uint64 amount , uint64 
 	 	 minStake ) internal inline returns ( Round , uint64 , uint64 , DePoolLib 
 	 	 . Participant , DePoolLib . Participant ) { optional ( StakeValue 
 	 	 ) optSourceStake = round . stakes . fetch ( source ) ; if ( ! optSourceStake 
 	 	 . hasValue ( ) ) return ( round , 0 , 0 , sourceParticipant , destinationParticipant 
 	 	 ) ; StakeValue sourceStake = optSourceStake . get ( ) ; uint64 prevSourceStake 
 	 	 = round . stakes [ source ] . ordinary ; uint64 newSourceStake ; 
 	 	 uint64 deltaDestinationStake ; if ( sourceStake . ordinary >= 
 	 	 amount ) { newSourceStake = sourceStake . ordinary - amount ; deltaDestinationStake 
 	 	 = amount ; } else { newSourceStake = 0 ; deltaDestinationStake 
 	 	 = sourceStake . ordinary ; } uint64 newDestStake = round . stakes 
 	 	 [ destination ] . ordinary + deltaDestinationStake ; if ( ( 0 < newSourceStake 
 	 	 && newSourceStake < minStake ) || ( 0 < newDestStake && newDestStake 
 	 	 < minStake ) ) { return ( round , 0 , prevSourceStake , sourceParticipant 
 	 	 , destinationParticipant ) ; } sourceStake . ordinary = newSourceStake 
 	 	 ; if ( activeAndNotStakeSum ( sourceStake ) == 0 ) { - - round . participantQty 
 	 	 ; delete round . stakes [ source ] ; - - sourceParticipant . roundQty 
 	 	 ; } else { round . stakes [ source ] = sourceStake ; } if ( ! round . stakes 
 	 	 . exists ( destination ) ) { + + round . participantQty ; + + destinationParticipant 
 	 	 . roundQty ; } round . stakes [ destination ] . ordinary + = deltaDestinationStake 
 	 	 ; return ( round , deltaDestinationStake , prevSourceStake , 
 	 	 sourceParticipant , destinationParticipant ) ; } *)
Definition RoundsBase_Ф_transferStakeInOneRound ( Л_round : RoundsBase_ι_Round )( Л_Participant : DePoolLib ) : LedgerT ( XErrorValue ( RoundsBase_ι_Round # XInteger64 # XInteger64 # := 
 optional ( ↑8 RoundsBase_ι_StakeValue ) XInteger ) $ Л_round ^^ RoundsBase_ι_Round_ι_stakes . fetch ( source ) >> 
 	 
 Ife ( ! optSourceStake . hasValue () { ) { return! { ( { $ Л_round { , { $ { xInt0 { , { $ { xInt0 { , { sourceParticipant { , { destinationParticipant { ) } >> d0! Л_sourceStake := optSourceStake ^^ get ( ) >> 
 	 d0! Л_prevSourceStake := $ Л_round ^^ RoundsBase_ι_Round_ι_stakes [ source ] ^^ RoundsBase_ι_StakeValue_ι_ordinary ; 
 	 
 Ife ( $ Л_sourceStake . ↑8 RoundsBase_ι_StakeValue_ι_ordinary ?>= ↑8 RoundsBase_ι_InvestParams_ι_amount ) { d0! Л_newSourceStake := $ Л_sourceStake . ↑8 RoundsBase_ι_StakeValue_ι_ordinary !- ↑8 RoundsBase_ι_InvestParams_ι_amount ; d0! Л_deltaDestinationStake := ↑8 RoundsBase_ι_InvestParams_ι_amount ; } else { d0! Л_newSourceStake := $ xInt0 ; d0! Л_deltaDestinationStake := $ Л_sourceStake . ↑8 RoundsBase_ι_StakeValue_ι_ordinary ; } >> d0! Л_newDestStake := $ Л_round . ↑8 RoundsBase_ι_Round_ι_stakes [ destination ] . ↑8 RoundsBase_ι_StakeValue_ι_ordinary !+ $ Л_deltaDestinationStake ; if ( ( $ xInt0 ?< $ Л_newSourceStake && $ Л_newSourceStake ?< minStake ) || ( $ xInt0 ?< $ Л_newDestStake && $ Л_newDestStake ?< minStake ) ) { return# ( $ Л_round , $ xInt0 , $ Л_prevSourceStake , sourceParticipant , destinationParticipant ) . 
 	 
 d2! Л_sourceStake ^^ RoundsBase_ι_StakeValue_ι_ordinary := $ Л_newSourceStake ; 
 	 
 Ife ( RoundsBase_Ф_activeAndNotStakeSum ( $ Л_sourceStake ) { ?== { $ { xInt0 { ) { -- $ Л_round ^^ RoundsBase_ι_Round_ι_participantQty ; 
 	 delete $ Л_round ^^ RoundsBase_ι_Round_ι_stakes [ source ] ; 
 	 -- sourceParticipant ^^ roundQty ; 
 	 
 } 
 else { d3! Л_round ^^ RoundsBase_ι_Round_ι_stakes [ source ] := $ Л_sourceStake ; 
 	 
 
 Ift ( ! $ Л_round . ↑8 RoundsBase_ι_Round_ι_stakes . exists ( destination ) { ) { ++ $ Л_round ^^ RoundsBase_ι_Round_ι_participantQty ; 
 	 ++ destinationParticipant ^^ roundQty ; 
 	 
 $ Л_round ^^ RoundsBase_ι_Round_ι_stakes [ destination d2! ] ^^ RoundsBase_ι_StakeValue_ι_ordinary += $ Л_deltaDestinationStake ; 
 	 return# ( $ Л_round , $ Л_deltaDestinationStake , $ Л_prevSourceStake , sourceParticipant , destinationParticipant ) .
(* function withdrawStakeInPoolingRound ( DePoolLib . Participant 
 	 	 participant , address participantAddress , uint64 targetAmount 
 	 	 , uint64 minStake ) internal inline returns ( uint64 , DePoolLib 
 	 	 . Participant ) { Round round = m_rounds . fetch ( m_roundQty - 1 
 	 	 ) . get ( ) ; optional ( StakeValue ) optSv = round . stakes . fetch 
 	 	 ( participantAddress ) ; if ( ! optSv . hasValue ( ) ) { return ( 0 , 
 	 	 participant ) ; } StakeValue sv = optSv . get ( ) ; targetAmount = 
 	 	 math . min ( targetAmount , sv . ordinary ) ; sv . ordinary - = targetAmount 
 	 	 ; round . stake - = targetAmount ; if ( sv . ordinary < minStake ) { 
 	 	 round . stake - = sv . ordinary ; targetAmount + = sv . ordinary ; sv 
 	 	 . ordinary = 0 ; } if ( activeAndNotStakeSum ( sv ) == 0 ) { - - round 
 	 	 . participantQty ; delete round . stakes [ participantAddress 
 	 	 ] ; - - participant . roundQty ; } else { round . stakes [ participantAddress 
 	 	 ] = sv ; } m_rounds [ m_roundQty - 1 ] = round ; return ( targetAmount 
 	 	 , participant ) ; } *)
Definition RoundsBase_Ф_withdrawStakeInPoolingRound ( Л_Participant : DePoolLib ) : LedgerT ( XErrorValue ( XInteger64 # := 
 d0! Л_round :=  ^^ fetch (  !- $ xInt1 ) XInteger ) ^^ get ( ) >> 
 	 optional ( ↑8 RoundsBase_ι_StakeValue ) $ Л_round ^^ RoundsBase_ι_Round_ι_stakes . fetch ( participantAddress ) >> 
 	 
 Ift ( ! optSv . hasValue () { ) { return# ( $ xInt0 , participant ) . 
 	 
 d0! Л_sv := optSv ^^ get ( ) >> 
 	 math ^^ min ( targetAmount , $ Л_sv ^^ RoundsBase_ι_StakeValue_ι_ordinary ) >> 
 	 d2! Л_sv ^^ RoundsBase_ι_StakeValue_ι_ordinary -= targetAmount ; 
 	 d2! Л_round ^^ RoundsBase_ι_Round_ι_stake -= targetAmount ; 
 	 
 Ift ( $ Л_sv . ↑8 RoundsBase_ι_StakeValue_ι_ordinary ?< minStake ) { $ Л_round . d1! RoundsBase_ι_Round_ι_stake -= $ Л_sv . ↑8 RoundsBase_ι_StakeValue_ι_ordinary ; $ Л_sv . ↑8 RoundsBase_ι_StakeValue_ι_ordinary ; $ Л_sv . d1! RoundsBase_ι_StakeValue_ι_ordinary := $ xInt0 ; } >> if ( RoundsBase_Ф_activeAndNotStakeSum ( $ Л_sv ) ?== $ xInt0 ) { -- $ Л_round ^^ RoundsBase_ι_Round_ι_participantQty ; 
 	 delete $ Л_round ^^ RoundsBase_ι_Round_ι_stakes [ participantAddress ] ; 
 	 -- participant ^^ roundQty ; 
 	 
 } 
 else { d3! Л_round ^^ RoundsBase_ι_Round_ι_stakes [ participantAddress ] := $ Л_sv ; 
 	 
  [  !- $ xInt1 $ Л_round ; 
 	 return# ( targetAmount , participant ) .
(* function activeAndNotStakeSum ( StakeValue stakes ) internal 
 	 	 inline returns ( uint64 ) { optional ( InvestParams ) v = stakes 
 	 	 . vesting ; optional ( InvestParams ) l = stakes . lock ; return stakes 
 	 	 . ordinary + ( v . hasValue ( ) ? v . get ( ) . amount : 0 ) + ( l . hasValue 
 	 	 ( ) ? l . get ( ) . amount : 0 ) ; } *)
Definition RoundsBase_Ф_activeAndNotStakeSum ( Л_stakes : RoundsBase_ι_StakeValue ) : LedgerT ( XErrorValue XInteger64 XInteger ) := 
 optional ( ↑8 RoundsBase_ι_InvestParams ) $ Л_stakes ^^ vesting ; 
 	 optional ( ↑8 RoundsBase_ι_InvestParams ) $ Л_stakes ^^ lock ; 
 	 $ Л_stakes ^^ RoundsBase_ι_StakeValue_ι_ordinary !+ ( v ^^ hasValue ( ) ? v ^^ get ( ) ^^ RoundsBase_ι_InvestParams_ι_amount : $ xInt0 ) !+ ( l ^^ hasValue ( ) ? l ^^ get ( ) ^^ RoundsBase_ι_InvestParams_ι_amount : $ xInt0 ) .
(* function activeStakeSum ( StakeValue stakes ) internal inline 
 	 	 returns ( uint64 ) { optional ( InvestParams ) v = stakes . vesting 
 	 	 ; optional ( InvestParams ) l = stakes . lock ; return stakes . ordinary 
 	 	 + ( v . hasValue ( ) && v . get ( ) . isActive ? v . get ( ) . amount : 0 ) + ( 
 	 	 l . hasValue ( ) && l . get ( ) . isActive ? l . get ( ) . amount : 0 ) ; } *) 
 	 	
Definition RoundsBase_Ф_activeStakeSum ( Л_stakes : RoundsBase_ι_StakeValue ) : LedgerT ( XErrorValue XInteger64 XInteger ) := 
 optional ( ↑8 RoundsBase_ι_InvestParams ) $ Л_stakes ^^ vesting ; 
 	 optional ( ↑8 RoundsBase_ι_InvestParams ) $ Л_stakes ^^ lock ; 
 	 $ Л_stakes ^^ RoundsBase_ι_StakeValue_ι_ordinary !+ ( v ^^ hasValue ( ) && v ^^ get ( ) ^^ RoundsBase_ι_InvestParams_ι_isActive ? v ^^ get ( ) ^^ RoundsBase_ι_InvestParams_ι_amount : $ xInt0 ) !+ ( l ^^ hasValue ( ) && l ^^ get ( ) ^^ RoundsBase_ι_InvestParams_ι_isActive ? l ^^ get ( ) ^^ RoundsBase_ι_InvestParams_ι_amount : $ xInt0 ) .
(* function toTruncatedRound ( Round round ) internal pure returns 
 	 	 ( TruncatedRound ) { return TruncatedRound ( round . id , round 
 	 	 . supposedElectedAt , round . unfreeze , round . step , round . completionReason 
 	 	 , round . participantQty , round . stake , round . rewards , round 
 	 	 . unused , round . start , round . end , round . vsetHashInElectionPhase 
 	 	 ) ; } *)
Definition RoundsBase_Ф_toTruncatedRound ( Л_round : RoundsBase_ι_Round ) : LedgerT ( XErrorValue RoundsBase_ι_TruncatedRound XInteger ) := 
 return! ↑8 RoundsBase_ι_TruncatedRound ( $ Л_round ^^ RoundsBase_ι_Round_ι_id , $ Л_round ^^ RoundsBase_ι_Round_ι_supposedElectedAt , $ Л_round ^^ RoundsBase_ι_Round_ι_unfreeze , $ Л_round ^^ RoundsBase_ι_Round_ι_step , $ Л_round ^^ RoundsBase_ι_Round_ι_completionReason , $ Л_round ^^ RoundsBase_ι_Round_ι_participantQty , $ Л_round ^^ RoundsBase_ι_Round_ι_stake , $ Л_round ^^ RoundsBase_ι_Round_ι_rewards , $ Л_round ^^ RoundsBase_ι_Round_ι_unused , $ Л_round ^^ RoundsBase_ι_Round_ι_start , $ Л_round ^^ RoundsBase_ι_Round_ι_end , $ Л_round ^^ RoundsBase_ι_Round_ι_vsetHashInElectionPhase ) >> . 
 

(* function getRounds ( ) external view returns ( mapping ( uint64 
 	 	 => TruncatedRound ) rounds ) { optional ( uint64 , Round ) pair = 
 	 	 m_rounds . min ( ) ; while ( pair . hasValue ( ) ) { ( uint64 id , Round 
 	 	 round ) = pair . get ( ) ; TruncatedRound r = toTruncatedRound ( round 
 	 	 ) ; rounds [ r . id ] = r ; pair = m_rounds . next ( id ) ; } return rounds 
 	 	 ; } *)
Definition RoundsBase_Ф_getRounds : LedgerT ( XErrorValue True XInteger ) := 
 optional ( uint64 , ↑8 RoundsBase_ι_Round )  ^^ min ( ) >> 
 	 while ( pair ^^ hasValue ( ) ) { {( $ Л_id , Л_round pair get ( >> 
 d0! Л_r RoundsBase_Ф_toTruncatedRound (! Л_round !) 
 	 [ $ ^^ $ Л_r 
 	 ^^ next $ Л_id >> 
 
 } 
 return! ; 
 
 } >> . 
 

(* function Constructor7 ( uint64 minRoundStake , address proxy0 
 	 	 , address proxy1 , address validatorWallet , uint64 minStake 
 	 	 ) CheckAndAcceptBase ( minStake , minRoundStake ) ValidatorBase 
 	 	 ( validatorWallet ) ProxyBase ( proxy0 , proxy1 ) public { m_minRoundStake 
 	 	 = minRoundStake ; m_minStake = minStake ; m_poolClosed = false 
 	 	 ; ( , uint32 electionsStartBefore , , ) = roundTimeParams ( ) ; ( 
 	 	 uint256 curValidatorHash , , uint32 validationEnd ) = getCurValidatorData 
 	 	 ( ) ; uint256 prevValidatorHash = getPrevValidatorHash ( ) ; bool 
 	 	 areElectionsStarted = now >= validationEnd - electionsStartBefore 
 	 	 ; Round r2 = generateRound ( ) ; Round r1 = generateRound ( ) ; Round 
 	 	 r0 = generateRound ( ) ; ( r2 . step , r2 . completionReason , r2 . unfreeze 
 	 	 ) = ( RoundStep . Completed , CompletionReason . FakeRound , 0 ) 
 	 	 ; ( r1 . step , r1 . completionReason , r1 . unfreeze ) = ( RoundStep 
 	 	 . WaitingUnfreeze , CompletionReason . FakeRound , 0 ) ; r1 . vsetHashInElectionPhase 
 	 	 = areElectionsStarted? curValidatorHash : prevValidatorHash 
 	 	 ; m_rounds [ r0 . id ] = r0 ; m_rounds [ r1 . id ] = r1 ; m_rounds [ r2 . id 
 	 	 ] = r2 ; } *)
Definition DePoolContract_Ф_Constructor7 ( Л_minRoundStake : XInteger64 )( Л_proxy0 : XAddress )( Л_proxy1 : XAddress )( Л_validatorWallet : XAddress )( Л_minStake : XInteger64 ) : LedgerT ( XErrorValue True XInteger ) := 
 d1! DePoolContract_ι_m_minRoundStake := $ Л_minRoundStake ; 
 	 d1! DePoolContract_ι_m_minStake := $ Л_minStake ; 
 	 d1! DePoolContract_ι_m_poolClosed := $ xBoolFalse ; 
 	 ( , $ Л_electionsStartBefore , _ , DebugDePool_Ф_roundTimeParams () ; 
 	 {( $ Л_curValidatorHash , , $ DebugDePool_Ф_getCurValidatorData () 
 	 Л_prevValidatorHash := () ; 	 d0! := )} := tvm_now ?>= $ Л_validationEnd !- $ Л_electionsStartBefore ; 
 	 d0! Л_r2 := DePoolContract_Ф_generateRound () ; 
 	 d0! Л_r1 := DePoolContract_Ф_generateRound () ; 
 	 d0! Л_r0 := DePoolContract_Ф_generateRound () ; 
 	 ( $ Л_r2 ^^ RoundsBase_ι_Round_ι_step , $ Л_r2 ^^ RoundsBase_ι_Round_ι_completionReason , $ Л_r2 ^^ RoundsBase_ι_Round_ι_unfreeze ( RoundStep ^^ Completed , CompletionReason ^^ FakeRound , $ xInt0 ) >> 
 	 ( $ Л_r1 ^^ RoundsBase_ι_Round_ι_step , $ Л_r1 ^^ RoundsBase_ι_Round_ι_completionReason , $ Л_r1 ^^ RoundsBase_ι_Round_ι_unfreeze ( RoundStep ^^ WaitingUnfreeze , CompletionReason ^^ FakeRound , $ xInt0 ) >> 
 	 d2! Л_r1 ^^ RoundsBase_ι_Round_ι_vsetHashInElectionPhase := areElectionsStarted? Л_curValidatorHash : $ Л_prevValidatorHash ; 
 	  [ $ Л_r0 ^^ RoundsBase_ι_Round_ι_id $ Л_r0 ; 
 	  [ $ Л_r1 ^^ RoundsBase_ι_Round_ι_id $ Л_r1 ; 
 	  [ $ Л_r2 ^^ RoundsBase_ι_Round_ι_id $ Л_r2 ; . 
 

(* function _returnChange ( ) private pure { msg_sender . transfer 
 	 	 ( 0 , false , 64 ) ; } *)
Definition DePoolContract_Ф__returnChange ( msg_sender : XInteger ) : LedgerT ( XErrorValue True XInteger ) := 
 $ msg_sender ^^ transfer {( $ xInt0 , xBoolFalse , xInt64 ) 
 	 } >> . 
 

(* function _calcLastRoundInterest ( uint64 totalStake , uint64 
 	 	 rewards ) private pure inline returns ( uint64 ) { return totalStake 
 	 	 ! = 0 ? math . muldiv ( rewards , 100 * 1e9 , totalStake ) : 0 ; } *)
Definition DePoolContract_Ф__calcLastRoundInterest ( Л_totalStake : XInteger64 )( Л_rewards : XInteger64 ) : LedgerT ( XErrorValue XInteger64 XInteger ) := 
 $ Л_totalStake ?!= $ xInt0 ? math ^^ muldiv ( $ Л_rewards , $ xInt100 !* 1e9 , $ Л_totalStake ) : $ xInt0 .
(* function _sendError ( uint32 errcode , uint64 comment ) private 
 	 	 { IParticipant ( msg_sender ) . receiveAnswer { value : 0 , bounce 
 	 	 : false , flag : 64 } ( errcode , comment ) ; } *)
Definition DePoolContract_Ф__sendError ( msg_sender : XInteger ) ( Л_errcode : XInteger32 )( Л_comment : XInteger64 ) : LedgerT ( XErrorValue True XInteger ) := 
 (* IParticipant ( $ msg_sender ) ^^ DePool_Ф_receiveAnswer { value : $ xInt0 , bounce : $ xBoolFalse , flag : $ xInt64 
 } 
 ( $ Л_errcode , $ Л_comment ) *) . 
 

(* function _sendAccept ( uint64 fee ) private { IParticipant 
 	 	 ( msg_sender ) . receiveAnswer { value : ANSWER_MSG_FEE , bounce 
 	 	 : false } ( STATUS_SUCCESS , fee ) ; } *)
Definition DePoolContract_Ф__sendAccept ( msg_sender : XInteger ) ( Л_fee : XInteger64 ) : LedgerT ( XErrorValue True XInteger ) := 
 (* IParticipant ( $ msg_sender ) ^^ DePool_Ф_receiveAnswer { value : DePoolContract_ι_ANSWER_MSG_FEE , bounce : $ xBoolFalse 
 } 
 ( ↑2 CheckAndAcceptBase_ι_STATUS_SUCCESS , $ Л_fee ) *) . 
 

(* function startRoundCompleting ( Round round , CompletionReason 
 	 	 reason ) private returns ( Round ) { round . completionReason = 
 	 	 reason ; round . step = RoundStep . Completing ; round . end = uint32 
 	 	 ( now ) ; this . completeRound { flag : 1 , bounce : false , value : VALUE_FOR_SELF_CALL 
 	 	 } ( round . id , round . participantQty ) ; emit RoundCompleted ( 
 	 	 toTruncatedRound ( round ) ) ; return round ; } *)
Definition DePoolContract_Ф_startRoundCompleting ( Л_round : RoundsBase_ι_Round )( Л_reason : CompletionReason ) : LedgerT ( XErrorValue RoundsBase_ι_Round XInteger ) := 
 d2! Л_round ^^ RoundsBase_ι_Round_ι_completionReason := $ Л_reason ; 
 	 d2! Л_round ^^ RoundsBase_ι_Round_ι_step := RoundStep ^^ Completing ; 
 	 d2! Л_round ^^ RoundsBase_ι_Round_ι_end := tvm_now ; 
 	 this ^^ DePoolContract_Ф_completeRound { flag : $ xInt1 , bounce : $ xBoolFalse , value : DePoolContract_ι_VALUE_FOR_SELF_CALL 
 } 
 ( $ Л_round ^^ RoundsBase_ι_Round_ι_id , $ Л_round ^^ RoundsBase_ι_Round_ι_participantQty ) >> 
 	 emit $ Л_RoundCompleted ( RoundsBase_Ф_toTruncatedRound (! $ Л_round !) ) >> 
 	 $ Л_round .
(* function cutWithdrawalValueAndActivateStake ( InvestParams 
 	 	 p ) private view returns ( optional ( InvestParams ) , uint64 ) { 
 	 	 uint64 periodQty = ( uint64 ( now ) - p . lastWithdrawalTime ) / p 
 	 	 . withdrawalPeriod ; uint64 withdrawal = math . min ( periodQty 
 	 	 * p . withdrawalValue , p . amount ) ; p . amount - = withdrawal ; if 
 	 	 ( p . amount < m_minStake ) { withdrawal + = p . amount ; p . amount = 
 	 	 0 ; } p . lastWithdrawalTime + = periodQty * p . withdrawalPeriod 
 	 	 ; p . isActive = true ; optional ( InvestParams ) opt ; opt . set ( p 
 	 	 ) ; return ( opt , withdrawal ) ; } *)
Definition DePoolContract_Ф_cutWithdrawalValueAndActivateStake ( Л_p : RoundsBase_ι_InvestParams ) : LedgerT ( XErrorValue True XInteger ) := 
 d0! Л_periodQty := ( tvm_now !- $ Л_p ^^ RoundsBase_ι_InvestParams_ι_lastWithdrawalTime ) !/ $ Л_p ^^ RoundsBase_ι_InvestParams_ι_withdrawalPeriod ; 
 	 d0! Л_withdrawal := math ^^ min ( $ Л_periodQty !* $ Л_p ^^ RoundsBase_ι_InvestParams_ι_withdrawalValue , $ Л_p ^^ RoundsBase_ι_InvestParams_ι_amount ) >> 
 	 d2! Л_p ^^ RoundsBase_ι_InvestParams_ι_amount -= $ Л_withdrawal ; 
 	 
 Ift ( $ Л_p . ↑8 RoundsBase_ι_InvestParams_ι_amount ?< ↑9 DePoolContract_ι_m_minStake ) { d0! Л_withdrawal += $ Л_p . ↑8 RoundsBase_ι_InvestParams_ι_amount ; $ Л_p . d1! RoundsBase_ι_InvestParams_ι_amount := $ xInt0 ; } >> $ Л_p . d1! RoundsBase_ι_InvestParams_ι_lastWithdrawalTime += $ Л_periodQty !* $ Л_p . ↑8 RoundsBase_ι_InvestParams_ι_withdrawalPeriod ; $ Л_p . d1! RoundsBase_ι_InvestParams_ι_isActive := $ xBoolTrue ; optional ( ↑8 RoundsBase_ι_InvestParams ) { opt } >> opt ^^ set ( $ Л_p ) >> 
 	 return# ( opt , $ Л_withdrawal ) .
(* function _returnOrReinvestForParticipant ( Round completedRound 
 	 	 , Round round0 , address addr , StakeValue stakes ) private inline 
 	 	 returns ( Round ) { bool validatorIsPunished = completedRound 
 	 	 . completionReason == CompletionReason . ValidatorIsPunished 
 	 	 ; optional ( DePoolLib . Participant ) optParticipant = m_participants 
 	 	 . fetch ( addr ) ; require ( optParticipant . hasValue ( ) , InternalErrors 
 	 	 . ERROR511 ) ; DePoolLib . Participant participant = optParticipant 
 	 	 . get ( ) ; - - participant . roundQty ; bool isZeroRoundStake = completedRound 
 	 	 . stake == 0 ; uint64 newStake ; uint64 reward ; if ( validatorIsPunished 
 	 	 ) { newStake = math . muldiv ( completedRound . unused , stakes . 
 	 	 ordinary , completedRound . stake ) ; } else { if ( ! isZeroRoundStake 
 	 	 ) { int stakeSum = activeStakeSum ( stakes ) ; reward = uint64 ( math 
 	 	 . max ( math . muldiv ( stakeSum , completedRound . rewards , completedRound 
 	 	 . stake ) - int ( RET_OR_REINV_FEE ) , 0 ) ) ; } participant . reward 
 	 	 + = reward ; newStake = stakes . ordinary + reward ; } optional ( InvestParams 
 	 	 ) newVesting = stakes . vesting ; if ( newVesting . hasValue ( ) ) 
 	 	 { if ( validatorIsPunished && newVesting . get ( ) . isActive ) { 
 	 	 InvestParams params = newVesting . get ( ) ; params . amount = math 
 	 	 . muldiv ( completedRound . unused , params . amount , completedRound 
 	 	 . stake ) ; newVesting . set ( params ) ; } uint64 withdrawalVesting 
 	 	 ; ( newVesting , withdrawalVesting ) = cutWithdrawalValueAndActivateStake 
 	 	 ( newVesting . get ( ) ) ; newStake + = withdrawalVesting ; } uint64 
 	 	 attachedValue ; uint64 curPause = math . min ( participant . withdrawValue 
 	 	 , newStake ) ; attachedValue + = curPause ; participant . withdrawValue 
 	 	 - = curPause ; newStake - = curPause ; if ( newStake < m_minStake 
 	 	 ) { attachedValue + = newStake ; newStake = 0 ; } optional ( InvestParams 
 	 	 ) newLock = stakes . lock ; if ( newLock . hasValue ( ) ) { if ( validatorIsPunished 
 	 	 && newLock . get ( ) . isActive ) { InvestParams params = newLock 
 	 	 . get ( ) ; params . amount = math . muldiv ( completedRound . unused 
 	 	 , params . amount , completedRound . stake ) ; newLock . set ( params 
 	 	 ) ; } uint64 withdrawalLock ; ( newLock , withdrawalLock ) = cutWithdrawalValueAndActivateStake 
 	 	 ( newLock . get ( ) ) ; if ( withdrawalLock ! = 0 ) { newLock . get ( ) . 
 	 	 owner . transfer ( withdrawalLock , false , 1 ) ; } } if ( m_poolClosed 
 	 	 ) { attachedValue + = newStake ; if ( newVesting . hasValue ( ) ) { 
 	 	 newVesting . get ( ) . owner . transfer ( newVesting . get ( ) . amount 
 	 	 , false , 1 ) ; } if ( newLock . hasValue ( ) ) { newLock . get ( ) . owner 
 	 	 . transfer ( newLock . get ( ) . amount , false , 1 ) ; } } else { if ( newVesting 
 	 	 . hasValue ( ) && newVesting . get ( ) . amount == 0 ) newVesting . reset 
 	 	 ( ) ; if ( newLock . hasValue ( ) && newLock . get ( ) . amount == 0 ) newLock 
 	 	 . reset ( ) ; attachedValue + = 1 ; if ( ! participant . reinvest ) { 
 	 	 attachedValue + = newStake ; newStake = 0 ; } ( round0 , participant 
 	 	 ) = _addStakes ( round0 , participant , addr , newStake , newVesting 
 	 	 , newLock ) ; } _setOrDeleteParticipant ( addr , participant ) 
 	 	 ; IParticipant ( addr ) . onRoundComplete { value : attachedValue 
 	 	 , bounce : false } ( completedRound . id , reward , stakes . ordinary 
 	 	 , stakes . vesting . hasValue ( ) && stakes . vesting . get ( ) . isActive? 
 	 	 stakes . vesting . get ( ) . amount : 0 , stakes . lock . hasValue ( ) 
 	 	 && stakes . lock . get ( ) . isActive? stakes . lock . get ( ) . amount 
 	 	 : 0 , participant . reinvest , uint8 ( completedRound . completionReason 
 	 	 ) ) ; return round0 ; } *)
Definition DePoolContract_Ф__returnOrReinvestForParticipant ( Л_completedRound : RoundsBase_ι_Round )( Л_round0 : RoundsBase_ι_Round )( Л_addr : XAddress )( Л_stakes : RoundsBase_ι_StakeValue ) : LedgerT ( XErrorValue RoundsBase_ι_Round XInteger ) := 
 d0! Л_validatorIsPunished := $ Л_completedRound ^^ RoundsBase_ι_Round_ι_completionReason ?== CompletionReason ^^ ValidatorIsPunished ; 
 	 optional (  DePoolLib_ι_DePoolHelper_ι_Participant )  ^^ fetch ( $ Л_addr ) >> 
 	 Require {{ optParticipant ^^ hasValue ( ) ,  InternalErrors_ι_ERROR511 }} ; 
 	 d0! Л_participant := optParticipant ^^ get ( ) >> 
 	 -- $ Л_participant ^^ roundQty ; 
 	 d0! Л_isZeroRoundStake := $ Л_completedRound ^^ RoundsBase_ι_Round_ι_stake ?== $ xInt0 ; 
 	 
 Ife ( $ Л_validatorIsPunished ) { d0! Л_newStake := math . muldiv ( $ Л_completedRound . ↑8 RoundsBase_ι_Round_ι_unused , $ Л_stakes . ↑8 RoundsBase_ι_StakeValue_ι_ordinary , $ Л_completedRound . ↑8 RoundsBase_ι_Round_ι_stake ) } >> 
 } 
 else { 
 Ift ( ! $ Л_isZeroRoundStake ) { d0! Л_stakeSum := RoundsBase_Ф_activeStakeSum ( $ Л_stakes ) } >> d0! Л_reward := math . max ( math . muldiv {( $ Л_stakeSum , Л_completedRound . RoundsBase_ι_Round_ι_rewards , Л_completedRound . RoundsBase_ι_Round_ι_stake !- DePoolContract_ι_RET_OR_REINV_FEE , xInt0 ) >> 
 
 } 
 d2! ^^ ↑10 += $ ; 
 d0! Л_newStake $ Л_stakes ↑8 RoundsBase_ι_StakeValue_ι_ordinary $ Л_reward 
 	 } >> optional ( RoundsBase_ι_InvestParams ) Л_stakes ^^ ; 
 
 Ift newVesting . () ) { Ift ( Л_validatorIsPunished && . get ) { { ↑8 { ) d0! Л_params newVesting ^^ ( ) 
 	 Л_params ^^ RoundsBase_ι_InvestParams_ι_amount := ^^ muldiv $ Л_completedRound ↑8 RoundsBase_ι_Round_ι_unused $ Л_params ↑8 RoundsBase_ι_InvestParams_ι_amount $ Л_completedRound ↑8 RoundsBase_ι_Round_ι_stake >> 
 newVesting ^^ ( $ ) >> 	 
 
 ( , $ DePoolContract_Ф_cutWithdrawalValueAndActivateStake (! . get !) ) 
 	 Л_newStake += Л_withdrawalVesting ; 	 
 >> 
 Л_curPause := ^^ min $ Л_participant withdrawValue , Л_newStake ) 
 	 Л_attachedValue += Л_curPause ; 	 d2! ^^ withdrawValue $ Л_curPause 
 	 Л_newStake -= Л_curPause ; 	 
 ( $ ?< ↑9 ) { Л_attachedValue += Л_newStake ; Л_newStake := xInt0 ; >> optional ↑8 RoundsBase_ι_InvestParams { newLock $ Л_stakes . { } >> Ift ( . hasValue ) { { 
 ( $ && newLock get ( { . ↑8 RoundsBase_ι_InvestParams_ι_isActive ) { Л_params := ^^ get ) >> 	 d2! ^^ ↑8 := math muldiv ( Л_completedRound ^^ RoundsBase_ι_Round_ι_unused , Л_params ^^ RoundsBase_ι_InvestParams_ι_amount , Л_completedRound ^^ RoundsBase_ι_Round_ι_stake ) 
 	 ^^ set $ Л_params >> 
 
 } ( newLock $ Л_withdrawalLock (! newLock get () >> 	 
 ( $ ?!= $ ) { . get ) { { ↑8 { . transfer { { $ { , $ { { , $ { { ) >> 
 >> 
 } >> 
 Ife ↑9 DePoolContract_ι_m_poolClosed { d0! += $ ; if newVesting . () { newVesting get ( ^^ . transfer newVesting ^^ ( ) ↑8 RoundsBase_ι_InvestParams_ι_amount $ xBoolFalse $ xInt1 >> 
 
 } 
 
 ( newLock hasValue ( { ) newLock ^^ ( ) ↑8 RoundsBase_ι_InvestParams_ι_owner transfer ( ^^ get ) ^^ RoundsBase_ι_InvestParams_ι_amount , xBoolFalse , xInt1 ) 
 	 } >> 
 } else { Ift ( . hasValue ) { { newVesting . { { () { { ↑8 { ?== $ { { ) newVesting { { reset ( { } >> Ift ( . hasValue ) { { newLock . { { () { { ↑8 { ?== $ { { ) newLock { { reset ( { } >> Л_attachedValue += xInt1 ; 	 
 ( ! Л_participant . ) { Л_attachedValue += Л_newStake ; Л_newStake := xInt0 ; ( $ , $ ) { { ( $ Л_round0 , { Л_participant { { $ { , $ Л_newStake , { { , newLock { } >> } >> ParticipantBase_Ф__setOrDeleteParticipant (! Л_addr , Л_participant !) 
 	 IParticipant ( Л_addr ) DePool_Ф_onRoundComplete { : $ , bounce $ xBoolFalse } 
 $ Л_completedRound ↑8 RoundsBase_ι_Round_ι_id $ Л_reward $ Л_stakes ↑8 RoundsBase_ι_StakeValue_ι_ordinary $ Л_stakes vesting *) hasValue ( && $ ^^ vesting get ( ^^ isActive? Л_stakes ^^ . get ) ^^ RoundsBase_ι_InvestParams_ι_amount : xInt0 , Л_stakes ^^ . hasValue ) && Л_stakes ^^ . get ) ^^ $ Л_stakes lock . () ↑8 RoundsBase_ι_InvestParams_ι_amount $ xInt0 $ Л_participant reinvest , Л_completedRound . RoundsBase_ι_Round_ι_completionReason ) 
 	 $ Л_round0 
 	 } >> . 
 

(* function _returnOrReinvest ( Round round , uint8 chunkSize 
 	 	 ) private returns ( Round ) { tvm_accept ( ) ; Round round0 = m_rounds 
 	 	 . fetch ( m_roundQty - 1 ) . get ( ) ; mapping ( address => StakeValue 
 	 	 ) stakes = round . stakes ; uint sentMsgs = 0 ; while ( ! stakes . empty 
 	 	 ( ) && sentMsgs < chunkSize ) { sentMsgs + + ; ( address addr , StakeValue 
 	 	 stake ) = stakes . delMin ( ) ; round0 = _returnOrReinvestForParticipant 
 	 	 ( round , round0 , addr , stake ) ; } m_rounds [ m_roundQty - 1 ] = round0 
 	 	 ; round . stakes = stakes ; if ( stakes . empty ( ) ) { round . step = RoundStep 
 	 	 . Completed ; this . ticktock { value : VALUE_FOR_SELF_CALL , bounce 
 	 	 : false } ( ) ; } return round ; } *)
Definition DePoolContract_Ф__returnOrReinvest ( Л_round : RoundsBase_ι_Round )( Л_chunkSize : XInteger8 ) : LedgerT ( XErrorValue RoundsBase_ι_Round XInteger ) := 
 tvm_accept () >> 
 	 d0! Л_round0 :=  ^^ fetch (  !- $ xInt1 ) ^^ get ( ) >> 
 	 d1! RoundsBase_ι_Round_ι_stakes := $ Л_round ^^ RoundsBase_ι_Round_ι_stakes ; 
 	 d0! Л_sentMsgs := $ xInt0 ; 
 	 while ( ! empty () && $ Л_sentMsgs ?< $ Л_chunkSize ) { $ Л_sentMsgs ++ ; 
 	 {( $ Л_addr , Л_stake delMin ) >> 	 d0! := )} := DePoolContract_Ф__returnOrReinvestForParticipant (! $ Л_round , $ Л_round0 , $ Л_addr , $ Л_stake !) ; 
 	 
  [  !- $ xInt1 $ Л_round0 ; 
 	 d2! Л_round ^^ RoundsBase_ι_Round_ι_stakes := ↑8 RoundsBase_ι_Round_ι_stakes ; 
 	 
 Ift ( ↑8 RoundsBase_ι_Round_ι_stakes . empty () { ) { d2! Л_round ^^ RoundsBase_ι_Round_ι_step := RoundStep ^^ Completed ; 
 	 this ^^ DePoolContract_Ф_ticktock { value : DePoolContract_ι_VALUE_FOR_SELF_CALL , bounce : $ xBoolFalse 
 } 
 () >> 
 	 
 $ Л_round .
(* function calculateStakeWithAssert ( bool doSplit , uint64 
 	 	 wholeFee ) private returns ( uint64 , bool ) { uint64 div = doSplit 
 	 	 ? 2 : 1 ; uint64 stake = uint64 ( msg_value / div ) ; uint64 fee = wholeFee 
 	 	 / div ; if ( stake < m_minStake + fee ) { _sendError ( STATUS_STAKE_TOO_SMALL 
 	 	 , m_minStake * div + wholeFee ) ; return ( 0 , false ) ; } if ( m_poolClosed 
 	 	 ) { _sendError ( STATUS_DEPOOL_CLOSED , 0 ) ; return ( 0 , false ) 
 	 	 ; } return ( stake - fee , true ) ; } *)
Definition DePoolContract_Ф_calculateStakeWithAssert ( msg_value : XInteger ) ( Л_doSplit : XBool )( Л_wholeFee : XInteger64 ) : LedgerT ( XErrorValue ( XInteger64 # XBool ) XInteger ) := 
 d0! Л_div := $ Л_doSplit ? $ xInt2 : $ xInt1 ; 
 	 d0! Л_stake := $ msg_value !/ $ Л_div ; 
 	 d0! Л_fee := $ Л_wholeFee !/ $ Л_div ; 
 	 
 Ift ( $ Л_stake ?< ↑9 DePoolContract_ι_m_minStake !+ $ Л_fee ) { DePoolContract_Ф__sendError ( ↑2 CheckAndAcceptBase_ι_STATUS_STAKE_TOO_SMALL , ↑9 DePoolContract_ι_m_minStake !* $ Л_div !+ $ Л_wholeFee ) } >> return# ( $ xInt0 , $ xBoolFalse ) . 
 	 
 
 Ift ( ↑9 DePoolContract_ι_m_poolClosed ) { DePoolContract_Ф__sendError ( ↑2 CheckAndAcceptBase_ι_STATUS_DEPOOL_CLOSED , $ xInt0 ) } >> return# ( $ xInt0 , $ xBoolFalse ) . 
 	 
 return# ( $ Л_stake !- $ Л_fee , $ xBoolTrue ) .
(* function addOrdinaryStake ( bool reinvest ) { require ( msg_sender 
 	 	 ! = address ( 0 ) , Errors . IS_EXT_MSG ) ; DePoolLib . Participant 
 	 	 participant = m_participants [ msg_sender ] ; ( uint64 stake , 
 	 	 bool ok ) = calculateStakeWithAssert ( false , ADD_STAKE_FEE 
 	 	 ) ; if ( ! ok ) { return ; } Round round = m_rounds . fetch ( m_roundQty 
 	 	 - 1 ) . get ( ) ; optional ( InvestParams ) empty ; ( round , participant 
 	 	 ) = _addStakes ( round , participant , msg_sender , stake , empty 
 	 	 , empty ) ; m_rounds [ m_roundQty - 1 ] = round ; participant . reinvest 
 	 	 = reinvest ; _setOrDeleteParticipant ( msg_sender , participant 
 	 	 ) ; _sendAccept ( ADD_STAKE_FEE ) ; } *)
Definition DePoolContract_Ф_addOrdinaryStake ( msg_sender : XInteger ) ( Л_reinvest : XBool ) : LedgerT ( XErrorValue True XInteger ) := 
 Require {{ $ msg_sender ?!= xInt0 ,  Errors_ι_IS_EXT_MSG }} ; 
 	 d0! Л_participant :=  [ $ msg_sender ] ; 
 	 {( $ Л_stake , Л_ok )} := DePoolContract_Ф_calculateStakeWithAssert (! $ xBoolFalse , ↑9 DePoolContract_ι_ADD_STAKE_FEE !) ; 
 	 
 Ift ( ! $ Л_ok ) { return! ; } >> d0! Л_round :=  . fetch (  !- $ xInt1 ) { . { get { ( { ) } >> optional ( ↑8 RoundsBase_ι_InvestParams ) empty ; 
 	 {( $ Л_round , Л_participant )} := RoundsBase_Ф__addStakes (! $ Л_round , $ Л_participant , $ msg_sender , $ Л_stake , empty , empty !) ; 
 	  [  !- $ xInt1 $ Л_round ; 
 	 d2! Л_participant ^^ reinvest := $ Л_reinvest ; 
 	 ParticipantBase_Ф__setOrDeleteParticipant (! $ msg_sender , $ Л_participant !) ; 
 	 DePoolContract_Ф__sendAccept (! ↑9 DePoolContract_ι_ADD_STAKE_FEE !) ; . 
 

(* function removeOrdinaryStake ( uint64 withdrawValue ) { require 
 	 	 ( msg_sender ! = address ( 0 ) , Errors . IS_EXT_MSG ) ; if ( msg_value 
 	 	 < REMOVE_ORDINARY_STAKE_FEE ) { return _sendError ( STATUS_MSG_VAL_TOO_SMALL 
 	 	 , REMOVE_ORDINARY_STAKE_FEE ) ; } if ( m_poolClosed ) { return 
 	 	 _sendError ( STATUS_DEPOOL_CLOSED , 0 ) ; } optional ( DePoolLib 
 	 	 . Participant ) optParticipant = m_participants . fetch ( msg_sender 
 	 	 ) ; if ( ! optParticipant . hasValue ( ) ) { return _sendError ( STATUS_NO_PARTICIPANT 
 	 	 , 0 ) ; } DePoolLib . Participant participant = optParticipant 
 	 	 . get ( ) ; uint64 removedPoolingStake ; ( removedPoolingStake 
 	 	 , participant ) = withdrawStakeInPoolingRound ( participant 
 	 	 , msg_sender , withdrawValue , m_minStake ) ; _setOrDeleteParticipant 
 	 	 ( msg_sender , participant ) ; msg_sender . transfer ( removedPoolingStake 
 	 	 , false , 1 ) ; } *)
Definition DePoolContract_Ф_removeOrdinaryStake ( msg_value : XInteger ) ( msg_sender : XInteger ) ( Л_withdrawValue : XInteger64 ) : LedgerT ( XErrorValue True XInteger ) := 
 Require {{ $ msg_sender ?!= xInt0 ,  Errors_ι_IS_EXT_MSG }} ; 
 	 
 Ift ( $ msg_value ?< ↑9 DePoolContract_ι_REMOVE_ORDINARY_STAKE_FEE ) { DePoolContract_Ф__sendError ( ↑2 CheckAndAcceptBase_ι_STATUS_MSG_VAL_TOO_SMALL , ↑9 DePoolContract_ι_REMOVE_ORDINARY_STAKE_FEE ) } >> 
 } >> 
 
 Ift ( ↑9 DePoolContract_ι_m_poolClosed ) { return! DePoolContract_Ф__sendError ( ↑2 CheckAndAcceptBase_ι_STATUS_DEPOOL_CLOSED , $ xInt0 ) } >> 
 } >> 
 optional (  DePoolLib_ι_DePoolHelper_ι_Participant )  ^^ fetch ( $ msg_sender ) . 
 	 
 Ift ( ! optParticipant . hasValue () { ) { DePoolContract_Ф__sendError (! ↑2 CheckAndAcceptBase_ι_STATUS_NO_PARTICIPANT , $ xInt0 !) . 
 	 
 d0! Л_participant := optParticipant ^^ get ( ) >> 
 	 {( $ Л_removedPoolingStake , Л_participant )} := RoundsBase_Ф_withdrawStakeInPoolingRound (! $ Л_participant , $ msg_sender , $ Л_withdrawValue , ↑9 DePoolContract_ι_m_minStake !) ; 
 	 ParticipantBase_Ф__setOrDeleteParticipant (! $ msg_sender , $ Л_participant !) ; 
 	 $ msg_sender ^^ transfer {( $ Л_removedPoolingStake , xBoolFalse , xInt1 ) 
 	 } >> . 
 

(* function addVestingStake ( address beneficiary , uint32 withdrawalPeriod 
 	 	 , uint32 totalPeriod ) public { addVestingOrLock ( beneficiary 
 	 	 , withdrawalPeriod , totalPeriod , true ) ; } *)
Definition DePoolContract_Ф_addVestingStake ( Л_beneficiary : XAddress )( Л_withdrawalPeriod : XInteger32 )( Л_totalPeriod : XInteger32 ) : LedgerT ( XErrorValue True XInteger ) := 
 DePoolContract_Ф_addVestingOrLock (! $ Л_beneficiary , $ Л_withdrawalPeriod , $ Л_totalPeriod , $ xBoolTrue !) ; . 
 

(* function addLockStake ( address beneficiary , uint32 withdrawalPeriod 
 	 	 , uint32 totalPeriod ) public { addVestingOrLock ( beneficiary 
 	 	 , withdrawalPeriod , totalPeriod , false ) ; } *)
Definition DePoolContract_Ф_addLockStake ( Л_beneficiary : XAddress )( Л_withdrawalPeriod : XInteger32 )( Л_totalPeriod : XInteger32 ) : LedgerT ( XErrorValue True XInteger ) := 
 DePoolContract_Ф_addVestingOrLock (! $ Л_beneficiary , $ Л_withdrawalPeriod , $ Л_totalPeriod , $ xBoolFalse !) ; . 
 

(* function addVestingOrLock ( address beneficiary , uint32 
 	 	 withdrawalPeriod , uint32 totalPeriod , bool isVesting ) private 
 	 	 { require ( beneficiary . isStdAddrWithoutAnyCast ( ) , Errors 
 	 	 . INVALID_ADDRESS ) ; if ( beneficiary == address ( 0 ) ) { beneficiary 
 	 	 = msg_sender ; } ( uint64 halfStake , bool ok ) = calculateStakeWithAssert 
 	 	 ( true , ADD_VESTING_OR_LOCK_FEE ) ; if ( ! ok ) { return ; } if ( withdrawalPeriod 
 	 	 > totalPeriod ) { return _sendError ( STATUS_WITHDRAWAL_PERIOD_GREATER_TOTAL_PERIOD 
 	 	 , 0 ) ; } if ( totalPeriod >= 18 * ( 365 days ) ) { return _sendError ( 
 	 	 STATUS_TOTAL_PERIOD_MORE_18YEARS , 0 ) ; } if ( withdrawalPeriod 
 	 	 == 0 ) { return _sendError ( STATUS_WITHDRAWAL_PERIOD_IS_ZERO 
 	 	 , 0 ) ; } if ( totalPeriod % withdrawalPeriod ! = 0 ) { return _sendError 
 	 	 ( STATUS_TOTAL_PERIOD_IS_NOT_DIVED_BY_WITHDRAWAL_PERIOD 
 	 	 , 0 ) ; } DePoolLib . Participant participant = m_participants 
 	 	 [ beneficiary ] ; if ( isVesting ) { if ( participant . haveVesting 
 	 	 ) { return _sendError ( STATUS_PARTICIPANT_HAVE_ALREADY_VESTING 
 	 	 , 0 ) ; } } else { if ( participant . haveLock ) { return _sendError 
 	 	 ( STATUS_PARTICIPANT_HAVE_ALREADY_LOCK , 0 ) ; } } uint64 withdrawalValue 
 	 	 = math . muldiv ( halfStake , withdrawalPeriod , totalPeriod ) 
 	 	 ; if ( withdrawalValue == 0 ) { return _sendError ( STATUS_PERIOD_PAYMENT_IS_ZERO 
 	 	 , 0 ) ; } InvestParams vestingOrLock = InvestParams ( { isActive 
 	 	 : false , amount : halfStake , lastWithdrawalTime : uint64 ( now 
 	 	 ) , withdrawalPeriod : withdrawalPeriod , withdrawalValue : 
 	 	 withdrawalValue , owner : msg_sender } ) ; for ( uint64 i = 1 ; i <= 
 	 	 2 ; + + i ) { uint64 round_id = m_roundQty - i ; Round round = m_rounds 
 	 	 . fetch ( round_id ) . get ( ) ; vestingOrLock . isActive = round . 
 	 	 step == RoundStep . WaitingValidatorRequest || i == 1 ; optional 
 	 	 ( InvestParams ) v ; optional ( InvestParams ) l ; if ( isVesting 
 	 	 ) { v . set ( vestingOrLock ) ; } else { l . set ( vestingOrLock ) ; } ( 
 	 	 round , participant ) = _addStakes ( round , participant , beneficiary 
 	 	 , 0 , v , l ) ; m_rounds [ round_id ] = round ; } _setOrDeleteParticipant 
 	 	 ( beneficiary , participant ) ; _sendAccept ( ADD_STAKE_FEE ) 
 	 	 ; } *)
Definition DePoolContract_Ф_addVestingOrLock ( msg_sender : XInteger ) ( Л_beneficiary : XAddress )( Л_withdrawalPeriod : XInteger32 )( Л_totalPeriod : XInteger32 )( Л_isVesting : XBool ) : LedgerT ( XErrorValue True XInteger ) := 
 Require {{ $ Л_beneficiary ^^ isStdAddrWithoutAnyCast ( ) ,  Errors_ι_INVALID_ADDRESS }} ; 
 	 
 Ift ( $ Л_beneficiary ?== address(0) ) { d0! Л_beneficiary := $ msg_sender ; } {( $ Л_halfStake , Л_ok ) DePoolContract_Ф_calculateStakeWithAssert { { $ xBoolTrue { { ↑9 { ) >> 
 ( ! Л_ok ) return! ; >> if $ Л_withdrawalPeriod $ Л_totalPeriod { return! (! ↑2 , $ !) ; 	 
 >> 
 Ift ( Л_totalPeriod ?>= xInt18 !* $ Л_days { ) return! )} := DePoolContract_Ф__sendError (! ↑2 CheckAndAcceptBase_ι_STATUS_TOTAL_PERIOD_MORE_18YEARS , $ xInt0 !) ; 
 	 
 
 Ift ( $ Л_withdrawalPeriod ?== $ xInt0 ) { DePoolContract_Ф__sendError ( ↑2 CheckAndAcceptBase_ι_STATUS_WITHDRAWAL_PERIOD_IS_ZERO , $ xInt0 ) } >> 
 } >> 
 
 Ift ( $ Л_totalPeriod $ Л_% $ Л_withdrawalPeriod ?!= $ xInt0 ) { return! DePoolContract_Ф__sendError ( ↑2 CheckAndAcceptBase_ι_STATUS_TOTAL_PERIOD_IS_NOT_DIVED_BY_WITHDRAWAL_PERIOD , $ xInt0 ) } >> 
 } >> 
 d0! Л_participant :=  [ $ Л_beneficiary ] . 
 	 
 Ife ( $ Л_isVesting ) { if ( $ Л_participant . haveVesting ) { DePoolContract_Ф__sendError (! ↑2 CheckAndAcceptBase_ι_STATUS_PARTICIPANT_HAVE_ALREADY_VESTING , $ xInt0 !) . 
 	 
 
 } 
 else { 
 Ift ( $ Л_participant . haveLock ) { DePoolContract_Ф__sendError ( ↑2 CheckAndAcceptBase_ι_STATUS_PARTICIPANT_HAVE_ALREADY_LOCK , $ xInt0 ) } >> 
 } >> 
 
 } >> 
 d0! Л_withdrawalValue := math ^^ muldiv ( $ Л_halfStake , $ Л_withdrawalPeriod , $ Л_totalPeriod ) . 
 	 
 Ift ( $ Л_withdrawalValue ?== $ xInt0 ) { DePoolContract_Ф__sendError ( ↑2 CheckAndAcceptBase_ι_STATUS_PERIOD_PAYMENT_IS_ZERO , $ xInt0 ) } >> 
 } >> 
 d0! Л_vestingOrLock := ↑8 RoundsBase_ι_InvestParams ( { ↑8 RoundsBase_ι_InvestParams_ι_isActive : $ xBoolFalse , ↑8 RoundsBase_ι_InvestParams_ι_amount : $ Л_halfStake , ↑8 RoundsBase_ι_InvestParams_ι_lastWithdrawalTime : tvm_now , Л_withdrawalPeriod : $ Л_withdrawalPeriod , Л_withdrawalValue : $ Л_withdrawalValue , ↑8 RoundsBase_ι_InvestParams_ι_owner : $ msg_sender 
 } >> 
 ) . 
 	 for ( d0! Л_i := $ xInt1 ; 
 	 $ Л_i ?<= $ xInt2 ; 
 	 ++ $ Л_i ) { d0! Л_round_id :=  !- $ Л_i ; 
 	 d0! Л_round :=  ^^ fetch ( $ Л_round_id ) ^^ get ( ) >> 
 	 d2! Л_vestingOrLock ^^ RoundsBase_ι_InvestParams_ι_isActive := $ Л_round ^^ RoundsBase_ι_Round_ι_step ?== RoundStep ^^ WaitingValidatorRequest || $ Л_i ?== $ xInt1 ; 
 	 optional ( ↑8 RoundsBase_ι_InvestParams ) v ; 
 	 optional ( ↑8 RoundsBase_ι_InvestParams ) l ; 
 	 
 Ife ( $ Л_isVesting ) { v . set ( $ Л_vestingOrLock ) } >> 
 } 
 else { l ^^ set ( $ Л_vestingOrLock ) >> 
 	 
 } 
 {( $ Л_round , Л_participant )} := RoundsBase_Ф__addStakes (! $ Л_round , $ Л_participant , $ Л_beneficiary , $ xInt0 , v , l !) ; 
 	 d4!  [ Л_round_id ] := $ Л_round ; 
 	 
 ParticipantBase_Ф__setOrDeleteParticipant (! $ Л_beneficiary , $ Л_participant !) ; 
 	 DePoolContract_Ф__sendAccept (! ↑9 DePoolContract_ι_ADD_STAKE_FEE !) ; . 
 

(* function withdrawPartAfterCompleting ( uint64 withdrawValue 
 	 	 ) { require ( msg_sender ! = address ( 0 ) , Errors . IS_EXT_MSG ) ; 
 	 	 if ( msg_value < WITHDRAW_PART_AFTER_COMPLETING_FEE ) { return 
 	 	 _sendError ( STATUS_MSG_VAL_TOO_SMALL , WITHDRAW_PART_AFTER_COMPLETING_FEE 
 	 	 ) ; } if ( m_poolClosed ) { return _sendError ( STATUS_DEPOOL_CLOSED 
 	 	 , 0 ) ; } optional ( DePoolLib . Participant ) optParticipant = m_participants 
 	 	 . fetch ( msg_sender ) ; if ( ! optParticipant . hasValue ( ) ) { return 
 	 	 _sendError ( STATUS_NO_PARTICIPANT , 0 ) ; } DePoolLib . Participant 
 	 	 participant = optParticipant . get ( ) ; participant . withdrawValue 
 	 	 = withdrawValue ; _setOrDeleteParticipant ( msg_sender , participant 
 	 	 ) ; _sendAccept ( WITHDRAW_PART_AFTER_COMPLETING_FEE ) ; } *) 
 	 	
Definition DePoolContract_Ф_withdrawPartAfterCompleting ( msg_value : XInteger ) ( msg_sender : XInteger ) ( Л_withdrawValue : XInteger64 ) : LedgerT ( XErrorValue True XInteger ) := 
 Require {{ $ msg_sender ?!= xInt0 ,  Errors_ι_IS_EXT_MSG }} ; 
 	 
 Ift ( $ msg_value ?< ↑9 DePoolContract_ι_WITHDRAW_PART_AFTER_COMPLETING_FEE ) { DePoolContract_Ф__sendError ( ↑2 CheckAndAcceptBase_ι_STATUS_MSG_VAL_TOO_SMALL , ↑9 DePoolContract_ι_WITHDRAW_PART_AFTER_COMPLETING_FEE ) } >> 
 } >> 
 
 Ift ( ↑9 DePoolContract_ι_m_poolClosed ) { return! DePoolContract_Ф__sendError ( ↑2 CheckAndAcceptBase_ι_STATUS_DEPOOL_CLOSED , $ xInt0 ) } >> 
 } >> 
 optional (  DePoolLib_ι_DePoolHelper_ι_Participant )  ^^ fetch ( $ msg_sender ) . 
 	 
 Ift ( ! optParticipant . hasValue () { ) { DePoolContract_Ф__sendError (! ↑2 CheckAndAcceptBase_ι_STATUS_NO_PARTICIPANT , $ xInt0 !) . 
 	 
 d0! Л_participant := optParticipant ^^ get ( ) >> 
 	 d2! Л_participant ^^ withdrawValue := $ Л_withdrawValue ; 
 	 ParticipantBase_Ф__setOrDeleteParticipant (! $ msg_sender , $ Л_participant !) ; 
 	 DePoolContract_Ф__sendAccept (! ↑9 DePoolContract_ι_WITHDRAW_PART_AFTER_COMPLETING_FEE !) ; . 
 

(* function withdrawAllAfterCompleting ( bool doWithdrawAll 
 	 	 ) { require ( msg_sender ! = address ( 0 ) , Errors . IS_EXT_MSG ) ; 
 	 	 if ( msg_value < WITHDRAW_ALL_AFTER_COMPLETING_FEE ) { return 
 	 	 _sendError ( STATUS_MSG_VAL_TOO_SMALL , WITHDRAW_ALL_AFTER_COMPLETING_FEE 
 	 	 ) ; } optional ( DePoolLib . Participant ) optParticipant = m_participants 
 	 	 . fetch ( msg_sender ) ; if ( ! optParticipant . hasValue ( ) ) { return 
 	 	 _sendError ( STATUS_NO_PARTICIPANT , 0 ) ; } DePoolLib . Participant 
 	 	 participant = optParticipant . get ( ) ; if ( m_poolClosed ) { return 
 	 	 _sendError ( STATUS_DEPOOL_CLOSED , 0 ) ; } participant . reinvest 
 	 	 = ! doWithdrawAll ; _setOrDeleteParticipant ( msg_sender , participant 
 	 	 ) ; _sendAccept ( WITHDRAW_ALL_AFTER_COMPLETING_FEE ) ; } *) 
 	 	
Definition DePoolContract_Ф_withdrawAllAfterCompleting ( msg_value : XInteger ) ( msg_sender : XInteger ) ( Л_doWithdrawAll : XBool ) : LedgerT ( XErrorValue True XInteger ) := 
 Require {{ $ msg_sender ?!= xInt0 ,  Errors_ι_IS_EXT_MSG }} ; 
 	 
 Ift ( $ msg_value ?< ↑9 DePoolContract_ι_WITHDRAW_ALL_AFTER_COMPLETING_FEE ) { DePoolContract_Ф__sendError ( ↑2 CheckAndAcceptBase_ι_STATUS_MSG_VAL_TOO_SMALL , ↑9 DePoolContract_ι_WITHDRAW_ALL_AFTER_COMPLETING_FEE ) } >> 
 } >> 
 optional (  DePoolLib_ι_DePoolHelper_ι_Participant )  ^^ fetch ( $ msg_sender ) . 
 	 
 Ift ( ! optParticipant . hasValue () { ) { DePoolContract_Ф__sendError (! ↑2 CheckAndAcceptBase_ι_STATUS_NO_PARTICIPANT , $ xInt0 !) . 
 	 
 d0! Л_participant := optParticipant ^^ get ( ) >> 
 	 
 Ift ( ↑9 DePoolContract_ι_m_poolClosed ) { DePoolContract_Ф__sendError ( ↑2 CheckAndAcceptBase_ι_STATUS_DEPOOL_CLOSED , $ xInt0 ) } >> 
 } >> 
 d2! Л_participant ^^ reinvest := ! $ Л_doWithdrawAll . 
 	 ParticipantBase_Ф__setOrDeleteParticipant (! $ msg_sender , $ Л_participant !) ; 
 	 DePoolContract_Ф__sendAccept (! ↑9 DePoolContract_ι_WITHDRAW_ALL_AFTER_COMPLETING_FEE !) ; . 
 

(* function transferStake ( address dest , uint64 amount ) { require 
 	 	 ( msg_sender ! = address ( 0 ) , Errors . IS_EXT_MSG ) ; require ( dest 
 	 	 . isStdAddrWithoutAnyCast ( ) && ! dest . isStdZero ( ) , Errors 
 	 	 . INVALID_ADDRESS ) ; address src = msg_sender ; if ( src == dest 
 	 	 ) { return _sendError ( STATUS_TRANSFER_SELF , 0 ) ; } optional 
 	 	 ( DePoolLib . Participant ) optSrcParticipant = m_participants 
 	 	 . fetch ( src ) ; if ( ! optSrcParticipant . hasValue ( ) ) { return 
 	 	 _sendError ( STATUS_NO_PARTICIPANT , 0 ) ; } DePoolLib . Participant 
 	 	 srcParticipant = optSrcParticipant . get ( ) ; if ( msg_value < 
 	 	 TRANSFER_STAKE_FEE ) { return _sendError ( STATUS_MSG_VAL_TOO_SMALL 
 	 	 , TRANSFER_STAKE_FEE ) ; } if ( m_poolClosed ) { return _sendError 
 	 	 ( STATUS_DEPOOL_CLOSED , 0 ) ; } if ( amount == 0 ) { amount = DePoolLib 
 	 	 . MAX_UINT64 ; } DePoolLib . Participant destParticipant = m_participants 
 	 	 [ dest ] ; uint64 totalSrcStake ; uint64 transferred ; mapping 
 	 	 ( uint64 => Round ) rounds = m_rounds ; optional ( uint64 , Round 
 	 	 ) pair = rounds . min ( ) ; while ( pair . hasValue ( ) && transferred 
 	 	 < amount ) { ( uint64 roundId , Round round ) = pair . get ( ) ; uint64 
 	 	 currentTransferred ; uint64 srcStake ; ( rounds [ roundId ] , currentTransferred 
 	 	 , srcStake , srcParticipant , destParticipant ) = transferStakeInOneRound 
 	 	 ( round , srcParticipant , destParticipant , src , dest , amount 
 	 	 - transferred , m_minStake ) ; transferred + = currentTransferred 
 	 	 ; totalSrcStake + = srcStake ; pair = rounds . next ( roundId ) ; } 
 	 	 if ( amount ! = DePoolLib . MAX_UINT64 ) { if ( totalSrcStake < amount 
 	 	 ) { return _sendError ( STATUS_TRANSFER_AMOUNT_IS_TOO_BIG 
 	 	 , 0 ) ; } if ( transferred < amount ) { return _sendError ( STATUS_REMAINING_STAKE_LESS_THAN_MINIMAL 
 	 	 , 0 ) ; } } m_rounds = rounds ; _setOrDeleteParticipant ( src , srcParticipant 
 	 	 ) ; _setOrDeleteParticipant ( dest , destParticipant ) ; IParticipant 
 	 	 ( dest ) . onTransfer { bounce : false } ( src , amount ) ; _sendAccept 
 	 	 ( TRANSFER_STAKE_FEE ) ; } *)
Definition DePoolContract_Ф_transferStake ( msg_sender : XInteger ) ( Л_dest : XAddress )( Л_amount : XInteger64 ) : LedgerT ( XErrorValue True XInteger ) := 
 Require {{ $ msg_sender ?!= xInt0 ,  Errors_ι_IS_EXT_MSG }} ; 
 	 Require {{ $ Л_dest ^^ isStdAddrWithoutAnyCast ( ) && ! $ Л_dest ^^ isStdZero ( ) ,  Errors_ι_INVALID_ADDRESS }} ; 
 	 d0! Л_src := $ msg_sender ; 
 	 
 Ift ( $ Л_src ?== $ Л_dest ) { DePoolContract_Ф__sendError ( ↑2 CheckAndAcceptBase_ι_STATUS_TRANSFER_SELF , $ xInt0 ) } >> 
 } >> 
 optional (  DePoolLib_ι_DePoolHelper_ι_Participant )  ^^ fetch ( $ Л_src ) . 
 	 
 Ift ( ! optSrcParticipant . hasValue () { ) { DePoolContract_Ф__sendError (! ↑2 CheckAndAcceptBase_ι_STATUS_NO_PARTICIPANT , $ xInt0 !) . 
 	 
 d0! Л_srcParticipant := optSrcParticipant ^^ get ( ) >> 
 	 
 Ift ( $ msg_value ?< ↑9 DePoolContract_ι_TRANSFER_STAKE_FEE ) { DePoolContract_Ф__sendError ( ↑2 CheckAndAcceptBase_ι_STATUS_MSG_VAL_TOO_SMALL , ↑9 DePoolContract_ι_TRANSFER_STAKE_FEE ) } >> 
 } >> 
 
 Ift ( ↑9 DePoolContract_ι_m_poolClosed ) { return! DePoolContract_Ф__sendError ( ↑2 CheckAndAcceptBase_ι_STATUS_DEPOOL_CLOSED , $ xInt0 ) } >> 
 } >> 
 
 Ift ( $ Л_amount ?== $ xInt0 ) { d0! Л_amount :=  DePoolLib_ι_MAX_UINT64 . } >> d0! Л_destParticipant :=  [ $ Л_dest ] ;  ; optional ( uint64 , ↑8 RoundsBase_ι_Round ) { pair { rounds { . { min { ( { ) } >> while ( pair ^^ hasValue ( ) && $ Л_transferred ?< $ Л_amount ) { {( $ Л_roundId , Л_round pair get ( >> 
 ( rounds $ Л_roundId , $ , $ , $ , $ RoundsBase_Ф_transferStakeInOneRound (! Л_round , Л_srcParticipant , Л_destParticipant , Л_src , Л_dest , Л_amount !- Л_transferred , DePoolContract_ι_m_minStake !) 
 	 Л_transferred += Л_currentTransferred ; 	 d0! += $ ; 
 rounds ^^ ( $ ) >> 	 
 >> 
 Ift ( Л_amount ?!= DePoolLib_ι_MAX_UINT64 ) if ( Л_totalSrcStake ?< Л_amount ) return! )} := DePoolContract_Ф__sendError (! ↑2 CheckAndAcceptBase_ι_STATUS_TRANSFER_AMOUNT_IS_TOO_BIG , $ xInt0 !) ; 
 	 
 
 Ift ( $ Л_transferred ?< $ Л_amount ) { DePoolContract_Ф__sendError ( ↑2 CheckAndAcceptBase_ι_STATUS_REMAINING_STAKE_LESS_THAN_MINIMAL , $ xInt0 ) } >> 
 } >> 
 
 } >> 
 rounds . 
 	 ParticipantBase_Ф__setOrDeleteParticipant (! $ Л_src , $ Л_srcParticipant !) ; 
 	 ParticipantBase_Ф__setOrDeleteParticipant (! $ Л_dest , $ Л_destParticipant !) ; 
 	 (* IParticipant ( $ Л_dest ) ^^ DePool_Ф_onTransfer { bounce : $ xBoolFalse 
 } 
 ( $ Л_src , $ Л_amount ) *) 
 	 DePoolContract_Ф__sendAccept (! ↑9 DePoolContract_ι_TRANSFER_STAKE_FEE !) ; . 
 

(* function participateInElections ( uint64 queryId , uint256 
 	 	 validatorKey , uint32 stakeAt , uint32 maxFactor , uint256 adnlAddr 
 	 	 , bytes signature ) public functionID ( 0x4E73744B { require ( 
 	 	 msg_sender == m_validatorWallet , Errors . IS_NOT_VALIDATOR 
 	 	 ) ; require ( ! m_poolClosed , Errors . DEPOOL_IS_CLOSED ) ; tvm_accept 
 	 	 ( ) ; Round round = m_rounds . fetch ( m_roundQty - 2 ) . get ( ) ; require 
 	 	 ( round . step == RoundStep . WaitingValidatorRequest , Errors 
 	 	 . NO_ELECTION_ROUND ) ; require ( stakeAt == round . supposedElectedAt 
 	 	 , Errors . INVALID_ELECTION_ID ) ; round . validatorRequest = 
 	 	 DePoolLib . Request ( queryId , validatorKey , stakeAt , maxFactor 
 	 	 , adnlAddr , signature ) ; _sendElectionRequest ( round . proxy 
 	 	 , round . id , round . stake , round . validatorRequest , round . elector 
 	 	 ) ; round . step = RoundStep . WaitingIfStakeAccepted ; m_rounds 
 	 	 [ m_roundQty - 2 ] = round ; _returnChange ( ) ; } *)
Definition DePoolContract_Ф_participateInElections ( msg_sender : XInteger ) ( Л_queryId : XInteger64 )( Л_validatorKey : XInteger256 )( Л_stakeAt : XInteger32 )( Л_maxFactor : XInteger32 )( Л_adnlAddr : XInteger256 )( Л_signature : XInteger8 ) : LedgerT ( XErrorValue True XInteger ) := 
 Require {{ $ msg_sender ?== ↑3 ValidatorBase_ι_m_validatorWallet ,  Errors_ι_IS_NOT_VALIDATOR }} ; 
 	 Require {{ ! ↑9 DePoolContract_ι_m_poolClosed ,  Errors_ι_DEPOOL_IS_CLOSED }} ; 
 	 tvm_accept () >> 
 	 d0! Л_round :=  ^^ fetch (  !- $ xInt2 ) ^^ get ( ) >> 
 	 Require {{ $ Л_round ^^ RoundsBase_ι_Round_ι_step ?== RoundStep ^^ WaitingValidatorRequest ,  Errors_ι_NO_ELECTION_ROUND }} ; 
 	 Require {{ $ Л_stakeAt ?== $ Л_round ^^ RoundsBase_ι_Round_ι_supposedElectedAt ,  Errors_ι_INVALID_ELECTION_ID }} ; 
 	 d2! Л_round ^^ validatorRequest :=  DePoolLib_ι_DePoolHelper_ι_Request {( $ Л_queryId , Л_validatorKey , Л_stakeAt , Л_maxFactor , Л_adnlAddr , Л_signature ) 
 	 (! $ . ↑8 , $ . ↑8 , $ . ↑8 , $ . validatorRequest $ Л_round ↑8 RoundsBase_ι_Round_ι_elector ; 
 d2! Л_round ↑8 RoundsBase_ι_Round_ι_step RoundStep ^^ ; 
  [ !- $ $ Л_round 
 	 () ; 	 
 >> . 
 

(* function generateRound ( ) internal returns ( Round ) { DePoolLib 
 	 	 . Request req ; Round r = Round ( { id : m_roundQty , supposedElectedAt 
 	 	 : 0 , unfreeze : DePoolLib . MAX_TIME , step : RoundStep . Pooling 
 	 	 , completionReason : CompletionReason . Undefined , participantQty 
 	 	 : 0 , stake : 0 , rewards : 0 , unused : 0 , validatorRequest : req , proxy 
 	 	 : getProxy ( m_roundQty ) , start : uint32 ( now ) , end : 0 , elector 
 	 	 : address ( 0 ) , vsetHashInElectionPhase : 0 } ) ; + + m_roundQty 
 	 	 ; return r ; } *)
Definition DePoolContract_Ф_generateRound : LedgerT ( XErrorValue RoundsBase_ι_Round XInteger ) := 
 d0! Л_r := ↑8 RoundsBase_ι_Round ( { Л_id :  , Л_supposedElectedAt : $ xInt0 , Л_unfreeze : DePoolLib_ι_MAX_TIME , Л_step : RoundStep ^^ Pooling , Л_completionReason : CompletionReason ^^ Undefined , Л_participantQty : $ xInt0 , Л_stake : $ xInt0 , Л_rewards : $ xInt0 , Л_unused : $ xInt0 , Л_validatorRequest : $ Л_req , Л_proxy : ProxyBase_Ф_getProxy (!  !) , Л_start : tvm_now , Л_end : $ xInt0 , Л_elector : xInt0 , Л_vsetHashInElectionPhase : $ xInt0 
 ) >> 
 	 ++  ; 
 	 $ Л_r .
(* function updateRound2 ( Round round2 , uint256 prevValidatorHash 
 	 	 , uint256 curValidatorHash , uint32 validationStart , uint32 
 	 	 stakeHeldFor ) private returns ( Round ) { if ( round2 . step == RoundStep 
 	 	 . Completing ) { this . completeRoundWithChunk { bounce : false 
 	 	 } ( round2 . id , 1 ) ; } if ( round2 . step == RoundStep . WaitingValidatorRequest 
 	 	 ) { round2 . step = RoundStep . WaitingUnfreeze ; if ( round2 . completionReason 
 	 	 == CompletionReason . Undefined ) { round2 . completionReason 
 	 	 = CompletionReason . NoValidatorRequest ; } round2 . unfreeze 
 	 	 = 0 ; } if ( round2 . vsetHashInElectionPhase ! = curValidatorHash 
 	 	 && round2 . vsetHashInElectionPhase ! = prevValidatorHash && 
 	 	 round2 . unfreeze == DePoolLib . MAX_TIME ) { round2 . unfreeze 
 	 	 = validationStart + stakeHeldFor ; } if ( now >= uint ( round2 . unfreeze 
 	 	 ) + DePoolLib . ELECTOR_UNFREEZE_LAG ) { if ( round2 . step == RoundStep 
 	 	 . WaitingUnfreeze && round2 . completionReason ! = CompletionReason 
 	 	 . Undefined ) { if ( round2 . participantQty == 0 ) { round2 . step 
 	 	 = RoundStep . Completed ; round2 . end = uint32 ( now ) ; emit RoundCompleted 
 	 	 ( toTruncatedRound ( round2 ) ) ; } else { round2 = startRoundCompleting 
 	 	 ( round2 , round2 . completionReason ) ; } } else if ( round2 . step 
 	 	 < RoundStep . WaitingReward ) { round2 . step = RoundStep . WaitingReward 
 	 	 ; _recoverStake ( round2 . proxy , round2 . id , round2 . elector 
 	 	 ) ; } } return round2 ; } *)
Definition DePoolContract_Ф_updateRound2 ( Л_round2 : RoundsBase_ι_Round )( Л_prevValidatorHash : XInteger256 )( Л_curValidatorHash : XInteger256 )( Л_validationStart : XInteger32 )( Л_stakeHeldFor : XInteger32 ) : LedgerT ( XErrorValue RoundsBase_ι_Round XInteger ) := 
 
 Ift ( $ Л_round2 . ↑8 RoundsBase_ι_Round_ι_step ?== RoundStep . Completing ) { this . DePoolContract_Ф_completeRoundWithChunk { bounce : $ xBoolFalse } ( $ Л_round2 . ↑8 RoundsBase_ι_Round_ι_id , $ xInt1 ) } >> 
 
 Ift ( $ Л_round2 . ↑8 RoundsBase_ι_Round_ι_step ?== RoundStep . WaitingValidatorRequest ) { $ Л_round2 . d1! RoundsBase_ι_Round_ι_step := RoundStep . WaitingUnfreeze ; if ( $ Л_round2 . ↑8 RoundsBase_ι_Round_ι_completionReason ?== CompletionReason . Undefined ) { d2! Л_round2 ^^ RoundsBase_ι_Round_ι_completionReason := CompletionReason ^^ NoValidatorRequest ; 
 	 
 d2! Л_round2 ^^ RoundsBase_ι_Round_ι_unfreeze := $ xInt0 ; 
 	 
 
 Ift ( $ Л_round2 . ↑8 RoundsBase_ι_Round_ι_vsetHashInElectionPhase ?!= $ Л_curValidatorHash && $ Л_round2 . ↑8 RoundsBase_ι_Round_ι_vsetHashInElectionPhase ?!= $ Л_prevValidatorHash && $ Л_round2 . ↑8 RoundsBase_ι_Round_ι_unfreeze ?==  DePoolLib_ι_MAX_TIME ) { $ Л_round2 . d1! RoundsBase_ι_Round_ι_unfreeze := $ Л_validationStart !+ $ Л_stakeHeldFor ; } >> if ( tvm_now ?>= uint ( $ Л_round2 . ↑8 RoundsBase_ι_Round_ι_unfreeze ) !+  DePoolLib_ι_ELECTOR_UNFREEZE_LAG ) { 
 Ife ( $ Л_round2 . ↑8 RoundsBase_ι_Round_ι_step ?== RoundStep . WaitingUnfreeze && $ Л_round2 . ↑8 RoundsBase_ι_Round_ι_completionReason ?!= CompletionReason . Undefined ) { if ( $ Л_round2 . ↑8 RoundsBase_ι_Round_ι_participantQty ?== $ xInt0 ) { d2! Л_round2 ^^ RoundsBase_ι_Round_ι_step := RoundStep ^^ Completed ; 
 	 d2! Л_round2 ^^ RoundsBase_ι_Round_ι_end := tvm_now ; 
 	 emit $ Л_RoundCompleted ( RoundsBase_Ф_toTruncatedRound (! $ Л_round2 !) ) >> 
 	 
 } 
 else { d0! Л_round2 := DePoolContract_Ф_startRoundCompleting (! $ Л_round2 , $ Л_round2 . ↑8 RoundsBase_ι_Round_ι_completionReason !) ; 
 	 
 
 } 
 else { if { ( { $ Л_round2 { . { ↑8 RoundsBase_ι_Round_ι_step { ?< { RoundStep { . { WaitingReward { ) { d2! Л_round2 ^^ RoundsBase_ι_Round_ι_step := RoundStep ^^ WaitingReward ; 
 	 ProxyBase_Ф__recoverStake (! $ Л_round2 . ↑8 RoundsBase_ι_Round_ι_proxy , $ Л_round2 . ↑8 RoundsBase_ι_Round_ι_id , $ Л_round2 . ↑8 RoundsBase_ι_Round_ι_elector !) ; 
 	 
 
 $ Л_round2 .
(* function updateRounds ( ) private { ( , uint32 electionsStartBefore 
 	 	 , , uint32 stakeHeldFor ) = roundTimeParams ( ) ; ( uint256 curValidatorHash 
 	 	 , uint32 validationStart , uint32 validationEnd ) = getCurValidatorData 
 	 	 ( ) ; uint256 prevValidatorHash = getPrevValidatorHash ( ) ; bool 
 	 	 areElectionsStarted = now >= validationEnd - electionsStartBefore 
 	 	 ; Round round0 = m_rounds . fetch ( m_roundQty - 1 ) . get ( ) ; Round 
 	 	 round1 = m_rounds . fetch ( m_roundQty - 2 ) . get ( ) ; Round round2 
 	 	 = m_rounds . fetch ( m_roundQty - 3 ) . get ( ) ; round2 = updateRound2 
 	 	 ( round2 , prevValidatorHash , curValidatorHash , validationStart 
 	 	 , stakeHeldFor ) ; if ( areElectionsStarted && round1 . vsetHashInElectionPhase 
 	 	 ! = curValidatorHash && round2 . step == RoundStep . Completed 
 	 	 ) { delete m_rounds [ round2 . id ] ; round2 = round1 ; round1 = round0 
 	 	 ; round0 = generateRound ( ) ; round2 = updateRound2 ( round2 , prevValidatorHash 
 	 	 , curValidatorHash , validationStart , stakeHeldFor ) ; round1 
 	 	 . supposedElectedAt = validationEnd ; round1 . elector = getElector 
 	 	 ( ) ; round1 . vsetHashInElectionPhase = curValidatorHash ; bool 
 	 	 isTotalStakeOk = round1 . stake >= m_minRoundStake ; bool isValidatorStake 
 	 	 = activeStakeSum ( round1 . stakes [ m_validatorWallet ] ) >= math 
 	 	 . muldiv ( m_minRoundStake , VALIDATOR_WALLET_MIN_STAKE , 100 
 	 	 ) ; if ( ! isTotalStakeOk || ! isValidatorStake ) { round1 . step 
 	 	 = RoundStep . WaitingUnfreeze ; round1 . completionReason = isTotalStakeOk 
 	 	 ? CompletionReason . ValidatorStakeIsTooSmall : CompletionReason 
 	 	 . TotalStakeIsTooSmall ; round1 . unfreeze = 0 ; } else { round1 
 	 	 . step = RoundStep . WaitingValidatorRequest ; emit stakeSigningRequested 
 	 	 ( round1 . supposedElectedAt , round1 . proxy ) ; } } if ( round1 . 
 	 	 step == RoundStep . WaitingValidationStart && round1 . vsetHashInElectionPhase 
 	 	 == prevValidatorHash ) { round1 . step = RoundStep . WaitingIfValidatorWinElections 
 	 	 ; _recoverStake ( round1 . proxy , round1 . id , round1 . elector 
 	 	 ) ; } m_rounds [ m_roundQty - 1 ] = round0 ; m_rounds [ m_roundQty 
 	 	 - 2 ] = round1 ; m_rounds [ m_roundQty - 3 ] = round2 ; } *)
Definition DePoolContract_Ф_updateRounds : LedgerT ( XErrorValue True XInteger ) := 
 ( , $ Л_electionsStartBefore , _ , $ Л_stakeHeldFor DebugDePool_Ф_roundTimeParams () ; 
 	 {( $ Л_curValidatorHash , Л_validationStart , Л_validationEnd )} := DebugDePool_Ф_getCurValidatorData () ; 
 	 d0! Л_prevValidatorHash := DebugDePool_Ф_getPrevValidatorHash () ; 
 	 d0! Л_areElectionsStarted := tvm_now ?>= $ Л_validationEnd !- $ Л_electionsStartBefore ; 
 	 d0! Л_round0 :=  ^^ fetch (  !- $ xInt1 ) ^^ get ( ) >> 
 	 d0! Л_round1 :=  ^^ fetch (  !- $ xInt2 ) ^^ get ( ) >> 
 	 d0! Л_round2 :=  ^^ fetch (  !- $ xInt3 ) ^^ get ( ) >> 
 	 d0! Л_round2 := DePoolContract_Ф_updateRound2 (! $ Л_round2 , $ Л_prevValidatorHash , $ Л_curValidatorHash , $ Л_validationStart , $ Л_stakeHeldFor !) ; 
 	 
 Ift ( $ Л_areElectionsStarted && $ Л_round1 . ↑8 RoundsBase_ι_Round_ι_vsetHashInElectionPhase ?!= $ Л_curValidatorHash && $ Л_round2 . ↑8 RoundsBase_ι_Round_ι_step ?== RoundStep . Completed ) { delete  [ $ Л_round2 . ↑8 RoundsBase_ι_Round_ι_id ] ; d0! Л_round2 := $ Л_round1 ; d0! Л_round1 := $ Л_round0 ; d0! Л_round0 := DePoolContract_Ф_generateRound () } >> d0! Л_round2 := DePoolContract_Ф_updateRound2 (! $ Л_round2 , $ Л_prevValidatorHash , $ Л_curValidatorHash , $ Л_validationStart , $ Л_stakeHeldFor !) ; 
 	 d2! Л_round1 ^^ RoundsBase_ι_Round_ι_supposedElectedAt := $ Л_validationEnd ; 
 	 d2! Л_round1 ^^ RoundsBase_ι_Round_ι_elector := DebugDePool_Ф_getElector () ; 
 	 d2! Л_round1 ^^ RoundsBase_ι_Round_ι_vsetHashInElectionPhase := $ Л_curValidatorHash ; 
 	 d0! Л_isTotalStakeOk := $ Л_round1 ^^ RoundsBase_ι_Round_ι_stake ?>= ↑9 DePoolContract_ι_m_minRoundStake ; 
 	 d0! Л_isValidatorStake := RoundsBase_Ф_activeStakeSum (! $ Л_round1 . ↑8 RoundsBase_ι_Round_ι_stakes [ ↑3 ValidatorBase_ι_m_validatorWallet ] !) ?>= math ^^ muldiv ( ↑9 DePoolContract_ι_m_minRoundStake , ↑9 DePoolContract_ι_VALIDATOR_WALLET_MIN_STAKE , $ xInt100 ) >> 
 	 
 Ife ( ! $ Л_isTotalStakeOk || ! $ Л_isValidatorStake ) { $ Л_round1 . d1! RoundsBase_ι_Round_ι_step := RoundStep . WaitingUnfreeze ; $ Л_round1 . d1! RoundsBase_ι_Round_ι_completionReason := $ Л_isTotalStakeOk ? CompletionReason . ValidatorStakeIsTooSmall : CompletionReason . TotalStakeIsTooSmall ; $ Л_round1 . d1! RoundsBase_ι_Round_ι_unfreeze := $ xInt0 ; } else { $ Л_round1 . d1! RoundsBase_ι_Round_ι_step := RoundStep . WaitingValidatorRequest ; emit $ Л_stakeSigningRequested ( $ Л_round1 . ↑8 RoundsBase_ι_Round_ι_supposedElectedAt , $ Л_round1 . ↑8 RoundsBase_ι_Round_ι_proxy ) } >> 
 
 
 Ift ( $ Л_round1 . ↑8 RoundsBase_ι_Round_ι_step ?== RoundStep . WaitingValidationStart && $ Л_round1 . ↑8 RoundsBase_ι_Round_ι_vsetHashInElectionPhase ?== $ Л_prevValidatorHash ) { $ Л_round1 . d1! RoundsBase_ι_Round_ι_step := RoundStep . WaitingIfValidatorWinElections ; ProxyBase_Ф__recoverStake ( $ Л_round1 . ↑8 RoundsBase_ι_Round_ι_proxy , $ Л_round1 . ↑8 RoundsBase_ι_Round_ι_id , $ Л_round1 . ↑8 RoundsBase_ι_Round_ι_elector ) } >> 
  [  !- $ xInt1 $ Л_round0 ; 
 	  [  !- $ xInt2 $ Л_round1 ; 
 	  [  !- $ xInt3 $ Л_round2 ; . 
 

(* function ticktock ( ) public { require ( msg_sender ! = address 
 	 	 ( 0 ) , Errors . IS_EXT_MSG ) ; updateRounds ( ) ; _returnChange ( 
 	 	 ) ; } *)
Definition DePoolContract_Ф_ticktock ( msg_sender : XInteger ) : LedgerT ( XErrorValue True XInteger ) := 
 Require {{ $ msg_sender ?!= xInt0 ,  Errors_ι_IS_EXT_MSG }} ; 
 	 DePoolContract_Ф_updateRounds () ; 
 	 DePoolContract_Ф__returnChange () ; . 
 

(* function completeRoundWithChunk ( uint64 roundId , uint8 
 	 	 chunkSize ) { require ( msg_sender == address ( this ) , Errors . 
 	 	 IS_NOT_DEPOOL ) ; tvm_accept ( ) ; require ( roundId == m_roundQty 
 	 	 - 3 || roundId ! = m_roundQty - 3 && m_poolClosed , InternalErrors 
 	 	 . ERROR522 ) ; optional ( Round ) optRound = m_rounds . fetch ( roundId 
 	 	 ) ; require ( optRound . hasValue ( ) , InternalErrors . ERROR519 
 	 	 ) ; Round round = optRound . get ( ) ; require ( round . step == RoundStep 
 	 	 . Completing , InternalErrors . ERROR518 ) ; round = _returnOrReinvest 
 	 	 ( round , chunkSize ) ; if ( chunkSize < MAX_MSGS_PER_TR && ! round 
 	 	 . stakes . empty ( ) ) { uint8 doubleChunkSize = 2 * chunkSize ; this 
 	 	 . completeRoundWithChunk { flag : 1 , bounce : false } ( roundId 
 	 	 , doubleChunkSize < MAX_MSGS_PER_TR? doubleChunkSize : chunkSize 
 	 	 ) ; this . completeRoundWithChunk { flag : 1 , bounce : false } ( roundId 
 	 	 , chunkSize ) ; } m_rounds [ roundId ] = round ; } *)
Definition DePoolContract_Ф_completeRoundWithChunk ( msg_sender : XInteger ) ( Л_roundId : XInteger64 )( Л_chunkSize : XInteger8 ) : LedgerT ( XErrorValue True XInteger ) := 
 Require {{ $ msg_sender ?== address(this) ,  Errors_ι_IS_NOT_DEPOOL }} ; 
 	 tvm_accept () >> 
 	 Require {{ $ Л_roundId ?==  !- $ xInt3 || $ Л_roundId ?!=  !- $ xInt3 && ↑9 DePoolContract_ι_m_poolClosed ,  InternalErrors_ι_ERROR522 }} ; 
 	 optional ( ↑8 RoundsBase_ι_Round )  ^^ fetch ( $ Л_roundId ) >> 
 	 Require {{ optRound ^^ hasValue ( ) ,  InternalErrors_ι_ERROR519 }} ; 
 	 d0! Л_round := optRound ^^ get ( ) >> 
 	 Require {{ $ Л_round ^^ RoundsBase_ι_Round_ι_step ?== RoundStep ^^ Completing ,  InternalErrors_ι_ERROR518 }} ; 
 	 d0! Л_round := DePoolContract_Ф__returnOrReinvest (! $ Л_round , $ Л_chunkSize !) ; 
 	 
 Ift ( $ Л_chunkSize ?< ↑9 DePoolContract_ι_MAX_MSGS_PER_TR && ! $ Л_round . ↑8 RoundsBase_ι_Round_ι_stakes . empty () { ) { d0! Л_doubleChunkSize := $ xInt2 !* $ Л_chunkSize ; 
 	 this ^^ DePoolContract_Ф_completeRoundWithChunk { flag : $ xInt1 , bounce : $ xBoolFalse 
 } 
 {( $ Л_roundId , Л_doubleChunkSize ?< Л_doubleChunkSize : Л_chunkSize ) 
 	 ^^ )} := DePoolContract_Ф_completeRoundWithChunk { flag : $ xInt1 , bounce : $ xBoolFalse 
 } 
 {( $ Л_roundId , Л_chunkSize ) 
 	 } >> d4!  Л_roundId ] $ Л_round 
 	 } >> . 
 

(* function completeRound ( uint64 roundId , uint32 participantQty 
 	 	 ) { require ( msg_sender == address ( this ) , Errors . IS_NOT_DEPOOL 
 	 	 ) ; tvm_accept ( ) ; require ( roundId == m_roundQty - 3 || roundId 
 	 	 ! = m_roundQty - 3 && m_poolClosed , InternalErrors . ERROR522 
 	 	 ) ; optional ( Round ) optRound = m_rounds . fetch ( roundId ) ; require 
 	 	 ( optRound . hasValue ( ) , InternalErrors . ERROR519 ) ; Round round 
 	 	 = optRound . get ( ) ; require ( round . step == RoundStep . Completing 
 	 	 , InternalErrors . ERROR518 ) ; this . completeRoundWithChunk 
 	 	 { flag : 1 , bounce : false } ( roundId , 1 ) ; tvm_commit ( ) ; tvm_accept 
 	 	 ( ) ; if ( participantQty < MAX_MSGS_PER_TR ) { round = _returnOrReinvest 
 	 	 ( round , MAX_MSGS_PER_TR ) ; m_rounds [ roundId ] = round ; } else 
 	 	 { uint outActionQty = ( participantQty + MAX_MSGS_PER_TR - 1 ) 
 	 	 / MAX_MSGS_PER_TR ; if ( outActionQty > MAX_QTY_OF_OUT_ACTIONS 
 	 	 ) { uint32 restParticipant = participantQty ; for ( int msgQty 
 	 	 = 0 ; restParticipant > 0 ; + + msgQty ) { uint32 curGroup = ( restParticipant 
 	 	 < MAX_PARTICIPANTS || msgQty + 1 == MAX_QTY_OF_OUT_ACTIONS ) 
 	 	 ? restParticipant : MAX_PARTICIPANTS ; this . completeRound 
 	 	 { flag : 1 , bounce : false } ( roundId , curGroup ) ; restParticipant 
 	 	 - = curGroup ; } } else { for ( uint i = 0 ; i < participantQty ; i + = MAX_MSGS_PER_TR 
 	 	 ) { this . completeRoundWithChunk { flag : 1 , bounce : false } ( roundId 
 	 	 , MAX_MSGS_PER_TR ) ; } } } } *)
Definition DePoolContract_Ф_completeRound ( msg_sender : XInteger ) ( Л_roundId : XInteger64 )( Л_participantQty : XInteger32 ) : LedgerT ( XErrorValue True XInteger ) := 
 Require {{ $ msg_sender ?== address(this) ,  Errors_ι_IS_NOT_DEPOOL }} ; 
 	 tvm_accept () >> 
 	 Require {{ $ Л_roundId ?==  !- $ xInt3 || $ Л_roundId ?!=  !- $ xInt3 && ↑9 DePoolContract_ι_m_poolClosed ,  InternalErrors_ι_ERROR522 }} ; 
 	 optional ( ↑8 RoundsBase_ι_Round )  ^^ fetch ( $ Л_roundId ) >> 
 	 Require {{ optRound ^^ hasValue ( ) ,  InternalErrors_ι_ERROR519 }} ; 
 	 d0! Л_round := optRound ^^ get ( ) >> 
 	 Require {{ $ Л_round ^^ RoundsBase_ι_Round_ι_step ?== RoundStep ^^ Completing ,  InternalErrors_ι_ERROR518 }} ; 
 	 this ^^ DePoolContract_Ф_completeRoundWithChunk { flag : $ xInt1 , bounce : $ xBoolFalse 
 } 
 {( $ Л_roundId , xInt1 ) 
 	 () 
 	 () 
 	 Ife ( Л_participantQty ?< DePoolContract_ι_MAX_MSGS_PER_TR ) d0! Л_round DePoolContract_Ф__returnOrReinvest ( Л_round , DePoolContract_ι_MAX_MSGS_PER_TR ) >> d4! [ Л_roundId := $ ; 
 
 } else { Л_outActionQty := $ Л_participantQty ↑9 DePoolContract_ι_MAX_MSGS_PER_TR $ xInt1 !/ ↑9 ; 
 
 Ife $ Л_outActionQty ↑9 DePoolContract_ι_MAX_QTY_OF_OUT_ACTIONS { d0! := $ ; for d0! Л_msgQty $ xInt0 $ Л_restParticipant $ xInt0 ++ $ ) { Л_curGroup := $ Л_restParticipant MAX_PARTICIPANTS || Л_msgQty !+ xInt1 ?== DePoolContract_ι_MAX_QTY_OF_OUT_ACTIONS ) Л_restParticipant : ; 
 this ^^ { flag $ xInt1 bounce : xBoolFalse 
 
 ( Л_roundId , Л_curGroup ) 
 	 Л_restParticipant -= Л_curGroup ; 	 
 >> 
 } 
 { for d0! Л_i $ xInt0 
 	 Л_i ?< Л_participantQty ; 	 d0! += ↑9 ) { ^^ )} := DePoolContract_Ф_completeRoundWithChunk { flag : $ xInt1 , bounce : $ xBoolFalse 
 } 
 {( $ Л_roundId , DePoolContract_ι_MAX_MSGS_PER_TR ) 
 	 } >> 
 } 
 
 >> 
 } >> . 
 

(* function onStakeAccept ( uint64 queryId , uint32 comment , 
 	 	 address elector ) public override { optional ( Round ) optRound 
 	 	 = m_rounds . fetch ( queryId ) ; require ( optRound . hasValue ( ) 
 	 	 , InternalErrors . ERROR513 ) ; Round round = optRound . get ( ) ; 
 	 	 require ( msg_sender == round . proxy , Errors . IS_NOT_PROXY ) 
 	 	 ; require ( elector == round . elector , Errors . IS_NOT_ELECTOR 
 	 	 ) ; require ( round . id == queryId , Errors . INVALID_QUERY_ID ) 
 	 	 ; require ( round . step == RoundStep . WaitingIfStakeAccepted 
 	 	 , Errors . INVALID_ROUND_STEP ) ; tvm_accept ( ) ; round . step = 
 	 	 RoundStep . WaitingValidationStart ; round . completionReason 
 	 	 = CompletionReason . Undefined ; m_rounds [ queryId ] = round ; 
 	 	 emit roundStakeIsAccepted ( round . validatorRequest . queryId 
 	 	 , comment ) ; } *)
Definition DePoolContract_Ф_onStakeAccept ( msg_sender : XInteger ) ( Л_queryId : XInteger64 )( Л_comment : XInteger32 )( Л_elector : XAddress ) : LedgerT ( XErrorValue True XInteger ) := 
 optional ( ↑8 RoundsBase_ι_Round )  ^^ fetch ( $ Л_queryId ) >> 
 	 Require {{ optRound ^^ hasValue ( ) ,  InternalErrors_ι_ERROR513 }} ; 
 	 d0! Л_round := optRound ^^ get ( ) >> 
 	 Require {{ $ msg_sender ?== $ Л_round ^^ RoundsBase_ι_Round_ι_proxy ,  Errors_ι_IS_NOT_PROXY }} ; 
 	 Require {{ $ Л_elector ?== $ Л_round ^^ RoundsBase_ι_Round_ι_elector ,  Errors_ι_IS_NOT_ELECTOR }} ; 
 	 Require {{ $ Л_round ^^ RoundsBase_ι_Round_ι_id ?== $ Л_queryId ,  Errors_ι_INVALID_QUERY_ID }} ; 
 	 Require {{ $ Л_round ^^ RoundsBase_ι_Round_ι_step ?== RoundStep ^^ WaitingIfStakeAccepted ,  Errors_ι_INVALID_ROUND_STEP }} ; 
 	 tvm_accept () >> 
 	 d2! Л_round ^^ RoundsBase_ι_Round_ι_step := RoundStep ^^ WaitingValidationStart ; 
 	 d2! Л_round ^^ RoundsBase_ι_Round_ι_completionReason := CompletionReason ^^ Undefined ; 
 	 d4!  [ Л_queryId ] := $ Л_round ; 
 	 emit $ Л_roundStakeIsAccepted ( $ Л_round ^^ validatorRequest . queryId , $ Л_comment ) >> . 
 

(* function onStakeReject ( uint64 queryId , uint32 comment , 
 	 	 address elector ) public override { optional ( Round ) optRound 
 	 	 = m_rounds . fetch ( queryId ) ; require ( optRound . hasValue ( ) 
 	 	 , InternalErrors . ERROR513 ) ; Round round = optRound . get ( ) ; 
 	 	 require ( msg_sender == round . proxy , Errors . IS_NOT_PROXY ) 
 	 	 ; require ( elector == round . elector , Errors . IS_NOT_ELECTOR 
 	 	 ) ; require ( round . id == queryId , Errors . INVALID_QUERY_ID ) 
 	 	 ; require ( round . step == RoundStep . WaitingIfStakeAccepted 
 	 	 , Errors . INVALID_ROUND_STEP ) ; round . step = RoundStep . WaitingValidatorRequest 
 	 	 ; round . completionReason = CompletionReason . StakeIsRejectedByElector 
 	 	 ; m_rounds [ queryId ] = round ; emit roundStakeIsRejected ( round 
 	 	 . validatorRequest . queryId , comment ) ; } *)
Definition DePoolContract_Ф_onStakeReject ( msg_sender : XInteger ) ( Л_queryId : XInteger64 )( Л_comment : XInteger32 )( Л_elector : XAddress ) : LedgerT ( XErrorValue True XInteger ) := 
 optional ( ↑8 RoundsBase_ι_Round )  ^^ fetch ( $ Л_queryId ) >> 
 	 Require {{ optRound ^^ hasValue ( ) ,  InternalErrors_ι_ERROR513 }} ; 
 	 d0! Л_round := optRound ^^ get ( ) >> 
 	 Require {{ $ msg_sender ?== $ Л_round ^^ RoundsBase_ι_Round_ι_proxy ,  Errors_ι_IS_NOT_PROXY }} ; 
 	 Require {{ $ Л_elector ?== $ Л_round ^^ RoundsBase_ι_Round_ι_elector ,  Errors_ι_IS_NOT_ELECTOR }} ; 
 	 Require {{ $ Л_round ^^ RoundsBase_ι_Round_ι_id ?== $ Л_queryId ,  Errors_ι_INVALID_QUERY_ID }} ; 
 	 Require {{ $ Л_round ^^ RoundsBase_ι_Round_ι_step ?== RoundStep ^^ WaitingIfStakeAccepted ,  Errors_ι_INVALID_ROUND_STEP }} ; 
 	 d2! Л_round ^^ RoundsBase_ι_Round_ι_step := RoundStep ^^ WaitingValidatorRequest ; 
 	 d2! Л_round ^^ RoundsBase_ι_Round_ι_completionReason := CompletionReason ^^ StakeIsRejectedByElector ; 
 	 d4!  [ Л_queryId ] := $ Л_round ; 
 	 emit $ Л_roundStakeIsRejected ( $ Л_round ^^ validatorRequest . queryId , $ Л_comment ) >> . 
 

(* function acceptRewardAndStartRoundCompleting ( Round round 
 	 	 , uint64 value ) private returns ( Round ) { uint64 effectiveStake 
 	 	 = round . stake - round . unused ; uint64 totalReward = value - effectiveStake 
 	 	 ; round . rewards = math . muldiv ( totalReward , PART_FRACTION 
 	 	 , 100 ) ; uint64 validatorReward = math . muldiv ( totalReward , 
 	 	 VALIDATOR_FRACTION , 100 ) ; m_validatorWallet . transfer ( validatorReward 
 	 	 , false , 1 ) ; m_lastRoundInterest = _calcLastRoundInterest 
 	 	 ( effectiveStake , round . rewards ) ; round = startRoundCompleting 
 	 	 ( round , CompletionReason . RewardIsReceived ) ; return round 
 	 	 ; } *)
Definition DePoolContract_Ф_acceptRewardAndStartRoundCompleting ( Л_round : RoundsBase_ι_Round )( Л_value : XInteger64 ) : LedgerT ( XErrorValue RoundsBase_ι_Round XInteger ) := 
 d0! Л_effectiveStake := $ Л_round ^^ RoundsBase_ι_Round_ι_stake !- $ Л_round ^^ RoundsBase_ι_Round_ι_unused ; 
 	 d0! Л_totalReward := $ Л_value !- $ Л_effectiveStake ; 
 	 d2! Л_round ^^ RoundsBase_ι_Round_ι_rewards := math ^^ muldiv {( $ Л_totalReward , DePoolContract_ι_PART_FRACTION , xInt100 ) 
 	 Л_validatorReward := ^^ muldiv $ Л_totalReward ↑9 DePoolContract_ι_VALIDATOR_FRACTION $ xInt100 >> 
 transfer ( Л_validatorReward , xBoolFalse , xInt1 ) 
 	 ↑9 DePoolContract_ι_m_lastRoundInterest DePoolContract_Ф__calcLastRoundInterest (! Л_effectiveStake , Л_round . RoundsBase_ι_Round_ι_rewards !) 
 	 Л_round := (! $ , CompletionReason RewardIsReceived !) 
 	 $ Л_round 
 	 } >> . 
 

(* function onSuccessToRecoverStake ( uint64 queryId , address 
 	 	 elector ) public override { optional ( Round ) optRound = m_rounds 
 	 	 . fetch ( queryId ) ; require ( optRound . hasValue ( ) , InternalErrors 
 	 	 . ERROR513 ) ; Round round = optRound . get ( ) ; require ( msg_sender 
 	 	 == round . proxy , Errors . IS_NOT_PROXY ) ; require ( elector == 
 	 	 round . elector , Errors . IS_NOT_ELECTOR ) ; uint64 value = uint64 
 	 	 ( msg_value ) + DePoolLib . PROXY_FEE ; if ( round . step == RoundStep 
 	 	 . WaitingIfValidatorWinElections ) { if ( value < round . stake 
 	 	 ) { round . step = RoundStep . WaitingUnfreeze ; round . unused = 
 	 	 value ; uint64 efectiveRoundStake = round . stake - round . unused 
 	 	 ; if ( m_minRoundStake > efectiveRoundStake ) { m_minRoundStake 
 	 	 = efectiveRoundStake ; } } else { round . step = RoundStep . WaitingUnfreeze 
 	 	 ; round . completionReason = CompletionReason . ElectionsAreLost 
 	 	 ; m_minRoundStake + = m_minRoundStake / 4 ; } } else if ( round . step 
 	 	 == RoundStep . WaitingReward ) { if ( value >= round . stake - round 
 	 	 . unused ) { round = acceptRewardAndStartRoundCompleting ( round 
 	 	 , value ) ; } else { round = startRoundCompleting ( round , CompletionReason 
 	 	 . ValidatorIsPunished ) ; round . unused + = value ; } } else { revert 
 	 	 ( InternalErrors . ERROR521 ) ; } m_rounds [ queryId ] = round ; } 
 	 	 *)
Definition DePoolContract_Ф_onSuccessToRecoverStake ( msg_value : XInteger ) ( msg_sender : XInteger ) ( Л_queryId : XInteger64 )( Л_elector : XAddress ) : LedgerT ( XErrorValue True XInteger ) := 
 optional ( ↑8 RoundsBase_ι_Round )  ^^ fetch ( $ Л_queryId ) >> 
 	 Require {{ optRound ^^ hasValue ( ) ,  InternalErrors_ι_ERROR513 }} ; 
 	 d0! Л_round := optRound ^^ get ( ) >> 
 	 Require {{ $ msg_sender ?== $ Л_round ^^ RoundsBase_ι_Round_ι_proxy ,  Errors_ι_IS_NOT_PROXY }} ; 
 	 Require {{ $ Л_elector ?== $ Л_round ^^ RoundsBase_ι_Round_ι_elector ,  Errors_ι_IS_NOT_ELECTOR }} ; 
 	 d0! Л_value := $ msg_value !+  DePoolLib_ι_PROXY_FEE ; 
 	 
 Ife ( $ Л_round . ↑8 RoundsBase_ι_Round_ι_step ?== RoundStep . WaitingIfValidatorWinElections ) { if ( $ Л_value ?< $ Л_round . ↑8 RoundsBase_ι_Round_ι_stake ) { d2! Л_round ^^ RoundsBase_ι_Round_ι_step := RoundStep ^^ WaitingUnfreeze ; 
 	 d2! Л_round ^^ RoundsBase_ι_Round_ι_unused := $ Л_value ; 
 	 d0! Л_efectiveRoundStake := $ Л_round ^^ RoundsBase_ι_Round_ι_stake !- $ Л_round ^^ RoundsBase_ι_Round_ι_unused ; 
 	 
 Ift ( ↑9 DePoolContract_ι_m_minRoundStake ?> $ Л_efectiveRoundStake ) { d1! DePoolContract_ι_m_minRoundStake := $ Л_efectiveRoundStake ; } >> } else { $ Л_round . d1! RoundsBase_ι_Round_ι_step := RoundStep . WaitingUnfreeze ; $ Л_round . d1! RoundsBase_ι_Round_ι_completionReason := CompletionReason . ElectionsAreLost ; d1! DePoolContract_ι_m_minRoundStake += ↑9 DePoolContract_ι_m_minRoundStake !/ $ xInt4 ; } >> } else if ( $ Л_round . ↑8 RoundsBase_ι_Round_ι_step ?== RoundStep . WaitingReward ) { 
 Ife ( $ Л_value ?>= $ Л_round . ↑8 RoundsBase_ι_Round_ι_stake !- $ Л_round . ↑8 RoundsBase_ι_Round_ι_unused ) { d0! Л_round := DePoolContract_Ф_acceptRewardAndStartRoundCompleting {( $ Л_round , Л_value ) >> 
 
 else d0! Л_round DePoolContract_Ф_startRoundCompleting (! Л_round , . ValidatorIsPunished ; 
 d2! Л_round ↑8 RoundsBase_ι_Round_ι_unused $ Л_value 
 	 } >> 
 } else { (  ) >> 	 
 >> 
  [ ] := Л_round ; 	 
 >> . 
 

(* function onFailToRecoverStake ( uint64 queryId , address 
 	 	 elector ) public override { optional ( Round ) optRound = m_rounds 
 	 	 . fetch ( queryId ) ; require ( optRound . hasValue ( ) , InternalErrors 
 	 	 . ERROR513 ) ; Round round = optRound . get ( ) ; require ( msg_sender 
 	 	 == round . proxy , Errors . IS_NOT_PROXY ) ; require ( elector == 
 	 	 round . elector , Errors . IS_NOT_ELECTOR ) ; if ( round . step == 
 	 	 RoundStep . WaitingIfValidatorWinElections ) { round . step 
 	 	 = RoundStep . WaitingUnfreeze ; } else if ( round . step == RoundStep 
 	 	 . WaitingReward ) { round = startRoundCompleting ( round , CompletionReason 
 	 	 . ValidatorIsPunished ) ; } else { revert ( InternalErrors . ERROR521 
 	 	 ) ; } m_rounds [ queryId ] = round ; } *)
Definition DePoolContract_Ф_onFailToRecoverStake ( msg_sender : XInteger ) ( Л_queryId : XInteger64 )( Л_elector : XAddress ) : LedgerT ( XErrorValue True XInteger ) := 
 optional ( ↑8 RoundsBase_ι_Round )  ^^ fetch ( $ Л_queryId ) >> 
 	 Require {{ optRound ^^ hasValue ( ) ,  InternalErrors_ι_ERROR513 }} ; 
 	 d0! Л_round := optRound ^^ get ( ) >> 
 	 Require {{ $ msg_sender ?== $ Л_round ^^ RoundsBase_ι_Round_ι_proxy ,  Errors_ι_IS_NOT_PROXY }} ; 
 	 Require {{ $ Л_elector ?== $ Л_round ^^ RoundsBase_ι_Round_ι_elector ,  Errors_ι_IS_NOT_ELECTOR }} ; 
 	 
 Ife ( $ Л_round . ↑8 RoundsBase_ι_Round_ι_step ?== RoundStep . WaitingIfValidatorWinElections ) { $ Л_round . d1! RoundsBase_ι_Round_ι_step := RoundStep . WaitingUnfreeze ; } else if ( $ Л_round . ↑8 RoundsBase_ι_Round_ι_step ?== RoundStep . WaitingReward ) { d0! Л_round := DePoolContract_Ф_startRoundCompleting (! $ Л_round , CompletionReason . ValidatorIsPunished !) ; 
 	 
 } 
 else { revert (  InternalErrors_ι_ERROR521 ) >> 
 	 
 d4!  [ Л_queryId ] := $ Л_round ; . 
 

(* function terminator ( ) { require ( msg_pubkey ( ) == tvm_pubkey 
 	 	 ( ) , Errors . IS_NOT_OWNER ) ; require ( ! m_poolClosed , Errors 
 	 	 . DEPOOL_IS_CLOSED ) ; m_poolClosed = true ; tvm_commit ( ) ; tvm_accept 
 	 	 ( ) ; Round round0 = m_rounds . fetch ( m_roundQty - 1 ) . get ( ) ; Round 
 	 	 round1 = m_rounds . fetch ( m_roundQty - 2 ) . get ( ) ; round0 = startRoundCompleting 
 	 	 ( round0 , CompletionReason . PoolClosed ) ; if ( round1 . step == 
 	 	 RoundStep . WaitingValidatorRequest ) { round1 = startRoundCompleting 
 	 	 ( round1 , CompletionReason . PoolClosed ) ; } emit dePoolPoolClosed 
 	 	 ( ) ; m_rounds [ m_roundQty - 1 ] = round0 ; m_rounds [ m_roundQty 
 	 	 - 2 ] = round1 ; } *)
Definition DePoolContract_Ф_terminator : LedgerT ( XErrorValue True XInteger ) := 
 Require {{ $ msg_pubkey () ?== tvm_pubkey () ,  Errors_ι_IS_NOT_OWNER }} ; 
 	 Require {{ ! ↑9 DePoolContract_ι_m_poolClosed ,  Errors_ι_DEPOOL_IS_CLOSED }} ; 
 	 d1! DePoolContract_ι_m_poolClosed := $ xBoolTrue ; 
 	 tvm_commit () >> 
 	 tvm_accept () >> 
 	 d0! Л_round0 :=  ^^ fetch (  !- $ xInt1 ) ^^ get ( ) >> 
 	 d0! Л_round1 :=  ^^ fetch (  !- $ xInt2 ) ^^ get ( ) >> 
 	 d0! Л_round0 := DePoolContract_Ф_startRoundCompleting (! $ Л_round0 , CompletionReason . PoolClosed !) ; 
 	 
 Ift ( $ Л_round1 . ↑8 RoundsBase_ι_Round_ι_step ?== RoundStep . WaitingValidatorRequest ) { d0! Л_round1 := DePoolContract_Ф_startRoundCompleting {( $ Л_round1 , . PoolClosed } >> } >> emit $ () 
 	 [  $ xInt1 Л_round0 ; 	   !- xInt2 $ ; 
 
 } >> . 
 

(* function receiveFunds ( ) public pure { } *)
Definition DePoolContract_Ф_receiveFunds : LedgerT ( XErrorValue True XInteger ) 
 	 := return! I .
(* function Constructor8 ( uint64 minRoundStake , address proxy0 
 	 	 , address proxy1 , address validatorWallet , uint64 minStake 
 	 	 ) DePoolContract ( minRoundStake , proxy0 , proxy1 , validatorWallet 
 	 	 , minStake ) public { } *)
Definition DePool_Ф_Constructor8 ( Л_minRoundStake : XInteger64 )( Л_proxy0 : XAddress )( Л_proxy1 : XAddress )( Л_validatorWallet : XAddress )( Л_minStake : XInteger64 ) : LedgerT ( XErrorValue True XInteger ) 
 	 := return! I .
(* function getParticipantInfo ( address addr ) public view returns 
 	 	 ( uint64 total , uint64 withdrawValue , bool reinvest , uint64 
 	 	 reward , mapping ( uint64 => uint64 ) stakes , mapping ( uint64 => 
 	 	 InvestParams ) vestings , mapping ( uint64 => InvestParams ) locks 
 	 	 ) { optional ( DePoolLib . Participant ) optParticipant = m_participants 
 	 	 . fetch ( addr ) ; require ( optParticipant . hasValue ( ) , Errors 
 	 	 . NO_SUCH_PARTICIPANT ) ; DePoolLib . Participant participant 
 	 	 = optParticipant . get ( ) ; reinvest = participant . reinvest ; 
 	 	 reward = participant . reward ; withdrawValue = participant . 
 	 	 withdrawValue ; optional ( uint64 , Round ) pair = m_rounds . min 
 	 	 ( ) ; while ( pair . hasValue ( ) ) { ( uint64 id , Round round ) = pair 
 	 	 . get ( ) ; optional ( StakeValue ) optSv = round . stakes . fetch ( 
 	 	 addr ) ; if ( optSv . hasValue ( ) ) { StakeValue sv = optSv . get ( ) ; 
 	 	 if ( sv . ordinary ! = 0 ) { stakes [ round . id ] = sv . ordinary ; total 
 	 	 + = sv . ordinary ; } if ( sv . vesting . hasValue ( ) ) { vestings [ round 
 	 	 . id ] = sv . vesting . get ( ) ; total + = sv . vesting . get ( ) . amount 
 	 	 ; } if ( sv . lock . hasValue ( ) ) { locks [ round . id ] = sv . lock . get 
 	 	 ( ) ; total + = sv . lock . get ( ) . amount ; } } pair = m_rounds . next ( 
 	 	 id ) ; } } *)
Definition DePool_Ф_getParticipantInfo ( Л_addr : XAddress ) : LedgerT ( XErrorValue ( XInteger64 # XInteger64 # XBool # XInteger64 # := 
 optional (  DePoolLib_ι_DePoolHelper_ι_Participant ) XInteger )  ^^ fetch ( $ Л_addr ) >> 
 	 Require {{ optParticipant ^^ hasValue ( ) ,  Errors_ι_NO_SUCH_PARTICIPANT }} ; 
 	 d0! Л_participant := optParticipant ^^ get ( ) >> 
 	 $ Л_participant ^^ reinvest ; 
 	 d1! TestElector_ι_Validator_ι_reward := $ Л_participant ^^ TestElector_ι_Validator_ι_reward ; 
 	 $ Л_participant ^^ withdrawValue ; 
 	 optional ( uint64 , ↑8 RoundsBase_ι_Round )  ^^ min ( ) >> 
 	 while ( pair ^^ hasValue ( ) ) { {( $ Л_id , Л_round pair get ( >> 
 optional ( RoundsBase_ι_StakeValue ) Л_round ^^ RoundsBase_ι_Round_ι_stakes . ( $ ) >> 	 
 ( optSv hasValue ( { ) d0! Л_sv optSv ^^ ( ) 
 	 Ift ( Л_sv . RoundsBase_ι_StakeValue_ι_ordinary ?!= xInt0 ) ↑8 RoundsBase_ι_Round_ι_stakes $ Л_round ↑8 RoundsBase_ι_Round_ι_id Л_sv . RoundsBase_ι_StakeValue_ι_ordinary ; Л_sv . RoundsBase_ι_StakeValue_ι_ordinary ; >> if $ Л_sv vesting . () { vestings $ Л_round ↑8 RoundsBase_ι_Round_ι_id Л_sv ^^ . get ) >> 	 $ ^^ vesting get ( ^^ ; 
 
 } 
 
 ( $ . lock hasValue ( { ) locks [ Л_round ^^ RoundsBase_ι_Round_ι_id $ ^^ lock get ( >> 
 $ Л_sv lock . () ↑8 RoundsBase_ι_InvestParams_ι_amount 
 	 } >> 
 } 
  next ( Л_id ) 
 	 } >> 
 } >> . 
 

(* function getDePoolInfo ( ) public view returns ( uint64 minStake 
 	 	 , uint64 minRoundStake , uint64 minValidatorStake , address 
 	 	 validatorWallet , mapping ( int => address ) proxies , bool poolClosed 
 	 	 , uint64 interest , uint64 addStakeFee , uint64 addVestingOrLockFee 
 	 	 , uint64 removeOrdinaryStakeFee , uint64 withdrawPartAfterCompletingFee 
 	 	 , uint64 withdrawAllAfterCompletingFee , uint64 transferStakeFee 
 	 	 , uint64 retOrReinvFee , uint64 answerMsgFee , uint64 proxyFee 
 	 	 , uint64 participantFraction , uint64 validatorFraction , uint64 
 	 	 validatorWalletMinStake ) { minStake = m_minStake ; minRoundStake 
 	 	 = m_minRoundStake ; minValidatorStake = ( m_minRoundStake * 
 	 	 VALIDATOR_WALLET_MIN_STAKE ) / 100 ; validatorWallet = m_validatorWallet 
 	 	 ; proxies = m_proxies ; poolClosed = m_poolClosed ; interest = 
 	 	 m_lastRoundInterest ; addStakeFee = ADD_STAKE_FEE ; addVestingOrLockFee 
 	 	 = ADD_VESTING_OR_LOCK_FEE ; removeOrdinaryStakeFee = REMOVE_ORDINARY_STAKE_FEE 
 	 	 ; withdrawPartAfterCompletingFee = WITHDRAW_PART_AFTER_COMPLETING_FEE 
 	 	 ; withdrawAllAfterCompletingFee = WITHDRAW_ALL_AFTER_COMPLETING_FEE 
 	 	 ; transferStakeFee = TRANSFER_STAKE_FEE ; retOrReinvFee = RET_OR_REINV_FEE 
 	 	 ; answerMsgFee = ANSWER_MSG_FEE ; proxyFee = DePoolLib . PROXY_FEE 
 	 	 ; participantFraction = PART_FRACTION ; validatorFraction 
 	 	 = VALIDATOR_FRACTION ; validatorWalletMinStake = VALIDATOR_WALLET_MIN_STAKE 
 	 	 ; } *)
Definition DePool_Ф_getDePoolInfo : LedgerT ( XErrorValue ( XInteger64 # XInteger64 # XInteger64 # XAddress # := 
 ↑9 DePoolContract_ι_m_minStake ; 
 	 ↑9 DePoolContract_ι_m_minRoundStake ; 
 	 ( ↑9 DePoolContract_ι_m_minRoundStake !* ↑9 DePoolContract_ι_VALIDATOR_WALLET_MIN_STAKE ) XInteger ) !/ $ xInt100 ; 
 	 ↑3 ValidatorBase_ι_m_validatorWallet ; 
 	 ↑4 ProxyBase_ι_m_proxies ; 
 	 ↑9 DePoolContract_ι_m_poolClosed ; 
 	 ↑9 DePoolContract_ι_m_lastRoundInterest ; 
 	 ↑9 DePoolContract_ι_ADD_STAKE_FEE ; 
 	 ↑9 DePoolContract_ι_ADD_VESTING_OR_LOCK_FEE ; 
 	 ↑9 DePoolContract_ι_REMOVE_ORDINARY_STAKE_FEE ; 
 	 ↑9 DePoolContract_ι_WITHDRAW_PART_AFTER_COMPLETING_FEE ; 
 	 ↑9 DePoolContract_ι_WITHDRAW_ALL_AFTER_COMPLETING_FEE ; 
 	 ↑9 DePoolContract_ι_TRANSFER_STAKE_FEE ; 
 	 ↑9 DePoolContract_ι_RET_OR_REINV_FEE ; 
 	 ↑9 DePoolContract_ι_ANSWER_MSG_FEE ; 
 	  DePoolLib_ι_PROXY_FEE ; 
 	 ↑9 DePoolContract_ι_PART_FRACTION ; 
 	 ↑9 DePoolContract_ι_VALIDATOR_FRACTION ; 
 	 ↑9 DePoolContract_ι_VALIDATOR_WALLET_MIN_STAKE ; . 
 

(* function getParticipants ( ) external view returns ( mapping 
 	 	 ( int => address ) participants ) { mapping ( address => bool ) used 
 	 	 ; optional ( address , DePoolLib . Participant ) pair = m_participants 
 	 	 . min ( ) ; while ( pair . hasValue ( ) ) { ( address p , ) = pair . get ( ) 
 	 	 ; if ( ! used . exists ( p ) ) { used [ p ] = true ; participants . push ( 
 	 	 p ) ; } pair = m_participants . next ( p ) ; } } *)
Definition DePool_Ф_getParticipants : LedgerT ( XErrorValue True XInteger ) := 
 used ; 
 	 optional ( address ,  DePoolLib_ι_DePoolHelper_ι_Participant )  ^^ min ( ) >> 
 	 while ( pair ^^ hasValue ( ) ) { {( $ Л_p , ^^ get ) >> 	 
 ( ! . exists $ Л_p { ) d4! used Л_p ] $ xBoolTrue 
 	 ^^ push $ Л_p >> 
 
 } 
  next ( Л_p ) 
 	 } >> 
 } >> . 
 

(* function onRoundComplete ( uint64 roundId , uint64 reward 
 	 	 , uint64 ordinaryStake , uint64 vestingStake , uint64 lockStake 
 	 	 , bool reinvest , uint8 reason ) external override { } *)
Definition Participant_Ф_onRoundComplete ( Л_roundId : XInteger64 )( Л_reward : XInteger64 )( Л_ordinaryStake : XInteger64 )( Л_vestingStake : XInteger64 )( Л_lockStake : XInteger64 )( Л_reinvest : XBool )( Л_reason : XInteger8 ) : LedgerT ( XErrorValue True XInteger ) 
 	 := return! I .
(* function receiveAnswer ( uint32 errcode , uint64 comment ) 
 	 	 external override { } *)
Definition Participant_Ф_receiveAnswer ( Л_errcode : XInteger32 )( Л_comment : XInteger64 ) : LedgerT ( XErrorValue True XInteger ) 
 	 := return! I .
(* function onTransfer ( address source , uint128 amount ) external 
 	 	 override { } *)
Definition Participant_Ф_onTransfer ( Л_source : XAddress )( Л_amount : XInteger128 ) : LedgerT ( XErrorValue True XInteger ) 
 	 := return! I .
(* function sendTransaction ( address dest , uint64 value , bool 
 	 	 bounce , uint16 flags , TvmCell payload ) public view { require 
 	 	 ( msg_pubkey ( ) == tvm_pubkey ( ) , Errors . IS_NOT_OWNER ) ; tvm_accept 
 	 	 ( ) ; dest . transfer ( value , bounce , flags , payload ) ; } *)
Definition Participant_Ф_sendTransaction ( Л_dest : XAddress )( Л_value : XInteger64 )( Л_bounce : XBool )( Л_flags : XInteger16 )( Л_payload : TvmCell ) : LedgerT ( XErrorValue True XInteger ) := 
 Require {{ $ msg_pubkey () ?== tvm_pubkey () ,  Errors_ι_IS_NOT_OWNER }} ; 
 	 tvm_accept () >> 
 	 $ Л_dest ^^ transfer {( $ Л_value , Л_bounce , Л_flags , Л_payload ) 
 	 } >> . 
 

(* function Constructor9 ( uint32 offset ) public { electAt = uint32 
 	 	 ( now ) + offset ; } *)
Definition TestElector_Ф_Constructor9 ( Л_offset : XInteger32 ) : LedgerT ( XErrorValue True XInteger ) := 
 d1! TestElector_ι_electAt := tvm_now !+ $ Л_offset ; . 
 

(* function getElectionId ( ) public view returns ( uint32 ) { return 
 	 	 electAt ; } *)
Definition TestElector_Ф_getElectionId : LedgerT ( XErrorValue XInteger32 XInteger ) := 
 return! ↑10 TestElector_ι_electAt ; . 
 

(* function process_new_stake ( uint64 queryId , uint256 validatorKey 
 	 	 , uint32 stakeAt , uint32 maxFactor , uint256 adnlAddr , bytes 
 	 	 signature ) public functionID ( 0x4e73744b ) { require ( msg_sender 
 	 	 ! = address ( 0 ) , 101 ) ; uint32 nowtime = uint32 ( now ) ; if ( nowtime 
 	 	 >= electAt ) { electAt + = ( ( nowtime - electAt ) / ELECTED_FOR + 1 
 	 	 ) * ELECTED_FOR ; } require ( nowtime >= ( electAt - ELECTIONS_BEGIN_BEFORE 
 	 	 ) , 103 ) ; require ( nowtime < ( electAt - ELECTIONS_END_BEFORE 
 	 	 ) , 103 ) ; require ( electAt == stakeAt , 102 ) ; require ( msg_value 
 	 	 >= 100000000000 , 104 ) ; ( , uint256 addr ) = msg_sender . unpack 
 	 	 ( ) ; elections [ addr ] = Validator ( uint64 ( msg_value ) - 1e9 , validatorKey 
 	 	 , 10000000000 , queryId , maxFactor , adnlAddr , signature ) ; IDePool 
 	 	 ( msg_sender ) . onStakeAccept . value ( 1000000000 ) ( queryId 
 	 	 , 0 ) ; } *)
Definition TestElector_Ф_process_new_stake ( msg_value : XInteger ) ( msg_sender : XInteger ) ( Л_queryId : XInteger64 )( Л_validatorKey : XInteger256 )( Л_stakeAt : XInteger32 )( Л_maxFactor : XInteger32 )( Л_adnlAddr : XInteger256 )( Л_signature : XInteger8 ) : LedgerT ( XErrorValue True XInteger ) := 
 Require {{ $ msg_sender ?!= xInt0 , $ xInt101 }} ; 
 	 d0! Л_nowtime := tvm_now ; 
 	 
 Ift ( $ Л_nowtime ?>= ↑10 TestElector_ι_electAt ) { d1! TestElector_ι_electAt += ( ( $ Л_nowtime !- ↑10 TestElector_ι_electAt ) !/ ↑10 TestElector_ι_ELECTED_FOR !+ $ xInt1 ) { !* { ↑10 TestElector_ι_ELECTED_FOR } >> 
 Require {{ $ Л_nowtime ?>= ( ↑10 TestElector_ι_electAt !- ↑10 TestElector_ι_ELECTIONS_BEGIN_BEFORE ) , $ xInt103 }} ; 
 	 Require {{ $ Л_nowtime ?< ( ↑10 TestElector_ι_electAt !- ↑10 TestElector_ι_ELECTIONS_END_BEFORE ) , $ xInt103 }} ; 
 	 Require {{ ↑10 TestElector_ι_electAt ?== $ Л_stakeAt , $ xInt102 }} ; 
 	 Require {{ $ msg_value ?>= $ xInt100000000000 , $ xInt104 }} ; 
 	 ( , $ Л_addr $ msg_sender ^^ unpack ( ) >> 
 	 d4! TestElector_ι_elections [ Л_addr ] := ↑10 TestElector_ι_Validator ( $ msg_value !- 1e9 , $ Л_validatorKey , $ xInt10000000000 , $ Л_queryId , $ Л_maxFactor , $ Л_adnlAddr , $ Л_signature ) >> 
 	 (* IDePool ( $ msg_sender ) ^^ DePoolProxyContract_Ф_onStakeAccept *) . value ( $ xInt1000000000 ) {( $ Л_queryId , xInt0 ) 
 	 } >> . 
 

(* function recover_stake ( uint64 queryId ) public functionID 
 	 	 ( 0x47657424 ) { ( , uint256 addr ) = msg_sender . unpack ( ) ; optional 
 	 	 ( Validator ) optValidator = elections . fetch ( addr ) ; require 
 	 	 ( optValidator . hasValue ( ) , Errors . IS_NOT_ELECTOR ) ; Validator 
 	 	 validator = optValidator . get ( ) ; uint32 time = uint32 ( now ) ; 
 	 	 if ( ( time > electAt ) && time < ( electAt + ELECTED_FOR + STAKE_HELD_FOR 
 	 	 ) ) { IDePool ( msg_sender ) . sendError . value ( 1000000000 ) ( queryId 
 	 	 , 0x47657424 ) ; } else { IDePool ( msg_sender ) . acceptRecoveredStake 
 	 	 . value ( validator . stake + validator . reward ) ( queryId ) ; delete 
 	 	 elections [ addr ] ; } } *)
Definition TestElector_Ф_recover_stake ( msg_sender : XInteger ) ( Л_queryId : XInteger64 ) : LedgerT ( XErrorValue True XInteger ) := 
 ( , $ Л_addr $ msg_sender ^^ unpack ( ) >> 
 	 optional ( ↑10 TestElector_ι_Validator ) fetch ( $ Л_addr ) >> 
 	 Require {{ optValidator ^^ hasValue ( ) ,  Errors_ι_IS_NOT_ELECTOR }} ; 
 	 d0! Л_validator := optValidator ^^ get ( ) >> 
 	 d0! Л_time := tvm_now ; 
 	 
 Ife ( ( $ Л_time ?> ↑10 TestElector_ι_electAt ) { && { $ Л_time { ?< { ( { ↑10 TestElector_ι_electAt { !+ { ↑10 TestElector_ι_ELECTED_FOR { !+ { ↑10 TestElector_ι_STAKE_HELD_FOR { ) { ) { (* IDePool ( $ msg_sender ) ^^ Participant_Ф_sendError *) . value ( $ xInt1000000000 ) {( $ Л_queryId , ) >> 	 
 
 else (* IDePool $ msg_sender ^^ )} := Participant_Ф_acceptRecoveredStake *) . value ( $ Л_validator ^^ RoundsBase_ι_Round_ι_stake !+ $ Л_validator ^^ TestElector_ι_Validator_ι_reward ) ( $ Л_queryId ) >> 
 	 delete ↑10 TestElector_ι_elections [ $ Л_addr ] ; . 
 

End DePoolFuncs.

