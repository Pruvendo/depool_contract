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

Module TVMModel (xt: XTypesSig) (sm: StateMonadSig).

Module LedgerClass := LedgerClass xt sm .
Import LedgerClass.
Import SolidityNotations.

Import xt. Import sm.

Set Typeclasses Iterative Deepening.

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
	↑16 (modify (fun r => setTransactionList (xListCons (TransactionC dest value bounce flags payload) (VMState_ι_transactions r)) r) >> 
	return! I ).
    
Notation " a '->transfer' '(!' b , c , d '!)' " := (do a' ← a ; do b' ← b ; do c' ← c ; do d' ← d ; 
    ( ↓ tvm_transfer a' b' c' d' default ) ) (at level 62, left associativity): solidity_scope.  
Notation " a '->transfer' '(!' b , c , d , e '!)' " := (do a' ← a ; do b' ← b ; do c' ← c ; do d' ← d ; do e' ← e ;
	( ↓ tvm_transfer a' b' c' d' e' ) ) (at level 62, left associativity): solidity_scope.	      

Definition msg_pubkey : LedgerT XInteger256 := ↑ε16 VMState_ι_msg_pubkey.
Definition msg_sender : LedgerT XAddress := ↑ε16 VMState_ι_msg_sender.	
Definition msg_value : LedgerT XInteger32 := ↑ε16 VMState_ι_msg_value.
Definition msg_data : LedgerT TvmCell := ↑ε16 VMState_ι_msg_data. 


Definition tvm_accept : LedgerT True := ↑16 (U1! VMState_ι_accepted := $ xBoolTrue).
Definition tvm_transLT : LedgerT XInteger64 := ↑ε16 VMState_ι_ltime.
Definition tvm_setcode (newcode : TvmCell) : LedgerT True := ↑16 (U1! VMState_ι_code := $ newcode).
Definition tvm_setCurrentCode (c: TvmCell) : LedgerT True := ↑16 (U1! VMState_ι_currentCode := $ c).

(* Definition tvm_tree_cell_size (slice: TvmSlice) : LedgerT (XInteger # XInteger) := return! [(xInt0, xInt0)].
Definition tvm_ctos (cell : TvmCell): LedgerT TvmSlice := return! xStrNull. 
Definition tvm_reset_storage: LedgerT True :=  <! Ledger_ι_DePoolContract <- default  !> >> return! I. *)

Parameter tvm_hash : TvmCell -> XInteger256.

(* 
{( Л_cell , Л_ok )} := tvm_rawConfigParam (! $ xInt34 !)  = ($ Л_cell) ->toSlice() ; 
    U0! Л_decoded := Л_s ->decode(uint8,uint32,uint32) ;
	U0! {( _ , Л_utime_since , Л_utime_until )} := $ Л_decoded ; 

*)

Definition tvm_rawConfigParam_34 :  LedgerT (TvmCell # XBool) :=
	return# (↑ε16 VMState_ι_curValidatorData , $ xBoolTrue ).
	

(* 

U0! {( Л_cell , Л_ok )} := tvm_rawConfigParam (! $ xInt32 !) ; = PrevValidatorData

*)

Definition tvm_rawConfigParam_32 :  LedgerT (TvmCell # XBool) :=
	return# (↑ε16 VMState_ι_prevValidatorData , $ xBoolTrue ).

(* 
U0! {( Л_cell , Л_ok )} := tvm_rawConfigParam (! $ xInt17 !) ; = U0! Л_s := ($ Л_cell) ->toSlice() ; 
 	Л_s ->loadTons() ;
 	Л_s ->loadTons() ; 
    Л_s ->loadTons() ;
    U0! Л_decoded := Л_s ->decode(uint32) ; = MaxStakeFactor
*)

Definition tvm_rawConfigParam_17 :  LedgerT (TvmCell # XBool) :=
	return# (↑ε16 VMState_ι_rawConfigParam_17 , $ xBoolTrue ).

(* {( Л_cell , Л_ok )} := tvm_rawConfigParam (! $ xInt1 !) ; = $ Л_cell) ->toSlice() ; 
 U0! Л_value := Л_s ->decode(uint256) ; 
  address->makeAddrStd (! $xInt0 !- $ xInt1 , $ Л_value !) *)

Definition tvm_rawConfigParam_1 :  LedgerT (TvmCell # XBool) :=
	return# (↑ε16 VMState_ι_rawConfigParam_1 , $ xBoolTrue ).

(* 
{( Л_validatorsElectedFor , Л_electionsStartBefore , Л_electionsEndBefore , Л_stakeHeldFor , Л_ok )} := tvm_configParam (! $ xInt15 !) ;
		@existT _ _ _ VMState_ι_validatorsElectedFor ,
		@existT _ _ _ VMState_ι_electionsStartBefore ,
		@existT _ _ _ VMState_ι_electionsEndBefore ,
		@existT _ _ _ VMState_ι_stakeHeldFor
*)

Definition tvm_configParam_15 :  LedgerT (XInteger32 # XInteger32 # XInteger32 # XInteger32 # XBool) :=
	return# (↑ε16 VMState_ι_validatorsElectedFor , 
			 ↑ε16 VMState_ι_electionsStartBefore , 
			 ↑ε16 VMState_ι_electionsEndBefore ,
			 ↑ε16 VMState_ι_stakeHeldFor ,
			 $ xBoolTrue ).

(* Parameter tvm_configParam : XInteger -> LedgerT (XInteger32 # XInteger32 # XInteger32 # XInteger32 # XBool) .
 *)

Definition tvm_balance : LedgerT XInteger128 := ↑ε16 VMState_ι_balance. 
Definition tvm_address : LedgerT XAddress := ↑ε16 VMState_ι_address.

Definition tvm_commit: LedgerT True :=
	do l ← get;
	put {$l with Ledger_ι_VMState := {$Ledger_ι_VMState l with VMState_ι_savedDePoolContracts := projEmbed l $}$};
	void!.

Definition tvm_revert {X E} (e: E): LedgerT (XErrorValue X E) :=
	do l ← get;
	put (injEmbed (VMState_ι_savedDePoolContracts (Ledger_ι_VMState l)) l  ) >>
	return! (xError e).

Definition callContractFunction {X E} (m: LedgerT (XErrorValue X E)) : LedgerT (XErrorValue X E) :=
	tvm_commit >> 
	m >>= fun ea => xErrorMapDefaultF (fun a => return! (xValue a)) ea tvm_revert.

(*********************************************************)

Parameter address_makeAddrStd : XInteger -> XInteger256 -> XAddress.
Notation " 'address->makeAddrStd' '(!' b ',' c '!)' " := (
												   do b' ← b; 
												   do c' ← c; 
												   return! (address_makeAddrStd b' c') )( at level 10, left associativity ): solidity_scope.		   

Parameter decode_uint8_uint32_uint32 : TvmSlice -> XInteger8 # XInteger32 # XInteger32 # TvmSlice.
Notation " 'U0!' d ':=' a '->decode(uint8,uint32,uint32)' ; t " := ( let dec := decode_uint8_uint32_uint32 a in let d := xProdFst dec in let a := xProdSnd dec in t)( at level 33, left associativity, t at level 50 ): solidity_scope.

Parameter toSlice: TvmCell -> TvmSlice.
Notation " a '->toSlice()' " := ( do a' ← a ; return! (toSlice a') )( at level 10, left associativity ): solidity_scope.

Parameter tvm_loadTons : TvmSlice -> TvmSlice.

Notation " a '->loadTons()' ; t " := ( let a := tvm_loadTons a in t )( at level 10, left associativity, t at level 50): solidity_scope.


Parameter decode_uint32 : TvmSlice -> XInteger32 # TvmSlice.
Notation " 'U0!' d ':=' a '->decode(uint32)' ; t " := ( let dec := decode_uint32 a in let d := xProdFst dec in let a := xProdSnd dec in t )( at level 33, left associativity , t at level 50): solidity_scope.

Parameter decode_uint256 : TvmSlice -> XInteger256 # TvmSlice.
Notation " 'U0!' d ':=' a '->decode(uint256)' ; t " := ( let dec := decode_uint256 a in let d := xProdFst dec in let a := xProdSnd dec in t )( at level 33, left associativity , t at level 50): solidity_scope.

Parameter isStdAddrWithoutAnyCast: XAddress -> XBool.
Notation " a '->isStdAddrWithoutAnyCast()' " := ( do a' ← a ; $ (isStdAddrWithoutAnyCast a') ) (at level 20, right associativity).

Parameter isStdZero :  XAddress -> XBool.
Notation " a '->isStdZero()' " := ( do a' ← a ; $ (isStdZero a') ) (at level 20, right associativity). 

Parameter builder_store : TvmBuilder -> XInteger -> XInteger -> TvmBuilder.
Notation "U0! b '->store' x i ; t" := (do x'←x; do i'←i; let b := builder_store b x' i' in t) (at level 33, t at level 50).

Parameter toCell : TvmBuilder -> TvmCell.
Notation "b '->toCell'" := (do b'←b; $ (toCell b')) (at level 62).

Parameter addressWid : XAddress -> XInteger.
Notation "x ->wid" := (do x' ← x; $ (addressWid x')) (at level 20).


Parameter tvm_buildEmptyData : XInteger256  -> TvmCell.
Parameter tvm_buildStateInit : TvmCell -> TvmCell -> TvmCell.

Parameter tvm_functionId : ContractFunctionWithId ->  XInteger32.

Parameter decode_uint64 : TvmSlice -> XInteger64 # TvmSlice.
Notation " 'U0!' d ':=' a '->decode(uint64)' ; t " := ( let dec := decode_uint64 a in let d := xProdFst dec in let a := xProdSnd dec in t )( at level 33, left associativity , t at level 50): solidity_scope.


Definition tvm_rawReserve (res : XInteger128)  (_: XInteger) :=
	↑16 (U1! VMState_ι_reserved := $ res).


Parameter selfdestruct : XAddress -> LedgerT True.
(* Notation "'->selfdestruct' a" := (do a' ← a; ↓ selfdestruct a') (at level 20).
 *)
Definition tvm_exit : LedgerT ( XValueValue True) := return! (xError I).


Definition deployablePrefix (dc: DeployableContract) : XInteger := 
	match dc with
	| NullContractD => xInt0
	| DePoolProxyContractD => xInt100
	| DePoolContractD => xInt200
	end.

Definition tvm_new (dc: DeployableContract) (msg: ConstructorMessage) (constr: LedgerT True) : LedgerT XAddress :=
	constr >>
	U0! n := ↑16 D2! VMState_ι_deployed [[ $ dc ]] ; 
	(↑16 U1! VMState_ι_deployed [[ $ dc ]] !++) >>
	U0! address := $ (deployablePrefix dc ) !+ $ n ; 
	tvm_transfer address (msg ->> cmessage_value) xBoolFalse xInt0 default >>
	$ address.
(* TODO: send change back to msg_sender if error *)
Definition tvm_newE {E} (dc: DeployableContract) (msg: LedgerT ConstructorMessage) (constr: LedgerT (XErrorValue True E)) : LedgerT (XErrorValue XAddress E) :=

U0! n := ↑16 D2! VMState_ι_deployed [[ $ dc ]] ; 
U0! address := $ (deployablePrefix dc ) !+ $ n ; 
(* (↑↑16 U2! VMState_ι_balance := D1! msg ^^ cmessage_value ) >>  *)
(* tvm_transfer address (m ->> cmessage_value) xBoolFalse xInt0 default >> *)
do _ ← constr ?;
(↑16 U1! VMState_ι_deployed [[ $ dc ]] !++) >>
$ address.


End TVMModel.

