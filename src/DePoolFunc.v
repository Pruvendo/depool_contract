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
(* Require Import depoolContract.ProofEnvironment. *) 
Require Import depoolContract.DePoolSpec. 
Require Import depoolContract.DePoolConsts . 

Require Import depoolContract.Lib.TVMModel. 

Module DePoolFuncs (xt: XTypesSig) (sm: StateMonadSig) (dc : DePoolConstsTypesSig xt sm ) . 

Module DePoolSpec := DePoolSpec xt sm. 
Import DePoolSpec. 
Import LedgerClass. 
Import SolidityNotations. 

Module TVMModel := TVMModel xt sm. 
Export TVMModel. 

Import xt. Import sm. Import dc. 

Set Typeclasses Iterative Deepening. 

Local Open Scope solidity_scope. 
Local Open Scope string_scope. 

(*the next notations cannot be moved to another location yet because of ↓ which is defined in Class file, not imported*) 
Notation " f '()' " := ( ↓ f ) (at level 22, left associativity, only parsing): solidity_scope. 
Notation " f '(!' a '!)' " := ( do a' ← a ; ↓ f a' ) (at level 22, left associativity, only parsing): solidity_scope. 
Notation " f '(!' a ',' b '!)' " := (do a' ← a ; do b' ← b ; ↓ f a' b' ) (at level 22, left associativity, only parsing): solidity_scope. 
Notation " f '(!' a ',' b ',' c '!)' " := (do a' ← a ; do b' ← b ; do c' ← c ; ↓ f a' b' c' ) (at level 22, left associativity, only parsing): solidity_scope. 
Notation " f '(!' a ',' b ',' c ',' d '!)' " := (do a' ← a ; do b' ← b ; do c' ← c ; do d' ← d ; ↓ f a' b' c' d' ) (at level 22, left associativity, only parsing): solidity_scope. 
Notation " f '(!' a ',' b ',' c ',' d ',' e '!)' " := (do a' ← a ; do b' ← b ; do c' ← c ; do d' ← d ; do e' ← e ; ↓ f a' b' c' d' e' ) (at level 22, left associativity, only parsing): solidity_scope. 
Notation " f '(!' a ',' b ',' c ',' d ',' e ',' i '!)' " := (do a' ← a ; do b' ← b ; do c' ← c ; do d' ← d ; do e' ← e ; do i' ← i ; ↓ f a' b' c' d' e' i' ) (at level 22, left associativity, only parsing): solidity_scope. 
Notation " f '(!' a ',' b ',' c ',' d ',' e ',' i ',' j '!)' " := (do a' ← a ; do b' ← b ; do c' ← c ; do d' ← d ; do e' ← e ; do i' ← i ; do j' ← j ; ↓ f a' b' c' d' e' i' j' ) (at level 22, left associativity, only parsing): solidity_scope. 

(*TODO*) 
(*TODO: try to move to another location?*) 
Definition intMin (a b: XInteger) := xBoolIfElse (xIntLeb a b) a b. 
Notation "'math->min2' '(!' a , b '!)'" := (do a' ← a; do b' ← b; return! (intMin a' b')) (at level 30, right associativity). 
Notation "'math->min3' '(!' a , b , c '!)'" := (do a' ← a; do b' ← b; do c' ← c; return! (intMin (intMin a' b') c')) (at level 30, right associativity). 

Definition intMulDiv (a b c: XInteger) := xIntDiv (xIntMult a b) c. 
Notation "'math->muldiv' '(!' a , b , c '!)'" := (do a' ← a; do b' ← b; do c' ← c; return! (intMulDiv a' b' c')) (at level 30, right associativity). 

Definition intMax (a b: XInteger) := xBoolIfElse (xIntLeb a b) b a. 
Notation "'math->max' '(!' a , b '!)'" := (do a' ← a; do b' ← b; return! (intMax a' b')) (at level 30, right associativity). 

Notation "'->selfdestruct' a" := (do a' ← a; ↓ selfdestruct a') (at level 20).

Unset Typeclasses Iterative Deepening. 
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
  return!! ( ↑3 D2! ProxyBase_ι_m_proxies [[  $ Л_roundId !% $xInt2 ]] ). 

Notation " i 'of' a '->sendMessage' f 'with' m" := (do a' ← a; 
                      do m' ← m; 
                      do f' ← f; 
                      sendMessage {| 
                      contractAddress := a'; 
                      contractFunction := f' ; 
                      contractMessage := m' 
                      |} ) (at level 30, right associativity, m at level 50, only parsing).	 

Notation " 'this->sendMessage' f 'with' m" := (
                      do m' ← m; 
                      do f' ← f; 
                      sendMessage {| 
                      contractAddress := xInt0 ;
                      contractFunction := f' ; 
                      contractMessage := m' 
                      |} ) (at level 30, right associativity, m at level 50, only parsing).	 

Notation " 'declareLocal' x ':>:' type ':=' a ';' t " := ( do a' ← a ; let x : type := a' in t ) (at level 33, left associativity, a at level 49, t at level 50, only parsing): solidity_scope.
Notation " 'declareLocal' x ':>:' type ';' t " := ( let x : type := default in t ) (at level 33, left associativity, t at level 50, only parsing): solidity_scope.
Notation " 'declareLocal' '{(' a ':>:' tya ',' b ':>:' tyb ')}' ':=' q ';' t " := (do q' ← q ; let a : tya := xProdFst q' in let b : tyb := xProdSnd q' in t)(at level 33, left associativity, t at level 50, only parsing): solidity_scope.
Notation " 'declareLocal' '{(' a ':>:' tya ',' b ':>:' tyb ',' c ':>:' tyc ')}' ':=' q ';' t " := (do q' ← q ; let a : tya := xProdFst ( xProdFst q' ) in let b : tyb := xProdSnd ( xProdFst q' ) in let c : tyc := xProdSnd q' in t)(at level 33, left associativity, t at level 50, only parsing): solidity_scope.
Notation " 'declareLocal' '{(' a ':>:' tya ',' b ':>:' tyb ',' c ':>:' tyc ',' d ':>:' tyd ')}' ':=' q ';' t " := (do q' ← q ; let a : tya := xProdFst ( xProdFst ( xProdFst q' ) ) in let b : tyb := xProdSnd ( xProdFst (xProdFst q') ) in let c : tyc := xProdSnd (xProdFst q') in let d : tyd := xProdSnd q' in t)(at level 33, left associativity, t at level 50, only parsing): solidity_scope.

Notation " 'declareLocal' x ':>:' type '?:=' a ';' t " := ( do a' ← a ?; let x : type := a' in t ) (at level 33, left associativity, a at level 49, t at level 50, only parsing): solidity_scope.
Notation " 'declareLocal' x ':>:' type '??:=' a ';' t " := ( do a' ← a ??; let x : type := a' in t ) (at level 33, left associativity, a at level 49, t at level 50, only parsing): solidity_scope.

Notation " 'declareLocal' '{(' a ':>:' tya ',' b ':>:' tyb ',' c ':>:' tyc ',' d ':>:' tyd ')}' '?:=' q ';' t " := (do q' ← q ?; let a : tya := xProdFst ( xProdFst ( xProdFst q' ) ) in let b : tyb := xProdSnd ( xProdFst (xProdFst q') ) in let c : tyc := xProdSnd (xProdFst q') in let d : tyd := xProdSnd q' in t)(at level 33, left associativity, t at level 50, only parsing): solidity_scope.

Notation " 'declareLocal' '{(' a ':>:' tya ',' b ':>:' tyb ',' c ':>:' tyc ')}' '??:=' q ';' t " := (do q' ← q ??; let a : tya := xProdFst ( xProdFst q' ) in let b : tyb := xProdSnd ( xProdFst q' ) in let c : tyc := xProdSnd q' in t)(at level 33, left associativity, t at level 50, only parsing): solidity_scope.
Notation " 'declareLocal' '{(' a ':>:' tya ',' b ':>:' tyb ',' c ':>:' tyc ',' d ':>:' tyd ')}' '??:=' q ';' t " := (do q' ← q ??; let a : tya := xProdFst ( xProdFst ( xProdFst q' ) ) in let b : tyb := xProdSnd ( xProdFst (xProdFst q') ) in let c : tyc := xProdSnd (xProdFst q') in let d : tyd := xProdSnd q' in t)(at level 33, left associativity, t at level 50, only parsing): solidity_scope.

Notation " 'declareLocal' d '::::' type ':=' a '->decode(uint256)' ; t " := ( let dec := decode_uint256 a in let d := xProdFst dec in let a := xProdSnd dec in t )( at level 33, left associativity , t at level 50, only parsing): solidity_scope.
Notation " 'declareLocal' d '::::' type ':=' a '->decode(uint64)' ; t " :=  ( let dec := decode_uint64  a in let d := xProdFst dec in let a := xProdSnd dec in t )( at level 33, left associativity , t at level 50, only parsing): solidity_scope.
Notation " 'declareLocal' d '::::' type ':=' a '->decode(uint32)' ; t " :=  ( let dec := decode_uint32  a in let d := xProdFst dec in let a := xProdSnd dec in t )( at level 33, left associativity , t at level 50, only parsing): solidity_scope.
Notation " 'declareLocal' d '::::' type ':=' a '->decode(uint8,uint32,uint32)' ; t " := ( let dec := decode_uint8_uint32_uint32 a in let d := xProdFst dec in let a := xProdSnd dec in t)( at level 33, left associativity, t at level 50, only parsing ): solidity_scope.

Notation " 'declareGlobal' x ':>:' type ';' t " := ( ( ↑17 U1! x := $ default ) >> t ) (at level 33, left associativity, only parsing): solidity_scope.
Notation " 'declareGlobal' x ':>:' type ':=' a " := ( ↑17 U1! x := a ) (at level 33, left associativity, a at level 49, only parsing): solidity_scope.
Notation " 'declareGlobal!' x ':>:' type ':=' a " := ( ↑↑17 U2! x := a ) (at level 33, left associativity, a at level 49, only parsing): solidity_scope.

Notation " 'declareInit' x := y " := ( ↑17 U1! x := y ) (at level 33, left associativity, y at level 49, only parsing): solidity_scope.


(* Notation " 'returns' '(' x ':>:' type1 , y ':>:' type2 ')' '([' f '])' " := ( 
declareLocal x :>: type1 ; declareLocal y :>: type2 ;
f >> return# ( $ x, $ y ))(at level 22, left associativity, only parsing ) : solidity_scope.  
 *)
(* Notation " 'returnsE' '(' x ':>:' type1 ',' y ':>:' type2 ',' z ':>:' type3 ')' ';' f " := ( 
declareLocal x :>: type1 ; declareLocal y :>: type2 ; declareLocal z :>: type3 ;
do _ ← f ?; return# ( $ x, $ y , $ z ))(at level 22, left associativity, f at level 50 , only parsing ) : solidity_scope.  
 *)

Notation " 'returns' '(' x ':>:' type1 , y ':>:' type2 ')' '>>' f " :=
( declareLocal x :>: type1 ; declareLocal y :>: type2 ; f )
(at level 22, left associativity, only parsing ) : solidity_scope. 

Notation " 'returns' '(' x ':>:' type1 ',' y ':>:' type2 ',' z ':>:' type3 ')' '>>' f " := 
( declareLocal x :>: type1 ; declareLocal y :>: type2 ; declareLocal z :>: type3 ; f )
(at level 22, left associativity, only parsing ) : solidity_scope. 

Notation " 'returns' '(' x ':>:' type1 ',' y ':>:' type2 ',' z ':>:' type3 ',' a ':>:' type4 ')' '>>' f " := 
( declareLocal x :>: type1 ; declareLocal y :>: type2 ; declareLocal z :>: type3 ; declareLocal a :>: type4 ; f )
(at level 22, left associativity, only parsing ) : solidity_scope. 

Notation " 'ς' x " := ( x )(at level 12, left associativity, only parsing ) : solidity_scope.

(* ξένος - alien *)
Notation " 'ξ' x " := ( x )(at level 12, left associativity, only parsing ) : solidity_scope. 

(* 
function _recoverStake(address proxy, uint64 requestId, address elector) internal { 
    IProxy(proxy).recover_stake{value: DePoolLib.ELECTOR_FEE + DePoolLib.PROXY_FEE}(requestId, elector); 
  } 
 *)  
Definition ProxyBase_Ф__recoverStake ( Л_proxy : XAddress )( Л_requestId : XInteger64 )( Л_elector : XAddress ) : LedgerT True := 
"IProxy" of ( $ Л_proxy ) ->sendMessage (DePoolProxyContract_Ф_recover_stakeF (!! $ Л_requestId , $ Л_elector !!)) with {|| messageValue ::= ξ $ DePoolLib_ι_ELECTOR_FEE !+ ξ $ DePoolLib_ι_PROXY_FEE ||} . 

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
Definition ProxyBase_Ф__sendElectionRequest ( Л_proxy : XAddress ) ( Л_requestId : XInteger64 ) ( Л_validatorStake : XInteger64 )( Л_req : ξ DePoolLib_ι_Request ) (Л_elector: XAddress) : LedgerT True := 
 "IProxy" of ( $ Л_proxy) ->sendMessage (DePoolProxyContract_Ф_process_new_stakeF (!! $ Л_requestId , 
   $ (Л_req ->> DePoolLib_ι_Request_ι_validatorKey) , 
   $ (Л_req ->> DePoolLib_ι_Request_ι_stakeAt) , 
   $ (Л_req ->> DePoolLib_ι_Request_ι_maxFactor) , 
   $ (Л_req ->> DePoolLib_ι_Request_ι_adnlAddr) , 
   $ (Л_req ->> DePoolLib_ι_Request_ι_signature) , 
   $ Л_elector !!) ) with {|| messageValue ::= $ Л_validatorStake !+ ξ$ DePoolLib_ι_ELECTOR_FEE !+ ξ$ DePoolLib_ι_PROXY_FEE ||}. 

(*  
function getCurValidatorData() virtual internal returns (uint256 hash, uint32 utime_since, uint32 utime_until) { 
    (TvmCell cell, bool ok) = tvm.rawConfigParam(34); 
    require(ok, InternalErrors.ERROR508); 
    hash = tvm.hash(cell); 
    TvmSlice s = cell.toSlice(); 
    (, utime_since, utime_until) = s.decode(uint8, uint32, uint32); 
  } 
 *)

Definition ConfigParamsBase_Ф_getCurValidatorData : LedgerT ( XErrorValue ( XInteger256 # XInteger32 # XInteger32 ) XInteger ) := 
returns ( Л_hash :>: XInteger256 , Л_utime_since :>: XInteger32 , Л_utime_until :>: XInteger32 ) >> 
	declareLocal {( Л_cell :>: TvmCell , Л_ok :>: XBool )} := tvm_rawConfigParam_34 () ; 
 	Require {{$ Л_ok , ξ$ InternalErrors_ι_ERROR508 }} ; 
 	U0! Л_hash := tvm_hash (!! $ Л_cell !!) ; 
  U0! Л_s := ( $ Л_cell) ->toSlice() ;  
  U0! Л_decoded := Л_s ->decode(uint8,uint32,uint32) ;
	U0! {( _ , Л_utime_since , Л_utime_until )} := $ Л_decoded ;
  ς return# ( $ Л_hash, $ Л_utime_since , $ Л_utime_until ). 

 
	(* return# ( $ Л_hash, $ Л_utime_since , $ Л_utime_until ).  *)
 

(* 
function getPrevValidatorHash() virtual internal returns (uint) { 
    (TvmCell cell, bool ok) = tvm.rawConfigParam(32); 
    require(ok, InternalErrors.ERROR507); 
    return tvm.hash(cell); 
  } 
 *) 
Definition ConfigParamsBase_Ф_getPrevValidatorHash : LedgerT ( XErrorValue XInteger XInteger ) := 
	declareLocal {( Л_cell :>: TvmCell , Л_ok :>: XBool )} := tvm_rawConfigParam_32 ; 
 	Require {{ $ Л_ok , ξ$ InternalErrors_ι_ERROR507 }} ; 
 	return!! ( tvm_hash (!! $ Л_cell !!) ). 
 

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
Definition ConfigParamsBase_Ф_roundTimeParams : LedgerT ( XErrorValue ( XInteger32 # XInteger32 # XInteger32 # XInteger32 ) XInteger ) := 
returns ( Л_validatorsElectedFor :>: XInteger32 , Л_electionsStartBefore :>: XInteger32 , Л_electionsEndBefore :>: XInteger32 , Л_stakeHeldFor :>: XInteger32 ) >>
<<<<<<< HEAD
declareLocal Л_ok :>: XBool ; 
U0! {( Л_validatorsElectedFor , Л_electionsStartBefore , Л_electionsEndBefore , Л_stakeHeldFor , Л_ok )} := tvm_configParam_15; 
=======
declareLocal Л_ok :>: XBool ;
  U0! {( Л_validatorsElectedFor , Л_electionsStartBefore , Л_electionsEndBefore , Л_stakeHeldFor , Л_ok )} := tvm_configParam_15; 
>>>>>>> 5c5e0757fc6242a2de005162d5c9b0c126a3de1c
  Require {{ $ Л_ok , ξ$ InternalErrors_ι_ERROR509 }} ; 
ς return# ( $ Л_validatorsElectedFor, $ Л_electionsStartBefore, $ Л_electionsEndBefore, $ Л_stakeHeldFor ). 
 

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
	declareLocal {( Л_cell :>: TvmCell , Л_ok :>: XBool )} := tvm_rawConfigParam_17; 
 	Require {{$ Л_ok , ξ$ InternalErrors_ι_ERROR516 }} ; 
 	declareLocal Л_s :>: TvmSlice := ( $ Л_cell ) ->toSlice() ; 
 	Л_s ->loadTons() ; 
 	Л_s ->loadTons() ; 
  Л_s ->loadTons() ; 
  U0! Л_decoded := Л_s ->decode(uint32) ; 
	  return! Л_decoded . 
	 
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
 declareLocal {( Л_cell :>: TvmCell , Л_ok :>: XBool )} := tvm_rawConfigParam_1 ; 
 Require {{ $ Л_ok , ξ$ InternalErrors_ι_ERROR517 }} ; 
 declareLocal Л_s :>: TvmSlice := ( $ Л_cell) ->toSlice() ; (* $ xInt0 . *)
 declareLocal Л_value :::: XInteger256 :=  Л_s ->decode(uint256)  ; 
 return!! ( address->makeAddrStd (! $xInt0 !- $ xInt1 , $ Л_value !) ). 
	 


(* 
function _setOrDeleteParticipant(address addr, DePoolLib.Participant participant) internal { 
    if (participant.roundQty == 0) 
      delete m_participants[addr]; 
    else 
      m_participants[addr] = participant; 
  } 
 *) 
Definition ParticipantBase_Ф__setOrDeleteParticipant ( Л_addr : XAddress ) ( Л_participant : ξ DePoolLib_ι_Participant ) : LedgerT True := 
 If ( $ (Л_participant ->> DePoolLib_ι_Participant_ι_roundQty) ?== $xInt0 ) then 
 { 
	↑5 U1! delete ParticipantBase_ι_m_participants [[ $ Л_addr ]] 
 } else 
 { 
	↑5 U1! ParticipantBase_ι_m_participants [[ $ Л_addr ]] := $ Л_participant 
 }. 

(* function getOrCreateParticipant(address addr) internal view returns (DePoolLib.Participant) { 
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
Definition ParticipantBase_Ф_getOrCreateParticipant' ( Л_addr : XAddress ) : LedgerT (XValueValue (ξ DePoolLib_ι_Participant)) := 
  declareLocal Л_optParticipant :>: ( XMaybe (ξ DePoolLib_ι_Participant) ) := ↑5 D1! (D2! ParticipantBase_ι_m_participants) ->fetch $ Л_addr ; 
  If! (( $ Л_optParticipant) ->hasValue ) then { 
   return!!! ( $ Л_optParticipant) ->get (* >>= _return (* fun x => return! (xError x) *)  *)
  }; 
  declareLocal Л_newParticipant :>: ξ DePoolLib_ι_Participant := {|| 
    DePoolLib_ι_Participant_ι_roundQty ::= $ xInt0 , 
    DePoolLib_ι_Participant_ι_reward ::= $ xInt0 , 
    DePoolLib_ι_Participant_ι_haveVesting ::= $ xBoolFalse , 
    DePoolLib_ι_Participant_ι_haveLock ::= $ xBoolFalse , 
    DePoolLib_ι_Participant_ι_reinvest ::= $ xBoolTrue , 
    DePoolLib_ι_Participant_ι_withdrawValue ::= $ xInt0 
  ||} ; 
    return! Л_newParticipant. 

Definition ParticipantBase_Ф_getOrCreateParticipant ( Л_addr : XAddress ) : LedgerT DePoolLib_ι_Participant := 
 do r ← ParticipantBase_Ф_getOrCreateParticipant' Л_addr; 
 return! (fromValueValue r). 

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

Definition DePoolProxyContract_Ф_constructor5 : LedgerT ( XErrorValue True XInteger ) := 
 ( declareGlobal LocalState_ι_constructor5_Л_ok :>: XBool := $ xBoolFalse) >> 
 ( ForIndexed (xListCons xInt0 (xListCons xInt1 xListNil)) do (fun (i: XInteger) => 
  declareLocal Л_b :>: TvmBuilder ; 
  U0! Л_b ->store msg_sender() $ i; 
  declareLocal Л_publicKey :>: XInteger256 := tvm_hash (!! $Л_b ->toCell !!); 
  (↑↑17 U2! LocalState_ι_constructor5_Л_ok := ((↑17 D2! LocalState_ι_constructor5_Л_ok) !| (tvm_pubkey () ?== $ Л_publicKey)) ) 
 )) >> 
 Require {{ ↑17 D2! LocalState_ι_constructor5_Л_ok , $ DePoolProxyContract_ι_ERROR_IS_NOT_DEPOOL }} ; 
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

    uint carry = msg.value - DePoolLib.PROXY_FEE; 
    require(address(this).balance >= carry + DePoolLib.MIN_PROXY_BALANCE, ERROR_BAD_BALANCE); 

    IElector(elector).process_new_stake{value: msg.value - DePoolLib.PROXY_FEE}( 
      queryId, validatorKey, stakeAt, maxFactor, adnlAddr, signature 
    ); 
  } 
 *) 
Definition DePoolProxyContract_Ф_process_new_stake ( Л_queryId : XInteger64 ) ( Л_validatorKey : XInteger256 ) ( Л_stakeAt : XInteger32 ) ( Л_maxFactor : XInteger32 ) ( Л_adnlAddr : XInteger256 ) ( Л_signature : XList XInteger8 ) ( Л_elector : XAddress ) : LedgerT ( XErrorValue True XInteger ) := 
 Require2 {{ msg_sender () ?== ↑ε10 DePoolProxyContract_ι_m_dePool , $ DePoolProxyContract_ι_ERROR_IS_NOT_DEPOOL }} ; 
 declareLocal Л_carry :>: XInteger := msg_value () !- ξ$ DePoolLib_ι_PROXY_FEE ; 
 Require {{ tvm_balance () ?>=  $Л_carry !+ ( ξ$ DePoolLib_ι_MIN_PROXY_BALANCE ) , $ DePoolProxyContract_ι_ERROR_BAD_BALANCE }} ; 
 IElector of ( $ Л_elector ) ->sendMessage ( IElector_И_process_new_stakeF (!! $ Л_queryId , $ Л_validatorKey , $ Л_stakeAt , $ Л_maxFactor , $ Л_adnlAddr , $ Л_signature !!) )
                with {|| messageValue ::= msg_value () !- ξ$ DePoolLib_ι_PROXY_FEE ||} .
(* 
function onStakeAccept(uint64 queryId, uint32 comment) public functionID(0xF374484C) { 
        IDePool(m_dePool).onStakeAccept{value: msg.value - DePoolLib.PROXY_FEE}(queryId, comment, msg.sender); 
  } 
 *) 
Definition DePoolProxyContract_Ф_onStakeAccept ( Л_queryId : XInteger64 )( Л_comment : XInteger32 ) : LedgerT True := 
  IDePool of ( ↑ε10 DePoolProxyContract_ι_m_dePool ) ->sendMessage ( DePoolContract_Ф_onStakeAcceptF (!! $ Л_queryId , $ Л_comment , ( msg_sender () ) !!) )
                with {|| messageValue ::= msg_value () !- ξ$ DePoolLib_ι_PROXY_FEE ||} .
 
(* 
function onStakeReject(uint64 queryId, uint32 comment) public functionID(0xEE6F454C) { 
    IDePool(m_dePool).onStakeReject{value: msg.value - DePoolLib.PROXY_FEE}(queryId, comment, msg.sender); 
  } 
 *) 
Definition DePoolProxyContract_Ф_onStakeReject ( Л_queryId : XInteger64 )( Л_comment : XInteger32 ) : LedgerT True := 
  IDePool of ( ↑ε10 DePoolProxyContract_ι_m_dePool ) ->sendMessage ( DePoolContract_Ф_onStakeRejectF (!! $ Л_queryId , $ Л_comment , ( msg_sender () ) !!) )
                with {|| messageValue ::= msg_value () !- ξ$ DePoolLib_ι_PROXY_FEE ||} .

(* 
function recover_stake(uint64 queryId, address elector) public override { 
require(msg.sender == m_dePool, ERROR_IS_NOT_DEPOOL); 

    uint carry = msg.value - DePoolLib.PROXY_FEE; 
    require(address(this).balance >= carry + DePoolLib.MIN_PROXY_BALANCE, ERROR_BAD_BALANCE); 

    IElector(elector).recover_stake{value: msg.value - DePoolLib.PROXY_FEE}(queryId); 
  } 
*) 
Definition DePoolProxyContract_Ф_recover_stake ( Л_queryId : XInteger64 ) ( Л_elector : XAddress ) : LedgerT ( XErrorValue True XInteger ) := 
 Require2 {{ msg_sender () ?== ↑ε10 DePoolProxyContract_ι_m_dePool , $ DePoolProxyContract_ι_ERROR_IS_NOT_DEPOOL }} ; 
 declareLocal Л_carry :>: XInteger := msg_value () !- ξ$ DePoolLib_ι_PROXY_FEE ; 
 Require {{ tvm_balance () ?>=  $Л_carry !+ ( ξ$ DePoolLib_ι_MIN_PROXY_BALANCE ) , 
        $ DePoolProxyContract_ι_ERROR_BAD_BALANCE }} ; 
 IElector of ( $ Л_elector ) ->sendMessage ( IElector_И_recover_stakeF (!! $ Л_queryId !!) )
                with {|| messageValue ::= msg_value () !- ξ$ DePoolLib_ι_PROXY_FEE ||} .
 
(* 
function onSuccessToRecoverStake(uint64 queryId) public functionID(0xF96F7324) { 
    IDePool(m_dePool).onSuccessToRecoverStake{value: msg.value - DePoolLib.PROXY_FEE}(queryId, msg.sender); 
  } 
*) 
Definition DePoolProxyContract_Ф_onSuccessToRecoverStake ( Л_queryId : XInteger64 ) : LedgerT True := 
  IDePool of ( ↑ε10 DePoolProxyContract_ι_m_dePool ) ->sendMessage ( DePoolContract_Ф_onSuccessToRecoverStakeF (!! $ Л_queryId , ( msg_sender () ) !!) )
                with {|| messageValue ::= msg_value () !- ξ$ DePoolLib_ι_PROXY_FEE ||} .

(* 
function getProxyInfo() public view returns (address depool, uint64 minBalance) { 
    depool = m_dePool; 
    minBalance = DePoolLib.MIN_PROXY_BALANCE; 
  } 
 *) 

Definition DePoolProxyContract_Ф_getProxyInfo : LedgerT ( XAddress # XInteger64 ) := 
returns ( Л_depool :>: XAddress , Л_minBalance :>: XInteger64 ) >>
 U0! Л_depool := ↑ε10 DePoolProxyContract_ι_m_dePool ; 
 U0! Л_minBalance := ξ$ DePoolLib_ι_MIN_PROXY_BALANCE ; 
ς return# ( $ Л_depool , $ Л_minBalance ) .

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
Definition RoundsBase_Ф__addStakes' (Л_round : RoundsBase_ι_Round ) (Л_participant : ξ DePoolLib_ι_Participant ) (Л_participantAddress: XAddress) (Л_stake: XInteger64) (Л_vesting: XMaybe RoundsBase_ι_InvestParams) (Л_lock: XMaybe RoundsBase_ι_InvestParams) : LedgerT (XValueValue ( RoundsBase_ι_Round # ( ξ DePoolLib_ι_Participant ) ) ) := 							  
 (* initialize local variables *) 						 
 ( declareInit LocalState_ι__addStakes_Л_round := $ Л_round ) >> 
 ( declareInit LocalState_ι__addStakes_Л_participant := $ Л_participant) >> 

 (* 
 if (stake == 0 && !vesting.hasValue() && !lock.hasValue()) { 
      return (round, participant); 
    } 
 *) 
 If! ( ( $ Л_stake ?== $ xInt0 ) !& ( !¬ ( $ Л_vesting ->hasValue) ) !& ( !¬ ( $ Л_lock ->hasValue) ) ) then { 
  return! (xError ( [( Л_round , Л_participant )] )) 
 } ; 	  
 (* 
 if (!round.stakes.exists(participantAddress)) { 
      round.participantQty++; 
      participant.roundQty++; 
    } 
 *) 
 ( If ( !¬ (D1! (↑17 D2! LocalState_ι__addStakes_Л_round ^^ RoundsBase_ι_Round_ι_stakes) ->exists $ Л_participantAddress) ) then { 
		(↑17 U1! LocalState_ι__addStakes_Л_round ^^ RoundsBase_ι_Round_ι_participantQty !++) >> 
		(↑17 U1! LocalState_ι__addStakes_Л_participant ^^ DePoolLib_ι_Participant_ι_roundQty !++) 
	} ) >> 
						 
 (*round.stake += stake; 
    StakeValue sv = round.stakes[participantAddress]; 
		sv.ordinary += stake;*) 			 
 ( ↑17 U1! LocalState_ι__addStakes_Л_round ^^ RoundsBase_ι_Round_ι_stake !+= $ Л_stake) >> 			 
 ( declareGlobal LocalState_ι__addStakes_Л_sv :>: RoundsBase_ι_StakeValue := D1! (D2! LocalState_ι__addStakes_Л_round ^^ RoundsBase_ι_Round_ι_stakes) [[ $ Л_participantAddress ]] ) >> 
 ( ↑17 U1! LocalState_ι__addStakes_Л_sv ^^ RoundsBase_ι_StakeValue_ι_ordinary !+= $ Л_stake) >> 

 (* 
 if (vesting.hasValue()) { 
      participant.haveVesting = true; 
     
        round.stake += vesting.get().amount; 
      
      sv.vesting = vesting; 
    } 
 *) 

 (If ( $ Л_vesting ->hasValue) then { 
	 
	(↑17 U1! LocalState_ι__addStakes_Л_participant ^^ DePoolLib_ι_Participant_ι_haveVesting := $ xBoolTrue ) >> 

	 (* (If (D1! ( $ Л_vesting ->get) ^^ RoundsBase_ι_InvestParams_ι_isActive) then { *) 
		(↑17 U1! LocalState_ι__addStakes_Л_round ^^ RoundsBase_ι_Round_ι_stake !+= (D1! ( $ Л_vesting ->get) ^^ RoundsBase_ι_InvestParams_ι_remainingAmount)) 
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

 (If ( $ Л_lock ->hasValue) then { 
	 
	(↑17 U1! LocalState_ι__addStakes_Л_participant ^^ DePoolLib_ι_Participant_ι_haveLock := $ xBoolTrue ) >> 

	(* (If (D1! ( $ Л_lock ->get) ^^ RoundsBase_ι_InvestParams_ι_isActive) then { *) 
		(↑17 U1! LocalState_ι__addStakes_Л_round ^^ RoundsBase_ι_Round_ι_stake !+= (D1! ( $ Л_lock ->get) ^^ RoundsBase_ι_InvestParams_ι_remainingAmount)) 
	 (* }) *) >> 

	 (↑17 U1! LocalState_ι__addStakes_Л_sv ^^ RoundsBase_ι_StakeValue_ι_lock := $ Л_lock) 
 }) >>		 

 (* round.stakes[participantAddress] = sv; *) 
 (↑17 U1! LocalState_ι__addStakes_Л_round ^^ RoundsBase_ι_Round_ι_stakes [[ $ Л_participantAddress ]] := D2! LocalState_ι__addStakes_Л_sv ) >> 

 return# ( ↑ε17 LocalState_ι__addStakes_Л_round , ↑ε17 LocalState_ι__addStakes_Л_participant).	 

Definition RoundsBase_Ф__addStakes (Л_round : RoundsBase_ι_Round ) 
                 (Л_participant : ξ DePoolLib_ι_Participant ) 
                 (Л_participantAddress: XAddress) 
                 (Л_stake: XInteger64) 
                 (Л_vesting: XMaybe RoundsBase_ι_InvestParams) 
                 (Л_lock: XMaybe RoundsBase_ι_InvestParams) 
              : LedgerT ( RoundsBase_ι_Round # ( ξ DePoolLib_ι_Participant ) )  := 							  
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
  declareLocal Л_v :>: ( XMaybe RoundsBase_ι_InvestParams ) := D0! Л_stakes ^^ RoundsBase_ι_StakeValue_ι_vesting ; 
  declareLocal Л_l :>: ( XMaybe RoundsBase_ι_InvestParams ):= D0! Л_stakes ^^ RoundsBase_ι_StakeValue_ι_lock ; 
  
  return!! ( D0! Л_stakes ^^ RoundsBase_ι_StakeValue_ι_ordinary !+ 
    ( (( $ Л_v ->hasValue ) ) ? ( D1! ( $ Л_v ->get ) ^^ RoundsBase_ι_InvestParams_ι_remainingAmount ) ::: $ xInt0 ) !+ 
    ( (( $ Л_l ->hasValue ) ) ? ( D1! ( $ Л_l ->get ) ^^ RoundsBase_ι_InvestParams_ι_remainingAmount ) ::: $ xInt0 ) ) . 


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
      Round,       uint64,       uint64,       DePoolLib.Participant,       DePoolLib.Participant     ) 
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
Definition RoundsBase_Ф_transferStakeInOneRound' ( Л_round : RoundsBase_ι_Round ) (Л_sourceParticipant: ξ DePoolLib_ι_Participant) (Л_destinationParticipant: ξ DePoolLib_ι_Participant) (Л_source : XAddress) (Л_destination: XAddress) (Л_amount: XInteger64) (Л_minStake : XInteger64) : LedgerT ( XValueValue ( RoundsBase_ι_Round # XInteger64 # XInteger64 # ( ξ DePoolLib_ι_Participant ) # ξ DePoolLib_ι_Participant) ) := 
  (*initialize pseudo locals*) 
  ( declareInit LocalState_ι_transferStakeInOneRound_Л_round := ( $ Л_round) ) >> 
  ( declareInit LocalState_ι_transferStakeInOneRound_Л_sourceParticipant := ( $ Л_sourceParticipant) ) >> 
  ( declareInit LocalState_ι_transferStakeInOneRound_Л_destinationParticipant := ( $ Л_destinationParticipant) ) >> 
  (* optional(StakeValue) optSourceStake = round.stakes.fetch(source); *) 
  declareLocal Л_optSourceStake :>: ( XMaybe RoundsBase_ι_StakeValue ) := D1! (D0! Л_round ^^ RoundsBase_ι_Round_ι_stakes) ->fetch ( $ Л_source) ; 
  (* if (!optSourceStake.hasValue()) 
    return (round, 0, 0, sourceParticipant, destinationParticipant); *) 
  If!! ( !¬ ( $ Л_optSourceStake ->hasValue) ) then { 
      return! (xError ( [( Л_round, xInt0, xInt0, Л_sourceParticipant, Л_destinationParticipant )] ) ) 
  } ; 				  
  (* StakeValue sourceStake = optSourceStake.get(); *) 
  ( declareGlobal LocalState_ι_transferStakeInOneRound_Л_sourceStake :>: RoundsBase_ι_StakeValue := ( $ Л_optSourceStake ->get) ) >> 
  (* uint64 prevSourceStake = round.stakes[source].ordinary; *) 
  declareLocal Л_prevSourceStake :>: XInteger64 := (D1! (D1! (D0! Л_round ^^ RoundsBase_ι_Round_ι_stakes) [[ $ Л_source ]] ) ^^ RoundsBase_ι_StakeValue_ι_ordinary ) ; 
  (* uint64 newSourceStake; *) 
  (* uint64 deltaDestinationStake; *) 
  
  (* if (sourceStake.ordinary >= amount) { 
    newSourceStake = sourceStake.ordinary - amount; 
    deltaDestinationStake = amount; 
  } else { 
    newSourceStake = 0; 
    deltaDestinationStake = sourceStake.ordinary; 
  } *)  
  declareGlobal LocalState_ι_transferStakeInOneRound_Л_newSourceStake :>: XInteger64 ;
  declareGlobal LocalState_ι_transferStakeInOneRound_Л_deltaDestinationStake :>: XInteger64 ;
  
  (If ( ↑17 D2! LocalState_ι_transferStakeInOneRound_Л_sourceStake ^^ RoundsBase_ι_StakeValue_ι_ordinary ?>= $ Л_amount) then { 

    (↑17 U1! LocalState_ι_transferStakeInOneRound_Л_newSourceStake := (D2! LocalState_ι_transferStakeInOneRound_Л_sourceStake ^^ RoundsBase_ι_StakeValue_ι_ordinary) !- ( $ Л_amount)) >> 
    (↑17 U1! LocalState_ι_transferStakeInOneRound_Л_deltaDestinationStake := ( $ Л_amount)) 
    
  } else { 
    
  (↑17 U1! LocalState_ι_transferStakeInOneRound_Л_newSourceStake := $ xInt0 ) >> 
  (↑17 U1! LocalState_ι_transferStakeInOneRound_Л_deltaDestinationStake := D2! LocalState_ι_transferStakeInOneRound_Л_sourceStake ^^ RoundsBase_ι_StakeValue_ι_ordinary) 

  }) >> 
  (* uint64 newDestStake = round.stakes[destination].ordinary + deltaDestinationStake; *) 
  declareLocal Л_newDestStake :>: XInteger64 := (D1! (D1! ( ↑17 D2! LocalState_ι_transferStakeInOneRound_Л_round ^^ RoundsBase_ι_Round_ι_stakes) [[ $ Л_destination ]] ) ^^ RoundsBase_ι_StakeValue_ι_ordinary) 
              !+ ( ↑ε17 LocalState_ι_transferStakeInOneRound_Л_deltaDestinationStake ); 


  (* if ((0 < newSourceStake && newSourceStake < minStake) || 
    (0 < newDestStake && newDestStake < minStake)) { 
    return (round, 0, prevSourceStake, sourceParticipant, destinationParticipant); 
  } *) 
  If! ((( $ xInt0 ?< (↑ε17 LocalState_ι_transferStakeInOneRound_Л_newSourceStake))!& 
    ((↑ε17 LocalState_ι_transferStakeInOneRound_Л_newSourceStake) ?< $ Л_minStake)) !| 
      (( $ xInt0 ?< $ Л_newDestStake) !& ( $ Л_newDestStake ?< $ Л_minStake) )) then { 
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
    (↑17 U1! LocalState_ι_transferStakeInOneRound_Л_round ^^ RoundsBase_ι_Round_ι_participantQty !--)  >> 
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
		 
Definition RoundsBase_Ф_transferStakeInOneRound ( Л_round : RoundsBase_ι_Round )(Л_sourceParticipant: ξ DePoolLib_ι_Participant) (Л_destinationParticipant: ξ DePoolLib_ι_Participant) (Л_source : XAddress) (Л_destination: XAddress) (Л_amount: XInteger64) (Л_minStake : XInteger64) : LedgerT ( RoundsBase_ι_Round # XInteger64 # XInteger64 # (ξ DePoolLib_ι_Participant) # ξ DePoolLib_ι_Participant) := 
do r ← 	RoundsBase_Ф_transferStakeInOneRound' Л_round Л_sourceParticipant Л_destinationParticipant Л_source Л_destination Л_amount Л_minStake ; 
return! (fromValueValue r). 


(* function isRoundPre0(uint64 id) internal inline returns (bool) { return id == m_roundQty - 1; } *) 
Definition RoundsBase_Ф_isRoundPre0 (Л_id: XInteger64) : LedgerT XBool := 
 return!! (  $ Л_id ?== (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt1 ). 
(* function isRound0(uint64 id)  internal inline returns (bool) { return id == m_roundQty - 2; } *) 
Definition RoundsBase_Ф_isRound0 (Л_id: XInteger64) : LedgerT XBool := 
 return!! (  $ Л_id ?== (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt2 ). 
(* function isRound1(uint64 id)  internal inline returns (bool) { return id == m_roundQty - 3; } *) 
Definition RoundsBase_Ф_isRound1 (Л_id: XInteger64) : LedgerT XBool := 
  return!! (  $ Л_id ?== (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt3 ). 
(* function isRound2(uint64 id)  internal inline returns (bool) { return id == m_roundQty - 4; } *) 
Definition RoundsBase_Ф_isRound2 (Л_id: XInteger64) : LedgerT XBool := 
  return!! (  $ Л_id ?== (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt4 ). 


(* function roundAt(uint64 id) internal returns (Round) { 
  return m_rounds.fetch(id).get(); 
} *) 
Definition RoundsBase_Ф_roundAt (Л_id: XInteger64) : LedgerT RoundsBase_ι_Round := 
  return!! (  (D1! (↑11 D2! RoundsBase_ι_m_rounds) ->fetch $ Л_id) ->get ). 
(* function getRoundPre0() internal inline returns (Round) { return roundAt(m_roundQty - 1); } *) 
Definition RoundsBase_Ф_getRoundPre0 : LedgerT RoundsBase_ι_Round := 
 return!! (  RoundsBase_Ф_roundAt (! (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt1 !) ). 
(* function getRound0()  internal inline returns (Round) { return roundAt(m_roundQty - 2); } *) 
Definition RoundsBase_Ф_getRound0 : LedgerT RoundsBase_ι_Round := 
 return!! (  RoundsBase_Ф_roundAt (! (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt2 !) ). 
(* function getRound1()  internal inline returns (Round) { return roundAt(m_roundQty - 3); } *) 
Definition RoundsBase_Ф_getRound1 : LedgerT RoundsBase_ι_Round := 
 return!! (  RoundsBase_Ф_roundAt (! (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt3 !) ). 
(* function getRound2()  internal inline returns (Round) { return roundAt(m_roundQty - 4); } *) 
Definition RoundsBase_Ф_getRound2 : LedgerT RoundsBase_ι_Round := 
 return!! (  RoundsBase_Ф_roundAt (! (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt4 !) ). 

(* function setRound(uint64 id, Round round) internal { 
  m_rounds[id] = round; 
} *) 
Definition RoundsBase_Ф_setRound (Л_id: XInteger) ( Л_round: RoundsBase_ι_Round) : LedgerT True := 
   ↑11 U1! RoundsBase_ι_m_rounds [[ $Л_id ]] := $Л_round. 
(* function setRoundPre0(Round r) internal inline { setRound(m_roundQty - 1, r); } *) 
Definition RoundsBase_Ф_setRoundPre0 ( Л_r: RoundsBase_ι_Round): LedgerT True := 
  RoundsBase_Ф_setRound (! (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt1 , $Л_r !). 
(* function setRound0(Round r)  internal inline { setRound(m_roundQty - 2, r); } *) 
Definition RoundsBase_Ф_setRound0 ( Л_r: RoundsBase_ι_Round): LedgerT True := 
  RoundsBase_Ф_setRound (! (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt2 , $Л_r !). 
(* function setRound1(Round r)  internal inline { setRound(m_roundQty - 3, r); } *) 
Definition RoundsBase_Ф_setRound1 ( Л_r: RoundsBase_ι_Round): LedgerT True := 
  RoundsBase_Ф_setRound (! (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt3 , $Л_r !). 
(* function setRound2(Round r)  internal inline { setRound(m_roundQty - 4, r); } *) 
Definition RoundsBase_Ф_setRound2 ( Л_r: RoundsBase_ι_Round): LedgerT True := 
  RoundsBase_Ф_setRound (! (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt4 , $Л_r !). 

(* 
function fetchRound(uint64 id) internal returns (optional(Round)) { 
  return m_rounds.fetch(id); 
} *) 
Definition RoundsBase_Ф_fetchRound (Л_id: XInteger64) : LedgerT (XMaybe RoundsBase_ι_Round) := 
 return!!  (D1! (↑11 D2! RoundsBase_ι_m_rounds) ->fetch $ Л_id) . 

(*contract ParticipantBase { 
  function fetchParticipant(address addr) internal view returns (optional(DePoolLib.Participant)) { 
    return m_participants.fetch(addr); 
  }*) 

Definition ParticipantBase_Ф_fetchParticipant (Л_addr: XAddress) : LedgerT (XMaybe (ξ DePoolLib_ι_Participant) ) := 
 return!!  (D1! (↑5 D2! ParticipantBase_ι_m_participants) ->fetch $ Л_addr) . 

(* function minRound() internal view returns(optional(uint64, Round)) { 
  return m_rounds.min(); 
} *) 

Definition RoundsBase_Ф_minRound : LedgerT (XMaybe (XInteger64 # RoundsBase_ι_Round)) := 
  return!! (D1! (↑11 D2! RoundsBase_ι_m_rounds) ->min) . 


(* function nextRound(uint64 id) internal view returns(optional(uint64, Round)) { 
  return m_rounds.next(id); 
} *) 
Definition RoundsBase_Ф_nextRound (Л_id: XInteger64) : LedgerT (XMaybe (XInteger64 # RoundsBase_ι_Round)) := 
  return!! (D1! (↑11 D2! RoundsBase_ι_m_rounds) ->next $ Л_id) . 

			 
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
Definition RoundsBase_Ф_withdrawStakeInPoolingRound' (Л_participant : ξ DePoolLib_ι_Participant ) (Л_participantAddress : XAddress) (Л_targetAmount : XInteger64) (Л_minStake : XInteger64) : LedgerT ( XValueValue (XInteger64 # ξ DePoolLib_ι_Participant) ) := 
  (*initialize pseudo locals*) 
  ( declareInit LocalState_ι_withdrawStakeInPoolingRound_Л_targetAmount := $ Л_targetAmount) >> 
  ( declareInit LocalState_ι_withdrawStakeInPoolingRound_Л_participant := $ Л_participant) >> 

  (* Round round = getRound0(); *) 
  ( declareGlobal! LocalState_ι_withdrawStakeInPoolingRound_Л_round :>: RoundsBase_ι_Round := RoundsBase_Ф_getRound0 () ) >> 
  (*optional(StakeValue) optSv = round.stakes.fetch(participantAddress);*) 
  declareLocal Л_optSv :>: ( XMaybe RoundsBase_ι_StakeValue ) := (D1! (↑17 D2! LocalState_ι_withdrawStakeInPoolingRound_Л_round ^^ RoundsBase_ι_Round_ι_stakes) ->fetch $ Л_participantAddress) ; 

  (*if (!optSv.hasValue()) { 
    return (0, participant); 
  }*) 
  If! ( !¬ ( $ Л_optSv) ->hasValue ) then { 
    return! (xError ( [( xInt0, Л_participant )] ) ) 
  } ; 

  (*StakeValue sv = optSv.get();*) 
  ( declareGlobal LocalState_ι_withdrawStakeInPoolingRound_Л_sv :>: RoundsBase_ι_StakeValue := ( $ Л_optSv) ->get) >> 
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
    (↑17 U1! LocalState_ι_withdrawStakeInPoolingRound_Л_round ^^ RoundsBase_ι_Round_ι_stake !-= D1! (ε LocalState_ι_withdrawStakeInPoolingRound_Л_sv) ^^ RoundsBase_ι_StakeValue_ι_ordinary) >> 
    (↑17 U1! LocalState_ι_withdrawStakeInPoolingRound_Л_targetAmount !+= D1! (ε LocalState_ι_withdrawStakeInPoolingRound_Л_sv) ^^ RoundsBase_ι_StakeValue_ι_ordinary) >> 
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
  (If (RoundsBase_Ф_stakeSum (! ↑ε17 LocalState_ι_withdrawStakeInPoolingRound_Л_sv !) ?== $xInt0 ) then { 
    (↑17 U1! LocalState_ι_withdrawStakeInPoolingRound_Л_round ^^ RoundsBase_ι_Round_ι_participantQty !--) >> 
    (↑17 U1! delete LocalState_ι_withdrawStakeInPoolingRound_Л_round ^^ RoundsBase_ι_Round_ι_stakes [[ $ Л_participantAddress ]] ) >> 
    (↑17 U1! LocalState_ι_withdrawStakeInPoolingRound_Л_participant ^^ DePoolLib_ι_Participant_ι_roundQty !--) 
  } else { 
    (↑17 U1! LocalState_ι_withdrawStakeInPoolingRound_Л_round ^^ RoundsBase_ι_Round_ι_stakes [[ $ Л_participantAddress ]] := ε LocalState_ι_withdrawStakeInPoolingRound_Л_sv) 
  }) >> 

  (*setRound0(round);*) 
  (RoundsBase_Ф_setRound0 (! ↑17 D2! LocalState_ι_withdrawStakeInPoolingRound_Л_round !)) >> 

  (*return (targetAmount, participant);*) 
  return# ( ↑ε17 LocalState_ι_withdrawStakeInPoolingRound_Л_targetAmount , ↑ε17 LocalState_ι_withdrawStakeInPoolingRound_Л_participant ). 

Definition RoundsBase_Ф_withdrawStakeInPoolingRound (Л_participant : ξ DePoolLib_ι_Participant ) (Л_participantAddress : XAddress) (Л_targetAmount : XInteger64) (Л_minStake : XInteger64) : LedgerT (XInteger64 # ξ DePoolLib_ι_Participant) := 
  do r ← RoundsBase_Ф_withdrawStakeInPoolingRound' Л_participant Л_participantAddress Л_targetAmount 	Л_minStake	; 
  return! (fromValueValue r).											 

(*                                                   WHY HERE NEED RETURNS???
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
return!! 
 {|| RoundsBase_ι_TruncatedRound_ι_id ::= $ Л_round ->> RoundsBase_ι_Round_ι_id , 
   RoundsBase_ι_TruncatedRound_ι_supposedElectedAt ::= $ Л_round ->> RoundsBase_ι_Round_ι_supposedElectedAt, 
   RoundsBase_ι_TruncatedRound_ι_unfreeze ::= $ Л_round ->> RoundsBase_ι_Round_ι_unfreeze , 
   RoundsBase_ι_TruncatedRound_ι_stakeHeldFor ::= $ Л_round ->> RoundsBase_ι_Round_ι_stakeHeldFor , 
   RoundsBase_ι_TruncatedRound_ι_vsetHashInElectionPhase ::= $ Л_round ->> RoundsBase_ι_Round_ι_vsetHashInElectionPhase , 
   RoundsBase_ι_TruncatedRound_ι_step ::= $ Л_round ->> RoundsBase_ι_Round_ι_step , 
   RoundsBase_ι_TruncatedRound_ι_completionReason ::= $ Л_round ->> RoundsBase_ι_Round_ι_completionReason , 
   RoundsBase_ι_TruncatedRound_ι_stake ::= $ Л_round ->> RoundsBase_ι_Round_ι_stake , 
   RoundsBase_ι_TruncatedRound_ι_recoveredStake ::= $ Л_round ->> RoundsBase_ι_Round_ι_recoveredStake , 
   RoundsBase_ι_TruncatedRound_ι_unused ::= $ Л_round ->> RoundsBase_ι_Round_ι_unused , 
   RoundsBase_ι_TruncatedRound_ι_isValidatorStakeCompleted ::= $ Л_round ->> RoundsBase_ι_Round_ι_isValidatorStakeCompleted , 
   RoundsBase_ι_TruncatedRound_ι_rewards ::= $ Л_round ->> RoundsBase_ι_Round_ι_rewards , 
   RoundsBase_ι_TruncatedRound_ι_participantQty ::= $ Л_round ->> RoundsBase_ι_Round_ι_participantQty , 
   RoundsBase_ι_TruncatedRound_ι_validatorStake ::= $ Л_round ->> RoundsBase_ι_Round_ι_validatorStake , 
   RoundsBase_ι_TruncatedRound_ι_validatorRemainingStake ::= $ Л_round ->> RoundsBase_ι_Round_ι_validatorRemainingStake , 
   RoundsBase_ι_TruncatedRound_ι_handledStakesAndRewards ::= $ Л_round ->> RoundsBase_ι_Round_ι_handledStakesAndRewards ||}. 


(* 
function getRounds() external view returns (mapping(uint64 => TruncatedRound)) { 
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
	( declareInit LocalState_ι_getRounds_Л_rounds := $ default ) >> 
	(*optional(uint64, Round) pair = m_rounds.min();*) 
	( declareGlobal! LocalState_ι_getRounds_Л_pair :>: ( XMaybe ( XInteger64 # RoundsBase_ι_Round ) ) := RoundsBase_Ф_minRound () ) >> 
	(*while (pair.hasValue()) { 
      (uint64 id, Round round) = pair.get(); 
      TruncatedRound r = toTruncatedRound(round); 
      rounds[r.id] = r; 
      pair = nextRound(id); 
    }*) 
	(While ((↑17 D2! LocalState_ι_getRounds_Л_pair) ->hasValue) do ( 
		declareLocal {( Л_id :>: XInteger64 , Л_round :>: RoundsBase_ι_Round )} := (↑17 D2! LocalState_ι_getRounds_Л_pair) ->get ; 
		declareLocal Л_r :>: RoundsBase_ι_TruncatedRound := RoundsBase_Ф_toTruncatedRound (! $ Л_round !) ; 
		(↑17 U1! LocalState_ι_getRounds_Л_rounds [[ $ (Л_r ->> RoundsBase_ι_TruncatedRound_ι_id ) ]] := $ Л_r) >> 
		(↑↑17 U2! LocalState_ι_getRounds_Л_pair := RoundsBase_Ф_nextRound (! $ Л_id !) ) >> 
		continue! I 
	)) >> 
	(*return rounds;*) 
	return!! ( ↑17 D2! LocalState_ι_getRounds_Л_rounds ). 

(* 
function generateRound() internal returns (Round) { 
    Request req; 
    Round r = Round({ 
      id: m_roundQty, 
      supposedElectedAt: 0,       
      unfreeze: DePoolLib.MAX_TIME,       
      stakeHeldFor: 0, 
      validatorsElectedFor: 0, 
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
      elector: address(0),       proxy: getProxy(m_roundQty) 
    }); 
    ++m_roundQty; 
    return r; 
  } 
*) 
Definition DePoolContract_Ф_generateRound : LedgerT RoundsBase_ι_Round := 
	declareLocal Л_req :>: DePoolLib_ι_Request ; 
	declareLocal Л_r :>: RoundsBase_ι_Round := {|| 
				 (*id: m_roundQty,*) 
				 RoundsBase_ι_Round_ι_id ::= ↑11 D2! RoundsBase_ι_m_roundQty , 
				 (*supposedElectedAt: 0*) 
				 RoundsBase_ι_Round_ι_supposedElectedAt ::= $ xInt0 , 
				 (*unfreeze: DePoolLib.MAX_TIME*) 
				 RoundsBase_ι_Round_ι_unfreeze ::= ξ$ DePoolLib_ι_MAX_TIME , 
         (* stakeHeldFor: 0, *)           
         RoundsBase_ι_Round_ι_stakeHeldFor ::= $ xInt0 , 
				 (* vsetHashInElectionPhase: 0 *) 
				 RoundsBase_ι_Round_ι_vsetHashInElectionPhase ::= $ xInt0 , 
				 (* step: RoundStep.Pooling, *) 
				 RoundsBase_ι_Round_ι_step ::= $ RoundsBase_ι_RoundStepP_ι_PrePooling , 
				 (*completionReason: CompletionReason.Undefined*) 
         RoundsBase_ι_Round_ι_completionReason ::= ξ$ RoundsBase_ι_CompletionReasonP_ι_Undefined , 
				 (* stake: 0, *) 
				 RoundsBase_ι_Round_ι_stake ::= $ xInt0 , 
         (* recoveredStake: 0, *)         
         RoundsBase_ι_Round_ι_recoveredStake ::= $ xInt0 , 
				 (* unused: 0, *) 
				 RoundsBase_ι_Round_ι_unused ::= $ xInt0 , 
         (* isValidatorStakeCompleted: false, *) 
         RoundsBase_ι_Round_ι_isValidatorStakeCompleted ::= $ xBoolFalse , 
         (* grossReward: 0, *) 
         RoundsBase_ι_Round_ι_grossReward ::= $ xInt0 , 
         (* rewards: 0, *) 
				 RoundsBase_ι_Round_ι_rewards ::= $ xInt0 , 
				 (* participantQty : 0, *) 
				 RoundsBase_ι_Round_ι_participantQty ::= $ xInt0 , 
         RoundsBase_ι_Round_ι_stakes ::= $ default , 
         (* validatorStake: 0,        
           validatorRemainingStake: 0,    
           handledStakesAndRewards: 0,  *)  
         RoundsBase_ι_Round_ι_validatorStake ::= $ xInt0 , 
         RoundsBase_ι_Round_ι_validatorRemainingStake ::= $ xInt0 , 
         RoundsBase_ι_Round_ι_handledStakesAndRewards ::= $ xInt0 , 
				 (* validatorRequest: req, *) 
				 RoundsBase_ι_Round_ι_validatorRequest ::= $ Л_req , 
				 (* elector: address(0), *) 
				 RoundsBase_ι_Round_ι_elector ::= $ xInt0 , 
				 (* proxy: getProxy(m_roundQty), *) 
				 RoundsBase_ι_Round_ι_proxy ::= ( ProxyBase_Ф_getProxy (! ↑11 D2! RoundsBase_ι_m_roundQty !) ) , 
         (* validatorsElectedFor: 0, *) 
         RoundsBase_ι_Round_ι_validatorsElectedFor ::= $ xInt0 
	       ||} ; 
	(↑11 U1! RoundsBase_ι_m_roundQty !++) >> 
return! Л_r. 
	 
(* 
constructor( 
    uint64 minStake, 
    uint64 validatorAssurance, 
    TvmCell proxyCode, 
    address validatorWallet, 
    uint8 participantRewardFraction, 
    (* uint64 balanceThreshold *) 
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
    require(participantRewardFraction > 0 && participantRewardFraction < 100, Errors.BAD_PART_REWARD); 
    uint8 validatorRewardFraction = 100 - participantRewardFraction; 
(* require(balanceThreshold >= CRITICAL_THRESHOLD, Errors.BAD_BALANCE_THRESHOLD); *) 

(* require(address(this).balance >= *) 
    require(address(this).balance > 
(* balanceThreshold + *) CRITICAL_THRESHOLD + 
          DePoolLib.DEPOOL_CONSTRUCTOR_FEE + 
          2 * (DePoolLib.MIN_PROXY_BALANCE + DePoolLib.PROXY_CONSTRUCTOR_FEE), 
        Errors.BAD_ACCOUNT_BALANCE);                      (*<<<<<<<<<<<<<<<<<<<*) 

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

Notation " 'initial' x " := ( x ) (at level 71, left associativity, only parsing ) : solidity_scope.
Notation " 'New' x " := ( x ) (at level 71, left associativity, only parsing ) : solidity_scope. 

(* address proxy = 
      new DePoolProxyContract{ 
        wid: -1, 
        value: DePoolLib.MIN_PROXY_BALANCE + DePoolLib.PROXY_CONSTRUCTOR_FEE, 
        stateInit: stateInit 
      }();  *)

(* Notation "  zhopa var '=' 'new DePoolProxyContract' '{' 'wid' ':' wid ',' 'value' ':' value ',' 'stateInit' ':' stateInit '}' " :=
( ↓ tvm_newE DePoolProxyContractD ( {|| cmessage_wid ::= wid , 
                   cmessage_value ::= value , 
                   cmessage_stateInit ::= stateInit ||} ) 
                   DePoolProxyContract_Ф_constructor5 >>= 
      fun ea => xErrorMapDefaultF (fun a => (↑17 U1! var := $ a) >> continue! (xValue I)) 
          ea (fun er => break! (xError er)) ?>>                       
  ( (↑↑3 U2! ProxyBase_ι_m_proxies push (↑17 D2! var) ) >> continue! (xValue I) ) )
(at level 71, left associativity, only parsing ) : solidity_scope. *)

Definition DePoolContract_Ф_Constructor6 ( Л_minStake : XInteger64 ) ( Л_validatorAssurance : XInteger64 ) ( Л_proxyCode : TvmCell ) ( Л_validatorWallet : XAddress ) ( Л_participantRewardFraction : XInteger8 ) : LedgerT ( XErrorValue True XInteger ) := 
    (* ValidatorBase(validatorWallet)  *)
  New ValidatorBase_Ф_Constructor2 (! $ Л_validatorWallet !) >> 

  initial ( ↑11 U1! RoundsBase_ι_m_roundQty := $ xInt0 ) >>
  (* require(address(this).wid == 0, Errors.NOT_WORKCHAIN0); *) 
  Require2 {{ tvm_address ->wid ?== $ xInt0, ξ$ Errors_ι_NOT_WORKCHAIN0 }} ; 
  (*require(msg.pubkey() == tvm.pubkey(), Errors.IS_NOT_OWNER);*) 
  Require2 {{ msg_pubkey () ?== tvm_pubkey () ,  ξ$ Errors_ι_IS_NOT_OWNER }} ; 

  (*require(tvm.pubkey() != 0, Errors.CONSTRUCTOR_NO_PUBKEY);*) 
  Require2 {{ tvm_pubkey () ?!= $ xInt0 , ξ$ Errors_ι_CONSTRUCTOR_NO_PUBKEY }} ; 

  (*require(minStake >= 1 ton, Errors.BAD_STAKES);*) 
  Require2 {{$ Л_minStake ?>= $ x1_ton , ξ$ Errors_ι_BAD_STAKES }} ; 

  (*require(minStake <= validatorAssurance, Errors.BAD_STAKES);*) 
  Require2 {{$ Л_minStake ?<= $ Л_validatorAssurance , ξ$ Errors_ι_BAD_STAKES }} ; 
   
  (* require(tvm.hash(proxyCode) == PROXY_CODE_HASH, Errors.BAD_PROXY_CODE); *) 
  Require2 {{ tvm_hash (!! $ Л_proxyCode !!) ?== ξ$ DePool_ι_PROXY_CODE_HASH , 
                          $ Errors_ι_BAD_PROXY_CODE }} ; 

  (*require(validatorWallet.isStdAddrWithoutAnyCast(), Errors.VALIDATOR_IS_NOT_STD);*) 
  Require2 {{ ( $ Л_validatorWallet) ->isStdAddrWithoutAnyCast() , ξ$ Errors_ι_VALIDATOR_IS_NOT_STD }} ; 

  (* require(participantRewardFraction > 0 && participantRewardFraction < 100, Errors.BAD_PART_REWARD); 
  uint8 validatorRewardFraction = 100 - participantRewardFraction; *) 
  Require2 {{ ( ( $ Л_participantRewardFraction ) ?> $ xInt0 ) !& 
        ( ( $ Л_participantRewardFraction ) ?< $ xInt100 ) , ξ$ Errors_ι_BAD_PART_REWARD }} ; 
  declareLocal Л_validatorRewardFraction :>: XInteger8 := $ xInt100 !- $ Л_participantRewardFraction ; 
  (* Require2 {{$ Л_balanceThreshold ?>= ( ↑ε12 DePoolContract_ι_CRITICAL_THRESHOLD ) , ↑ε7 Errors_ι_BAD_BALANCE_THRESHOLD }} ;*) 
  (* require(address(this).balance > 
      CRITICAL_THRESHOLD + 
        DePoolLib.DEPOOL_CONSTRUCTOR_FEE + 
            2 * (DePoolLib.MIN_PROXY_BALANCE + DePoolLib.PROXY_CONSTRUCTOR_FEE), 
                                                        Errors.BAD_ACCOUNT_BALANCE);*) 
  Require2 {{ tvm_balance () ?> ( $ DePool_ι_CRITICAL_THRESHOLD !+ 
                 ( ξ$ DePoolLib_ι_DEPOOL_CONSTRUCTOR_FEE ) !+ 
                  $ xInt2 !* ( ξ$ DePoolLib_ι_MIN_PROXY_BALANCE !+ 
             ξ$ DePoolLib_ι_PROXY_CONSTRUCTOR_FEE ) ) , ξ$ Errors_ι_BAD_ACCOUNT_BALANCE }} ; 
  (*tvm.accept();*) 
  tvm_accept () >> 
  (* for (uint8 i = 0; i < 2; ++i) { 
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

  do _ ← ( ForIndexedE (xListCons xInt0 (xListCons xInt1 xListNil)) do ( fun (i: XInteger) => 
  declareLocal Л_b :>: TvmBuilder ; 
  U0! Л_b ->store tvm_address $ i; 
  declareLocal Л_publicKey :>: XInteger256 := tvm_hash (!! ( $ Л_b ) ->toCell !!); 
  declareLocal Л_data :>: TvmCell := tvm_buildEmptyData (!! $ Л_publicKey !!); 
  declareLocal Л_stateInit :>: TvmCell := tvm_buildStateInit (!!  $ Л_proxyCode ,  $ Л_data !!); 

  declareGlobal LocalState_ι_constructor6_Л_proxy :>: XAddress ; 

 (* LocalState_ι_constructor6_Л_proxy = new DePoolProxyContract { wid : $ xInt0 !- $ xInt1 , value : ξ$ DePoolLib_ι_MIN_PROXY_BALANCE !+ ξ$ DePoolLib_ι_PROXY_CONSTRUCTOR_FEE , stateInit : $ Л_stateInit } *)

  tvm_newE DePoolProxyContractD ( {|| cmessage_wid ::= $ xInt0 !- $ xInt1 , 
                   cmessage_value ::= ξ$ DePoolLib_ι_MIN_PROXY_BALANCE !+ 
                     ξ$ DePoolLib_ι_PROXY_CONSTRUCTOR_FEE , 
                   cmessage_stateInit ::= $ Л_stateInit ||} ) DePoolProxyContract_Ф_constructor5 >>= 
      fun ea => xErrorMapDefaultF (fun a => (↑17 U1! LocalState_ι_constructor6_Л_proxy := $ a) >> continue! (xValue I)) 
                          ea 
                          (fun er => break! (xError er)) ?>>                       
  (  (↑↑3 U2! ProxyBase_ι_m_proxies push (↑17 D2! LocalState_ι_constructor6_Л_proxy)) >> 
    continue! (xValue I))                 
   ) >>= fun r => return! (xProdSnd r) ) ??; 

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

 (* m_balanceThreshold = balanceThreshold; *) 
(* (↑12 U1! DePoolContract_ι_m_balanceThreshold := $ Л_balanceThreshold) >> *) 

(*(, uint32 electionsStartBefore, ,) = roundTimeParams();*) 
declareLocal {( _ :>: _ , Л_electionsStartBefore :>: XInteger32 , _ :>: _ , _ :>: _ )} ??:= ConfigParamsBase_Ф_roundTimeParams () ; 

(*(uint256 curValidatorHash, , uint32 validationEnd) = getCurValidatorData();*) 
declareLocal {( Л_curValidatorHash :>: XInteger256, _ :>: _ , Л_validationEnd :>: XInteger32 )} ??:= ConfigParamsBase_Ф_getCurValidatorData () ; 

(* uint256 prevValidatorHash = getPrevValidatorHash(); *) 
declareLocal Л_prevValidatorHash :>: XInteger256 ?:= ConfigParamsBase_Ф_getPrevValidatorHash () ; 

(*bool areElectionsStarted = now >= validationEnd - electionsStartBefore;*) 
declareLocal Л_areElectionsStarted :>: XBool := tvm_now () ?>= $ Л_validationEnd !- $ Л_electionsStartBefore ; 

(*Round r2 = generateRound();*) 	 
declareLocal Л_r2 :>: RoundsBase_ι_Round := DePoolContract_Ф_generateRound () ; 
(* Round r1 = generateRound(); *) 
declareLocal Л_r1 :>: RoundsBase_ι_Round := DePoolContract_Ф_generateRound () ; 
(* Round r0 = generateRound(); *) 
declareLocal Л_r0  :>: RoundsBase_ι_Round := DePoolContract_Ф_generateRound () ; 
(* r0.step = RoundStep.Pooling; *) 
U0! Л_r0 ^^ RoundsBase_ι_Round_ι_step := $ RoundsBase_ι_RoundStepP_ι_Pooling ; 
(* Round preR0 = generateRound(); *) 
declareLocal Л_preR0  :>: RoundsBase_ι_Round := DePoolContract_Ф_generateRound () ; 


(* (r2.step, r2.completionReason, r2.unfreeze) = (RoundStep.Completed, CompletionReason.FakeRound, 0);*) 
U0! {( Л_r2 ^^ RoundsBase_ι_Round_ι_step , Л_r2 ^^ RoundsBase_ι_Round_ι_completionReason , Л_r2 ^^ RoundsBase_ι_Round_ι_unfreeze )} := 
   $ [( RoundsBase_ι_RoundStepP_ι_Completed, RoundsBase_ι_CompletionReasonP_ι_FakeRound, xInt0 )] ; 
(* (r1.step, r1.completionReason, r1.unfreeze) = (RoundStep.WaitingUnfreeze, CompletionReason.FakeRound, 0); *) 
U0! {( Л_r1 ^^ RoundsBase_ι_Round_ι_step , Л_r1 ^^ RoundsBase_ι_Round_ι_completionReason , Л_r1 ^^ RoundsBase_ι_Round_ι_unfreeze )} := 
   $ [( RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze, RoundsBase_ι_CompletionReasonP_ι_FakeRound, xInt0 )] ; 
(*r1.vsetHashInElectionPhase = areElectionsStarted ? curValidatorHash : prevValidatorHash;*) 
U0! Л_r1 ^^ RoundsBase_ι_Round_ι_vsetHashInElectionPhase := $ Л_areElectionsStarted ? $ Л_curValidatorHash ::: $ Л_prevValidatorHash; 

(* setRound(preR0.id, preR0); *) 
RoundsBase_Ф_setRound (! $ (Л_preR0 ->> RoundsBase_ι_Round_ι_id) ,  $Л_preR0 !) >> 
(* setRound(r0.id, r0); *) 
RoundsBase_Ф_setRound (! $ (Л_r0 ->> RoundsBase_ι_Round_ι_id) ,  $Л_r0 !) >> 
(* setRound(r1.id, r1); *) 
RoundsBase_Ф_setRound (! $ (Л_r1 ->> RoundsBase_ι_Round_ι_id) ,  $Л_r1 !) >> 
(* setRound(r2.id, r2); *) 
RoundsBase_Ф_setRound (! $ (Л_r2 ->> RoundsBase_ι_Round_ι_id) ,  $Л_r2 !) .

(* 
function setLastRoundInfo(Round round) internal { 
>     LastRoundInfo info = LastRoundInfo({ 
>       supposedElectedAt: round.supposedElectedAt, 
>       participantRewardFraction: m_participantRewardFraction, 
>       validatorRewardFraction: m_validatorRewardFraction, 
>       participantQty: round.participantQty, 
>       roundStake: round.stake, 
>       validatorWallet: m_validatorWallet, 
>       validatorPubkey: tvm.pubkey(), 
>       validatorAssurance: m_validatorAssurance, 
>       reward: round.grossReward, 
>       reason: uint8(round.completionReason), 
>       isDePoolClosed: m_poolClosed 
>     }); 
>     lastRoundInfo[false] = info; 
>   } *) 

Definition DePoolContract_Ф_setLastRoundInfo ( Л_round : RoundsBase_ι_Round ) : LedgerT True := 
declareLocal Л_info :>: DePool_ι_LastRoundInfo := {|| 
   DePool_ι_LastRoundInfo_ι_supposedElectedAt ::=     $ Л_round ->> RoundsBase_ι_Round_ι_supposedElectedAt , 
   DePool_ι_LastRoundInfo_ι_participantRewardFraction ::= ( ↑12 D2! DePoolContract_ι_m_participantRewardFraction ) , 
   DePool_ι_LastRoundInfo_ι_validatorRewardFraction ::=  ( ↑12 D2! DePoolContract_ι_m_validatorRewardFraction ) , 
   DePool_ι_LastRoundInfo_ι_participantQty ::=       $ Л_round ->> RoundsBase_ι_Round_ι_participantQty , 
   DePool_ι_LastRoundInfo_ι_roundStake ::=         $ Л_round ->> RoundsBase_ι_Round_ι_stake , 
   DePool_ι_LastRoundInfo_ι_validatorWallet ::=      ( ↑2 D2! ValidatorBase_ι_m_validatorWallet ) , 
   DePool_ι_LastRoundInfo_ι_validatorPubkey ::=      tvm_pubkey () , 
   DePool_ι_LastRoundInfo_ι_validatorAssurance ::=    ( ↑12 D2! DePoolContract_ι_m_validatorAssurance ) , 
   DePool_ι_LastRoundInfo_ι_reward ::=           $ Л_round ->> RoundsBase_ι_Round_ι_grossReward , 
   DePool_ι_LastRoundInfo_ι_reason ::=           $ Л_round ->> RoundsBase_ι_Round_ι_completionReason , 
   DePool_ι_LastRoundInfo_ι_isDePoolClosed ::=      ( ↑12 D2! DePoolContract_ι_m_poolClosed ) 
||} ; 
↑11 U1! RoundsBase_ι_lastRoundInfo [[ $ xBoolFalse ]] := $ Л_info . 

(* ↑5 U1! ParticipantBase_ι_m_participants [[ $ Л_addr ]] := $ Л_participant *) 
(* 
function _returnChange() private pure { 
    msg.sender.transfer(0, false, 64); 
  } 
*) 
Definition DePoolContract_Ф__returnChange : LedgerT True := 
  ( ( msg_sender () ) ->transfer (! $ xInt0 ,  $ xBoolFalse ,  $ xInt64 !) ) . 


(* 
function DePoolContract._sendError(uint32 errcode, uint64 comment) private { 
    IParticipant(msg.sender).receiveAnswer{value:0, bounce: false, flag: 64}(errcode, comment); 
  } *) 

Definition DePoolContract_Ф__sendError ( Л_errcode : XInteger32 ) ( Л_comment : XInteger64 ) : LedgerT True := 
IParticipant of (msg_sender ()) ->sendMessage ( IParticipant_И_receiveAnswerF (!! $ Л_errcode , $ Л_comment !!) )
with {|| messageValue ::= $ xInt0 , messageBounce ::= $ xBoolFalse , messageFlag ::= $ xInt64 ||} .

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
( declareInit LocalState_ι_startRoundCompleting_Л_round := $ Л_round ) >> 
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
            := ξ$ RoundsBase_ι_RoundStepP_ι_Completed ) >> 
        (* this.ticktock{value: VALUE_FOR_SELF_CALL, bounce: false}(); *) 
 this->sendMessage ( $ DePoolContract_Ф_ticktockF ) with {|| messageValue ::= $ DePool_ι_VALUE_FOR_SELF_CALL , messageBounce ::= $ xBoolFalse ||}
} 
else { 
        (* round.step = RoundStep.Completing; *) 
 ( ↑17 U1! LocalState_ι_startRoundCompleting_Л_round ^^ RoundsBase_ι_Round_ι_step 
            := ξ$ RoundsBase_ι_RoundStepP_ι_Completing ) >> 
        (* this.completeRound{flag: 1, bounce: false, value: VALUE_FOR_SELF_CALL}(round.id, round.participantQty); *) 
 ( this->sendMessage ( DePoolContract_Ф_completeRoundF (!! 
   ( ↑17 D1! ( D2! LocalState_ι_startRoundCompleting_Л_round ) ^^ RoundsBase_ι_Round_ι_id ) , 
   ( ↑17 D1! ( D2! LocalState_ι_startRoundCompleting_Л_round ) ^^ RoundsBase_ι_Round_ι_participantQty ) !!) ) 
       with {|| messageValue ::= $ DePool_ι_VALUE_FOR_SELF_CALL , 
            messageBounce ::= $ xBoolFalse , 
            messageFlag  ::= $ xInt1 ||} ) 
} ) >> 
        (* emit RoundCompleted(toTruncatedRound(round)); *) 
(->emit (RoundCompleted (!! RoundsBase_Ф_toTruncatedRound (! ↑ε17 LocalState_ι_startRoundCompleting_Л_round !) !!))) >> 
     (* setLastRoundInfo(round); *) 
   DePoolContract_Ф_setLastRoundInfo (! ↑ε17 LocalState_ι_startRoundCompleting_Л_round !) >> 
        (* return round; *) 
 return!! ( ↑ε17 LocalState_ι_startRoundCompleting_Л_round ) . 

(*   
    function cutWithdrawalValue(InvestParams p, bool doPunish, uint32 punishInterval) 
>     private 
>     returns (optional(InvestParams), uint64, uint64) 
>   { 
>     uint64 withdrawalTons = 0; 
>     uint64 tonsForOwner = 0; 
>     if (doPunish) { 
>       p.lastWithdrawalTime += punishInterval; 
>       tonsForOwner = math.muldiv(punishInterval, p.withdrawalValue, p.withdrawalPeriod); 
>       tonsForOwner = math.min(tonsForOwner, p.remainingAmount); 
>       p.remainingAmount -= tonsForOwner; 
>     } 
> 
>     if (uint64(now) > p.lastWithdrawalTime) { 
>       uint64 periodQty = (uint64(now) - p.lastWithdrawalTime) / p.withdrawalPeriod; 
>       if (periodQty > 0) { 
>         withdrawalTons = math.min(periodQty * p.withdrawalValue, p.remainingAmount); 
>         p.remainingAmount -= withdrawalTons; 
>         p.lastWithdrawalTime += periodQty * p.withdrawalPeriod; 
>       } 
    } 
                 (* p.lastWithdrawalTime += periodQty * p.withdrawalPeriod; *) 

>     if (p.remainingAmount < m_minStake) { 
>       withdrawalTons += p.remainingAmount; 
>       p.remainingAmount = 0; 
>     } 
    optional(InvestParams) opt; 
    opt.set(p); 
    return (opt, withdrawalTons, tonsForOwner); 
  } 
*) 

Unset Typeclasses Iterative Deepening. 
Set Typeclasses Depth 10. 

(* function cutWithdrawalValue(InvestParams p, bool doPunish, uint32 punishInterval) *) 
Definition DePoolContract_Ф_cutWithdrawalValue ( Л_p : RoundsBase_ι_InvestParams ) 
                                               ( Л_doPunish : XBool) 
                                               (Л_punishInterval : XInteger32) 
                  : LedgerT ( (XMaybe RoundsBase_ι_InvestParams) # XInteger64 # XInteger64 ) := 
 ( declareInit LocalState_ι_cutWithdrawalValue_Л_p := $ Л_p ) >> 
     (* uint64 withdrawalTons = 0; 
      uint64 tonsForOwner = 0; *) 
 ( declareGlobal LocalState_ι_cutWithdrawalValue_Л_withdrawalTons :>: XInteger64 := $ xInt0 ) >> 
 ( declareGlobal LocalState_ι_cutWithdrawalValue_Л_tonsForOwner :>: XInteger64 := $ xInt0 ) >> 
       (* if (doPunish) { 
       >       p.lastWithdrawalTime += punishInterval; 
       >       tonsForOwner = math.muldiv(punishInterval, p.withdrawalValue, p.withdrawalPeriod); 
       >       tonsForOwner = math.min(tonsForOwner, p.remainingAmount); 
       >       p.remainingAmount -= tonsForOwner; 
       >     } *) 
  ( If ( $ Л_doPunish ) 
   then { 
    ( ↑17 U1! LocalState_ι_cutWithdrawalValue_Л_p ^^ 
          RoundsBase_ι_InvestParams_ι_lastWithdrawalTime 
                        !+= $ Л_punishInterval ) >> 
    ( ↑17 U1! LocalState_ι_cutWithdrawalValue_Л_tonsForOwner := 
      math->muldiv (! $ Л_punishInterval , D1! ( D2! LocalState_ι_cutWithdrawalValue_Л_p) 
                          ^^ RoundsBase_ι_InvestParams_ι_withdrawalValue , 
                        D1! ( D2! LocalState_ι_cutWithdrawalValue_Л_p) 
                          ^^ RoundsBase_ι_InvestParams_ι_withdrawalPeriod !) ) >> 
    ( ↑17 U1! LocalState_ι_cutWithdrawalValue_Л_tonsForOwner := 
      math->min2 (! ε LocalState_ι_cutWithdrawalValue_Л_tonsForOwner , 
               D1! ( D2! LocalState_ι_cutWithdrawalValue_Л_p ) 
                          ^^ RoundsBase_ι_InvestParams_ι_remainingAmount !) ) >> 
    ( ↑17 U1! LocalState_ι_cutWithdrawalValue_Л_p ^^ 
       RoundsBase_ι_InvestParams_ι_remainingAmount !-= 
         D2! LocalState_ι_cutWithdrawalValue_Л_tonsForOwner ) 
     } 
  ) >> 
     (* if (uint64(now) > p.lastWithdrawalTime) { 
       uint64 periodQty = (uint64(now) - p.lastWithdrawalTime) / p.withdrawalPeriod; 
       if (periodQty > 0) { 
         withdrawalTons = math.min(periodQty * p.withdrawalValue, p.remainingAmount); 
         p.remainingAmount -= withdrawalTons; 
         p.lastWithdrawalTime += periodQty * p.withdrawalPeriod; } } *) 

  ( If ( tvm_now () ?> ( D1! ( ↑17 D2! LocalState_ι_cutWithdrawalValue_Л_p) 
                  ^^ RoundsBase_ι_InvestParams_ι_lastWithdrawalTime ) ) 
   then { 
       declareLocal Л_periodQty :>: XInteger64 := 
       (tvm_now () !- ( ↑17  ( D1! ( D2! LocalState_ι_cutWithdrawalValue_Л_p ) 
                  ^^ RoundsBase_ι_InvestParams_ι_lastWithdrawalTime ) )) 
                   !/ 
          ( ↑17 D1! ( D2! LocalState_ι_cutWithdrawalValue_Л_p ) 
                  ^^ RoundsBase_ι_InvestParams_ι_withdrawalPeriod )  ; 

     ( If ( $ Л_periodQty ?> $ xInt0 ) 
      then 
      { 
       ( ↑17 U1! LocalState_ι_cutWithdrawalValue_Л_withdrawalTons := 
         math->min2 (! $ Л_periodQty !* ( D1! (D2! LocalState_ι_cutWithdrawalValue_Л_p ) 
                          ^^ RoundsBase_ι_InvestParams_ι_withdrawalValue ) , 
                         ( D1! ( D2! LocalState_ι_cutWithdrawalValue_Л_p ) 
                          ^^ RoundsBase_ι_InvestParams_ι_remainingAmount ) !)  ) >> 
       ( ↑17 U1! LocalState_ι_cutWithdrawalValue_Л_p ^^ 
               RoundsBase_ι_InvestParams_ι_remainingAmount !-= 
                         D2! LocalState_ι_cutWithdrawalValue_Л_withdrawalTons ) >> 
       ( ↑17 U1! LocalState_ι_cutWithdrawalValue_Л_p ^^ 
               RoundsBase_ι_InvestParams_ι_lastWithdrawalTime !+= 
                     $ Л_periodQty !* ( D1! ( D2! LocalState_ι_cutWithdrawalValue_Л_p ) 
                          ^^ RoundsBase_ι_InvestParams_ι_withdrawalPeriod ) ) 
      } 
     ) 
   } 
  ) >> 
     (* if (p.remainingAmount < m_minStake) { 
       withdrawalTons += p.remainingAmount; 
       p.remainingAmount = 0; 
     } *) 
  ( If ( D1! ( ↑17 D2! LocalState_ι_cutWithdrawalValue_Л_p ) 
           ^^ RoundsBase_ι_InvestParams_ι_remainingAmount ?< ( ↑12 D2! DePoolContract_ι_m_minStake ) ) 
   then { 
     ( ↑17 U1! LocalState_ι_cutWithdrawalValue_Л_withdrawalTons !+= 
        D1! ( D2! LocalState_ι_cutWithdrawalValue_Л_p ) 
                          ^^ RoundsBase_ι_InvestParams_ι_remainingAmount ) >> 
     ( ↑17 U1! LocalState_ι_cutWithdrawalValue_Л_p 
                          ^^ RoundsBase_ι_InvestParams_ι_remainingAmount := $ xInt0 ) 
    } 
   ) >> 
  (* optional(InvestParams) opt; 
    opt.set(p); 
    return (opt, withdrawalTons, tonsForOwner); *) 
  declareLocal Л_opt :>: ( XMaybe RoundsBase_ι_InvestParams ) := $ default ; 
  ς U0! Л_opt ->set (↑17 D2! LocalState_ι_cutWithdrawalValue_Л_p ) ; 
  ς U0! Л_withdrawalTons := ↑ε17 LocalState_ι_cutWithdrawalValue_Л_withdrawalTons ; 
  ς U0! Л_tonsForOwner := ↑ε17 LocalState_ι_cutWithdrawalValue_Л_tonsForOwner ; 

return! [( Л_opt , Л_withdrawalTons , Л_tonsForOwner )].	 


(* Set Typeclasses Iterative Deepening. *) 		 

(*  
function _returnOrReinvestForParticipant( 
    Round round2, 
    Round round0, 
    address addr, 
    StakeValue stakes, 
    bool isValidator, 
    uint32 round1ValidatorsElectedFor 
  ) private returns (Round, Round) { 
    uint64 stakeSum = stakeSum(stakes); 
    bool stakeIsLost = round2.completionReason == CompletionReason.ValidatorIsPunished; 
    optional(Participant) optParticipant = fetchParticipant(addr); 
    require(optParticipant.hasValue(), InternalErrors.ERROR511); 
    Participant participant = optParticipant.get(); 
    --participant.roundQty; 
    uint64 lostFunds = stakeIsLost ? (round2.stake - round2.unused) - round2.recoveredStake : 0; 

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

        optional(InvestParams) newVesting = stakes.vesting; 
    if (newVesting.hasValue()) { 
      InvestParams params = newVesting.get(); 
      if (stakeIsLost) { 
        if (isValidator) { 
          uint64 delta = math.min(params.remainingAmount, lostFunds); 
          params.remainingAmount -= delta; 
          lostFunds -= delta; 
          round2.validatorRemainingStake += params.remainingAmount; 
        } else { 
          params.remainingAmount = math.muldiv( 
            round2.unused + round2.recoveredStake - round2.validatorRemainingStake, 
            params.remainingAmount, 
            round2.stake - round2.validatorStake 
          ); 
        } 
      } 
      round2.handledStakesAndRewards += params.remainingAmount; 
      uint64 withdrawalVesting; 
      uint64 tonsForOwner; 
      (newVesting, withdrawalVesting, tonsForOwner) = cutWithdrawalValue( 
        params, 
        isValidator && round2.completionReason != CompletionReason.RewardIsReceived, 
        round1ValidatorsElectedFor + round2.validatorsElectedFor 
      ); 
      newStake += withdrawalVesting; 
      if (tonsForOwner > 0) 
        newVesting.get().owner.transfer(tonsForOwner, false, 1); 

    } 

    uint64 attachedValue = 1; 
    uint64 curPause = math.min(participant.withdrawValue, newStake); 
    attachedValue += curPause; 
    participant.withdrawValue -= curPause; 
    newStake -= curPause; 
    if (newStake < m_minStake) {       attachedValue += newStake; 
      newStake = 0; 
    } 

         optional(InvestParams) newLock = stakes.lock; 
    if (newLock.hasValue()) { 
      InvestParams params = newLock.get(); 
      if (stakeIsLost) { 
        if (isValidator) { 
          uint64 delta = math.min(params.remainingAmount, lostFunds); 
          params.remainingAmount -= delta; 
          lostFunds -= delta; 
          round2.validatorRemainingStake += params.remainingAmount; 
        } else { 
          params.remainingAmount = math.muldiv( 
            round2.unused + round2.recoveredStake - round2.validatorRemainingStake, 
            params.remainingAmount, 
            round2.stake - round2.validatorStake 
          ); 
        } 
      } 
      round2.handledStakesAndRewards += params.remainingAmount; 
      uint64 withdrawalLock; 
      (newLock, withdrawalLock, ) = cutWithdrawalValue(params, false, 0); 
      if (withdrawalLock != 0) { 
        params.owner.transfer(withdrawalLock, false, 1); 
      } 
    } 

    if (m_poolClosed) { 
      attachedValue += newStake; 
      if (newVesting.hasValue()) { 
        newVesting.get().owner.transfer(newVesting.get().remainingAmount, false, 1); 
      } 
      if (newLock.hasValue()) { 
        newLock.get().owner.transfer(newLock.get().remainingAmount, false, 1); 
      } 
    } else { 
      if (newVesting.hasValue() && newVesting.get().remainingAmount == 0) newVesting.reset(); 
      if (newLock.hasValue() && newLock.get().remainingAmount == 0) newLock.reset(); 

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
      stakes.vesting.hasValue() ? stakes.vesting.get().remainingAmount : 0, 
      stakes.lock.hasValue() ? stakes.lock.get().remainingAmount : 0, 
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
                             ( Л_round1ValidatorsElectedFor : XInteger32 ) 
                         : LedgerT ( XErrorValue ( RoundsBase_ι_Round # RoundsBase_ι_Round ) XInteger ) := 
( declareInit LocalState_ι__returnOrReinvestForParticipant_Л_round2 := $ Л_round2) >> 
( declareInit LocalState_ι__returnOrReinvestForParticipant_Л_round0 := $ Л_round0) >> 

    (* 
    uint64 stakeSum = stakeSum(stakes); 
    bool stakeIsLost = round2.completionReason == CompletionReason.ValidatorIsPunished; 
    optional(Participant) optParticipant = fetchParticipant(addr); 
    require(optParticipant.hasValue(), InternalErrors.ERROR511); 
    Participant participant = optParticipant.get(); 
    --participant.roundQty; 
    uint64 lostFunds = stakeIsLost? (round2.stake - round2.unused) - round2.recoveredStake : 0; *) 


declareLocal Л_stakeSum :>: XInteger64 := RoundsBase_Ф_stakeSum (! $ Л_stakes !) ; 
declareLocal Л_stakeIsLost :>: XBool := ( $ (Л_round2 ->> RoundsBase_ι_Round_ι_completionReason) ) ?== ( ξ$ RoundsBase_ι_CompletionReasonP_ι_ValidatorIsPunished) ; 		 
declareLocal Л_optParticipant :>: ( XMaybe DePoolLib_ι_Participant ) := ParticipantBase_Ф_fetchParticipant (! $ Л_addr !) ; 
Require {{$ Л_optParticipant ->hasValue , ξ$ InternalErrors_ι_ERROR511 }} ; 

( declareGlobal LocalState_ι__returnOrReinvestForParticipant_Л_participant :>: (ξ DePoolLib_ι_Participant) := $ Л_optParticipant ->get) >> 
(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_participant ^^ DePoolLib_ι_Participant_ι_roundQty !--) >> 

( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds := $ Л_stakeIsLost ? 
  ( D1! (D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2) ^^ RoundsBase_ι_Round_ι_stake !- 
   D1! (D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2) ^^ RoundsBase_ι_Round_ι_unused ) !- 
   D1! (D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2) ^^ RoundsBase_ι_Round_ι_recoveredStake 
               ::: $ xInt0 ) 
>> 

                          (* uint64 newStake; 
                             uint64 reward; *) 

declareGlobal LocalState_ι__returnOrReinvestForParticipant_Л_newStake :>: XInteger64 ; 
declareGlobal LocalState_ι__returnOrReinvestForParticipant_Л_reward :>: XInteger64 ; 
( 
	If ( $ Л_stakeIsLost) then { 
  ( If ( $ Л_isValidator ) 
   then { 
      ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake := $ ( Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary ) ) >> 
      declareLocal Л_delta :>: XInteger64 := math->min2 (! ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake , 
                     ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds !) ; 
      ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake !-= $ Л_delta ) >> 
      ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds !-= $ Л_delta ) >> 
      ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ^^ RoundsBase_ι_Round_ι_validatorRemainingStake 
            := D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake ) 
   } 
   else { 
     (* round2.unused + round2.recoveredStake - round2.validatorRemainingStake, *) 
		(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake := math->muldiv (! 
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^ RoundsBase_ι_Round_ι_unused !+ 
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^ RoundsBase_ι_Round_ι_recoveredStake !- 
        D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^ RoundsBase_ι_Round_ι_validatorRemainingStake, 
				 $ Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary , 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^ RoundsBase_ι_Round_ι_stake !- 
    D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^ RoundsBase_ι_Round_ι_validatorStake !)) 
} ) 
	} else { 
    (* reward = math.muldiv(stakeSum, round2.rewards, round2.stake); 
      participant.reward += reward; 
      newStake = stakes.ordinary + reward; *) 
  (↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_reward := math->muldiv (! $ Л_stakeSum , 
    D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^ RoundsBase_ι_Round_ι_rewards , 
    D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^ RoundsBase_ι_Round_ι_stake !) ) >> 
		(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_participant ^^ DePoolLib_ι_Participant_ι_reward 
              !+= D2! LocalState_ι__returnOrReinvestForParticipant_Л_reward ) >> 
		(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake := $ ( Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary ) !+ 
                                      (D2! LocalState_ι__returnOrReinvestForParticipant_Л_reward)) 
	} 
) >> 
        (* round2.handledStakesAndRewards += newStake; 
           optional(InvestParams) newVesting = stakes.vesting; *) 
( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ^^ RoundsBase_ι_Round_ι_handledStakesAndRewards 
 !+= D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake ) >> 
 
( declareGlobal LocalState_ι__returnOrReinvestForParticipant_Л_newVesting :>: ( XMaybe RoundsBase_ι_InvestParams ) := 
         $ ( Л_stakes ->> RoundsBase_ι_StakeValue_ι_vesting ) ) >> (* $ [( default , default )]. *) 

( If ( ( ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting ) ->hasValue ) 
then 
{ 
 ( declareGlobal LocalState_ι__returnOrReinvestForParticipant_Л_params :>: RoundsBase_ι_InvestParams := 
       ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting ) ->get ) >> 
 ( If ( $ Л_stakeIsLost) then { 
 
  ( If ( $ Л_isValidator ) 
   then { 
      declareLocal Л_delta :>: XInteger64 := math->min2 (! ↑17 D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params ) ^^ 
                       RoundsBase_ι_InvestParams_ι_remainingAmount , 
                     ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds !) ; 
      ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_params ^^ 
                       RoundsBase_ι_InvestParams_ι_remainingAmount !-= $ Л_delta ) >> 
      ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds !-= $ Л_delta ) >> 
      ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ^^ RoundsBase_ι_Round_ι_validatorRemainingStake 
            !+= D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params ) 
                      ^^ RoundsBase_ι_InvestParams_ι_remainingAmount ) 
   } (*+*) 
   else { 
		( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_params ^^ 
                       RoundsBase_ι_InvestParams_ι_remainingAmount := math->muldiv (! 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^ RoundsBase_ι_Round_ι_unused !+ 
    D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^ RoundsBase_ι_Round_ι_recoveredStake !- 
    D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^ RoundsBase_ι_Round_ι_validatorRemainingStake 
       , 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params ) 
                      ^^ RoundsBase_ι_InvestParams_ι_remainingAmount , 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^ RoundsBase_ι_Round_ι_stake !- 
    D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^ RoundsBase_ι_Round_ι_validatorStake !) ) 
} ) 
	} ) (*+*) >> 
            (* round2.handledStakesAndRewards += params.remainingAmount; *) 
 ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ^^ RoundsBase_ι_Round_ι_handledStakesAndRewards !+= 
  D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params ) ^^ RoundsBase_ι_InvestParams_ι_remainingAmount ) 
>> (* + *)  
      (* uint64 withdrawalVesting; 
         uint64 tonsForOwner; *)

 declareLocal Л_withdrawalVesting :>: XInteger64 ; 
 declareLocal Л_tonsForOwner :>: XInteger64 ;

            (* (newVesting, withdrawalVesting, tonsForOwner) = cutWithdrawalValue( 
                params, 
                isValidator && round2.completionReason != CompletionReason.RewardIsReceived, 
                round1ValidatorsElectedFor + round2.validatorsElectedFor 
      ); *) 
 U0! {( Л_newVesting , Л_withdrawalVesting , Л_tonsForOwner )} := DePoolContract_Ф_cutWithdrawalValue (! 
                ( ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_params ) , 
                 $ Л_isValidator !& ( D1! ( ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) 
                            ^^ RoundsBase_ι_Round_ι_completionReason ) ?!= 
                            ξ$ RoundsBase_ι_CompletionReasonP_ι_RewardIsReceived , 
                           ( $ Л_round1ValidatorsElectedFor !+ 
                           ( D1! ( ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^ 
                               RoundsBase_ι_Round_ι_validatorsElectedFor ) ) 
                           !) ;     

 ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting := $ Л_newVesting ) >> 
 ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake !+= $ Л_withdrawalVesting ) >> 
      (* if (tonsForOwner > 0) 
        newVesting.get().owner.transfer(tonsForOwner, false, 1); *) 
 ( If ( $ Л_tonsForOwner ?> $ xInt0 ) 
  then { 
	(D1! ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting) ->get) ^^ RoundsBase_ι_InvestParams_ι_owner ) ->transfer 
      (! $ Л_tonsForOwner , $ xBoolFalse, $ xInt1 !) 
    } ) 
} ) 
>> (* + *)  (* $ [( default , default )]. *)  

( declareGlobal LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue :>: XInteger64 := $ xInt1) >> 
(* uint64 curPause = math.min(participant.withdrawValue, newStake); *) 
declareLocal Л_curPause :>: XInteger64 := math->min2 (! (D1! (↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_participant) ^^ DePoolLib_ι_Participant_ι_withdrawValue) , 
								(↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake) !) ; 
(* attachedValue += curPause; *) 
( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue !+= $Л_curPause ) >> 
(* participant.withdrawValue -= curPause; *) 
( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_participant ^^ DePoolLib_ι_Participant_ι_withdrawValue !-= 
                 $Л_curPause ) >> 
(* newStake -= curPause; *) 
( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake !-= $Л_curPause ) >> 
(* if (newStake < m_minStake) { 	attachedValue += newStake; 
	newStake = 0; 
} *) 
( If ( ( ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake ) ?< 
                     (↑12 D2! DePoolContract_ι_m_minStake ) ) then { 
	( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue !+= 
              D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake ) >> 
	( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake := $xInt0 ) 
} ) >>    (* + *) (* $ [( default , default )]. *) 

(declareGlobal LocalState_ι__returnOrReinvestForParticipant_Л_newLock :>: (XMaybe RoundsBase_ι_InvestParams) := 
         $ ( Л_stakes ->> RoundsBase_ι_StakeValue_ι_lock ) ) >> (* + *) (* $ [( default , default )]. *) 

( If ( ( ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock ) ->hasValue ) (* + *) 
then 
{ 
                  (* InvestParams params = newLock.get(); *) 
 ( declareGlobal LocalState_ι__returnOrReinvestForParticipant_Л_params :>: RoundsBase_ι_InvestParams := 
       ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock ) ->get )    >> (* + *) 
	( If ( $ Л_stakeIsLost ) then { 
 
  ( If ( $ Л_isValidator ) 
   then { 
      declareLocal Л_delta :>: XInteger64 := math->min2 (! ↑17 D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params ) ^^ 
                             RoundsBase_ι_InvestParams_ι_remainingAmount , 
                     ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds !) ; 
      ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_params ^^ 
                       RoundsBase_ι_InvestParams_ι_remainingAmount !-= $ Л_delta ) 
>> 
      ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds !-= $ Л_delta ) >> 
      ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ^^ RoundsBase_ι_Round_ι_validatorRemainingStake 
            !+= D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params ) 
                      ^^ RoundsBase_ι_InvestParams_ι_remainingAmount ) 
   } (* + *) 
   else { 
		( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_params ^^ 
                       RoundsBase_ι_InvestParams_ι_remainingAmount := math->muldiv (! 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^ RoundsBase_ι_Round_ι_unused !+ 
    D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^ RoundsBase_ι_Round_ι_recoveredStake !- 
    D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^ RoundsBase_ι_Round_ι_validatorRemainingStake 
       , 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params ) 
                      ^^ RoundsBase_ι_InvestParams_ι_remainingAmount , 
				D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^ RoundsBase_ι_Round_ι_stake !- 
    D1! ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ) ^^ RoundsBase_ι_Round_ι_validatorStake !) ) 
} ) 
	} ) >> (* + *) 
           (*round2.handledStakesAndRewards += params.remainingAmount;*) 
 ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ^^ RoundsBase_ι_Round_ι_handledStakesAndRewards !+= 
 ( D2! LocalState_ι__returnOrReinvestForParticipant_Л_params ^^ RoundsBase_ι_InvestParams_ι_remainingAmount ) ) >> 
  (* + *) 

 declareLocal Л_withdrawalLock :>: XInteger64 ;  
           (* (newLock, withdrawalLock,) = cutWithdrawalValue(params,false,0); *) 
 U0! {( Л_newLock , Л_withdrawalLock , _ )} := DePoolContract_Ф_cutWithdrawalValue 
       (! ( ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_params ) , $ xBoolFalse , $ xInt0 !) ; 
 ( ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newLock := $ Л_newLock ) >> 
 (If ( $ Л_withdrawalLock ?!= $xInt0 ) then { 
           (* params.owner.transfer(withdrawalLock, false, 1); *) 
  ( D1! ( ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_params ) ^^ RoundsBase_ι_InvestParams_ι_owner ) ->transfer 
      (! $ Л_withdrawalLock , $xBoolFalse, $ xInt1 !) 
   } ) 
} ) >> (* + *) 

(* if (m_poolClosed) { 
	attachedValue += newStake; 
	if (newVesting.hasValue()) { 
		newVesting.get().owner.transfer(newVesting.get().remainingAmount, false, 1); 
	} 
	if (newLock.hasValue()) { 
		newLock.get().owner.transfer(newLock.get().remainingAmount, false, 1); 
	} 
} else { 
	if (newVesting.hasValue() && newVesting.get().remainingAmount == 0) newVesting.reset(); 
	if (newLock.hasValue() && newLock.get().remainingAmount == 0) newLock.reset(); 

	if (!participant.reinvest) { 
		attachedValue += newStake; 
		newStake = 0; 
	} 
	(round0, participant) = _addStakes(round0, participant, addr, newStake, newVesting, newLock); 
} *) 

(If (↑12 D2! DePoolContract_ι_m_poolClosed) then { 
	(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue !+= 
             D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake) >> 
	(If ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting) ->hasValue) then { 
	(D1! ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting) ->get) ^^ 
                 RoundsBase_ι_InvestParams_ι_owner ) ->transfer 
                (! D1! ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting) ->get) ^^ 
                 RoundsBase_ι_InvestParams_ι_remainingAmount , $xBoolFalse, $ xInt1 !) 
	}) >> 
	(If ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock) ->hasValue) then { 
	(D1! ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock) ->get) ^^ RoundsBase_ι_InvestParams_ι_owner ) 
                                             ->transfer 
      (! D1! ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock) ->get) ^^ 
                 RoundsBase_ι_InvestParams_ι_remainingAmount , $xBoolFalse, $ xInt1 !) 
  }) 
 } else { 
	(If ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting) ->hasValue) !& 
		(D1! ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting) ->get) ^^ RoundsBase_ι_InvestParams_ι_remainingAmount ?== $xInt0) 
	then { 
		 ↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting ->reset 
	}) >> 
	(If ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock) ->hasValue) !& 
		(D1! ((↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock) ->get) ^^ RoundsBase_ι_InvestParams_ι_remainingAmount ?== $xInt0) 
	then { 
		↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newLock ->reset 
	}) >> 
	(If ( !¬ (D1! (↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_participant) ^^ DePoolLib_ι_Participant_ι_reinvest)) then { 
		(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue !+= D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake) >> 
		(↑17 U1! LocalState_ι__returnOrReinvestForParticipant_Л_newStake := $xInt0) 
	}) >> 
	(↑↑17 U2! {( LocalState_ι__returnOrReinvestForParticipant_Л_round0, 
			  LocalState_ι__returnOrReinvestForParticipant_Л_participant )} := RoundsBase_Ф__addStakes (! (↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_round0) , 
				(↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_participant) , 
				 $Л_addr , 
				(↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newStake) , 
				(↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newVesting) , 
				(↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_newLock)  !) ) 
 
 }) >> 
 (* _setOrDeleteParticipant(addr, participant); *) 
 ParticipantBase_Ф__setOrDeleteParticipant (! $Л_addr , (↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_participant) !) >> 
(* IParticipant(addr).onRoundComplete{value: attachedValue, bounce: false}( 
	completedRound.id, (TODO: ???)
	reward, 
	stakes.ordinary, 
	stakes.vesting.hasValue() && stakes.vesting.get().isActive? stakes.vesting.get().amount : 0, 
	stakes.lock.hasValue() && stakes.lock.get().isActive? stakes.lock.get().amount : 0, 
	participant.reinvest, 
	uint8(completedRound.completionReason) 
); *) 
 
( IParticipant of ( $ Л_addr ) ->sendMessage ( IParticipant_И_onRoundCompleteF (!! 
          ( ↑17 D1! (D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2) ^^ RoundsBase_ι_Round_ι_id ) , 
																	( ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_reward ) , 
																	( $ Л_stakes ->> RoundsBase_ι_StakeValue_ι_ordinary ) , 
																(	( ( $ Л_stakes ->> RoundsBase_ι_StakeValue_ι_vesting) ->hasValue ) ? 
																			 ( D1! (( $ Л_stakes ->> RoundsBase_ι_StakeValue_ι_vesting) ->get) ^^ 
                          RoundsBase_ι_InvestParams_ι_remainingAmount ) ::: $ xInt0 ) , 
																	( ( ( $ Л_stakes ->> RoundsBase_ι_StakeValue_ι_lock) ->hasValue ) ? 
																			 (D1! (( $ Л_stakes ->> RoundsBase_ι_StakeValue_ι_lock) ->get) ^^ 
                          RoundsBase_ι_InvestParams_ι_remainingAmount) ::: $xInt0 ) , 
																	( D1! (↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_participant) ^^ 
                                                                    DePoolLib_ι_Participant_ι_reinvest ) , 
																	  (completionReason2XInteger (!! 
                       ↑17 D1! (D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2) ^^ 
                          RoundsBase_ι_Round_ι_completionReason !!) ) !!) )
                 with {|| messageValue ::= ( ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue ) , 
			                    messageBounce ::= $ xBoolFalse ||} ) >>

(* return (round0, round2); *) 
 return# ( ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_round0 , 
      ↑17 D2! LocalState_ι__returnOrReinvestForParticipant_Л_round2 ). (* + *) 


(*   
function _returnOrReinvest(Round round2, uint8 chunkSize) private returns (Round) { 
    tvm.accept(); 

    Round round0 = getRound0(); 
    uint32 round1ValidatorsElectedFor = getRound1().validatorsElectedFor; 
    uint startIndex = 0; 
    if (!round2.isValidatorStakeCompleted) { 
      round2.isValidatorStakeCompleted = true; 
      optional(StakeValue) optStake = round2.stakes.fetch(m_validatorWallet); 
      if (optStake.hasValue()) { 
        StakeValue stake = optStake.get(); 
        startIndex = 1; 
        delete round2.stakes[m_validatorWallet]; 
        (round0, round2) = _returnOrReinvestForParticipant(round2, round0, m_validatorWallet, stake, true, round1ValidatorsElectedFor); 
      } 
    } 

    for (uint i = startIndex; i < chunkSize && !round2.stakes.empty(); ++i) { 
      (address addr, StakeValue stake) = round2.stakes.delMin().get(); 
      (round0, round2) = _returnOrReinvestForParticipant(round2, round0, addr, stake, false, round1ValidatorsElectedFor); 
    } 

    setRound0(round0); 
    if (round2.stakes.empty()) { 
      round2.step = RoundStep.Completed; 
      this.ticktock{value: VALUE_FOR_SELF_CALL, bounce: false}(); 
    } 
    return round2; 
  }*) 

Definition DePoolContract_Ф__returnOrReinvest ( Л_round2 : RoundsBase_ι_Round ) 
                       ( Л_chunkSize : XInteger8 ) 
                       : LedgerT ( XErrorValue RoundsBase_ι_Round XInteger ) 
											 :=  
(*init*) 
( declareInit LocalState_ι__returnOrReinvest_Л_round2   := $ Л_round2 ) >> 
(* ( declareInit LocalState_ι__returnOrReinvest_Л_chunkSize := $ Л_chunkSize ) >>  *)
(*tvm.accept();*) 
tvm_accept () >> 
    (* Round round0 = getRound0(); *) 
( declareGlobal! LocalState_ι__returnOrReinvest_Л_round0 :>: RoundsBase_ι_Round := RoundsBase_Ф_getRound0 () ) >> 
    (* uint32 round1ValidatorsElectedFor = getRound1 ( ) . validatorsElectedFor ; *) 
 U0! Л_round := ( RoundsBase_Ф_getRound1 () ) ; 
 declareLocal Л_round1ValidatorsElectedFor :>: XInteger32 :=  $ Л_round ->> RoundsBase_ι_Round_ι_validatorsElectedFor ; 
(*    uint startIndex = 0;  *) 
( declareGlobal! LocalState_ι__returnOrReinvest_Л_startIndex :>: XInteger := $ xInt0 ) >> 
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
 
(*     if (!round2.isValidatorStakeCompleted) { *) 
If!! ( !¬ ( ↑17 D1! ( D2! LocalState_ι__returnOrReinvest_Л_round2 ) ^^ 
            RoundsBase_ι_Round_ι_isValidatorStakeCompleted ) ) 
then 
{ (*     round2.isValidatorStakeCompleted = true; optional(StakeValue) optStake = round2.stakes.fetch(m_validatorWallet); *) 
  ( ↑17 U1! LocalState_ι__returnOrReinvest_Л_round2 ^^ 
        RoundsBase_ι_Round_ι_isValidatorStakeCompleted := $ xBoolTrue ) >> 
             (* optional(StakeValue) optStake = round2.stakes.fetch(m_validatorWallet); *)
  declareLocal Л_optStake :>: (XMaybe RoundsBase_ι_StakeValue) := (D1! (↑17 D2! LocalState_ι__returnOrReinvest_Л_round2 ^^ 
                                                                           RoundsBase_ι_Round_ι_stakes) 
         ->fetch ( ↑2 D2! ValidatorBase_ι_m_validatorWallet ) ) ; 
  (*     if (optStake.hasValue()) { *) 
   If! ( ( $ Л_optStake ) ->hasValue ) 
   then  
   { 
    (*   StakeValue stake = optStake.get(); *) 
    declareLocal Л_stake :>: RoundsBase_ι_StakeValue := ( $ Л_optStake ) ->get ; 
    (*   startIndex = 1; *)  
    ( ↑17 U1! LocalState_ι__returnOrReinvest_Л_startIndex := $ xInt1 ) >> 
    (*   delete round2.stakes[m_validatorWallet]; *) 
    ( ↑↑17 U2! delete LocalState_ι__returnOrReinvest_Л_round2 ^^ 
             RoundsBase_ι_Round_ι_stakes [[ ↑2 D2! ValidatorBase_ι_m_validatorWallet ]] ) >> 
    (*   (round0, round2) = _returnOrReinvestForParticipant(round2, round0, m_validatorWallet, stake, true); *) 
    U0! Л_rounds ?:= 
        DePoolContract_Ф__returnOrReinvestForParticipant (! 
         ↑17 D2! LocalState_ι__returnOrReinvest_Л_round2 , 
         ↑17 D2! LocalState_ι__returnOrReinvest_Л_round0 , 
         ↑2 D2! ValidatorBase_ι_m_validatorWallet , 
         $ Л_stake , 
         $ xBoolTrue , 
         $ Л_round1ValidatorsElectedFor !) ; 
( ↑17 U1! {( LocalState_ι__returnOrReinvest_Л_round0 , LocalState_ι__returnOrReinvest_Л_round2 )} := $ Л_rounds ) 
   } ; $ I 
} ; (* $ (xValue default). *) 
 
(* for (uint i = startIndex; i < chunkSize && !round2.stakes.empty(); ++i) { 
      (address addr, StakeValue stake) = round2.stakes.delMin().get(); 
      (round0, round2) = _returnOrReinvestForParticipant(round2, round0, addr, stake, false); 
    } *) 

do _ ← ( WhileE ( ( ↑17 D2! LocalState_ι__returnOrReinvest_Л_startIndex ?< $ Л_chunkSize ) !& 
   ( !¬ ( ( ↑17 D2! LocalState_ι__returnOrReinvest_Л_round2 ^^ RoundsBase_ι_Round_ι_stakes) ->empty ) ) ) 
do 
( 
           (* (address addr, StakeValue stake) = round2.stakes.delMin().get();  *)
(* TODO need ->get *)
declareLocal {( Л_addr :>: XAddress , Л_stake :>: RoundsBase_ι_StakeValue )} := ( ↑17 U1! delMin LocalState_ι__returnOrReinvest_Л_round2 ^^ RoundsBase_ι_Round_ι_stakes ) (* ->get *) ; 

DePoolContract_Ф__returnOrReinvestForParticipant (!  
         ↑17 D2! LocalState_ι__returnOrReinvest_Л_round2 , 
         ↑17 D2! LocalState_ι__returnOrReinvest_Л_round0 , 
         $ Л_addr , 
         $ Л_stake , 
         $ xBoolFalse , 
         $ Л_round1ValidatorsElectedFor !) >>= 
fun ea => xErrorMapDefaultF (fun a => (↑17 U1! {( LocalState_ι__returnOrReinvest_Л_round0 , LocalState_ι__returnOrReinvest_Л_round2 )} := $ a ) >> continue! (xValue I)) 
          ea (fun er => break! (xError er)))) >>= 
    fun r => return! (xProdSnd r) ?; 
 (* return! default. *) 
 
    (* setRound0(round0); *) 
 ( RoundsBase_Ф_setRound0 (! ↑17 D2! LocalState_ι__returnOrReinvest_Л_round0 !) ) >> 
     (* if (round2.stakes.empty()) { 
      round2.step = RoundStep.Completed; 
      this.ticktock{value: VALUE_FOR_SELF_CALL, bounce: false}();  } *) 
 ( If ( ( ↑17 D2! LocalState_ι__returnOrReinvest_Л_round2 ^^ RoundsBase_ι_Round_ι_stakes ) ->empty ) 
 then 
{ 
	(↑17 U1! LocalState_ι__returnOrReinvest_Л_round2 ^^ RoundsBase_ι_Round_ι_step := 
                       ξ$ RoundsBase_ι_RoundStepP_ι_Completed ) >> 

     this->sendMessage ( $ DePoolContract_Ф_ticktockF ) with {|| messageValue ::= $ DePool_ι_VALUE_FOR_SELF_CALL , 
			  						  messageBounce ::= $ xBoolFalse||}  
    } ) >> 
(*return round2;*) 
return!! ( ↑17 D2! LocalState_ι__returnOrReinvest_Л_round2 ) . (* + *) 


  
(*  function sendAcceptAndReturnChange128(uint64 fee) private { 
    tvm.rawReserve(address(this).balance - fee, 0); 
    IParticipant(msg.sender).receiveAnswer{value: 0, bounce: false, flag: 128}(STATUS_SUCCESS, 0); 
  } *) 


Definition DePoolContract_Ф_sendAcceptAndReturnChange128 (Л_fee : XInteger64) : LedgerT True := 
  tvm_rawReserve (! tvm_balance () !- $ Л_fee,  $xInt0 !) >> 
  IParticipant of ( msg_sender () ) ->sendMessage (IParticipant_И_receiveAnswerF (!! $ DePool_ι_STATUS_SUCCESS , $xInt0 !!))
    with {|| messageValue ::= $ xInt0 , messageBounce ::= $ xBoolFalse , messageFlag ::= $ xInt128 ||} .
                       
(* function sendAcceptAndReturnChange() private { 
  IParticipant(msg.sender).receiveAnswer{value: 0, bounce: false, flag: 64}(STATUS_SUCCESS, 0); 
} *)                       
Definition DePoolContract_Ф_sendAcceptAndReturnChange : LedgerT True := 
  IParticipant of ( msg_sender () ) ->sendMessage (IParticipant_И_receiveAnswerF (!! $ DePool_ι_STATUS_SUCCESS , $xInt0 !!))
    with {|| messageValue ::= $ xInt0 , messageBounce ::= $ xBoolFalse , messageFlag ::= $ xInt64 ||} .
(* 
function addOrdinaryStake(uint64 stake) public { 
    require(msg.sender != address(0), Errors.IS_EXT_MSG); 
                    
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
 Require {{ msg_sender () ?!= $ xInt0 , ξ$ Errors_ι_IS_EXT_MSG }} ; 
                (*if (m_poolClosed) { return _sendError(STATUS_DEPOOL_CLOSED, 0); } *) 
 If!! ( ↑12 D2! DePoolContract_ι_m_poolClosed ) then { 
  return!!! ( DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_DEPOOL_CLOSED , $ xInt0 !) ) } ; 
               (* uint64 msgValue = uint64(msg.value); *) 
 declareLocal Л_msgValue :>: XInteger64 := msg_value () ; 
               (* if (msgValue < uint(stake) + STAKE_FEE) {return _sendError(STATUS_FEE_TOO_SMALL, STAKE_FEE);} *) 
 If!! ( $ Л_msgValue ?< $ Л_stake !+ $ DePool_ι_STAKE_FEE ) then { 
  return!!! ( DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_FEE_TOO_SMALL , 
                        $ DePool_ι_STAKE_FEE !) ) } ; 

              (* uint64 fee = msgValue - stake; *) 
 declareLocal Л_fee :>: XInteger64 := $ Л_msgValue !- $ Л_stake ; 
              (* if (stake < m_minStake) {return _sendError(STATUS_STAKE_TOO_SMALL, m_minStake);} *) 
 If! ( $ Л_stake ?< ↑12 D2! DePoolContract_ι_m_minStake ) then { 
  return!!! ( DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_STAKE_TOO_SMALL , 
                        ( ↑ε12 DePoolContract_ι_m_minStake ) !) ) } ; 

                    (*DePoolLib.Participant participant = getOrCreateParticipant(msg.sender);*) 
 declareLocal Л_participant :>: ξ DePoolLib_ι_Participant := ParticipantBase_Ф_getOrCreateParticipant (! msg_sender () !) ; 
                    (* Round round = getRound0(); *) 
 declareLocal Л_round :>: RoundsBase_ι_Round := RoundsBase_Ф_getRound0 () ; 
                    (*optional(InvestParams) empty;*) 
 declareLocal Л_empty :>: (XMaybe RoundsBase_ι_InvestParams) ; 
                    (*(round, participant) = _addStakes(round, participant, msg.sender, stake, empty, empty);*) 
 U0! {( Л_round , Л_participant )} := RoundsBase_Ф__addStakes (! $ Л_round , 
                                  $ Л_participant , 
                                  msg_sender () , 
                                  $ Л_stake , 
                                  $ Л_empty , 
										              $ Л_empty !) ; 
                    (* setRound0(round); *) 
 RoundsBase_Ф_setRound0 (! $ Л_round !) >> 
                   (* _setOrDeleteParticipant(msg.sender, participant); *) 
 (ParticipantBase_Ф__setOrDeleteParticipant (! msg_sender () , $ Л_participant !)) >> 
                   (* sendAcceptAndReturnChange128(fee); *) 
 (DePoolContract_Ф_sendAcceptAndReturnChange128 (! $ Л_fee !)) . 

Definition DePoolContract_Ф_addOrdinaryStake ( Л_stake : XInteger64 ) : LedgerT ( XErrorValue True XInteger ) := 
 do r ← DePoolContract_Ф_addOrdinaryStake' Л_stake ; 
return! (xErrorMapDefaultF (xValue ∘ fromValueValue) r xError). 

(* 
function addVestingOrLock(uint64 stake, address beneficiary, uint32 withdrawalPeriod, uint32 totalPeriod, bool isVesting) private { 
    if (m_poolClosed) { 
      return _sendError(STATUS_DEPOOL_CLOSED, 0); 
    } 

    if (!beneficiary.isStdAddrWithoutAnyCast() || beneficiary == address(0)) 
      return _sendError(STATUS_INVALID_ADDRESS, 0); 

    if (msg.sender == beneficiary) 
      return _sendError(STATUS_INVALID_BENEFICIARY, 0); 


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

    if (totalPeriod >= 18 * (365 days)) {  return _sendError(STATUS_TOTAL_PERIOD_MORE_18YEARS, 0); 
    } 

    if (withdrawalPeriod == 0) { 
      return _sendError(STATUS_WITHDRAWAL_PERIOD_IS_ZERO, 0); 
    } 

    if (totalPeriod % withdrawalPeriod != 0) { 
      return _sendError(STATUS_TOTAL_PERIOD_IS_NOT_DIVISIBLE_BY_WITHDRAWAL_PERIOD, 0); 
    } 

    Participant participant = getOrCreateParticipant(beneficiary); 
    if (isVesting) { 
      if (participant.haveVesting) { 
        return _sendError(STATUS_PARTICIPANT_ALREADY_HAS_VESTING, 0); 
      } 
    } else { 
      if (participant.haveLock) { 
        return _sendError(STATUS_PARTICIPANT_ALREADY_HAS_LOCK, 0); 
      } 
    } 

    uint64 withdrawalValue = math.muldiv(halfStake, withdrawalPeriod, totalPeriod); 

    for (uint i = 0; i < 2; ++i) { 
      bool isFirstPart = i == 0; 
      InvestParams vestingOrLock = InvestParams({ 
        reamainingAmount: isFirstPart? halfStake : stake - halfStake, 
        lastWithdrawalTime: uint64(now), 
        withdrawalPeriod: withdrawalPeriod, 
        withdrawalValue: withdrawalValue, 
        owner: msg.sender 
      }); 

      optional(InvestParams) v; 
      optional(InvestParams) l; 
      if (isVesting) { 
        v.set(vestingOrLock); 
      } else { 
        l.set(vestingOrLock); 
      } 

      Round round = isFirstPart? getRoundPre0() : getRound0(); 
      (round, participant) = _addStakes(round, participant, beneficiary, 0, v, l); 
      isFirstPart? setRoundPre0(round) : setRound0(round); 
    } 

    _setOrDeleteParticipant(beneficiary, participant); 
    sendAcceptAndReturnChange128(fee); 
  } *) 
	 
Unset Typeclasses Iterative Deepening. 
Set Typeclasses Depth 10. 


(*function addVestingOrLock(uint64 stake, 
             address beneficiary, uint32 withdrawalPeriod, uint32 totalPeriod, bool isVesting) private {*) 

Definition DePoolContract_Ф_addVestingOrLock' ( Л_stake : XInteger64 ) 
                       ( Л_beneficiary : XAddress ) 
                       ( Л_withdrawalPeriod : XInteger32 ) 
                       ( Л_totalPeriod : XInteger32 ) 
                       ( Л_isVesting : XBool ) : 
                     LedgerT (XValueValue True) := 
(* if (m_poolClosed) {return _sendError(STATUS_DEPOOL_CLOSED, 0); } *) 
If!! ( ↑ε12 DePoolContract_ι_m_poolClosed ) 
then { 
 return!!! ( DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_DEPOOL_CLOSED , $ xInt0 !) ) 
 } ; 
  (* if (!beneficiary.isStdAddrWithoutAnyCast() || beneficiary == address(0)) 
  return _sendError(STATUS_INVALID_ADDRESS, 0);  
  if (msg.sender == beneficiary) 
  return _sendError(STATUS_INVALID_BENEFICIARY, 0); *) 
If!! ( ( !¬ ( ( $ Л_beneficiary ) ->isStdAddrWithoutAnyCast() ) ) !| ( $ Л_beneficiary ?== $ xInt0 ) ) 
then { 
 return!!! ( DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_INVALID_ADDRESS , $ xInt0 !) ) 
 } ; 

If!! ( ( msg_sender () ) ?== $ Л_beneficiary ) 
then { 
 return!!! ( DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_INVALID_BENEFICIARY , $ xInt0 !) ) 
 } ; 
   (* uint64 msgValue = uint64(msg.value); *)
declareLocal Л_msgValue :>: XInteger64 := msg_value () ;
 
If!! ( $ Л_msgValue ?< ( $ Л_stake !+ ( $ DePool_ι_STAKE_FEE ) ) ) 
then 
{ 
 return!!! (DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_FEE_TOO_SMALL , 
                      $ DePool_ι_STAKE_FEE !) ) 
} ; 
                    (* uint64 fee = msgValue - stake; 
                    uint64 halfStake = stake / 2; *) 
declareLocal Л_fee :>: XInteger64 := $ Л_msgValue !- $ Л_stake ; 
declareLocal Л_halfStake :>: XInteger64 := $ Л_stake !/ $ xInt2 ; 

If!! ( $ Л_halfStake ?< ↑12 D2! DePoolContract_ι_m_minStake ) 
then 
{ 
return!!! (DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_STAKE_TOO_SMALL , $ xInt2 !* ( ↑12 D2! DePoolContract_ι_m_minStake ) !) ) 
} ; 

If!! ( $ Л_withdrawalPeriod ?> $ Л_totalPeriod ) 
then 
{ 
return!!! ( DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_WITHDRAWAL_PERIOD_GREATER_TOTAL_PERIOD , $ xInt0 !) ) 
} ; 

If!! ( $ Л_totalPeriod ?>= ( $ xInt18 !* $ xInt365 !* $ x1_day ) ) 
then 
{ 
return!!! (DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_TOTAL_PERIOD_MORE_18YEARS , $ xInt0 !) ) 
} ; 

If!! ( $ Л_withdrawalPeriod ?== $ xInt0 ) 
then 
{ 
return!!! (DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_WITHDRAWAL_PERIOD_IS_ZERO , $ xInt0 !) ) 
} ; 

If!! ( ( $ Л_totalPeriod !% $ Л_withdrawalPeriod ) ?!= $ xInt0 ) 
then 
{ 
return!!! ( DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_TOTAL_PERIOD_IS_NOT_DIVISIBLE_BY_WITHDRAWAL_PERIOD , $ xInt0 !) ) 
} ; 
                        (* Participant participant = getOrCreateParticipant(beneficiary); *) 
declareLocal Л_participant :>: DePoolLib_ι_Participant := ParticipantBase_Ф_getOrCreateParticipant (! $ Л_beneficiary !) ; 
If! ( $ Л_isVesting ) 
then { 
If! ( $ Л_participant ->> DePoolLib_ι_Participant_ι_haveVesting ) 
then { 
return!!! ( DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_PARTICIPANT_ALREADY_HAS_VESTING , $ xInt0 !) ) 
} ; $ I 
} 
else 
{ 
If! ( $ Л_participant ->> DePoolLib_ι_Participant_ι_haveLock ) 
then { 
return!!! ( DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_PARTICIPANT_ALREADY_HAS_LOCK , $ xInt0 !) ) 
} ; $ I 
} ; 
                    (* uint64 withdrawalValue = math.muldiv(halfStake, withdrawalPeriod, totalPeriod);  *)
declareLocal Л_withdrawalValue :>: XInteger64 := math->muldiv (! $ Л_halfStake , $ Л_withdrawalPeriod , $ Л_totalPeriod !) ; 
 
    (* for (uint i = 0; i < 2; ++i) { 
>    bool isFirstPart = i == 0; 
>    InvestParams vestingOrLock = InvestParams({ 
>    amount: isFirstPart? halfStake : stake - halfStake, 
>    lastWithdrawalTime: uint64(now), 
>    withdrawalPeriod: withdrawalPeriod, 
>    withdrawalValue: withdrawalValue, 
>    owner: msg.sender 
>    }); *) 

(* TODO: for (uint i = 0; i < 2; ++i) { *) 
( ↑17 U1! LocalState_ι_addVestingOrLock_Л_participant := $ Л_participant ) >> 

( 
ForIndexed (xListCons xInt0 (xListCons xInt1 xListNil)) do (fun (i: XInteger) => 
                    (* bool isFirstPart = i == 0; 
                    InvestParams vestingOrLock = InvestParams({ *) 
declareLocal Л_isFirstPart :>: XBool := ( $ i ?== $ xInt0 ) ; 
declareLocal Л_vestingOrLock :>: RoundsBase_ι_InvestParams := {|| 
  RoundsBase_ι_InvestParams_ι_remainingAmount ::= $ Л_isFirstPart ? $ Л_halfStake ::: $Л_stake !- $Л_halfStake, 
  RoundsBase_ι_InvestParams_ι_lastWithdrawalTime ::= tvm_now () , 
  RoundsBase_ι_InvestParams_ι_withdrawalPeriod ::= $ Л_withdrawalPeriod , 
  RoundsBase_ι_InvestParams_ι_withdrawalValue ::= $ Л_withdrawalValue , 
  RoundsBase_ι_InvestParams_ι_owner ::= msg_sender () ||} ; 
(*     optional(InvestParams) v; 
      optional(InvestParams) l; *) 
    (* if (isVesting) { 
      v.set(vestingOrLock); 
    } else { 
      l.set(vestingOrLock); } *) 
  declareGlobal LocalState_ι_addVestingOrLock_Л_v :>: ( XMaybe RoundsBase_ι_InvestParams ) ; 
  declareGlobal LocalState_ι_addVestingOrLock_Л_l  :>: ( XMaybe RoundsBase_ι_InvestParams ) ; 
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
declareLocal Л_round :>: RoundsBase_ι_Round := $ Л_isFirstPart ? RoundsBase_Ф_getRoundPre0 () ::: RoundsBase_Ф_getRound0 () ; 
ς U0! Л_participant := ↑17 D2! LocalState_ι_addVestingOrLock_Л_participant ;
         (* (round, participant) = _addStakes(round, participant, beneficiary, 0, v, l); *)
U0! {( Л_round , Л_participant )} := RoundsBase_Ф__addStakes (! ( $ Л_round) , ( $ Л_participant ) , 
                              ( $ Л_beneficiary ) , 
                              ( $ xInt0 ) , 
                              ( ↑17 D2! LocalState_ι_addVestingOrLock_Л_v ), 
                              ( ↑17 D2! LocalState_ι_addVestingOrLock_Л_l ) !) ; 
( ↑17 U1! LocalState_ι_addVestingOrLock_Л_participant := $ Л_participant ) >>
              (*isFirstPart? setRoundPre0(round) : setRound0(round); *) 
 $ Л_isFirstPart ? RoundsBase_Ф_setRoundPre0 (! $ Л_round !) ::: RoundsBase_Ф_setRound0 (! $ Л_round !) 
) ) >> 
        (* _setOrDeleteParticipant(beneficiary, participant); 
            sendAcceptAndReturnChange128(fee); *) 
ParticipantBase_Ф__setOrDeleteParticipant (! ( $ Л_beneficiary) , ↑17 D2! LocalState_ι_addVestingOrLock_Л_participant !) >> 
DePoolContract_Ф_sendAcceptAndReturnChange128 (! $ Л_fee !) .		 

Definition DePoolContract_Ф_addVestingOrLock ( Л_stake : XInteger64 ) 
                       ( Л_beneficiary : XAddress ) 
											 ( Л_withdrawalPeriod : XInteger32 ) 
											 ( Л_totalPeriod : XInteger32 ) 
											 ( Л_isVesting : XBool ) : LedgerT True := 
do r ← DePoolContract_Ф_addVestingOrLock' Л_stake Л_beneficiary Л_withdrawalPeriod Л_totalPeriod Л_isVesting ; 
return! ( fromValueValue r ). 


(*function addVestingStake(uint64 stake, address beneficiary, uint32 withdrawalPeriod, uint32 totalPeriod) public { 
    addVestingOrLock(beneficiary, withdrawalPeriod, totalPeriod, true); 
  } *) 
Definition DePoolContract_Ф_addVestingStake ( Л_stake : XInteger64 ) 
                                            (Л_beneficiary: XAddress) 
											                      (Л_withdrawalPeriod: XInteger32) 
											                      (Л_totalPeriod: XInteger32) 
                                              : LedgerT True := 
DePoolContract_Ф_addVestingOrLock (! $ Л_stake , $ Л_beneficiary , $ Л_withdrawalPeriod , $ Л_totalPeriod , $ xBoolTrue !). 

(* 
function addLockStake(uint64 stake, address beneficiary, uint32 withdrawalPeriod, uint32 totalPeriod) public { 
    addVestingOrLock(stake, beneficiary, withdrawalPeriod, totalPeriod, false);} 
*) 
Definition DePoolContract_Ф_addLockStake ( Л_stake : XInteger64 ) 
                                         (Л_beneficiary: XAddress) 
										                     (Л_withdrawalPeriod: XInteger32) 
										                     (Л_totalPeriod: XInteger32) 
                                       : LedgerT True := 
DePoolContract_Ф_addVestingOrLock (! $ Л_stake , $ Л_beneficiary , $ Л_withdrawalPeriod , $ Л_totalPeriod , $ xBoolFalse !).											 
 

(* 
function withdrawPart (uint64 withdrawValue) public { 
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
Require {{ msg_sender () ?!= $ xInt0 , ξ$ Errors_ι_IS_EXT_MSG }} ; 

                (* if (m_poolClosed) {return _sendError(STATUS_DEPOOL_CLOSED, 0); } *) 
If!! ( ↑ε12 DePoolContract_ι_m_poolClosed ) 
then { 
 return!!! ( DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_DEPOOL_CLOSED , $ xInt0 !) ) 
 } ; 
              (* optional(DePoolLib.Participant) optParticipant = fetchParticipant(msg.sender); 
               if (!optParticipant.hasValue()) { 
	               return _sendError(STATUS_NO_PARTICIPANT, 0); 
               }*) 
declareLocal Л_optParticipant :>: (XMaybe (ξ DePoolLib_ι_Participant)) := ParticipantBase_Ф_fetchParticipant (! msg_sender () !) ; 
If! ( !¬ ( $ Л_optParticipant ->hasValue ) ) 
then { 
  return!!! ( DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_NO_PARTICIPANT , $ xInt0 !) )													 
 } ; 
                  (*DePoolLib.Participant participant = optParticipant.get();*) 
declareLocal Л_participant :>: ξ DePoolLib_ι_Participant := $ Л_optParticipant ->get ; 
                     (*    participant.withdrawValue = withdrawValue;*) 
U0! Л_participant ^^ DePoolLib_ι_Participant_ι_withdrawValue := $ Л_withdrawValue ; 
                    (*    
                    _setOrDeleteParticipant(msg.sender, participant); 
                    sendAcceptAndReturnChange();  
                    *) 
(ParticipantBase_Ф__setOrDeleteParticipant (! msg_sender () , $ Л_participant !)) >> 
return!! (DePoolContract_Ф_sendAcceptAndReturnChange () ). 

Definition DePoolContract_Ф_withdrawPart ( Л_withdrawValue : XInteger64 ) 
                           : LedgerT (XErrorValue True XInteger) := 
do r ← DePoolContract_Ф_withdrawPart' Л_withdrawValue ; 
	return! (xErrorMapDefaultF (xValue ∘ fromValueValue) r xError).	 
	 
(* 
function withdrawAll()         
           public { 
    require(msg.sender != address(0), Errors.IS_EXT_MSG); 
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
	 
Definition DePoolContract_Ф_withdrawAll' : LedgerT (XErrorValue (XValueValue True) XInteger) := 
  (*require(msg.sender != address(0), Errors.IS_EXT_MSG);*) 
Require {{ msg_sender () ?!= $ xInt0 , ξ$ Errors_ι_IS_EXT_MSG }} ; 
(* if (m_poolClosed) { 
      return _sendError(STATUS_DEPOOL_CLOSED, 0); 
    } *) 
If!! ( ↑ε12 DePoolContract_ι_m_poolClosed ) 
then { 
 return!!! ( DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_DEPOOL_CLOSED , $ xInt0 !) ) 
 } ; 
(* optional(DePoolLib.Participant) optParticipant = fetchParticipant(msg.sender); 
    if (!optParticipant.hasValue()) { 
      return _sendError(STATUS_NO_PARTICIPANT, 0); 
    } *) 
declareLocal Л_optParticipant :>: (XMaybe (ξ DePoolLib_ι_Participant) ) := ParticipantBase_Ф_fetchParticipant (! msg_sender () !) ; 
If! ( !¬ ( $ Л_optParticipant ->hasValue ) ) 
then { 
 return!!! ( DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_NO_PARTICIPANT , $ xInt0 !) )													 
 } ; 
(*     DePoolLib.Participant participant = optParticipant.get(); *) 
declareLocal Л_participant :>: ξ DePoolLib_ι_Participant := $ Л_optParticipant ->get ; 
(*  participant.reinvest = false; *) 
U0! Л_participant ^^ DePoolLib_ι_Participant_ι_reinvest := $ xBoolFalse ; 
(*    
_setOrDeleteParticipant(msg.sender, participant); 
sendAcceptAndReturnChange();  
*) 
(ParticipantBase_Ф__setOrDeleteParticipant (! msg_sender () , $ Л_participant !)) >> 
return!! (DePoolContract_Ф_sendAcceptAndReturnChange () ). 


Definition DePoolContract_Ф_withdrawAll : LedgerT (XErrorValue True XInteger) := 
do r ← DePoolContract_Ф_withdrawAll' ; 
	return! (xErrorMapDefaultF (xValue ∘ fromValueValue) r xError). 


(* function cancelWithdrawal() public onlyInternalMessage {
        if (m_poolClosed) {
            return _sendError(STATUS_DEPOOL_CLOSED, 0);
        }

        optional(Participant) optParticipant = fetchParticipant(msg.sender);
        if (!optParticipant.hasValue()) {
            return _sendError(STATUS_NO_PARTICIPANT, 0);
        }
        Participant participant = optParticipant.get();

        participant.reinvest = true;
        participant.withdrawValue = 0;
        _setOrDeleteParticipant(msg.sender, participant);
        sendAcceptAndReturnChange();
    } *) 

Definition DePoolContract_Ф_cancelWithdrawal' : LedgerT (XErrorValue (XValueValue True) XInteger) := 
  (*require(msg.sender != address(0), Errors.IS_EXT_MSG);*) 
Require {{ msg_sender () ?!= $ xInt0 , $ Errors_ι_IS_EXT_MSG }} ; 
(* if (m_poolClosed) { 
      return _sendError(STATUS_DEPOOL_CLOSED, 0); 
    } *) 
If!! ( ↑ε12 DePoolContract_ι_m_poolClosed ) 
then { 
 return!!! ( DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_DEPOOL_CLOSED , $ xInt0 !) ) 
 } ; 
(* optional(DePoolLib.Participant) optParticipant = fetchParticipant(msg.sender); 
    if (!optParticipant.hasValue()) { 
      return _sendError(STATUS_NO_PARTICIPANT, 0); 
    } *) 
declareLocal Л_optParticipant :>: (XMaybe ( ξ DePoolLib_ι_Participant ) ) := ParticipantBase_Ф_fetchParticipant (! msg_sender () !) ; 
If! ( !¬ ( $ Л_optParticipant ->hasValue ) ) 
then { 
 return!!! ( DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_NO_PARTICIPANT , $ xInt0 !) )
 } ; 

                     (* DePoolLib.Participant participant = optParticipant.get(); *) 
declareLocal Л_participant :>: ξ DePoolLib_ι_Participant := $ Л_optParticipant ->get ; 
                    (*  participant.reinvest = true; *) 
U0! Л_participant ^^ DePoolLib_ι_Participant_ι_reinvest := $ xBoolTrue ; 
U0! Л_participant ^^ DePoolLib_ι_Participant_ι_withdrawValue := $ xInt0 ; 

(*    
_setOrDeleteParticipant(msg.sender, participant); 
sendAcceptAndReturnChange();  
*) 
(ParticipantBase_Ф__setOrDeleteParticipant (! msg_sender () , $ Л_participant !)) >> 
return!! (DePoolContract_Ф_sendAcceptAndReturnChange () ). 

Definition DePoolContract_Ф_cancelWithdrawal : LedgerT (XErrorValue True XInteger) := 
do r ← DePoolContract_Ф_cancelWithdrawal' ; 
	return! (xErrorMapDefaultF (xValue ∘ fromValueValue) r xError). 

(* 
  function transferStake(address dest, uint64 amount) public onlyInternalMessage {
        if (m_poolClosed) {
            return _sendError(STATUS_DEPOOL_CLOSED, 0);
        }

        // target address should be set.
        if (!dest.isStdAddrWithoutAnyCast() || dest.isStdZero())
            return _sendError(STATUS_INVALID_ADDRESS, 0);

        // check self transfer
        address src = msg.sender;
        if (src == dest)  {
            return _sendError(STATUS_TRANSFER_SELF, 0);
        }

        if (src == m_validatorWallet || dest == m_validatorWallet) {
            return _sendError(STATUS_TRANSFER_TO_OR_FROM_VALIDATOR, 0);
        }

        optional(Participant) optSrcParticipant = fetchParticipant(src);
        if (!optSrcParticipant.hasValue()) {
            return _sendError(STATUS_NO_PARTICIPANT, 0);
        }
        Participant srcParticipant = optSrcParticipant.get();

        if (amount == 0) {
            amount = DePoolLib.MAX_UINT64;
        }

        Participant destParticipant = getOrCreateParticipant(dest);

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
    }
*) 

(* Unset Typeclasses Iterative Deepening. 
Set Typeclasses Depth 10. 
 *) 
Definition DePoolContract_Ф_transferStake' (Л_dest : XAddress ) (Л_amount : XInteger64 ) : 
                      LedgerT ( XErrorValue (XValueValue True) XInteger ) := 
 (* require(msg.sender != address(0), Errors.IS_EXT_MSG); *)                      
 Require {{ msg_sender () ?!= $xInt0 ,  $ Errors_ι_IS_EXT_MSG  }} ; 										  
 (*init*) 
 (↑17 U1! LocalState_ι_transferStake_Л_amount := $ Л_amount)	>>	 
 
 (* if (m_poolClosed) { 
      return _sendError(STATUS_DEPOOL_CLOSED, 0); 
    } *) 
If!! ( ↑ε12 DePoolContract_ι_m_poolClosed ) 
then { 
 return!!! ( DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_DEPOOL_CLOSED , $ xInt0 !) ) 
 } ; 
 
 (* if (!dest.isStdAddrWithoutAnyCast() || dest.isStdZero()) 
     return _sendError(STATUS_INVALID_ADDRESS, 0);*) 
If!! ( ( !¬ ( ( $ Л_dest ) ->isStdAddrWithoutAnyCast() ) ) !| ( ( $ Л_dest ) ->isStdZero() ) ) 
 then { 
   return!!! ( DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_INVALID_ADDRESS , $ xInt0 !) ) 
   } ; 
 (* 	 address src = msg.sender; *) 
 declareLocal Л_src :>: XAddress := msg_sender ()	 ; 

(*     if (src == dest) { 
      return _sendError(STATUS_TRANSFER_SELF, 0); 
		} *) 
 If!! ( $ Л_src ?== $ Л_dest ) then { 
	return!!! ( DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_TRANSFER_SELF , $xInt0 !) ) 
 } ; 

(* if (src == m_validatorWallet || dest == m_validatorWallet) { 
      return _sendError(STATUS_TRANSFER_TO_OR_FROM_VALIDATOR, 0); 
    } *) 

If!! (( $Л_src ?== ↑ε2 ValidatorBase_ι_m_validatorWallet ) !| ( $Л_dest ?== ↑ε2 ValidatorBase_ι_m_validatorWallet)) then { 
	return!!! (DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_TRANSFER_TO_OR_FROM_VALIDATOR , $xInt0 !)) 
 } ; 
 (* optional(DePoolLib.Participant) optSrcParticipant = fetchParticipant(src); *) 
 declareLocal Л_optSrcParticipant :>: (XMaybe (ξ DePoolLib_ι_Participant) ) := ParticipantBase_Ф_fetchParticipant (! $Л_src !); 
 (* if (!optSrcParticipant.hasValue()) { 
      return _sendError(STATUS_NO_PARTICIPANT, 0); 
		} *) 
 If!! ( !¬ $Л_optSrcParticipant ->hasValue )then { 
	return!!! (DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_NO_PARTICIPANT , $xInt0 !)) 
 }	; 
 (* DePoolLib.Participant srcParticipant = optSrcParticipant.get(); *) 
 ( declareGlobal LocalState_ι_transferStake_Л_srcParticipant :>: ξ DePoolLib_ι_Participant := $Л_optSrcParticipant ->get) >> 

(* if (amount == 0) { 
      amount = DePoolLib.MAX_UINT64; 
    }*) 
 (If (↑17 D2! LocalState_ι_transferStake_Л_amount ?== $xInt0) then { 
	↑↑17 U2! LocalState_ι_transferStake_Л_amount := $ DePoolLib_ι_MAX_UINT64 
    }) >> 
 (*DePoolLib.Participant destParticipant = getOrCreateParticipant(dest);*) 	 
 ( declareGlobal! LocalState_ι_transferStake_Л_destParticipant :>: ξ DePoolLib_ι_Participant := ParticipantBase_Ф_getOrCreateParticipant (! $Л_dest !)) >> 
 (*uint64 totalSrcStake;*) 
 declareGlobal LocalState_ι_transferStake_Л_totalSrcStake :>: XInteger64 ; 
 (* uint64 transferred; *) 
 declareGlobal LocalState_ι_transferStake_Л_transferred :>: XInteger64 ; 
 (* mapping(uint64 => Round) rounds = m_rounds; *) 
 ( declareGlobal! LocalState_ι_transferStake_Л_rounds :>: ( XHMap XInteger64 RoundsBase_ι_Round ) := ↑11 D2! RoundsBase_ι_m_rounds) >> 
 (* optional(uint64, Round) pair = rounds.min(); *) 
 ( declareGlobal LocalState_ι_transferStake_Л_pair :>: ( XMaybe ( XInteger64 # RoundsBase_ι_Round ) ) := D1! (D2! LocalState_ι_transferStake_Л_rounds) ->min) >> 
 (*     while (pair.hasValue() && transferred < amount) { 
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
	 ((While ( ((↑17 D2! LocalState_ι_transferStake_Л_pair) ->hasValue)  !& 
		   ((↑17 D2! LocalState_ι_transferStake_Л_transferred) ?< (↑17 D2! LocalState_ι_transferStake_Л_amount)) ) do 
		  (
                                (* (uint64 roundId, Round round) = pair.get(); 
                                uint64 currentTransferred; 
                                uint64 srcStake; *) 
 			  declareLocal {( Л_roundId :>: XInteger64 , Л_round :>: RoundsBase_ι_Round )} := (↑17 D2! LocalState_ι_transferStake_Л_pair) ->get ; 
			  declareLocal Л_currentTransferred :>: XInteger64 ; 
			  declareLocal Л_srcStake :>: XInteger64 ; 

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
			  (↑17 U1! LocalState_ι_transferStake_Л_pair := D1! (D2! LocalState_ι_transferStake_Л_rounds) ->next $ Л_roundId) >> 
 			  continue! I 
		  )))  >> 

    (* if (amount != DePoolLib.MAX_UINT64) { 
      if (totalSrcStake < amount) { 
        return _sendError(STATUS_TRANSFER_AMOUNT_IS_TOO_BIG, 0); 
      } 

      if (transferred < amount) { 
        return _sendError(STATUS_REMAINING_STAKE_LESS_THAN_MINIMAL, 0); 
      } 
		} *) 
		 
		If! ((↑17 D2! LocalState_ι_transferStake_Л_amount) ?!= ( ξ$ DePoolLib_ι_MAX_UINT64 )) then { 
			If!! ((↑17 D2! LocalState_ι_transferStake_Л_totalSrcStake) ?< (↑17 D2! LocalState_ι_transferStake_Л_amount)) then 
			{ 
				return!!! (DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_TRANSFER_AMOUNT_IS_TOO_BIG , $ xInt0 !)) 
			} ; 
			If! ((↑17 D2! LocalState_ι_transferStake_Л_transferred) ?< (↑17 D2! LocalState_ι_transferStake_Л_amount)) then 
			{ 
				return!!! (DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_REMAINING_STAKE_LESS_THAN_MINIMAL , $ xInt0 !)) 
			} ; $ I 
    } ; 

		(* m_rounds = rounds; *) 
		(↑↑11 U2! RoundsBase_ι_m_rounds := ↑17 D2! LocalState_ι_transferStake_Л_rounds) >> 

		(* _setOrDeleteParticipant(src, srcParticipant); *) 
		ParticipantBase_Ф__setOrDeleteParticipant (! $ Л_src , (↑17 D2! LocalState_ι_transferStake_Л_srcParticipant) !) >> 
    (* _setOrDeleteParticipant(dest, destParticipant); *) 
		ParticipantBase_Ф__setOrDeleteParticipant (! $ Л_dest , (↑17 D2! LocalState_ι_transferStake_Л_destParticipant) !) >> 
		(* IParticipant(dest).onTransfer{bounce: false}(src, amount); *) 

   ( IParticipant of ( $ Л_dest ) ->sendMessage ( IParticipant_И_onTransferF (!! $ Л_src , ↑17 D2! LocalState_ι_transferStake_Л_amount !!) )
                     with {|| messageBounce ::= $ xBoolFalse ||} ) >>

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
                     (* uint64 stakes = 0; *) 
  ( declareGlobal LocalState_ι_totalParticipantFunds_Л_stakes :>: XInteger64 := $ xInt0) >> 
                     (*   optional(uint64, Round) pair = minRound(); *) 
  ( declareGlobal! LocalState_ι_totalParticipantFunds_Л_pair :>: ( XMaybe (XInteger64 # RoundsBase_ι_Round) ) := RoundsBase_Ф_minRound ()) >> 
                     (*   while (pair.hasValue()) { *) 
  (While ((↑17 D2! LocalState_ι_totalParticipantFunds_Л_pair) ->hasValue) do ( 
                     (*     (uint64 id, Round round) = pair.get(); *) 
  declareLocal {( Л_id :>: XInteger64 , Л_round :>: RoundsBase_ι_Round )} := (↑17 D2! LocalState_ι_totalParticipantFunds_Л_pair) ->get ; 
                     (*    RoundStep step = round.step; *) 
  declareLocal Л_step :>: RoundsBase_ι_RoundStep := $ (Л_round ->> RoundsBase_ι_Round_ι_step) ; 
                     (*     if (id != ingoreRoundId && step != RoundStep.Completed) { *) 
  (If (( $Л_id ?!= $Л_ingoreRoundId) !& ( $Л_step ?!= ξ$ RoundsBase_ι_RoundStepP_ι_Completed )) then { 
                      (*       if (step == RoundStep.Completing) { *) 
  If ( $Л_step ?== ξ$ RoundsBase_ι_RoundStepP_ι_Completing) then { 
                       (*         if (round.completionReason == CompletionReason.ValidatorIsPunished) *) 
  If ( $ (Л_round ->> RoundsBase_ι_Round_ι_completionReason) ?== ξ$ RoundsBase_ι_CompletionReasonP_ι_ValidatorIsPunished) then { 
  (*           stakes += (round.unused + round.recoveredStake) - round.handledStakesAndRewards; *) 
    (↑17 U1! LocalState_ι_totalParticipantFunds_Л_stakes !+= ( $ (Л_round ->> RoundsBase_ι_Round_ι_unused) !+ 
                                  $ (Л_round ->> RoundsBase_ι_Round_ι_recoveredStake)) !- 
                                  $ (Л_round ->> RoundsBase_ι_Round_ι_handledStakesAndRewards)) 
  } 
  (*         else { *) 
  else { 
  (*           stakes += (round.stake + round.rewards) - round.handledStakesAndRewards; *) 
    (↑17 U1! LocalState_ι_totalParticipantFunds_Л_stakes !+= ( $ (Л_round ->> RoundsBase_ι_Round_ι_stake) !+ 
       $ (Л_round ->> RoundsBase_ι_Round_ι_rewards)) !- $ (Л_round ->> RoundsBase_ι_Round_ι_handledStakesAndRewards)) 
  (*         } *) 
  } 
  (*      } else if ( *) 
  (*        step == RoundStep.PrePooling || *) 
  (*         step == RoundStep.Pooling || *) 
  (*         step == RoundStep.WaitingValidatorRequest || *) 
  (*         step == RoundStep.WaitingUnfreeze && round.completionReason != CompletionReason.Undefined *) 
  (*       ) { *) 
  } else { If ( $Л_step ?== ξ$ RoundsBase_ι_RoundStepP_ι_PrePooling) !| 
        ( $Л_step ?== ξ$ RoundsBase_ι_RoundStepP_ι_Pooling) !| 
        ( $Л_step ?== ξ$ RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest) !| 
        (( $Л_step ?== ξ$ RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze) !& 
        ( $ (Л_round ->> RoundsBase_ι_Round_ι_completionReason) ?== ξ$ RoundsBase_ι_CompletionReasonP_ι_Undefined)) then { 
  (*         stakes += round.stake; *) 
    (↑17 U1! LocalState_ι_totalParticipantFunds_Л_stakes !+= $ (Л_round ->> RoundsBase_ι_Round_ι_stake)) 
  (*       } else { *) 
  } else { 
  (*        stakes += round.unused; *) 
    (↑17 U1! LocalState_ι_totalParticipantFunds_Л_stakes !+= $ (Л_round ->> RoundsBase_ι_Round_ι_unused)) 
  (*       } *) 
  } 
  (*     } *) 
  } 
  }) >> 
  (*     pair = nextRound(id); *) 
  (↑↑17 U2! LocalState_ι_totalParticipantFunds_Л_pair := RoundsBase_Ф_nextRound (! $Л_id !)) >> 
  (*   } *) 
  continue! I) ) >> 
  (*   return stakes; *) 
 return!! (↑17 D2! LocalState_ι_totalParticipantFunds_Л_stakes). 

 
(* Set Typeclasses Iterative Deepening. 
Set Typeclasses Depth 10. *) 

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
                  (* uint stakes = totalParticipantFunds(0); 
                  uint64 msgValue = uint64(msg.value); 
                  uint sum = CRITICAL_THRESHOLD + stakes + msgValue; *) 
  declareLocal Л_stakes :>: XInteger := DePoolContract_Ф_totalParticipantFunds (! $xInt0 !) ; 
  declareLocal Л_msgValue :>: XInteger64 := msg_value ; 
  declareLocal Л_sum :>: XInteger := $ DePool_ι_CRITICAL_THRESHOLD !+ $ Л_stakes !+ $ Л_msgValue; 
  If! ( tvm_balance () ?< $ Л_sum ) then { 
       (* uint replenishment = sum - address(this).balance; *) 
    declareLocal Л_replenishment :>: XInteger := $ Л_sum !- tvm_balance (); 
    (->emit TooLowDePoolBalance (!! $ Л_replenishment !!)) >> 
    return! (xError xBoolFalse)         
  }; return! xBoolTrue. 

Definition DePoolContract_Ф_checkPureDePoolBalance : LedgerT XBool :=   
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
    ) public functionID(0x4E73744B) onlyValidatorContract {
        if (m_poolClosed)
            return _sendError(STATUS_DEPOOL_CLOSED, 0);
        tvm.accept();
        if (checkPureDePoolBalance()) {
            Round round = getRound1();
            if (round.step != RoundStep.WaitingValidatorRequest)
                return _sendError(STATUS_NO_ELECTION_ROUND, 0);
            if (stakeAt != round.supposedElectedAt)
                return _sendError(STATUS_INVALID_ELECTION_ID, 0);
            round.validatorRequest = Request(queryId, validatorKey, stakeAt, maxFactor, adnlAddr, signature);
            _sendElectionRequest(round.proxy, round.id, round.stake, round.validatorRequest, round.elector);
            round.step = RoundStep.WaitingIfStakeAccepted;
            setRound1(round);
        }
        _returnChange();
    } *) 

Definition DePoolContract_Ф_participateInElections' ( Л_queryId : XInteger64 ) 
													( Л_validatorKey : XInteger256 ) 
													( Л_stakeAt : XInteger32 ) 
													( Л_maxFactor : XInteger32 ) 
													( Л_adnlAddr : XInteger256 ) 
													( Л_signature : XList XInteger8 ) 
             : LedgerT ( XErrorValue (XValueValue True) XInteger ) := 
              (*require(msg.sender == m_validatorWallet, Errors.IS_NOT_VALIDATOR);*) 
Require {{ msg_sender () ?== ↑2 D2! ValidatorBase_ι_m_validatorWallet , $ Errors_ι_IS_NOT_VALIDATOR }} ; 
                (*if (m_poolClosed) 
                   return _sendError(STATUS_DEPOOL_CLOSED, 0);*) 
If!! ( ↑12 D2! DePoolContract_ι_m_poolClosed ) 
then { 
 return!!! ( DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_DEPOOL_CLOSED , $ xInt0 !) ) 
} ; 
                   (* tvm.accept(); *) 					 
tvm_accept () >> 
If! (DePoolContract_Ф_checkPureDePoolBalance ()) then {							 
                    (*Round round = getRound1();*) 
declareLocal Л_round :>: RoundsBase_ι_Round := RoundsBase_Ф_getRound1 (); 
                    (*if (round.step != RoundStep.WaitingValidatorRequest) 
                      return _sendError(STATUS_NO_ELECTION_ROUND, 0);*) 
If!! ( $ Л_round ->> RoundsBase_ι_Round_ι_step ?!= ξ$ RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest ) 
then { 
 return!!! ( DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_NO_ELECTION_ROUND , $ xInt0 !) ) 
} ; 
                       (*if (stakeAt != round.supposedElectedAt) 
                          return _sendError(STATUS_INVALID_ELECTION_ID, 0);*) 
If! ( $ Л_stakeAt ?!=  $ (Л_round ->> RoundsBase_ι_Round_ι_supposedElectedAt) ) 
then { 
 return!!! ( DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_INVALID_ELECTION_ID , $ xInt0 !) ) 
} ; 
                        (*round.validatorRequest = DePoolLib.Request(queryId, validatorKey, stakeAt, maxFactor, adnlAddr, signature);*) 
U0! Л_round ^^ RoundsBase_ι_Round_ι_validatorRequest := $ (ξ DePoolLib_ι_RequestC Л_queryId Л_validatorKey Л_stakeAt Л_maxFactor Л_adnlAddr Л_signature) ; 
                          (*_sendElectionRequest(round.proxy, round.id, round.stake, round.validatorRequest, round.elector);*) 
(ProxyBase_Ф__sendElectionRequest (! $ (Л_round ->> RoundsBase_ι_Round_ι_proxy) , 
									  $ (Л_round ->> RoundsBase_ι_Round_ι_id) , 
									  $ (Л_round ->> RoundsBase_ι_Round_ι_stake) , 
									  $ (Л_round ->> RoundsBase_ι_Round_ι_validatorRequest) , 
									  $ (Л_round ->> RoundsBase_ι_Round_ι_elector) !)) >> 
                      (*round.step = RoundStep.WaitingIfStakeAccepted;*) 
U0! Л_round ^^ RoundsBase_ι_Round_ι_step := ξ$ RoundsBase_ι_RoundStepP_ι_WaitingIfStakeAccepted ; 
                   (*setRound1(round);*) 	 
(RoundsBase_Ф_setRound1 (! $ Л_round !) ) } ; 
                   (* _returnChange();*) 
DePoolContract_Ф__returnChange (). 
                          (*00:11*) 
                          (* = 17 minutes / 11 clauses = ~1,5 min / clause*) 	 

Definition DePoolContract_Ф_participateInElections ( Л_queryId : XInteger64 ) 
													( Л_validatorKey : XInteger256 ) 
													( Л_stakeAt : XInteger32 ) 
													( Л_maxFactor : XInteger32 ) 
													( Л_adnlAddr : XInteger256 ) 
													( Л_signature : XList XInteger8 ) 
             : LedgerT ( XErrorValue True XInteger ) := 
do r ← DePoolContract_Ф_participateInElections' Л_queryId Л_validatorKey Л_stakeAt Л_maxFactor Л_adnlAddr Л_signature; 
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
            round2.step = RoundStep.WaitingUnfreeze;
            if (round2.completionReason == CompletionReason.Undefined) {
                round2.completionReason = CompletionReason.NoValidatorRequest;
            }
            round2.unfreeze = 0;
        } else if (round2.step == RoundStep.Completing) {
            this.completeRoundWithChunk{bounce: false}(round2.id, 1);
            // For situations when there exists stake with value==V, but DePool balance == (V - epsilon)
            // In such situations some extra funds must be sent to DePool balance (See function 'receiveFunds')
        }

        // try to update unfreeze time
        if (round2.vsetHashInElectionPhase != curValidatorHash &&
            round2.vsetHashInElectionPhase != prevValidatorHash &&
            round2.unfreeze == DePoolLib.MAX_TIME
        )
        {
            round2.unfreeze = validationStart + round2.stakeHeldFor;
        }
        if (now >= uint(round2.unfreeze) + DePoolLib.ELECTOR_UNFREEZE_LAG) {
            if (round2.step == RoundStep.WaitingUnfreeze &&
                round2.completionReason != CompletionReason.Undefined
            )
            {
                round2 = startRoundCompleting(round2, round2.completionReason);
            } else if (
                round2.step == RoundStep.WaitingValidationStart ||
                round2.step == RoundStep.WaitingUnfreeze
            )
            {
                round2.step = RoundStep.WaitingReward;
                _recoverStake(round2.proxy, round2.id, round2.elector);
            }
        }
(*         return round2;    } *)  *)

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
( declareInit LocalState_ι_updateRound2_Л_round2 := $ Л_round2) >>						 
                      (* if (round2.step == RoundStep.WaitingValidatorRequest) { *) 
( If ( (↑17 D2! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_step) ?==  ξ$ RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest ) then { 
      (*       			round2.step = RoundStep.WaitingUnfreeze; *) 
   (↑17 U1! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_step := $RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze	) >> 
                      (* if (round2.completionReason == CompletionReason.Undefined) { 
                        round2.completionReason = CompletionReason.NoValidatorRequest; 
			                } *) 
	 (If (↑17 D2! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_completionReason ?== ξ$ RoundsBase_ι_CompletionReasonP_ι_Undefined) then { 
		↑17 U1! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_completionReason := $RoundsBase_ι_CompletionReasonP_ι_NoValidatorRequest 
	 })	>>	 
		                 (* round2.unfreeze = 0; *) 
	 (↑17 U1! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_unfreeze := $xInt0)	  
} 
		                 (* else if (round2.step == RoundStep.Completing) { *) 
else { 
	 If ((↑17 D2! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_step) ?==  ξ$ RoundsBase_ι_RoundStepP_ι_Completing ) 
   then { 
		this->sendMessage ( DePoolContract_Ф_completeRoundWithChunkF (!! ↑17 D2! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_id , 
						 																	 $ xInt1 !!)) with {|| messageBounce ::= $ xBoolFalse ||} 
	     } 
} ) >> 
                      (* if (round2.vsetHashInElectionPhase != curValidatorHash && 
                            round2.vsetHashInElectionPhase != prevValidatorHash && 
			                      round2.unfreeze == DePoolLib.MAX_TIME) *) 
			 
(If ( ((↑17 D2! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_vsetHashInElectionPhase) ?!= $Л_curValidatorHash) !& 
	 ((↑17 D2! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_vsetHashInElectionPhase) ?!= $Л_prevValidatorHash) !& 
	 ((↑17 D2! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_unfreeze) ?== ξ$ DePoolLib_ι_MAX_TIME )) then { 
		 (*      { 
            round2.unfreeze = validationStart + round2.stakeHeldFor;  } *) 
    (↑17 U1! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_unfreeze := 
              $Л_validationStart !+ 
             (D1! (D2! LocalState_ι_updateRound2_Л_round2) ^^ RoundsBase_ι_Round_ι_stakeHeldFor)) 
} ) >> 
( 
	                  (* if (now >= uint(round2.unfreeze) + DePoolLib.ELECTOR_UNFREEZE_LAG) { *) 
	If ( tvm_now () ?>= ((↑17 D2! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_unfreeze) !+ 
						 ( ξ$ DePoolLib_ι_ELECTOR_UNFREEZE_LAG )) ) then { 
		(* if (round2.step == RoundStep.WaitingUnfreeze && 
        round2.completionReason != CompletionReason.Undefined 
			) *) 
		If ( ((↑17 D2! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_step) ?== $RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze ) !& 
		   ((↑17 D2! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_completionReason) ?!= ξ$ RoundsBase_ι_CompletionReasonP_ι_Undefined)) then { 
        (* round2 = startRoundCompleting(round2, round2.completionReason); *) 
      ↑↑17 U2! LocalState_ι_updateRound2_Л_round2	 := DePoolContract_Ф_startRoundCompleting (! 
              ↑17 D2! LocalState_ι_updateRound2_Л_round2 , 
														↑17 D2! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_completionReason !) 
		}	else { 
			(* if ( 
        round2.step == RoundStep.WaitingValidationStart || 
        round2.step == RoundStep.WaitingUnfreeze 
			) *) 
			If ( ((↑17 D2! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_step) ?== ξ$ RoundsBase_ι_RoundStepP_ι_WaitingValidationStart) !| 
				 ((↑17 D2! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_step) ?== ξ$ RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze) ) then { 
				(* { 
                round2.step = RoundStep.WaitingReward; 
                _recoverStake(round2.proxy, round2.id, round2.elector); 
			} *) 
			(↑17 U1! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_step := ξ$ RoundsBase_ι_RoundStepP_ι_WaitingReward) >> 
			(ProxyBase_Ф__recoverStake (! ↑17 D2! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_proxy , 
										 ↑17 D2! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_id , 
										 ↑17 D2! LocalState_ι_updateRound2_Л_round2 ^^ RoundsBase_ι_Round_ι_elector !)) 
			} 
      
		} 
	} 
) >> 

(* return round2;*) 

return!! (↑17 D2! LocalState_ι_updateRound2_Л_round2). 


(* function isEmptyRound(Round round) private pure returns (bool) { 
  return round.step == RoundStep.Completed || round.stake == 0; 
} *) 
 
Definition DePoolContract_Ф_isEmptyRound (Л_round: RoundsBase_ι_Round) : LedgerT XBool := 
 return!! ( $(Л_round ->> RoundsBase_ι_Round_ι_step) ?== (ξ$ RoundsBase_ι_RoundStepP_ι_Completed) !| 
   $(Л_round ->> RoundsBase_ι_Round_ι_stake) ?== $ xInt0). 

(* 
function updateRounds() private { 
    (uint32 validatorsElectedFor, uint32 electionsStartBefore,,) = roundTimeParams(); 
    (uint256 curValidatorHash, uint32 validationStart, uint32 validationEnd) = getCurValidatorData(); 
    uint256 prevValidatorHash = getPrevValidatorHash(); 
    bool areElectionsStarted = now >= validationEnd - electionsStartBefore; 
    Round roundPre0 = getRoundPre0();     Round round0  = getRound0();     Round round1  = getRound1();     Round round2  = getRound2(); 
        if (m_poolClosed && isEmptyRound(round2) && isEmptyRound(round1) && isEmptyRound(round0) && isEmptyRound(roundPre0) ) { 
      selfdestruct(m_validatorWallet); 
      tvm.exit(); 
    } 

    round2 = updateRound2(round2, prevValidatorHash, curValidatorHash, validationStart); 

        if (round1.step == RoundStep.WaitingValidationStart && 
      round1.vsetHashInElectionPhase == prevValidatorHash 
    ) 
    { 
      round1.step = RoundStep.WaitingIfValidatorWinElections; 
      _recoverStake(round1.proxy, round1.id, round1.elector); 
    } 

        if (areElectionsStarted &&       round1.vsetHashInElectionPhase != curValidatorHash &&       round2.step == RoundStep.Completed     ) { 
            delete m_rounds[round2.id]; 
      round2 = round1; 
      round1 = round0; 
      round0 = roundPre0; 
      roundPre0 = generateRound(); 

            round2 = updateRound2(round2, prevValidatorHash, curValidatorHash, validationStart); 

            if (!m_poolClosed) { 
        round1.supposedElectedAt = validationEnd; 
round1.validatorsElectedFor = validatorsElectedFor; 
        round1.elector = getElector(); 
        round1.vsetHashInElectionPhase = curValidatorHash; 
        (, , ,uint32 stakeHeldFor) = roundTimeParams(); 
        round1.stakeHeldFor = stakeHeldFor; 
                round1.validatorStake = stakeSum(round1.stakes[m_validatorWallet]); 
        bool isValidatorStakeOk = round1.validatorStake >= m_validatorAssurance; 
        if (!isValidatorStakeOk) { 
          round1.step = RoundStep.WaitingUnfreeze; 
          round1.completionReason = CompletionReason.ValidatorStakeIsTooSmall; 
          round1.unfreeze = 0; 
        } else { 
          round1.step = RoundStep.WaitingValidatorRequest; 
          emit StakeSigningRequested(round1.supposedElectedAt, round1.proxy); 
        } 
      } 

            if (!m_poolClosed) 
        round0.step = RoundStep.Pooling; 
    } 

    setRoundPre0(roundPre0); 
    setRound0(round0); 
    setRound1(round1); 
    setRound2(round2); 
  }*) 

Definition DePoolContract_Ф_updateRounds : LedgerT (XErrorValue (XValueValue True) XInteger) := 
             (* (uint32 validatorsElectedFor, uint32 electionsStartBefore,,) = roundTimeParams();  *) 
declareLocal {( Л_validatorsElectedFor :>: XInteger32 , Л_electionsStartBefore :>: XInteger32 , _ :>: _ , _ :>: _ )} ??:= ConfigParamsBase_Ф_roundTimeParams () ; 
               (* (uint256 curValidatorHash, uint32 validationStart, uint32 validationEnd) = getCurValidatorData(); *) 
declareLocal {( Л_curValidatorHash :>: XInteger256 , Л_validationStart :>: XInteger32 , Л_validationEnd  :>: XInteger32 )} ??:= ConfigParamsBase_Ф_getCurValidatorData () ; 
                (*uint256 prevValidatorHash = getPrevValidatorHash();*) 
declareLocal Л_prevValidatorHash  :>: XInteger256 ??:= ConfigParamsBase_Ф_getPrevValidatorHash () ; 
                (*bool areElectionsStarted = now >= validationEnd - electionsStartBefore;*) 
declareLocal Л_areElectionsStarted :>: XBool := ( tvm_now () ?>=  $ Л_validationEnd !- $ Л_electionsStartBefore ) ; 

                (*Round roundPre0 = getRoundPre0(); *) 
( declareGlobal! LocalState_ι_updateRounds_Л_roundPre0 :>: RoundsBase_ι_Round := RoundsBase_Ф_getRoundPre0 () ) >> 
                (*Round round0  = getRound0();*) 
( declareGlobal! LocalState_ι_updateRounds_Л_round0 :>: RoundsBase_ι_Round := RoundsBase_Ф_getRound0 () ) >> 
                (*Round round1  = getRound1();*) 
( declareGlobal! LocalState_ι_updateRounds_Л_round1 :>: RoundsBase_ι_Round := RoundsBase_Ф_getRound1 () ) >> 
(* Round round2  = getRound2(); *) 
( declareGlobal! LocalState_ι_updateRounds_Л_round2 :>: RoundsBase_ι_Round := RoundsBase_Ф_getRound2 () ) >> 

(*     if (m_poolClosed && isEmptyRound(round2) && isEmptyRound(round1) && isEmptyRound(round0) && isEmptyRound(roundPre0) ) { 
      selfdestruct(m_validatorWallet); 
      tvm.exit(); 
    } *) 
If2!! ((↑ε12 DePoolContract_ι_m_poolClosed ) !& 
  (DePoolContract_Ф_isEmptyRound (! ↑17 D2! LocalState_ι_updateRounds_Л_round2 !) ) !& 
  (DePoolContract_Ф_isEmptyRound (! ↑17 D2! LocalState_ι_updateRounds_Л_round1 !) ) !& 
  (DePoolContract_Ф_isEmptyRound (! ↑17 D2! LocalState_ι_updateRounds_Л_round0 !) ) !& 
  (DePoolContract_Ф_isEmptyRound (! ↑17 D2! LocalState_ι_updateRounds_Л_roundPre0 !))) then { 
    (->selfdestruct ( ↑2 D2! ValidatorBase_ι_m_validatorWallet ) ) >> 
    tvm_exit () 
  };          

(*round2 = updateRound2(round2, prevValidatorHash, curValidatorHash, validationStart);*) 
(↑↑17 U2! LocalState_ι_updateRounds_Л_round2 := DePoolContract_Ф_updateRound2 (! ↑17 D2! LocalState_ι_updateRounds_Л_round2 , 
																				  $ Л_prevValidatorHash , 
																				  $ Л_curValidatorHash , 
                      $ Л_validationStart !) ) >> 

(* 
if (round1.step == RoundStep.WaitingValidationStart && 
	round1.vsetHashInElectionPhase == prevValidatorHash 
) 
{ 
	round1.step = RoundStep.WaitingIfValidatorWinElections; 
	_recoverStake(round1.proxy, round1.id, round1.elector); 
} 
*) 
If!! ( (↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_step ?== ξ$ RoundsBase_ι_RoundStepP_ι_WaitingValidationStart) !& 
(↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_vsetHashInElectionPhase ?== $ Л_prevValidatorHash)) then { 

(↑17 U1! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_step := ξ$ RoundsBase_ι_RoundStepP_ι_WaitingIfValidatorWinElections) >> 
ProxyBase_Ф__recoverStake (! ↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_proxy , 
              ↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_id , 
              ↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_elector !) >> $ xValue I 
}; 
                                          
(*if (areElectionsStarted && 	round1.vsetHashInElectionPhase != curValidatorHash && 	round2.step == RoundStep.Completed ) {*) 																				 
If! ( $ Л_areElectionsStarted !& 
	 (↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_vsetHashInElectionPhase ?!= $ Л_curValidatorHash) !& 
	 (↑17 D2! LocalState_ι_updateRounds_Л_round2 ^^ RoundsBase_ι_Round_ι_step ?== ξ$ RoundsBase_ι_RoundStepP_ι_Completed)) then { 
		(*delete m_rounds[round2.id];*) 
		(↑↑11 U2! delete RoundsBase_ι_m_rounds [[ ↑17 D2! LocalState_ι_updateRounds_Л_round2 ^^ RoundsBase_ι_Round_ι_id ]]) >> 
		(*		 round2 = round1;*) 
		(↑17 U1! LocalState_ι_updateRounds_Л_round2 := D2! LocalState_ι_updateRounds_Л_round1) >> 
		(*round1 = round0;*) 
		(↑17 U1! LocalState_ι_updateRounds_Л_round1 := D2! LocalState_ι_updateRounds_Л_round0) >> 
    (*round0 = roundPre0;*) 
    (↑17 U1! LocalState_ι_updateRounds_Л_round0 := D2! LocalState_ι_updateRounds_Л_roundPre0) >> 
    (*roundPre0 = generateRound();*) 
		(↑↑17 U2! LocalState_ι_updateRounds_Л_roundPre0 := DePoolContract_Ф_generateRound () ) >> 
    
    (*round2 = updateRound2(round2, prevValidatorHash, curValidatorHash, validationStart, stakeHeldFor);*) 
		(↑↑17 U2! LocalState_ι_updateRounds_Л_round2 := DePoolContract_Ф_updateRound2 (! ↑17 D2! LocalState_ι_updateRounds_Л_round2 , 
																				  $ Л_prevValidatorHash , 
																				  $ Л_curValidatorHash , 
                                          $ Л_validationStart !) ) >> 
    If! ( !¬ (↑12 D2! DePoolContract_ι_m_poolClosed) ) then { 
      (*round1.supposedElectedAt = validationEnd;*) 
      (↑17 U1! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_supposedElectedAt := $ 	Л_validationEnd) >> 
                       (* round1.validatorsElectedFor = validatorsElectedFor; *) 
      (↑17 U1! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_validatorsElectedFor := $ Л_validatorsElectedFor ) >> 
      (*round1.elector = getElector();*) 
      ↑↑17 U2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_elector ??:= ConfigParamsBase_Ф_getElector () ; 
      (*round1.vsetHashInElectionPhase = curValidatorHash;*) 
      (↑17 U1! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_vsetHashInElectionPhase := $ Л_curValidatorHash) >> 
      (*(, , ,uint32 stakeHeldFor) = roundTimeParams();*) 
declareLocal {( _ :>: _ , _ :>: _ , _ :>: _ , Л_stakeHeldFor :>: XInteger32 )} ?:= ConfigParamsBase_Ф_roundTimeParams () ; 
      (* round1.stakeHeldFor = stakeHeldFor; *) 
      (↑17 U1! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_stakeHeldFor := $ Л_stakeHeldFor) >> 

      (*           round1.validatorStake = stakeSum(round1.stakes[m_validatorWallet]); 
          bool isValidatorStakeOk = round1.validatorStake >= m_validatorAssurance; *) 
      (↑↑17 U2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_validatorStake := 
          RoundsBase_Ф_stakeSum (! D1! (↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_stakes) [[ ↑2 D2! ValidatorBase_ι_m_validatorWallet ]] !)) >> 
      declareLocal Л_isValidatorStakeOk :>: XBool := (↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_validatorStake) ?>= 
                     (↑12 D2! DePoolContract_ι_m_validatorAssurance)	; 
      (*if (!isValidatorStakeOk) { 
      round1.step = RoundStep.WaitingUnfreeze; 
      round1.completionReason = CompletionReason.ValidatorStakeIsTooSmall; 
      round1.unfreeze = 0; 
    } else { 
      round1.step = RoundStep.WaitingValidatorRequest; 
      emit stakeSigningRequested(round1.supposedElectedAt, round1.proxy); 
    }*) 
      (If ( !¬ $ Л_isValidatorStakeOk ) then { 
        (↑17 U1! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_step := ξ$ RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze) >> 
        (↑17 U1! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_completionReason := ξ$ RoundsBase_ι_CompletionReasonP_ι_ValidatorStakeIsTooSmall) >> 
        (↑17 U1! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_unfreeze := $ xInt0) 
      } else { 
        (↑17 U1! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_step := ξ$ RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest) >> 
        (->emit StakeSigningRequested (!! ↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_supposedElectedAt , 
                        ↑17 D2! LocalState_ι_updateRounds_Л_round1 ^^ RoundsBase_ι_Round_ι_proxy  !!)) 
      }) }; 
      (* if (!m_poolClosed) 
        round0.step = RoundStep.Pooling; *) 

      (If ( !¬ (↑12 D2! DePoolContract_ι_m_poolClosed) ) then { 
        (↑17 U1! LocalState_ι_updateRounds_Л_round0 ^^ RoundsBase_ι_Round_ι_step := ξ$ RoundsBase_ι_RoundStepP_ι_Pooling) 
      })  
      
      } ;        
      (*     setRoundPre0(roundPre0); 
            setRound0(round0); 
            setRound1(round1); 
            setRound2(round2); *) 
      ( RoundsBase_Ф_setRoundPre0 (! ↑17 D2! LocalState_ι_updateRounds_Л_roundPre0 !) ) >> 
      ( RoundsBase_Ф_setRound0 (! ↑17 D2! LocalState_ι_updateRounds_Л_round0 !) ) >> 
      ( RoundsBase_Ф_setRound1 (! ↑17 D2! LocalState_ι_updateRounds_Л_round1 !) ) >> 
      ( RoundsBase_Ф_setRound2 (! ↑17 D2! LocalState_ι_updateRounds_Л_round2 !) ) >> 
return! (xValue I) . 

(* 
function ticktock() public override { 
    require(msg.sender != address(0), Errors.IS_EXT_MSG); 

    if (checkPureDePoolBalance()) 
    { 
      updateRounds(); 
    } 
    if (msg.sender != address(this)) 
      _returnChange(); 
  } 
*) 
  
Definition DePoolContract_Ф_ticktock : LedgerT ( XErrorValue True XInteger ) := 
 Require2 {{ msg_sender () ?!= $xInt0, ξ$ Errors_ι_IS_EXT_MSG }} ; 
 If! (DePoolContract_Ф_checkPureDePoolBalance () ) then 
 { U0! _ ?:= DePoolContract_Ф_updateRounds () ; $I } ; 
 (If (msg_sender () ?!= tvm_address () ) then { 
  DePoolContract_Ф__returnChange () 
 }). 
   
(*   
function acceptRewardAndStartRoundCompleting(Round round2, uint64 value) private returns (Round) { 
    uint64 effectiveStake = round2.stake - round2.unused; 
    uint64 reward = value - effectiveStake; 
    round2.grossReward = reward; 

    reward -= math.min ( reward , RET_OR_REINV_FEE + round2.participantQty * RET_OR_REINV_FEE ) ; 

    round2.rewards = math.muldiv(reward, m_participantRewardFraction, 100); 
        round2.rewards -= math.min(round2.rewards, round2.participantQty * RET_OR_REINV_FEE); 

    uint64 validatorReward = math.muldiv(reward, m_validatorRewardFraction, 100); 
    
    m_validatorWallet.transfer(validatorReward, false, 1); 

    round2 = startRoundCompleting(round2, CompletionReason.RewardIsReceived); 
    return round2; 
  } *) 

Definition DePoolContract_Ф_acceptRewardAndStartRoundCompleting ( Л_round2 : RoundsBase_ι_Round ) 
                                ( Л_value : XInteger64 ) : 
                                 LedgerT RoundsBase_ι_Round := 
(* uint64 effectiveStake = round2.stake - round2.unused; *) 
declareLocal Л_effectiveStake :>: XInteger64 := $ (Л_round2 ->> RoundsBase_ι_Round_ι_stake) !- 
                      $ (Л_round2 ->> RoundsBase_ι_Round_ι_unused) ; 
(* uint64 reward = value - effectiveStake; *) 
declareLocal Л_reward :>: XInteger64  := $ Л_value !- $ Л_effectiveStake ; 
       (* round2.grossReward = reward; *) 
U0! Л_round2 ^^ RoundsBase_ι_Round_ι_grossReward := $ Л_reward ; 
(* reward -= math.min ( reward , RET_OR_REINV_FEE + round2.participantQty * RET_OR_REINV_FEE ) ; *) 
U0! Л_reward !-= ( math->min2 (! $ Л_reward , 
               ( ( $ DePool_ι_RET_OR_REINV_FEE ) !+ 
                 $ ( Л_round2 ->> RoundsBase_ι_Round_ι_participantQty ) !* 
                ( $ DePool_ι_RET_OR_REINV_FEE ) ) !) ) ; 
(* round2.rewards = math.muldiv(reward, m_participantRewardFraction, 100); *) 
U0! Л_round2 ^^ RoundsBase_ι_Round_ι_rewards := math->muldiv (! $ Л_reward, 
                        ↑12 D2! DePoolContract_ι_m_participantRewardFraction , 
                         $ xInt100 !) ; 
(* uint64 validatorReward = math.muldiv(reward, m_validatorRewardFraction, 100); *) 
declareLocal Л_validatorReward  :>: XInteger64 := ( math->muldiv (! $ Л_reward, 
                     ↑12 D2! DePoolContract_ι_m_validatorRewardFraction , 
                     $ xInt100 !) ) ; 
          (* m_validatorWallet.transfer(validatorReward, false, 1); *) 
( (↑2 D2! ValidatorBase_ι_m_validatorWallet) ->transfer (! $ Л_validatorReward , 
                             $ xBoolFalse , 
                             $ xInt1 !) ) >> 

(* round2 = startRoundCompleting(round2, CompletionReason.RewardIsReceived); *) 
U0! Л_round2 := DePoolContract_Ф_startRoundCompleting (! $Л_round2 , 
                    ξ$ RoundsBase_ι_CompletionReasonP_ι_RewardIsReceived !); 
(* return round2; *) 
return! Л_round2. 
 
(* function onSuccessToRecoverStake(uint64 queryId, address elector) public override {
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
            round.recoveredStake = value;
            if (value >= round.stake - round.unused) {
                round = acceptRewardAndStartRoundCompleting(round, value);
            } else {
                round = startRoundCompleting(round, CompletionReason.ValidatorIsPunished);
            }
        } else {
            revert(InternalErrors.ERROR521);
        }

        setRound(queryId, round);  } *) 

Definition DePoolContract_Ф_onSuccessToRecoverStake ( Л_queryId : XInteger64 ) ( Л_elector : XAddress ) : 
                           LedgerT ( XErrorValue True XInteger ) := 
               (*optional(Round) optRound = fetchRound(queryId);*) 	 
declareLocal Л_optRound :>: ( XMaybe RoundsBase_ι_Round ) := RoundsBase_Ф_fetchRound (! $ Л_queryId !) ; 
                (* require(optRound.hasValue(), InternalErrors.ERROR513);*) 
Require2 {{$ Л_optRound ->hasValue , ξ$ InternalErrors_ι_ERROR513 }} ; 
                   (* Round round = optRound.get();*) 
declareLocal Л_round :>: RoundsBase_ι_Round := ( $ Л_optRound) ->get ; 
                   (*require(msg.sender == round.proxy, Errors.IS_NOT_PROXY);*) 
Require2 {{ msg_sender () ?== $ Л_round ->> RoundsBase_ι_Round_ι_proxy , ξ$ Errors_ι_IS_NOT_PROXY }} ; 
                    (*require(elector == round.elector, Errors.IS_NOT_ELECTOR);*) 
Require2 {{$ Л_elector ?== $ Л_round ->> RoundsBase_ι_Round_ι_elector , ξ$ Errors_ι_IS_NOT_ELECTOR }} ; 

(tvm_accept ()) >> 

(*init*) 
( declareInit LocalState_ι_onSuccessToRecoverStake_Л_round := $ Л_round) >> 
(* uint64 value = uint64(msg.value) + DePoolLib.PROXY_FEE;*) 
declareLocal Л_value :>: XInteger64 := msg_value () !+ ξ$ DePoolLib_ι_PROXY_FEE ; 

(*if (round.step == RoundStep.WaitingIfValidatorWinElections) { *) 
If! (↑17 D2! LocalState_ι_onSuccessToRecoverStake_Л_round ^^ RoundsBase_ι_Round_ι_step ?== ξ$ RoundsBase_ι_RoundStepP_ι_WaitingIfValidatorWinElections) then { 
(*if (value < round.stake) {*) 
(If ( $Л_value ?< (↑17 D2! LocalState_ι_onSuccessToRecoverStake_Л_round ^^ RoundsBase_ι_Round_ι_stake )) then { 
(* round.step = RoundStep.WaitingUnfreeze; 
round.unused = value; *) 
(↑17 U1! LocalState_ι_onSuccessToRecoverStake_Л_round ^^ RoundsBase_ι_Round_ι_step := ξ$ RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze )	>> 
(↑17 U1! LocalState_ι_onSuccessToRecoverStake_Л_round ^^ RoundsBase_ι_Round_ι_unused := $ Л_value) 
} else { 
(*round.step = RoundStep.WaitingUnfreeze; 
round.completionReason = CompletionReason.ElectionsAreLost;*) 
(↑17 U1! LocalState_ι_onSuccessToRecoverStake_Л_round ^^ RoundsBase_ι_Round_ι_step := ξ$ RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze )	>> 
(↑17 U1! LocalState_ι_onSuccessToRecoverStake_Л_round ^^ RoundsBase_ι_Round_ι_completionReason := ξ$ RoundsBase_ι_CompletionReasonP_ι_ElectionsAreLost) 
}) >> $ (xValue I) 
} 
(*} else if (round.step == RoundStep.WaitingReward) {*) 		 
else {   
If (↑17 D2! LocalState_ι_onSuccessToRecoverStake_Л_round ^^ RoundsBase_ι_Round_ι_step ?== ξ$ RoundsBase_ι_RoundStepP_ι_WaitingReward) then { 
(* round.recoveredStake = value; *) 
(↑17 U1! LocalState_ι_onSuccessToRecoverStake_Л_round ^^ RoundsBase_ι_Round_ι_recoveredStake := $ Л_value) >> 
(* if (value >= round.stake - round.unused) { *) 	 
(If ( $ Л_value ?>= (↑17 D2! LocalState_ι_onSuccessToRecoverStake_Л_round ^^ RoundsBase_ι_Round_ι_stake) !- (↑17 D2! LocalState_ι_onSuccessToRecoverStake_Л_round ^^ RoundsBase_ι_Round_ι_unused) ) then { 
(*round = acceptRewardAndStartRoundCompleting(round, value);*) 
↑↑17 U2! LocalState_ι_onSuccessToRecoverStake_Л_round := DePoolContract_Ф_acceptRewardAndStartRoundCompleting(! ↑17 D2! LocalState_ι_onSuccessToRecoverStake_Л_round , 
                                       $ Л_value !) 

} else { 
(*round = startRoundCompleting(round, CompletionReason.ValidatorIsPunished);*) 
↑↑17 U2! LocalState_ι_onSuccessToRecoverStake_Л_round := DePoolContract_Ф_startRoundCompleting(! ↑17 D2! LocalState_ι_onSuccessToRecoverStake_Л_round , 
                                  ξ$ RoundsBase_ι_CompletionReasonP_ι_ValidatorIsPunished !) 
}) >> $ (xValue I) 
} else { 
(*revert(InternalErrors.ERROR521);*) 
tvm_revert (! ξ$ InternalErrors_ι_ERROR521  !) 
} } ; 

(* setRound(queryId, round); *) 
(RoundsBase_Ф_setRound (! $Л_queryId , ↑17 D2! LocalState_ι_onSuccessToRecoverStake_Л_round !) ). 

(*function onFailToRecoverStake(uint64 queryId, address elector) public override {
        optional(Round) optRound = fetchRound(queryId);
        require(optRound.hasValue(), InternalErrors.ERROR513);
        Round round = optRound.get();
        require(msg.sender == round.proxy, Errors.IS_NOT_PROXY);
        require(elector == round.elector, Errors.IS_NOT_ELECTOR);
        tvm.accept();
        if (round.step == RoundStep.WaitingIfValidatorWinElections) {
             round.step = RoundStep.WaitingUnfreeze;
        } else if (round.step == RoundStep.WaitingReward) {
            round = startRoundCompleting(round, CompletionReason.ValidatorIsPunished);
        } else {
            revert(InternalErrors.ERROR521);
        }
        setRound(queryId, round); } *) 
  
Definition DePoolContract_Ф_onFailToRecoverStake ( Л_queryId : XInteger64 ) ( Л_elector : XAddress ) : LedgerT ( XErrorValue True XInteger ) := 
(*optional(Round) optRound = fetchRound(queryId);*) 	 
declareLocal Л_optRound :>: ( XMaybe RoundsBase_ι_Round ):= RoundsBase_Ф_fetchRound (! $Л_queryId !) ; 
(* require(optRound.hasValue(), InternalErrors.ERROR513);*) 
Require2 {{$ Л_optRound ->hasValue , ξ$ InternalErrors_ι_ERROR513 }} ; 
(* Round round = optRound.get();*) 
declareLocal Л_round :>: RoundsBase_ι_Round := ( $ Л_optRound) ->get ; 
(*require(msg.sender == round.proxy, Errors.IS_NOT_PROXY);*) 
Require2 {{ msg_sender () ?== $ Л_round ->> RoundsBase_ι_Round_ι_proxy , ξ$ Errors_ι_IS_NOT_PROXY }} ; 
(*require(elector == round.elector, Errors.IS_NOT_ELECTOR);*) 
Require2 {{$ Л_elector ?== $ Л_round ->> RoundsBase_ι_Round_ι_elector , ξ$ Errors_ι_IS_NOT_ELECTOR }} ; 
tvm_accept () >> 
(*init*) 
(↑17 U1! LocalState_ι_onFailToRecoverStake_Л_round := $ Л_round) >> 
(* 
if (round.step == RoundStep.WaitingIfValidatorWinElections) { 
round.step = RoundStep.WaitingUnfreeze; 
} else if (round.step == RoundStep.WaitingReward) { 
round = startRoundCompleting(round, CompletionReason.ValidatorIsPunished); 
} else { 
revert(InternalErrors.ERROR521); 
} 
*) 
If! (↑17 D2! LocalState_ι_onFailToRecoverStake_Л_round ^^ RoundsBase_ι_Round_ι_step ?== ξ$ RoundsBase_ι_RoundStepP_ι_WaitingIfValidatorWinElections) then { 
(↑17 U1! LocalState_ι_onFailToRecoverStake_Л_round ^^ RoundsBase_ι_Round_ι_step := ξ$ RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze ) >> 
 $ (xValue I) 
} else { If (↑17 D2! LocalState_ι_onFailToRecoverStake_Л_round ^^ RoundsBase_ι_Round_ι_step ?== ξ$ RoundsBase_ι_RoundStepP_ι_WaitingReward) then { 
↑↑17 U2! LocalState_ι_onFailToRecoverStake_Л_round := DePoolContract_Ф_startRoundCompleting(! ↑17 D2! LocalState_ι_onFailToRecoverStake_Л_round , 
                               ξ$ RoundsBase_ι_CompletionReasonP_ι_ValidatorIsPunished !) >> 
 $ (xValue I) 
} else { 
tvm_revert (! ξ$ InternalErrors_ι_ERROR521  !) 
} } ; 

(* setRound(queryId, round); *) 
( RoundsBase_Ф_setRound (! $Л_queryId , ↑17 D2! LocalState_ι_onFailToRecoverStake_Л_round !) ). 

(* 
function terminator() public { 
require(msg.pubkey() == tvm.pubkey(), Errors.IS_NOT_OWNER); 
    require(!m_poolClosed, Errors.DEPOOL_IS_CLOSED); 
    m_poolClosed = true; 
    tvm.commit(); 
    tvm.accept(); 

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
(*require(msg.pubkey() == tvm.pubkey(), Errors.IS_NOT_OWNER);*) 	 
Require2 {{ msg_pubkey () ?== tvm_pubkey () , ξ$ Errors_ι_IS_NOT_OWNER }} ; 
(*require(!m_poolClosed, Errors.DEPOOL_IS_CLOSED);*) 
Require {{ !¬ ↑12 D2! DePoolContract_ι_m_poolClosed , ξ$ Errors_ι_DEPOOL_IS_CLOSED }} ; 
(* m_poolClosed = true; *) 
(↑12 U1! DePoolContract_ι_m_poolClosed := $xBoolTrue) >> 
(* tvm.commit(); *) 
tvm_commit () >> 
(* tvm.accept(); *) 
tvm_accept () >> 


(* Round roundPre0 = getRoundPre0(); *) 
declareLocal Л_roundPre0 :>: RoundsBase_ι_Round := RoundsBase_Ф_getRoundPre0 (); 
(* Round round0 = getRound0(); *) 
declareLocal Л_round0 :>: RoundsBase_ι_Round := RoundsBase_Ф_getRound0 (); 
(*Round round1 = getRound1();*) 
(declareGlobal! LocalState_ι_terminator_Л_round1 :>: RoundsBase_ι_Round := RoundsBase_Ф_getRound1 () ) >> 

(* roundPre0 = startRoundCompleting(roundPre0, CompletionReason.PoolClosed); *) 
U0! Л_roundPre0 := DePoolContract_Ф_startRoundCompleting (! $ Л_roundPre0 , 
														 ξ$ RoundsBase_ι_CompletionReasonP_ι_PoolClosed !) ; 
(*round0 = startRoundCompleting(round0, CompletionReason.PoolClosed);*) 
U0! Л_round0 := DePoolContract_Ф_startRoundCompleting (! $ Л_round0 , 
														 ξ$ RoundsBase_ι_CompletionReasonP_ι_PoolClosed !) ; 
(* if (round1.step == RoundStep.WaitingValidatorRequest) { 
	round1 = startRoundCompleting(round1, CompletionReason.PoolClosed); 
} *) 
(If (↑17 D2! LocalState_ι_terminator_Л_round1 ^^ RoundsBase_ι_Round_ι_step ?== ξ$ RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest) then { 
	↑↑17 U2! LocalState_ι_terminator_Л_round1 := DePoolContract_Ф_startRoundCompleting (! ↑17 D2! LocalState_ι_terminator_Л_round1 , 
																						  ξ$ RoundsBase_ι_CompletionReasonP_ι_PoolClosed !) 
}) >> 
(* emit DePoolClosed(); *) 
->emit $ DePoolClosed >> 
(* setRoundPre0(roundPre0); *) 
(RoundsBase_Ф_setRoundPre0 (! $ Л_roundPre0 !) ) >> 
(* setRound0(round0); *) 
(RoundsBase_Ф_setRound0 (! $ Л_round0 !) ) >> 
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
        r1.step = RoundStep.WaitingValidatorRequest;         emit ProxyHasRejectedTheStake(r1.validatorRequest.queryId); 
        optRound.set(r1); 
      } else { 
        if (isRound2(roundId)) { 
          Round r2 = optRound.get(); 
          require(r2.step == RoundStep.WaitingReward, InternalErrors.ERROR526); 
          r2.step = RoundStep.WaitingUnfreeze;           optRound.set(r2); 
        } else if (isRound1(roundId)) { 
          Round r1 = optRound.get(); 
          require(r1.step == RoundStep.WaitingIfValidatorWinElections, InternalErrors.ERROR527); 
          r1.step = RoundStep.WaitingValidationStart;           optRound.set(r1); 
        } else { 
          revert(InternalErrors.ERROR528); 
        } 
        emit ProxyHasRejectedRecoverRequest(roundId); 
      } 
      setRound(roundId, optRound.get()); 
    } 
  } *) 
(***************************************************************************************************************************)

Definition DePoolContract_Ф_onBounce (Л_body: TvmSlice) : LedgerT (XErrorValue True XInteger) := 
                             (* uint32 functionId = body.decode(uint32); *) 
  declareLocal Л_functionId :::: XInteger32 := Л_body ->decode(uint32) ; 
                             (* bool isProcessNewStake = functionId == tvm.functionId(IProxy.process_new_stake); *) 
  declareLocal Л_isProcessNewStake :>: XBool := ( $ Л_functionId) ?== $ (tvm_functionId IProxy_И_process_new_stakeF) ; 
                              (* bool isRecoverStake = functionId == tvm.functionId(IProxy.recover_stake); *) 
  declareLocal Л_isRecoverStake  :>: XBool := ( $ Л_functionId) ?== $ (tvm_functionId IProxy_И_recover_stakeF) ; 
                              (* if (isProcessNewStake || isRecoverStake) { *) 
  If! (( $Л_isProcessNewStake) !| ( $Л_isRecoverStake) ) then { 
                              (*  uint64 roundId = body.decode(uint64); *) 
   declareLocal Л_roundId :::: XInteger64 := Л_body ->decode(uint64) ; 
                              (*  optional(Round) optRound = fetchRound(roundId); *) 
   ( declareGlobal! LocalState_ι_onBounce_Л_optRound :>: ( XMaybe RoundsBase_ι_Round ) := RoundsBase_Ф_fetchRound (! $ Л_roundId !) ) >> 
                               (*  if (isProcessNewStake) { *) 
   If!! ( $Л_isProcessNewStake) then { 
                               (*    require(isRound1(roundId), InternalErrors.ERROR524); *) 
   ( Require2 {{ RoundsBase_Ф_isRound1 (! $ Л_roundId !) , ξ$ InternalErrors_ι_ERROR524  }} ; 
                                (*    Round r1 = optRound.get(); *) 
   Require2 {{ (↑17 D2! LocalState_ι_onBounce_Л_optRound) ->hasValue,  ξ$ InternalErrors_ι_ERROR519 }} ; 
   declareLocal Л_r1 :>: RoundsBase_ι_Round := (↑17 D2! LocalState_ι_onBounce_Л_optRound) ->get ; 
                                (*    require(r1.step == RoundStep.WaitingIfStakeAccepted, InternalErrors.ERROR525); *) 
   Require {{  $(Л_r1 ->> RoundsBase_ι_Round_ι_step) ?==  ξ$ RoundsBase_ι_RoundStepP_ι_WaitingIfStakeAccepted , 
                             ξ$ InternalErrors_ι_ERROR525 }} ; 
                                 (*    r1.step = RoundStep.WaitingValidatorRequest; *)   
   U0! Л_r1 ^^ RoundsBase_ι_Round_ι_step := ξ$ RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest ; 
                                (*emit ProxyHasRejectedTheStake(r1.validatorRequest.queryId); *) 
   (->emit (ProxyHasRejectedTheStake (!! $((Л_r1 ->> RoundsBase_ι_Round_ι_validatorRequest) ->> DePoolLib_ι_Request_ι_queryId) !!) )) >> 
                                (*    optRound.set(r1); *) 
   (↑17 U1! LocalState_ι_onBounce_Л_optRound ->set $ Л_r1) ) 
                                (*  } else { *) } 
   else { 
                                (*    if (isRound2(roundId)) { *) 
   If! (RoundsBase_Ф_isRound2 (! $ Л_roundId !)) then { 
                           (*      Round r2 = optRound.get(); *) 
    ( Require2 {{ (↑17 D2! LocalState_ι_onBounce_Л_optRound) ->hasValue , $ InternalErrors_ι_ERROR519 }} ; 
    declareLocal Л_r2 :>: RoundsBase_ι_Round := (↑17 D2! LocalState_ι_onBounce_Л_optRound) ->get ; 
                          (*      require(r2.step == RoundStep.WaitingReward, InternalErrors.ERROR526); *) 
    Require {{  $(Л_r2 ->> RoundsBase_ι_Round_ι_step) ?==  ξ$ RoundsBase_ι_RoundStepP_ι_WaitingReward , 
                           ξ$ InternalErrors_ι_ERROR526 }} ; 
                          (*      r2.step = RoundStep.WaitingUnfreeze;      *)
   U0! Л_r2 ^^ RoundsBase_ι_Round_ι_step := ξ$ RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze ; 
                           (*  optRound.set(r2); *) 
    (↑17 U1! LocalState_ι_onBounce_Л_optRound ->set $ Л_r2) ) 
                           (*    } else if (isRound1(roundId)) { *) 
   } else { If! (RoundsBase_Ф_isRound1 (! $ Л_roundId !)) then { 
                            (*      Round r1 = optRound.get(); *) 
   ( Require2 {{ (↑17 D2! LocalState_ι_onBounce_Л_optRound) ->hasValue ,  ξ$ InternalErrors_ι_ERROR519 }} ; 
   declareLocal Л_r1 :>: RoundsBase_ι_Round := (↑17 D2! LocalState_ι_onBounce_Л_optRound) ->get ; 
                          (*      require(r1.step == RoundStep.WaitingIfValidatorWinElections, InternalErrors.ERROR527); *) 
   Require {{  $(Л_r1 ->> RoundsBase_ι_Round_ι_step) ?==  ξ$ RoundsBase_ι_RoundStepP_ι_WaitingIfValidatorWinElections , 
                  ξ$ InternalErrors_ι_ERROR527 }} ; 
                               (*      r1.step = RoundStep.WaitingValidationStart;    
                                     optRound.set(r1); *) 
   U0! Л_r1 ^^ RoundsBase_ι_Round_ι_step := $RoundsBase_ι_RoundStepP_ι_WaitingValidationStart ;                                     
   (↑17 U1! LocalState_ι_onBounce_Л_optRound ->set $ Л_r1) ) } 
   (*    } else { *) 
       else { 
                              (*      revert(InternalErrors.ERROR528); *) 
   tvm_revert (! ξ$ InternalErrors_ι_ERROR528  !) 
   (*    } *) 
   } ; $I }; 
                              (*    emit ProxyHasRejectedRecoverRequest(roundId); *) 
   ->emit ProxyHasRejectedRecoverRequest (!! $ Л_roundId !!) 
                             (*  } *)  
   } ; 
                               (*  setRound(roundId, optRound.get()); *) 
   Require {{ (↑17 D2! LocalState_ι_onBounce_Л_optRound) ->hasValue, ξ$ InternalErrors_ι_ERROR519 }} ; 
   RoundsBase_Ф_setRound (! $ Л_roundId, (↑17 D2! LocalState_ι_onBounce_Л_optRound) ->get !) 
  }; $I. 


(* 
function completeRoundWithChunk(uint64 roundId, uint8 chunkSize) public selfCall { 
    tvm.accept(); 
    if (!(isRound2(roundId) || m_poolClosed)) 
      return; 
    if (!checkPureDePoolBalance()) { 
      return; 
    } 
    optional(Round) optRound = fetchRound(roundId); 
    require(optRound.hasValue(), InternalErrors.ERROR519); 
    Round round = optRound.get(); 
    if (round.step != RoundStep.Completing) 
      return; 

    round = _returnOrReinvest(round, chunkSize); 

    if (chunkSize < MAX_MSGS_PER_TR && !round.stakes.empty()) { 
      uint8 doubleChunkSize = 2 * chunkSize; 
      this.completeRoundWithChunk{flag: 1, bounce: false}( 
        roundId, 
        doubleChunkSize < MAX_MSGS_PER_TR? doubleChunkSize : chunkSize 
      ); 
      this.completeRoundWithChunk{flag: 1, bounce: false}(roundId, chunkSize); 
    } 

    setRound(roundId, round); 
  }*) 

Definition DePoolContract_Ф_completeRoundWithChunk ( Л_roundId : XInteger64 ) 
                          ( Л_chunkSize : XInteger8 ) 
                    : LedgerT (XErrorValue ( XValueValue True ) XInteger ) := 
Require2 {{ msg_sender () ?== tvm_address (),  ξ$ Errors_ι_IS_NOT_DEPOOL }} ; 
(* tvm.accept();*)  
tvm_accept () >> 
    (* if (!(isRound2(roundId) || m_poolClosed)) 
      return; *) 
If2!! ( !¬ ( ( RoundsBase_Ф_isRound2 (! $ Л_roundId !) ) !| ( ↑12 D2! DePoolContract_ι_m_poolClosed ) ) ) 
then 
{  
 return! ( xError I ) 
} ; 
       (* if ( ! checkPureDePoolBalance ( ) )  { 
             return ; 
            } *) 
If2!! ( !¬ ( DePoolContract_Ф_checkPureDePoolBalance () ) ) 
then 
{  
 return! ( xError I ) 
} ; 
          (* optional(Round) optRound = fetchRound(roundId); *) 
declareLocal Л_optRound :>: ( XMaybe RoundsBase_ι_Round ) := ( RoundsBase_Ф_fetchRound (! $ Л_roundId !) ) ; 
          (* require(optRound.hasValue(), InternalErrors.ERROR519); *) 
Require2 {{ ( $ Л_optRound ) ->hasValue , ξ$ InternalErrors_ι_ERROR519 }} ;  
          (* Round round = optRound.get(); *) 
declareLocal Л_round :>: RoundsBase_ι_Round := ( $ Л_optRound ) ->get ; 
          (* if (round.step != RoundStep.Completing) 
            return; *) 
If2!! ( ↑11 D0! Л_round ^^ RoundsBase_ι_Round_ι_step ?!= ξ$ RoundsBase_ι_RoundStepP_ι_Completing ) 
then 
{ 
 return! ( xError I ) 
} ; 
          (* round = _returnOrReinvest(round, chunkSize); *) 
U0! Л_round ?:= DePoolContract_Ф__returnOrReinvest (! $ Л_round , $ Л_chunkSize !) ; 

(If ( ( $ Л_chunkSize ?< ( $ DePool_ι_MAX_MSGS_PER_TR )) !& 
   ( !¬ ( ( $ (Л_round ->> RoundsBase_ι_Round_ι_stakes)) ->empty ) ) ) 
then 
{ 
	(*uint8 doubleChunkSize = 2 * chunkSize;*) 
	declareLocal Л_doubleChunkSize :>: XInteger8 := $xInt2 !*  $ Л_chunkSize; 
	(* this.completeRoundWithChunk{flag: 1, bounce: false}( 
        roundId, 
        doubleChunkSize < MAX_MSGS_PER_TR? doubleChunkSize : chunkSize 
			); *) 

    ( this->sendMessage ( DePoolContract_Ф_completeRoundWithChunkF (!! $ Л_roundId , ( $Л_doubleChunkSize ?< $ DePool_ι_MAX_MSGS_PER_TR ) ? $ Л_doubleChunkSize ::: $ Л_chunkSize !!) )
                with {|| messageBounce ::= $xBoolFalse , messageFlag ::= $xInt1 ||} ) >>

	 (*this.completeRoundWithChunk{flag: 1, bounce: false}(roundId, chunkSize);*) 
	 ( this->sendMessage ( DePoolContract_Ф_completeRoundWithChunkF (!! $ Л_roundId , $ Л_chunkSize !!) )
                with {|| messageBounce ::= $xBoolFalse , messageFlag ::= $xInt1 ||} ) 
} ) >> 
           (* setRound(roundId, round); *) 
 RoundsBase_Ф_setRound (! $ Л_roundId , $ Л_round !) >> 
 $ (xValue I).  

(* 
 function completeRound(uint64 roundId, uint32 participantQty) public selfCall {
        tvm.accept();
        require(isRound2(roundId) || m_poolClosed, InternalErrors.ERROR522);
        optional(Round) optRound = fetchRound(roundId);
        require(optRound.hasValue(), InternalErrors.ERROR519);
        Round round = optRound.get();
        require(round.step == RoundStep.Completing, InternalErrors.ERROR518);

        this.completeRoundWithChunk{flag: 1, bounce: false}(roundId, 1);

        tvm.commit();
       
        uint outActionQty = (participantQty + MAX_MSGS_PER_TR - 1) / MAX_MSGS_PER_TR;
        if (outActionQty > MAX_QTY_OF_OUT_ACTIONS) {

            uint32 maxQty = uint32(MAX_QTY_OF_OUT_ACTIONS) * MAX_MSGS_PER_TR;
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
Require2 {{ msg_sender () ?== tvm_address (),  ξ$ Errors_ι_IS_NOT_DEPOOL }} ; 
(* tvm.accept();*) 
tvm_accept () >> 
(*require(isRound2(roundId) || m_poolClosed, InternalErrors.ERROR522);*) 
Require2 {{ RoundsBase_Ф_isRound2 (! $ Л_roundId !) !| ↑12 D2! DePoolContract_ι_m_poolClosed , 
                          ξ$ InternalErrors_ι_ERROR522 }} ; 
(*optional(Round) optRound = m_rounds.fetch(roundId);*) 
declareLocal Л_optRound :>: (XMaybe RoundsBase_ι_Round ) := RoundsBase_Ф_fetchRound (! $ Л_roundId !) ; 
(*require(optRound.hasValue(), InternalErrors.ERROR519);*) 
Require2 {{ ( $ Л_optRound) ->hasValue, ξ$ InternalErrors_ι_ERROR519 }} ; 
(* Round round = optRound.get(); *) 
declareLocal Л_round :>: RoundsBase_ι_Round := ( $ Л_optRound ) ->get ; 
(*require(round.step == RoundStep.Completing, InternalErrors.ERROR518);*) 
Require {{ ( ( $ Л_round ->> RoundsBase_ι_Round_ι_step ) ?== ( ξ$ RoundsBase_ι_RoundStepP_ι_Completing ) ) , 
                      ξ$ InternalErrors_ι_ERROR518 }} ; 
(* this.completeRoundWithChunk{flag: 1, bounce: false}(roundId, 1); *)
( this->sendMessage ( DePoolContract_Ф_completeRoundWithChunkF (!! $ Л_roundId , $ xInt1 !!) )
                with {|| messageBounce ::= $xBoolFalse , messageFlag ::= $xInt1 ||} )  >> 
    (*tvm.commit();*) 					 
tvm_commit () >> 
    (* uint outActionQty = (participantQty + MAX_MSGS_PER_TR - 1) / MAX_MSGS_PER_TR; *) 
declareLocal Л_outActionQty :>: XInteger := ( ( $ Л_participantQty !+ ( $ DePool_ι_MAX_MSGS_PER_TR ) !- $ xInt1 ) !/ 
               ( $ DePool_ι_MAX_MSGS_PER_TR ) ) ; 

    (* if (outActionQty > MAX_QTY_OF_OUT_ACTIONS) { {*) 
( If ( $ Л_outActionQty ?> ( $ DePool_ι_MAX_QTY_OF_OUT_ACTIONS ) ) then { 
	   (* uint32 maxQty = uint32(MAX_QTY_OF_OUT_ACTIONS) * MAX_MSGS_PER_TR;*) 
	declareLocal Л_maxQty :>: XInteger32 := ( $ DePool_ι_MAX_QTY_OF_OUT_ACTIONS ) !* ( $ DePool_ι_MAX_MSGS_PER_TR ) ; 
	   (* uint32 restParticipant = participantQty; *) 
	( declareGlobal LocalState_ι_completeRound_Л_restParticipant :>: XInteger32 := $ Л_participantQty) >> 

     (* for (int msgQty = 0; restParticipant > 0; ++msgQty) { 
        uint32 curGroup = 
          (restParticipant < maxQty || msgQty + 1 == MAX_QTY_OF_OUT_ACTIONS) ? 
          restParticipant : 
          maxQty; 
        this.completeRound{flag: 1, bounce: false}(roundId, curGroup); 
        restParticipant -= curGroup; 
      } *) 
		( ↑17 U1! LocalState_ι_completeRound_Л_msgQty := $ xInt0 ) >> 
	( While ( ↑17 D2! LocalState_ι_completeRound_Л_restParticipant ?> $ xInt0 ) do ( 
			declareLocal Л_curGroup :>: XInteger32 := ( ( ↑17 D2! LocalState_ι_completeRound_Л_restParticipant ) ?< ( $ Л_maxQty ) !| 
			          ( ( (↑17 D2! LocalState_ι_completeRound_Л_msgQty) !+ $ xInt1 ) ?== 
                 $ DePool_ι_MAX_QTY_OF_OUT_ACTIONS ) ) ? 
           ( ↑17 D2! LocalState_ι_completeRound_Л_restParticipant ) ::: 
             ( $ Л_maxQty ) ;		 
			(* this.completeRound{flag: 1, bounce: false}(roundId, curGroup); *) 
( this->sendMessage ( DePoolContract_Ф_completeRoundF (!! $Л_roundId , $ Л_curGroup !!) )
                with {|| messageBounce ::= $xBoolFalse , messageFlag ::= $xInt1 ||} ) >>
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
		( While ( ↑17 D2! LocalState_ι_completeRound_Л_i ?< $ Л_participantQty ) do ( 

( this->sendMessage ( DePoolContract_Ф_completeRoundWithChunkF (!! $Л_roundId , $ DePool_ι_MAX_MSGS_PER_TR !!) )
                with {|| messageBounce ::= $xBoolFalse , messageFlag ::= $xInt1 ||} ) >>
				continue! I		 
			) ) >>  $I		 
	} ) . 
	 

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

    emit RoundStakeIsAccepted(round.validatorRequest.queryId, comment); } *) 
Definition DePoolContract_Ф_onStakeAccept ( Л_queryId : XInteger64 ) 
                     ( Л_comment : XInteger32 ) 
                     ( Л_elector : XAddress ) 
                     : LedgerT ( XErrorValue True XInteger ) := 
          (*optional(Round) optRound = fetchRound(queryId);*) 	 
declareLocal Л_optRound :>: ( XMaybe RoundsBase_ι_Round ) := RoundsBase_Ф_fetchRound (! $ Л_queryId !) ; 
(* require(optRound.hasValue(), InternalErrors.ERROR513);*) 
Require2 {{$ Л_optRound ->hasValue , ξ$ InternalErrors_ι_ERROR513 }} ; 
(* Round round = optRound.get();*) 
declareLocal Л_round :>: RoundsBase_ι_Round := ( $ Л_optRound) ->get ; 
(*require(msg.sender == round.proxy, Errors.IS_NOT_PROXY);*) 
Require2 {{ msg_sender () ?== $ Л_round ->> RoundsBase_ι_Round_ι_proxy , ξ$ Errors_ι_IS_NOT_PROXY }} ; 
(*require(elector == round.elector, Errors.IS_NOT_ELECTOR);*) 
Require2 {{$ Л_elector ?== $ Л_round ->> RoundsBase_ι_Round_ι_elector , ξ$ Errors_ι_IS_NOT_ELECTOR }} ; 
(*require(round.id == queryId, Errors.INVALID_QUERY_ID);*) 
Require2 {{$ Л_round ->> RoundsBase_ι_Round_ι_id ?== $ Л_queryId ,  ξ$ Errors_ι_INVALID_QUERY_ID }} ; 
(*require(round.step == RoundStep.WaitingIfStakeAccepted, Errors.INVALID_ROUND_STEP);*) 
Require {{$ Л_round ->> RoundsBase_ι_Round_ι_step ?== ξ$ RoundsBase_ι_RoundStepP_ι_WaitingIfStakeAccepted , 
                         ξ$ Errors_ι_INVALID_ROUND_STEP }} ; 
(*tvm.accept();*) 
tvm_accept() >> 
(*round.step = RoundStep.WaitingValidationStart;*) 
U0! Л_round ^^ RoundsBase_ι_Round_ι_step := ξ$ RoundsBase_ι_RoundStepP_ι_WaitingValidationStart ; 
(* round.completionReason = CompletionReason.Undefined; *) 
U0! Л_round ^^ RoundsBase_ι_Round_ι_completionReason := ξ$ RoundsBase_ι_CompletionReasonP_ι_Undefined ; 
            (* setRound(queryId, round); *) 
RoundsBase_Ф_setRound (! $ Л_queryId , $Л_round !) >> 
(*emit roundStakeIsAccepted(round.validatorRequest.queryId, comment); *) 
->emit roundStakeIsAccepted (!! $ (Л_round ->> RoundsBase_ι_Round_ι_validatorRequest) ->> DePoolLib_ι_Request_ι_queryId , 
								 $ Л_comment !!). 
 	 
(* 
function onStakeReject(uint64 queryId, uint32 comment, address elector) public override {
        optional(Round) optRound = fetchRound(queryId);
        require(optRound.hasValue(), InternalErrors.ERROR513);
        Round round = optRound.get();
        require(msg.sender == round.proxy, Errors.IS_NOT_PROXY);
        require(elector == round.elector, Errors.IS_NOT_ELECTOR);
        require(round.id == queryId, Errors.INVALID_QUERY_ID);
        require(round.step == RoundStep.WaitingIfStakeAccepted, Errors.INVALID_ROUND_STEP);

        tvm.accept();
        round.step = RoundStep.WaitingValidatorRequest;
        round.completionReason = CompletionReason.StakeIsRejectedByElector;
        setRound(queryId, round);

        emit RoundStakeIsRejected(round.validatorRequest.queryId, comment);
    } *) 
Definition DePoolContract_Ф_onStakeReject ( Л_queryId : XInteger64 ) 
                     ( Л_comment : XInteger32 ) 
                     ( Л_elector : XAddress ) 
                     : LedgerT ( XErrorValue True XInteger ) := 
(*optional(Round) optRound = m_rounds.fetch(queryId);*) 	 
declareLocal Л_optRound :>: ( XMaybe RoundsBase_ι_Round ) := RoundsBase_Ф_fetchRound (! $ Л_queryId !) ; 
(* require(optRound.hasValue(), InternalErrors.ERROR513);*) 
Require2 {{$ Л_optRound ->hasValue , ξ$ InternalErrors_ι_ERROR513 }} ; 
(* Round round = optRound.get();*) 
declareLocal Л_round :>: RoundsBase_ι_Round := ( $ Л_optRound) ->get ; 
(*require(msg.sender == round.proxy, Errors.IS_NOT_PROXY);*) 
Require2 {{ msg_sender () ?== $ Л_round ->> RoundsBase_ι_Round_ι_proxy , ξ$ Errors_ι_IS_NOT_PROXY }} ; 
(*require(elector == round.elector, Errors.IS_NOT_ELECTOR);*) 
Require2 {{$ Л_elector ?== $ Л_round ->> RoundsBase_ι_Round_ι_elector , ξ$ Errors_ι_IS_NOT_ELECTOR }} ; 
(*require(round.id == queryId, Errors.INVALID_QUERY_ID);*) 
Require2 {{$ Л_round ->> RoundsBase_ι_Round_ι_id ?== $ Л_queryId ,  ξ$ Errors_ι_INVALID_QUERY_ID }} ; 
(*require(round.step == RoundStep.WaitingIfStakeAccepted, Errors.INVALID_ROUND_STEP);*) 
Require {{$ Л_round ->> RoundsBase_ι_Round_ι_step ?== ξ$ RoundsBase_ι_RoundStepP_ι_WaitingIfStakeAccepted , 
                          ξ$ Errors_ι_INVALID_ROUND_STEP }} ; 
tvm_accept() >> 
(*round.step = RoundStep.WaitingValidatorRequest*) 
U0! Л_round ^^ RoundsBase_ι_Round_ι_step := ξ$ RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest ; 
(* round.completionReason = CompletionReason.Undefined; *) 
U0! Л_round ^^ RoundsBase_ι_Round_ι_completionReason := ξ$ RoundsBase_ι_CompletionReasonP_ι_StakeIsRejectedByElector ; 
             (* setRound(queryId, round); *) 
RoundsBase_Ф_setRound (! $ Л_queryId , $Л_round !) >> 
(*emit roundStakeIsRejected(round.validatorRequest.queryId, comment); *) 
->emit roundStakeIsRejected (!! $ (Л_round ->> RoundsBase_ι_Round_ι_validatorRequest) ->> DePoolLib_ι_Request_ι_queryId , 
								 $ Л_comment !!). 
 
(* 
function receiveFunds() public pure { } *) 
Definition DePoolContract_Ф_receiveFunds : LedgerT True := $ I . 

(* function getParticipantInfo(address addr) public view
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
        optional(Participant) optParticipant = fetchParticipant(addr);
        require(optParticipant.hasValue(), Errors.NO_SUCH_PARTICIPANT);
        Participant participant = optParticipant.get();

        reinvest = participant.reinvest;
        reward = participant.reward;
        withdrawValue = participant.withdrawValue;

        optional(uint64, Round) pair = minRound();
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
                    total += sv.vesting.get().remainingAmount;
                }
                if (sv.lock.hasValue()) {
                    locks[round.id] = sv.lock.get();
                    total += sv.lock.get().remainingAmount;
                }
            }
            pair = nextRound(id);
        }
    }
 *) 
	 
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
function getDePoolInfo() public view returns ( 
    bool poolClosed, 
    uint64 minStake, 
    uint64 validatorAssurance, 
    uint8 participantRewardFraction, 
    uint8 validatorRewardFraction, 

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

    validatorWallet = m_validatorWallet; 
    proxies = m_proxies; 

    stakeFee = STAKE_FEE; 
    retOrReinvFee = RET_OR_REINV_FEE; 
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


(* 		  function getDePoolInfo() public view returns ( 
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
			uint64 validatorWalletMinStake 		)	 *) 	  
Set Typeclasses Depth 100. 
Definition DePool_Ф_getDePoolInfo 
		  : LedgerT ( XInteger64 # XInteger64 # XInteger64 # XAddress # XAddress # XAddress # XBool # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 ) := return! default. 
Set Typeclasses Depth 10. 

 (* function setValidatorRewardFraction(uint8 fraction) public { 
     require(msg.pubkey() == tvm.pubkey(), Errors.IS_NOT_OWNER); 
     require(fraction < m_validatorRewardFraction, Errors.NEW_VALIDATOR_FRACTION_MUST_BE_GREATER_THAN_OLD); 
     require(fraction > 0, Errors.FRACTION_MUST_NOT_BE_ZERO); 
     tvm.accept(); 
 
     m_validatorRewardFraction = fraction; 
     m_participantRewardFraction = 100 - m_validatorRewardFraction; 
     emit RewardFractionsChanged(m_validatorRewardFraction, m_participantRewardFraction); 
  } *) 
 
 Definition DePoolContract_Ф_setValidatorRewardFraction ( Л_fraction : XInteger8 ) 
                                           : LedgerT ( XErrorValue True XInteger ) := 
Require2 {{ ( msg_pubkey () ) ?== ( tvm_pubkey () ) , ξ$ Errors_ι_IS_NOT_OWNER }} ; 
Require2 {{ ( $ Л_fraction ) ?< ( ↑12 D2! DePoolContract_ι_m_validatorRewardFraction ) , 
                    ξ$ Errors_ι_NEW_VALIDATOR_FRACTION_MUST_BE_GREATER_THAN_OLD }} ; 
Require {{ ( $ Л_fraction ) ?> ( $ xInt0 ) , ξ$ Errors_ι_FRACTION_MUST_NOT_BE_ZERO }} ; 
tvm_accept () >> 
( ↑12 U1! DePoolContract_ι_m_validatorRewardFraction := $ Л_fraction ) >> 
( ↑12 U1! DePoolContract_ι_m_participantRewardFraction := ( ( $ xInt100 ) !- $ Л_fraction ) ) >> 
( ->emit ( RewardFractionsChanged (!! ( ↑ε12 DePoolContract_ι_m_validatorRewardFraction ) , 
                  ( ↑ε12 DePoolContract_ι_m_participantRewardFraction ) !!) ) ) . 

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

Definition DePoolContract_Ф_withdrawFromPoolingRound' ( Л_withdrawValue : XInteger64 ) 
                 : LedgerT (XErrorValue (XValueValue True) XInteger) := 
  (*require(msg.sender != address(0), Errors.IS_EXT_MSG);*) 
Require {{ msg_sender () ?!= $ xInt0 , ξ$ Errors_ι_IS_EXT_MSG }} ; 
(* if (m_poolClosed) { 
      return _sendError(STATUS_DEPOOL_CLOSED, 0); 
    } *) 
If!! ( ↑ε12 DePoolContract_ι_m_poolClosed ) 
then { 
 return!!! ( DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_DEPOOL_CLOSED , $ xInt0 !) ) 
 } ; 
(* optional(DePoolLib.Participant) optParticipant = fetchParticipant(msg.sender); 
    if (!optParticipant.hasValue()) { 
      return _sendError(STATUS_NO_PARTICIPANT, 0); 
    } *) 
declareLocal Л_optParticipant :>: ( XMaybe (ξ DePoolLib_ι_Participant) ) := ParticipantBase_Ф_fetchParticipant (! msg_sender () !) ; 
If! ( !¬ ( $ Л_optParticipant ->hasValue ) ) 
then { 
 return!!! ( DePoolContract_Ф__sendError (! $ DePool_ι_STATUS_NO_PARTICIPANT , $ xInt0 !) )													 
 } ; 

(*     DePoolLib.Participant participant = optParticipant.get(); *) 
declareLocal Л_participant :>: ξ DePoolLib_ι_Participant := $ Л_optParticipant ->get ; 
                (* uint64 removedPoolingStake; *)
declareLocal Л_removedPoolingStake :>: XInteger64 ;
(* (removedPoolingStake, participant) = withdrawStakeInPoolingRound(participant, msg.sender, withdrawValue, m_minStake); *) 
U0! {( Л_removedPoolingStake , Л_participant )} := RoundsBase_Ф_withdrawStakeInPoolingRound 
          (! $ Л_participant , msg_sender () , $ Л_withdrawValue , 
                     (↑12 D2! DePoolContract_ι_m_minStake) !) ; 

(*    
_setOrDeleteParticipant(msg.sender, participant); 
msg.sender.transfer(removedPoolingStake, false, 64);  
*) 
(ParticipantBase_Ф__setOrDeleteParticipant (! msg_sender () , $ Л_participant !)) >> 
( ( msg_sender () ) ->transfer (! $Л_removedPoolingStake ,  $ xBoolFalse ,  $ xInt64 !) ) . 


Definition DePoolContract_Ф_withdrawFromPoolingRound ( Л_withdrawValue : XInteger64 ) 
                   : LedgerT (XErrorValue True XInteger) := 
do r ← DePoolContract_Ф_withdrawFromPoolingRound' Л_withdrawValue ; 
	return! (xErrorMapDefaultF (xValue ∘ fromValueValue) r xError). 

Module DePoolFunSpec <: DePoolSpecSig. 

Definition ProxyBase_Ф__recoverStake := ProxyBase_Ф__recoverStake .
Definition ProxyBase_Ф__sendElectionRequest := ProxyBase_Ф__sendElectionRequest .
Definition ConfigParamsBase_Ф_getCurValidatorData := ConfigParamsBase_Ф_getCurValidatorData .
Definition ConfigParamsBase_Ф_getPrevValidatorHash := ConfigParamsBase_Ф_getPrevValidatorHash .
Definition ConfigParamsBase_Ф_roundTimeParams := ConfigParamsBase_Ф_roundTimeParams .
Definition ConfigParamsBase_Ф_getMaxStakeFactor := ConfigParamsBase_Ф_getMaxStakeFactor .
Definition ConfigParamsBase_Ф_getElector := ConfigParamsBase_Ф_getElector .
Definition ParticipantBase_Ф__setOrDeleteParticipant := ParticipantBase_Ф__setOrDeleteParticipant .
Definition ParticipantBase_Ф_getOrCreateParticipant  := ParticipantBase_Ф_getOrCreateParticipant .
Definition DePoolProxyContract_Ф_constructor5 := DePoolProxyContract_Ф_constructor5 .
Definition DePoolProxyContract_Ф_process_new_stake := DePoolProxyContract_Ф_process_new_stake .
Definition DePoolProxyContract_Ф_onStakeAccept := DePoolProxyContract_Ф_onStakeAccept .
Definition DePoolProxyContract_Ф_onStakeReject := DePoolProxyContract_Ф_onStakeReject .
Definition DePoolProxyContract_Ф_recover_stake := DePoolProxyContract_Ф_recover_stake .
Definition DePoolProxyContract_Ф_onSuccessToRecoverStake := DePoolProxyContract_Ф_onSuccessToRecoverStake .
Definition DePoolProxyContract_Ф_getProxyInfo := DePoolProxyContract_Ф_getProxyInfo .
Definition RoundsBase_Ф__addStakes := RoundsBase_Ф__addStakes .
Definition RoundsBase_Ф_stakeSum := RoundsBase_Ф_stakeSum .
Definition RoundsBase_Ф_transferStakeInOneRound := RoundsBase_Ф_transferStakeInOneRound .
Definition RoundsBase_Ф_isRoundPre0 := RoundsBase_Ф_isRoundPre0 .
Definition RoundsBase_Ф_isRound0 := RoundsBase_Ф_isRound0 .
Definition RoundsBase_Ф_isRound1 := RoundsBase_Ф_isRound1 .
Definition RoundsBase_Ф_isRound2 := RoundsBase_Ф_isRound2 .
Definition RoundsBase_Ф_roundAt := RoundsBase_Ф_roundAt .
Definition RoundsBase_Ф_getRoundPre0 := RoundsBase_Ф_getRoundPre0 .
Definition RoundsBase_Ф_getRound0 := RoundsBase_Ф_getRound0 .
Definition RoundsBase_Ф_getRound1 := RoundsBase_Ф_getRound1 .
Definition RoundsBase_Ф_getRound2 := RoundsBase_Ф_getRound2 .
Definition RoundsBase_Ф_setRound := RoundsBase_Ф_setRound .
Definition RoundsBase_Ф_setRoundPre0 := RoundsBase_Ф_setRoundPre0 .
Definition RoundsBase_Ф_setRound0 := RoundsBase_Ф_setRound0 .
Definition RoundsBase_Ф_setRound1 := RoundsBase_Ф_setRound1 .
Definition RoundsBase_Ф_setRound2 := RoundsBase_Ф_setRound2 .
Definition RoundsBase_Ф_fetchRound :=  RoundsBase_Ф_fetchRound .
Definition ParticipantBase_Ф_fetchParticipant := ParticipantBase_Ф_fetchParticipant .
Definition RoundsBase_Ф_minRound := RoundsBase_Ф_minRound .
Definition RoundsBase_Ф_nextRound := RoundsBase_Ф_nextRound .
Definition RoundsBase_Ф_withdrawStakeInPoolingRound := RoundsBase_Ф_withdrawStakeInPoolingRound .
Definition RoundsBase_Ф_toTruncatedRound := RoundsBase_Ф_toTruncatedRound .
Definition RoundsBase_Ф_getRounds := RoundsBase_Ф_getRounds .
Definition DePoolContract_Ф_generateRound := DePoolContract_Ф_generateRound .
Definition DePoolContract_Ф_Constructor6 := DePoolContract_Ф_Constructor6 .
Definition DePoolContract_Ф_setLastRoundInfo := DePoolContract_Ф_setLastRoundInfo .
Definition DePoolContract_Ф__returnChange := DePoolContract_Ф__returnChange .
Definition DePoolContract_Ф__sendError := DePoolContract_Ф__sendError .
Definition DePoolContract_Ф_startRoundCompleting := DePoolContract_Ф_startRoundCompleting .
Definition DePoolContract_Ф_cutWithdrawalValue := DePoolContract_Ф_cutWithdrawalValue .
Definition DePoolContract_Ф__returnOrReinvestForParticipant := DePoolContract_Ф__returnOrReinvestForParticipant .
Definition DePoolContract_Ф__returnOrReinvest := DePoolContract_Ф__returnOrReinvest .
Definition DePoolContract_Ф_sendAcceptAndReturnChange128 := DePoolContract_Ф_sendAcceptAndReturnChange128 .
Definition DePoolContract_Ф_sendAcceptAndReturnChange := DePoolContract_Ф_sendAcceptAndReturnChange .
Definition DePoolContract_Ф_addOrdinaryStake := DePoolContract_Ф_addOrdinaryStake .
Definition DePoolContract_Ф_addVestingOrLock := DePoolContract_Ф_addVestingOrLock .
Definition DePoolContract_Ф_addVestingStake := DePoolContract_Ф_addVestingStake .
Definition DePoolContract_Ф_addLockStake := DePoolContract_Ф_addLockStake . 
Definition DePoolContract_Ф_withdrawPart := DePoolContract_Ф_withdrawPart .
Definition DePoolContract_Ф_withdrawAll := DePoolContract_Ф_withdrawAll .
Definition DePoolContract_Ф_cancelWithdrawal := DePoolContract_Ф_cancelWithdrawal .
Definition DePoolContract_Ф_transferStake := DePoolContract_Ф_transferStake .
Definition DePoolContract_Ф_totalParticipantFunds := DePoolContract_Ф_totalParticipantFunds .
Definition DePoolContract_Ф_checkPureDePoolBalance := DePoolContract_Ф_checkPureDePoolBalance .
Definition DePoolContract_Ф_participateInElections := DePoolContract_Ф_participateInElections .
Definition DePoolContract_Ф_updateRound2 := DePoolContract_Ф_updateRound2 .
Definition DePoolContract_Ф_isEmptyRound := DePoolContract_Ф_isEmptyRound .
Definition DePoolContract_Ф_updateRounds := DePoolContract_Ф_updateRounds .
Definition DePoolContract_Ф_ticktock := DePoolContract_Ф_ticktock .
Definition DePoolContract_Ф_acceptRewardAndStartRoundCompleting := DePoolContract_Ф_acceptRewardAndStartRoundCompleting .
Definition DePoolContract_Ф_onSuccessToRecoverStake := DePoolContract_Ф_onSuccessToRecoverStake .
Definition DePoolContract_Ф_onFailToRecoverStake := DePoolContract_Ф_onFailToRecoverStake .
Definition DePoolContract_Ф_terminator := DePoolContract_Ф_terminator .
Definition DePoolContract_Ф_onBounce := DePoolContract_Ф_onBounce .
Definition DePoolContract_Ф_completeRoundWithChunk := DePoolContract_Ф_completeRoundWithChunk .
Definition DePoolContract_Ф_completeRound := DePoolContract_Ф_completeRound .
Definition DePoolContract_Ф_onStakeAccept := DePoolContract_Ф_onStakeAccept .
Definition DePoolContract_Ф_onStakeReject := DePoolContract_Ф_onStakeReject .
Definition DePoolContract_Ф_receiveFunds := DePoolContract_Ф_receiveFunds .
Definition DePool_Ф_getParticipantInfo := DePool_Ф_getParticipantInfo .
Definition DePoolContract_Ф_setValidatorRewardFraction := DePoolContract_Ф_setValidatorRewardFraction .
Definition DePool_Ф_getParticipants := DePool_Ф_getParticipants .
Definition DePoolContract_Ф_withdrawFromPoolingRound := DePoolContract_Ф_withdrawFromPoolingRound .

End DePoolFunSpec. 

End DePoolFuncs. 

