Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.
Require Import omega.Omega.
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

(* Check hmapIsMember. *)


(* Lemma foo: forall (l: Ledger) addr, isSome
(eval_state
 (callEmbeddedStateAdj (H0 :=  FullState_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13xT14xT15xT16_T17)
 (DePoolFuncs.ParticipantBase_Ф_fetchParticipant
 addr)
 DePoolFuncs.DePoolSpec.LedgerClass.local0)
 l) =
isSome
(eval_state
 (callEmbeddedStateAdj (H0 :=  FullState_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13xT14xT15xT16_T17)
 (DePoolFuncs.ParticipantBase_Ф_fetchParticipant
 addr)
 DePoolFuncs.DePoolSpec.LedgerClass.local0)
 l).
 Proof.
    intros.
    reflexivity.
 Qed.    *)

(* Existing Instance embeddedLocalState.
 
Existing Instance monadStateT.
Existing Instance monadStateStateT. *)

(* Existing Instance embeddedLocalState.
Existing Instance embeddedMultisig. *)

 
 
 
 (* function ConfigParamsBase.getCurValidatorData (  )  virtual internal returns  ( uint256 hash ,  uint32 utime_since ,  uint32 utime_until )   { 
         ( TvmCell cell ,  bool ok )  = tvm_rawConfigParam ( 34 )  ; 
        require ( ok ,  InternalErrors . ERROR508 )  ; 
        hash = tvm_hash ( cell )  ; 
        TvmSlice s = cell . toSlice (  )  ; 
         (  ,  utime_since ,  utime_until )  = s . decode ( uint8 ,  uint32 ,  uint32 )  ; 
     } 

Definition ConfigParamsBase_Ф_getCurValidatorData :  LedgerT ( XErrorValue ( XInteger256 # XInteger32 # XInteger32 ) XInteger ) :=  
	U0! {( Л_cell , Л_ok )} := tvm_rawConfigParam (! $ xInt34 !) ;
 	Require {{ $ Л_ok , ↑ε8 InternalErrors_ι_ERROR508 }} ; 
 	U0! Л_hash := tvm_hash (! $ Л_cell !) ; 
 	U0! Л_s := ($ Л_cell) ->toSlice() ; 
	U0! {( _ , Л_utime_since , Л_utime_until )} := ($ Л_s) ->decode(uint8,uint32,uint32) ;  (* (uint8 , uint32 , uint32) *)
	return# ( $Л_hash, $Л_utime_since , $Л_utime_until ). 
*) 



 Lemma ConfigParamsBase_Ф_getCurValidatorData_exec : forall (l: Ledger), 
    exec_state ( ConfigParamsBase_Ф_getCurValidatorData ) l = l. 
 Proof. 
   intros. destruct l. compute. auto.
 Qed. 
 
 Lemma ConfigParamsBase_Ф_getCurValidatorData_eval : forall (l: Ledger) ,
 eval_state ( ConfigParamsBase_Ф_getCurValidatorData ) l =

 let (Л_cell, Л_ok) := eval_state (tvm_rawConfigParam_34) l in
 let hash := tvm_hash Л_cell in 
 let sliceRaw := toSlice Л_cell in
 let res := decode_uint8_uint32_uint32 sliceRaw in
  if Л_ok then Value (hash , snd (fst (fst res)) , snd (fst res))
          else Error (eval_state ( ↑8 ε InternalErrors_ι_ERROR508) l).
 Proof. 
   intros. destruct l. compute.  auto. 
 Qed. 

Axiom tvm_rawConfigParam_34_eval: forall  (l: Ledger) ,
let (raw34, b) := eval_state (tvm_rawConfigParam_34) l in 
let unknown34 := eval_state (↑16 ε VMState_ι_unknown34) l in
let utime_since := eval_state (↑16 ε VMState_ι_utime_since ) l in
let utime_until := eval_state (↑16 ε VMState_ι_utime_until ) l in 
fst (decode_uint8_uint32_uint32 (toSlice raw34)) = (unknown34, utime_since, utime_until).


 Lemma ConfigParamsBase_Ф_getCurValidatorData_eval2 : forall (l: Ledger) ,
 eval_state ( ConfigParamsBase_Ф_getCurValidatorData ) l =

 let (_, Л_ok) := eval_state (tvm_rawConfigParam_34) l in
 let сurValidatorDataCell := eval_state (↑16 ε VMState_ι_curValidatorData) l in
 let utime_since := eval_state (↑16 ε VMState_ι_utime_since ) l in
 let utime_until := eval_state (↑16 ε VMState_ι_utime_until ) l in 
 let hash := tvm_hash сurValidatorDataCell in 
 let sliceRaw := toSlice сurValidatorDataCell in
 let res := decode_uint8_uint32_uint32 sliceRaw in
  if Л_ok then Value (hash , utime_since , utime_until )
          else Error (eval_state ( ↑8 ε InternalErrors_ι_ERROR508) l).
 Proof.
   intros.
   remember (tvm_rawConfigParam_34_eval l) as A.
   rewrite ConfigParamsBase_Ф_getCurValidatorData_eval.
   destruct l.
   destruct Ledger_ι_VMState.
   compute. compute in A.
   clear HeqA.
   rewrite A.
   auto. 
 Qed.
 
 
 (* function ConfigParamsBase.getPrevValidatorHash (  )  virtual internal returns  ( uint )   { 
         ( TvmCell cell ,  bool ok )  = tvm_rawConfigParam ( 32 )  ; 
        require ( ok ,  InternalErrors . ERROR507 )  ; 
        return tvm_hash ( cell )  ; 
     } 

Definition ConfigParamsBase_Ф_getPrevValidatorHash : LedgerT ( XErrorValue XInteger XInteger ) := 
	U0! {( Л_cell , Л_ok )} := tvm_rawConfigParam (! $ xInt32 !) ;
 	Require {{ $ Л_ok , ↑ε8 InternalErrors_ι_ERROR507 }} ; 
 	 tvm_hash (! $ Л_cell !).*) 

 Lemma ConfigParamsBase_Ф_getPrevValidatorHash_exec : forall (l: Ledger) , 
 	 exec_state (  ConfigParamsBase_Ф_getPrevValidatorHash ) l = l .  
 Proof. 
   intros. destruct l. auto. 
 Qed. 
 
 Lemma ConfigParamsBase_Ф_getPrevValidatorHash_eval : forall (l: Ledger)  ,
 eval_state (  ConfigParamsBase_Ф_getPrevValidatorHash ) l = 
 
 let (Л_cell, Л_ok) := eval_state (tvm_rawConfigParam_32) l in
 let hash := tvm_hash Л_cell in

 if Л_ok then Value hash
 else Error (eval_state ( ↑8 ε InternalErrors_ι_ERROR507) l).
 Proof. 
   intros. compute. auto.
 Qed. 
 
 (* function ConfigParamsBase.roundTimeParams (  )  virtual internal returns  ( 
        uint32 validatorsElectedFor , 
        uint32 electionsStartBefore , 
        uint32 electionsEndBefore , 
        uint32 stakeHeldFor
     )   { 
        bool ok ; 
         ( validatorsElectedFor ,  electionsStartBefore ,  electionsEndBefore ,  stakeHeldFor ,  ok )  = tvm_configParam ( 15 )  ; 
        require ( ok ,  InternalErrors . ERROR509 )  ; 
     } 

Definition ConfigParamsBase_Ф_roundTimeParams  : LedgerT ( XErrorValue ( XInteger32 # XInteger32 # XInteger32 # XInteger32 ) XInteger )  := 
 U0! {( Л_validatorsElectedFor , Л_electionsStartBefore , Л_electionsEndBefore , Л_stakeHeldFor , Л_ok )} := tvm_configParam (! $ xInt15 !) ; 
 Require {{ $ Л_ok , ↑ε8 InternalErrors_ι_ERROR509 }} ; 
 return# ($Л_validatorsElectedFor, $Л_electionsStartBefore, $Л_electionsEndBefore, $Л_stakeHeldFor ). 
*) 
 Lemma ConfigParamsBase_Ф_roundTimeParams_exec : forall (l: Ledger) , 
 	 exec_state (  ConfigParamsBase_Ф_roundTimeParams ) l = l .  
 Proof. 
   intros. destruct l. auto. 
 Qed. 
 
 Lemma ConfigParamsBase_Ф_roundTimeParams_eval : forall (l: Ledger) ,
  eval_state ConfigParamsBase_Ф_roundTimeParams l = 
  let (Л_params, Л_ок) := eval_state (tvm_configParam_15) l in
  let stakeHeldFor := snd Л_params in
  let electionsEndBefore := snd (fst Л_params) in
  let electionsStartBefore := snd (fst (fst Л_params)) in
  let validatorsElectedFor := fst (fst (fst Л_params)) in
   if Л_ок
    then
      Value (validatorsElectedFor,
            electionsStartBefore,
            electionsEndBefore,
            stakeHeldFor)
    else Error (eval_state ( ↑8 ε InternalErrors_ι_ERROR509) l). 
 Proof. 
   intros. destruct l.  compute. auto.
 Qed. 
 
 (* function ConfigParamsBase.getMaxStakeFactor (  )  virtual pure internal returns  ( uint32 )   { 
         ( TvmCell cell ,  bool ok )  = tvm_rawConfigParam ( 17 )  ; 
        require ( ok ,  InternalErrors . ERROR516 )  ; 
        TvmSlice s = cell . toSlice (  )  ; 
        s . loadTons (  )  ; 
        s . loadTons (  )  ; 
        s . loadTons (  )  ; 
        return s . decode ( uint32 )  ; 
     } 

Definition ConfigParamsBase_Ф_getMaxStakeFactor : LedgerT ( XErrorValue XInteger32 XInteger ) := 
	U0! {( Л_cell , Л_ok )} := tvm_rawConfigParam (! $ xInt17 !) ; 
 	Require {{ $ Л_ok , ↑ε8 InternalErrors_ι_ERROR516 }} ; 
 	U0! Л_s := ($ Л_cell) ->toSlice() ; 
 	Л_s ->loadTons() ;
 	Л_s ->loadTons() ; 
 	Л_s ->loadTons() ;
	($ Л_s) ->decode(uint32) . (*uint32*)
*) 

 Lemma ConfigParamsBase_Ф_getMaxStakeFactor_exec : forall (l: Ledger) , 
 	 exec_state ConfigParamsBase_Ф_getMaxStakeFactor l = l .  
 Proof. 
   intros. destruct l. auto. 
 Qed. 
 
 Lemma ConfigParamsBase_Ф_getMaxStakeFactor_eval : forall (l: Ledger)  ,
 eval_state (  ConfigParamsBase_Ф_getMaxStakeFactor ) l = 

 let (Л_cell, Л_ok) := eval_state (tvm_rawConfigParam_17) l in 
 let sliceRaw := toSlice Л_cell in
 let t1 := tvm_loadTons (tvm_loadTons (tvm_loadTons sliceRaw)) in
 let res := fst (decode_uint32 t1) in 
 if Л_ok
 then Value res
 else  Error (eval_state ( ↑8 ε InternalErrors_ι_ERROR516) l). 
 Proof. 
   intros. destruct l. 
   compute. auto.
 Qed. 
 
 (* function ConfigParamsBase.getElector (  )  virtual pure internal returns  ( address )   { 
         ( TvmCell cell ,  bool ok )  = tvm_rawConfigParam ( 1 )  ; 
        require ( ok ,  InternalErrors . ERROR517 )  ; 
        TvmSlice s = cell . toSlice (  )  ; 
        uint256 value = s . decode ( uint256 )  ; 
        return address . makeAddrStd (  - 1 ,  value )  ; 
     } 

Definition ConfigParamsBase_Ф_getElector : LedgerT ( XErrorValue XAddress XInteger ) := 
 U0! {( Л_cell , Л_ok )} := tvm_rawConfigParam (! $ xInt1 !) ; 
 Require {{ $ Л_ok , ↑ε8 InternalErrors_ι_ERROR517 }} ; 
 U0! Л_s := ($ Л_cell) ->toSlice() ; 
 U0! Л_value := ($ Л_s) ->decode(uint256) ; 
  address->makeAddrStd (! $xInt0 !- $ xInt1 , $ Л_value !) .
*) 

 Lemma ConfigParamsBase_Ф_getElector_exec : forall (l: Ledger) , 
 	 exec_state ConfigParamsBase_Ф_getElector l = l .  
 Proof. 
   intros. destruct l. auto. 
 Qed. 
 
 Lemma ConfigParamsBase_Ф_getElector_eval : forall (l: Ledger) ,
 eval_state  ConfigParamsBase_Ф_getElector l =

 let (Л_cell, Л_ok) := eval_state (tvm_rawConfigParam_1) l in

 let sliceRaw := toSlice Л_cell in      
 let v := fst (decode_uint256 sliceRaw) in
 let res := address_makeAddrStd (-1)%Z v in

  if Л_ok then Value res
    else Error (eval_state ( ↑8 ε InternalErrors_ι_ERROR517) l).
 Proof. 
  intros. destruct l.
  compute. auto.
 Qed. 
 
