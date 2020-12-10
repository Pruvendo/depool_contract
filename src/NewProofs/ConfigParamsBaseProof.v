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
Module ConfigParamsBaseProofs (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.


(* ConfigParamsBase_Ф_getCurValidatorData *)

Lemma ConfigParamsBase_Ф_getCurValidatorData_exec : forall (l: Ledger), 
    exec_state ( ↓ ConfigParamsBase_Ф_getCurValidatorData ) l = l. 
Proof. 
  intros. destruct l. compute. auto.
Qed. 

 Lemma ConfigParamsBase_Ф_getCurValidatorData_eval : forall (l: Ledger) ,
 let (Л_cell, Л_ok) := eval_state (tvm_rawConfigParam_34) l in
 let hash := tvm_hash Л_cell in 
 let sliceRaw := toSlice Л_cell in
 let res := decode_uint8_uint32_uint32 sliceRaw in

 eval_state ( ↓ ConfigParamsBase_Ф_getCurValidatorData ) l =
  if Л_ok then Value (hash , snd (fst (fst res)) , snd (fst res))
          else Error InternalErrors_ι_ERROR508.
 Proof. 
   intros. destruct l. compute.  auto. 
 Qed. 

Axiom tvm_rawConfigParam_34_evalAx: forall  (l: Ledger) ,
let (raw34, b) := eval_state (tvm_rawConfigParam_34) l in 
let unknown34 := eval_state (↑16 ε VMState_ι_unknown34) l in
let utime_since := eval_state (↑16 ε VMState_ι_utime_since ) l in
let utime_until := eval_state (↑16 ε VMState_ι_utime_until ) l in 
fst (decode_uint8_uint32_uint32 (toSlice raw34)) = (unknown34, utime_since, utime_until).


 Lemma ConfigParamsBase_Ф_getCurValidatorData_eval2 : forall (l: Ledger) ,
(*  let (_, Л_ok) := eval_state (tvm_rawConfigParam_34) l in *)
 let сurValidatorDataCell := eval_state (↑16 ε VMState_ι_curValidatorData) l in
 let utime_since := eval_state (↑16 ε VMState_ι_utime_since ) l in
 let utime_until := eval_state (↑16 ε VMState_ι_utime_until ) l in 
 let hash := tvm_hash сurValidatorDataCell in 
 let sliceRaw := toSlice сurValidatorDataCell in
 let res := decode_uint8_uint32_uint32 sliceRaw in

  eval_state ( ↓ ConfigParamsBase_Ф_getCurValidatorData ) l =
  (* if Л_ok then  *)Value (hash , utime_since , utime_until )
         (*  else Error (eval_state ( ↑8 ε InternalErrors_ι_ERROR508) l) *).
 Proof.
   intros.
   remember (tvm_rawConfigParam_34_evalAx l) as A.
   rewrite ConfigParamsBase_Ф_getCurValidatorData_eval.
   destruct l.
   destruct Ledger_ι_VMState.
   compute. compute in A.
   clear HeqA.
   rewrite A.
   auto. 
 Qed.
 

(* ConfigParamsBase_Ф_getPrevValidatorHash *) 
 
Lemma ConfigParamsBase_Ф_getPrevValidatorHash_exec : forall (l: Ledger) , 
 	 exec_state ( ↓ ConfigParamsBase_Ф_getPrevValidatorHash ) l = l .  
 Proof. 
   intros. destruct l. auto. 
 Qed. 
 
Lemma ConfigParamsBase_Ф_getPrevValidatorHash_eval : forall (l: Ledger)  ,
let (_, Л_ok) := eval_state tvm_rawConfigParam_32 l in
let Л_cell := eval_state (↑ε16 VMState_ι_prevValidatorData) l in
let hash := tvm_hash Л_cell in

    eval_state ( ↓ ConfigParamsBase_Ф_getPrevValidatorHash ) l = 
    if Л_ok then Value hash
            else Error InternalErrors_ι_ERROR507 .
 Proof. 
   intros. compute. auto.
 Qed. 

Lemma ConfigParamsBase_Ф_getPrevValidatorHash_eval2 : forall (l: Ledger)  ,
(* let (_, Л_ok) := eval_state tvm_rawConfigParam_32 l in *)
let Л_cell := eval_state (↑ε16 VMState_ι_prevValidatorData) l in
let hash := tvm_hash Л_cell in

    eval_state ( ↓ ConfigParamsBase_Ф_getPrevValidatorHash ) l = 
    (* if Л_ok then  *)Value hash
            (* else Error InternalErrors_ι_ERROR507 *) .
 Proof. 
   intros. compute. auto.
 Qed. 


 (* ConfigParamsBase_Ф_roundTimeParams *)

 Lemma ConfigParamsBase_Ф_roundTimeParams_exec : forall (l: Ledger) , 
 	 exec_state (↓ ConfigParamsBase_Ф_roundTimeParams ) l = l .  
 Proof. 
   intros. destruct l. auto. 
 Qed. 
 
Lemma ConfigParamsBase_Ф_roundTimeParams_eval : forall (l: Ledger) ,
let (_ , ок) := eval_state (tvm_configParam_15) l in

let validatorsElectedFor := eval_state (↑16 ε VMState_ι_validatorsElectedFor) l in
let electionsStartBefore := eval_state (↑16 ε VMState_ι_electionsStartBefore) l in
let electionsEndBefore := eval_state (↑16 ε VMState_ι_electionsEndBefore) l in
let stakeHeldFor := eval_state (↑16 ε VMState_ι_stakeHeldFor) l in

   eval_state (↓ ConfigParamsBase_Ф_roundTimeParams) l = 
   if ок then Value (validatorsElectedFor, electionsStartBefore, electionsEndBefore, stakeHeldFor)
         else Error InternalErrors_ι_ERROR509 . 
 Proof. 
   intros. destruct l.  compute. auto.
 Qed.
 
 
Lemma ConfigParamsBase_Ф_roundTimeParams_eval2 : forall (l: Ledger) ,
(* let (_ , ок) := eval_state (tvm_configParam_15) l in
 *)
let validatorsElectedFor := eval_state (↑16 ε VMState_ι_validatorsElectedFor) l in
let electionsStartBefore := eval_state (↑16 ε VMState_ι_electionsStartBefore) l in
let electionsEndBefore := eval_state (↑16 ε VMState_ι_electionsEndBefore) l in
let stakeHeldFor := eval_state (↑16 ε VMState_ι_stakeHeldFor) l in

   eval_state (↓ ConfigParamsBase_Ф_roundTimeParams) l = 
   (* if ок then  *)Value (validatorsElectedFor, electionsStartBefore, electionsEndBefore, stakeHeldFor)
         (* else Error InternalErrors_ι_ERROR509 *). 
 Proof. 
   intros. destruct l.  compute. auto.
 Qed.


 (* ConfigParamsBase_Ф_getMaxStakeFactor *)

Lemma ConfigParamsBase_Ф_getMaxStakeFactor_exec : forall (l: Ledger) , 
  exec_state (↓ ConfigParamsBase_Ф_getMaxStakeFactor) l = l .  
Proof. 
  intros. destruct l. auto. 
Qed. 
 
Lemma ConfigParamsBase_Ф_getMaxStakeFactor_eval : forall (l: Ledger)  ,
let (Л_cell, Л_ok) := eval_state tvm_rawConfigParam_17 l in 
let sliceRaw := toSlice Л_cell in
let t1 := tvm_loadTons (tvm_loadTons (tvm_loadTons sliceRaw)) in
let res := fst (decode_uint32 t1) in 
    eval_state (↓ ConfigParamsBase_Ф_getMaxStakeFactor ) l = 
    if Л_ok then Value res
            else Error InternalErrors_ι_ERROR516 . 
Proof. 
  intros. destruct l. 
  compute. auto.
Qed. 

(* VMState_ι_unknown17_1 : I8 ; (*check the type*)
		VMState_ι_unknown17_2 : I8 ; 
		VMState_ι_unknown17_3 : I8 ; 
		VMState_ι_maxStakeFactor : I32; *)

Axiom tvm_rawConfigParam_17_evalAx: forall  (l: Ledger) ,
let (raw17, b) := eval_state tvm_rawConfigParam_17 l in 
(* let unknown17_1 := eval_state (↑16 ε VMState_ι_unknown17_1) l in
let unknown17_2 := eval_state (↑16 ε VMState_ι_unknown17_2 ) l in
let unknown17_3 := eval_state (↑16 ε VMState_ι_unknown17_3 ) l in  *)
let maxStakeFactor := eval_state (↑16 ε VMState_ι_maxStakeFactor ) l in 

fst (decode_uint32 (tvm_loadTons (tvm_loadTons (tvm_loadTons (toSlice raw17))))) = maxStakeFactor.

Lemma ConfigParamsBase_Ф_getMaxStakeFactor_eval2 : forall (l: Ledger)  ,
let maxStakeFactor := eval_state (↑16 ε VMState_ι_maxStakeFactor ) l in 
    eval_state (↓ ConfigParamsBase_Ф_getMaxStakeFactor ) l =  Value maxStakeFactor. 
Proof. 
  intros.
  remember (tvm_rawConfigParam_17_evalAx l) as A.
  rewrite ConfigParamsBase_Ф_getMaxStakeFactor_eval.
  destruct l.
  destruct Ledger_ι_VMState.
  compute. compute in A.
  clear HeqA.
  rewrite A.
  auto. 
Qed.


(* ConfigParamsBase_Ф_getElector *)


Lemma ConfigParamsBase_Ф_getElector_exec : forall (l: Ledger) , 
  exec_state (↓ ConfigParamsBase_Ф_getElector) l = l .  
Proof. 
  intros. destruct l. auto. 
Qed. 
 
Lemma ConfigParamsBase_Ф_getElector_eval : forall (l: Ledger) ,
let (Л_cell, Л_ok) := eval_state (tvm_rawConfigParam_1) l in
let sliceRaw := toSlice Л_cell in      
let v := fst (decode_uint256 sliceRaw) in
let res := address_makeAddrStd (-1)%Z v in

eval_state (↓ ConfigParamsBase_Ф_getElector) l =
if Л_ok then Value res
        else Error InternalErrors_ι_ERROR517 .
Proof. 
  intros. destruct l.
  compute. auto.
Qed. 

Axiom tvm_rawConfigParam_1_evalAx: forall  (l: Ledger) ,
let (raw1, b) := eval_state tvm_rawConfigParam_1 l in 
let electorRawAddress := eval_state (↑16 ε VMState_ι_electorRawAddress ) l in 

fst (decode_uint256 (toSlice raw1)) = electorRawAddress.

Lemma ConfigParamsBase_Ф_getElector_eval2 : forall (l: Ledger) ,
let electorRawAddress := eval_state (↑16 ε VMState_ι_electorRawAddress ) l in 
let res := address_makeAddrStd (-1)%Z electorRawAddress in
  eval_state (↓ ConfigParamsBase_Ф_getElector) l = Value res.
Proof. 
  intros.
  remember (tvm_rawConfigParam_1_evalAx l) as A.
  rewrite ConfigParamsBase_Ф_getElector_eval.
  destruct l.
  destruct Ledger_ι_VMState.
  compute. compute in A.
  clear HeqA.
  rewrite A.
  auto. 
Qed. 

 
End ConfigParamsBaseProofs.