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
Module DePoolContract_Ф_constructor6 (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.


Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair intInc hmapPush.

(* Check eval_state tvm_address _. *)

(* Locate "address". *)

Lemma DePoolContract_Ф_constructor6_exec: forall  ( minStake validatorAssurance: Z )
                                                  ( proxyCode: TvmCell ) 
                                                  ( validatorWallet : Z )
                                                  ( participantRewardFraction : Z )
                                                  ( l: Ledger ),
let lv := exec_state (↓ ValidatorBase_Ф_Constructor2 validatorWallet) l in 
let lv := {$ lv With (RoundsBase_ι_m_roundQty, 0) $} in
let address := eval_state tvm_address l in 
let wid := addressWid address in
    let wid0 := wid =? 0 in
let tvm_pubkey := eval_state tvm_pubkey l in
let msg_pubkey := eval_state msg_pubkey l in
    let pubkeys :=  msg_pubkey =? tvm_pubkey in
    let tvm_pubkey0 := negb (tvm_pubkey =? 0) in
    let minstake1 := minStake >=? x1_ton in
    let minStakeValidator := minStake <=? validatorAssurance in
let proxy_code_hash := tvm_hash proxyCode in
let PROXY_CODE_HASH := DePool_ι_PROXY_CODE_HASH in 
    let proxyCodeSame := proxy_code_hash =? PROXY_CODE_HASH in 
    let validatorStdAddrWithoutAnyCast := isStdAddrWithoutAnyCast validatorWallet in
   (*  let associationStdAddrWithoutAnyCast := isStdAddrWithoutAnyCast validatorWallet in  *)
    let participantRewardFraction0 := ( ( participantRewardFraction >? 0 ) && 
                                        ( participantRewardFraction <? 100 ) )%bool in
let validatorRewardFraction := 100 - participantRewardFraction in
let CRITICAL_THRESHOLD := DePool_ι_CRITICAL_THRESHOLD in
   (*  let if1 : bool := balanceThreshold >=? CRITICAL_THRESHOLD in *)
let balance := eval_state tvm_balance l in 
let DEPOOL_CONSTRUCTOR_FEE :=  DePoolLib_ι_DEPOOL_CONSTRUCTOR_FEE in
let MIN_PROXY_BALANCE := DePoolLib_ι_MIN_PROXY_BALANCE in 
let PROXY_CONSTRUCTOR_FEE := DePoolLib_ι_PROXY_CONSTRUCTOR_FEE in 
    let balance2 := balance >? CRITICAL_THRESHOLD + DEPOOL_CONSTRUCTOR_FEE + 
                                2 * ( MIN_PROXY_BALANCE + PROXY_CONSTRUCTOR_FEE ) in

    let roundTimeParams := eval_state ConfigParamsBase_Ф_roundTimeParams l in
    let curValidatorData := eval_state ConfigParamsBase_Ф_getCurValidatorData l in
    let prevValidatorHash := eval_state ConfigParamsBase_Ф_getPrevValidatorHash l in

let sender := eval_state (↓ msg_sender) l in
let isDepool : bool := ((tvm_pubkey =? tvm_hash (toCell (builder_store default sender 0))) ||
                       (tvm_pubkey =? tvm_hash (toCell (builder_store default sender 1))))%bool in    
(*** end of require section ****)
let la := exec_state (↓ tvm_accept) lv in    
let address := eval_state (↓ tvm_address) la in 

let b0 := builder_store default address 0 in
let b1 := builder_store default address 1 in
let pk0 := tvm_hash (toCell b0) in
let pk1 := tvm_hash (toCell b1) in
let data0 := tvm_buildEmptyData pk0 in
let data1 := tvm_buildEmptyData pk1 in
let stateInit0 := tvm_buildStateInit proxyCode data0 in
let stateInit1 := tvm_buildStateInit proxyCode data1 in
let m_proxies := eval_state (↑3 ε ProxyBase_ι_m_proxies) l in
let (epa0, lp0) := run (↓ tvm_newE DePoolProxyContractD 
                                {|| cmessage_wid ::= $ xInt0 !- $ xInt1 ,
                                cmessage_value ::= $ DePoolLib_ι_MIN_PROXY_BALANCE !+ $ DePoolLib_ι_PROXY_CONSTRUCTOR_FEE ,
                                cmessage_stateInit ::= $ stateInit0 ||}
                                DePoolProxyContract_Ф_constructor5 ) la in
let (epa1, lp1) := run (↓ tvm_newE DePoolProxyContractD 
                                {|| cmessage_wid ::= $ xInt0 !- $ xInt1 ,
                                cmessage_value ::= $ DePoolLib_ι_MIN_PROXY_BALANCE !+ $ DePoolLib_ι_PROXY_CONSTRUCTOR_FEE ,
                                cmessage_stateInit ::= $ stateInit1 ||}
                                DePoolProxyContract_Ф_constructor5 ) lp0 in
let pa0 := errorMapDefault Datatypes.id epa0 (-1) in
let pa1 := errorMapDefault Datatypes.id epa1 (-1) in
let lp1' := {$ lp1 With (DePoolContract_ι_m_poolClosed, false); 
                         (DePoolContract_ι_m_minStake, minStake); 
                         (DePoolContract_ι_m_validatorAssurance, validatorAssurance);
                         (DePoolContract_ι_m_participantRewardFraction, participantRewardFraction);
                         (DePoolContract_ι_m_validatorRewardFraction, validatorRewardFraction)  ;
                         (ProxyBase_ι_m_proxies, hmapPush pa1 (hmapPush pa0 m_proxies)  )  $} in

let (r2, lr2) := run (↓ DePoolContract_Ф_generateRound) lp1' in
let (r1, lr1) := run (↓ DePoolContract_Ф_generateRound) lr2 in
let (r0, lr0) := run (↓ DePoolContract_Ф_generateRound) lr1 in
let (rpre0, lrpre0) := run (↓ DePoolContract_Ф_generateRound) lr0 in

let now := eval_state (↓ tvm_now) lrpre0 in
let validationEnd := errorMapDefaultF snd curValidatorData (fun _ => 0) in
let electionsStartBefore := errorMapDefaultF snd roundTimeParams (fun _ => 0) in
let areElectionsStarted := now >=? validationEnd - electionsStartBefore  in 
let vhash := if areElectionsStarted then  (errorMapDefaultF (fst ∘ fst) curValidatorData (fun _ => 0)) else (errorMapDefaultF Datatypes.id prevValidatorHash (fun _ => 0)) in


let r0 := {$ r0 with (RoundsBase_ι_Round_ι_step, RoundsBase_ι_RoundStepP_ι_Pooling) $} in
let r2 := {$ r2 with (RoundsBase_ι_Round_ι_step, RoundsBase_ι_RoundStepP_ι_Completed);
                     (RoundsBase_ι_Round_ι_completionReason, RoundsBase_ι_CompletionReasonP_ι_FakeRound);
                     (RoundsBase_ι_Round_ι_unfreeze, 0)  $} in
let r1 := {$ r1 with (RoundsBase_ι_Round_ι_step, RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze);
                     (RoundsBase_ι_Round_ι_completionReason, RoundsBase_ι_CompletionReasonP_ι_FakeRound);
                     (RoundsBase_ι_Round_ι_unfreeze, 0);
                     (RoundsBase_ι_Round_ι_vsetHashInElectionPhase, vhash)  $} in 
                  
let lsetPre0 := exec_state (↓ RoundsBase_Ф_setRound (rpre0 ->> RoundsBase_ι_Round_ι_id) rpre0) lrpre0 in
let lset0 := exec_state (↓ RoundsBase_Ф_setRound (r0 ->> RoundsBase_ι_Round_ι_id) r0) lsetPre0 in
let lset1 := exec_state (↓ RoundsBase_Ф_setRound (r1 ->> RoundsBase_ι_Round_ι_id) r1) lset0 in
let lset2 := exec_state (↓ RoundsBase_Ф_setRound (r2 ->> RoundsBase_ι_Round_ι_id) r2) lset1 in
                        
exec_state (↓ DePoolContract_Ф_Constructor6 minStake validatorAssurance 
                                          proxyCode validatorWallet 
                                          participantRewardFraction) l = 
if (wid0) then 
    if (pubkeys) then 
        if (tvm_pubkey0) then  
            if (minstake1) then 
                if (minStakeValidator) then  
                    if (proxyCodeSame) then 
                        if (validatorStdAddrWithoutAnyCast) then
                            if (participantRewardFraction0) then 
                                if (balance2) then 
                                    if isDepool then
                                         if (errorValueIsValue roundTimeParams) then 
                                            if (errorValueIsValue curValidatorData) then 
                                                if (errorValueIsValue prevValidatorHash) then  lset2
                                                 else lp1'
                                            else lp1'
                                        else lp1'     
                                    else la
                                else lv 
                            else lv
                        else lv
                    else lv
                else lv
            else lv
        else lv
    else lv
else lv. 

Proof.
    intros.
    destructLedger l. 
    compute.

    repeat rewrite letIf.  idtac.
    repeat rewrite matchIf.  idtac.
    repeat rewrite letIf.  idtac.
    repeat rewrite matchIf.  idtac.
    repeat rewrite letIf.  idtac. 

    all: repeat destructIf_solve2. (* idtac. *)
    
    (* idtac.*)

   (* Require Import depoolContract.Lib.CommonStateProofs.
    all: apply ledgerEq; auto. idtac.
    simpl.

    apply RoundsBaseEq; auto. idtac.
    simpl. idtac.

    all: try congruence. *)

Qed.

Lemma DePoolContract_Ф_constructor6_eval: forall  ( minStake validatorAssurance: Z )
                                                  ( proxyCode: TvmCell ) 
                                                  ( validatorWallet : Z )
                                                  ( participantRewardFraction : Z )
                                                  ( l: Ledger ),
let address := eval_state tvm_address l in
let wid := addressWid address in
    let wid0 := wid =? 0 in
let tvm_pubkey := eval_state tvm_pubkey l in
let msg_pubkey := eval_state msg_pubkey l in
    let pubkeys :=  msg_pubkey =? tvm_pubkey in
    let tvm_pubkey0 := negb (tvm_pubkey =? 0) in
    let minstake1 := minStake >=? x1_ton in
    let minStakeValidator := minStake <=? validatorAssurance in
let proxy_code_hash := tvm_hash proxyCode in
let PROXY_CODE_HASH :=  DePool_ι_PROXY_CODE_HASH in
    let proxyCodeSame := proxy_code_hash =? PROXY_CODE_HASH in 
    let validatorStdAddrWithoutAnyCast := isStdAddrWithoutAnyCast validatorWallet in
   (*  let associationStdAddrWithoutAnyCast := isStdAddrWithoutAnyCast validatorWallet in  *)
    let participantRewardFraction0 := ( ( participantRewardFraction >? 0 ) && 
                                        ( participantRewardFraction <? 100 ) )%bool in
let validatorRewardFraction := 100 - participantRewardFraction in
let CRITICAL_THRESHOLD :=  DePool_ι_CRITICAL_THRESHOLD  in
   (*  let if1 : bool := balanceThreshold >=? CRITICAL_THRESHOLD in *)
let balance := eval_state tvm_balance l in 
let DEPOOL_CONSTRUCTOR_FEE := DePoolLib_ι_DEPOOL_CONSTRUCTOR_FEE  in
let MIN_PROXY_BALANCE :=  DePoolLib_ι_MIN_PROXY_BALANCE in 
let PROXY_CONSTRUCTOR_FEE :=  DePoolLib_ι_PROXY_CONSTRUCTOR_FEE in 
    let balance2 := balance >? CRITICAL_THRESHOLD + DEPOOL_CONSTRUCTOR_FEE + 
                                2 * ( MIN_PROXY_BALANCE + PROXY_CONSTRUCTOR_FEE ) in

    let roundTimeParams := eval_state ConfigParamsBase_Ф_roundTimeParams l in
    let curValidatorData := eval_state ConfigParamsBase_Ф_getCurValidatorData l in
    let prevValidatorHash := eval_state ConfigParamsBase_Ф_getPrevValidatorHash l in

let sender := eval_state (↓ msg_sender) l in
let isDepool : bool := ((tvm_pubkey =? tvm_hash (toCell (builder_store default sender 0))) ||
                       (tvm_pubkey =? tvm_hash (toCell (builder_store default sender 1))))%bool in    

eval_state (↓ DePoolContract_Ф_Constructor6 minStake validatorAssurance 
                                          proxyCode validatorWallet 
                                          participantRewardFraction) l = 

if (wid0) then 
    if (pubkeys) then 
        if (tvm_pubkey0) then  
            if (minstake1) then 
                if (minStakeValidator) then  
                    if (proxyCodeSame) then 
                        if (validatorStdAddrWithoutAnyCast) then                          
                            if (participantRewardFraction0) then 
                                if (balance2) then 
                                    if isDepool then
                                        if (errorValueIsValue roundTimeParams) then 
                                            if (errorValueIsValue curValidatorData) then 
                                                if (errorValueIsValue prevValidatorHash) then Value I
                                                else errorMapDefaultF (fun _ => Value I) prevValidatorHash (fun er => Error er)
                                            else errorMapDefaultF (fun _ => Value I) curValidatorData (fun er => Error er) 
                                        else errorMapDefaultF (fun _ => Value I) roundTimeParams (fun er => Error er)      
                                    else Error (eval_state (↑ε10 DePoolProxyContract_ι_ERROR_IS_NOT_DEPOOL) l)                    
                                else Error (eval_state (↑ε7 Errors_ι_BAD_ACCOUNT_BALANCE) l )                               
                            else Error (eval_state (↑ε7 Errors_ι_BAD_PART_REWARD) l)
                        else Error (eval_state (↑ε7 Errors_ι_VALIDATOR_IS_NOT_STD) l)                         
                    else Error (eval_state (↑ε7 Errors_ι_BAD_PROXY_CODE) l) 
                else Error (eval_state (↑ε7 Errors_ι_BAD_STAKES) l)   
            else Error (eval_state (↑ε7 Errors_ι_BAD_STAKES) l)   
        else Error (eval_state (↑ε7 Errors_ι_CONSTRUCTOR_NO_PUBKEY) l)       
    else Error (eval_state (↑ε7 Errors_ι_IS_NOT_OWNER) l)    
else  Error (eval_state (↑ε7 Errors_ι_NOT_WORKCHAIN0) l) . 

Proof.
    intros.
    destructLedger l. 
    compute.
  
    Time repeat destructIf_solve. idtac.

    all: try congruence.

Qed.


End DePoolContract_Ф_constructor6.