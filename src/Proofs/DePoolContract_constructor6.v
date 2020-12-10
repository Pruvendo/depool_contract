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

Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair.

(* Opaque tvm_accept DePoolContract_Ф_checkPureDePoolBalance RoundsBase_Ф_getRound1. *)


Lemma ifSimpleState: forall X (b: bool) (f g: Ledger -> X * Ledger), 
(if b then SimpleState f else SimpleState g ) =
SimpleState (if b then f else  g).
Proof.
  intros. destruct b; auto.
Qed.  

Lemma ifFunApply: forall X (b: bool) (f g: Ledger -> X * Ledger) l, 
(if b then f else  g ) l =
(if b then f l else g l).
Proof.
  intros. destruct b; auto.
Qed. 



Lemma fstImplies : forall  X Y T (f: X*T) (g: X -> Y)  ,  (let (x, _) := f in g x) = g (fst f).
Proof.
  intros.
  destruct f; auto.
Qed.


Lemma sndImplies : forall  X Y T (f: X*T) (g: T -> Y)  ,  (let (_, t) := f in g t) = g (snd f).
Proof.
  intros.
  destruct f; auto.
Qed.

Lemma fstsndImplies : forall  X Y T (f: X*T) (g: X -> T -> Y)  ,  (let (x, t) := f in g x t) = g (fst f) (snd f).
Proof.
  intros.
  destruct f; auto.
Qed.


Ltac pr_numgoals := let n := numgoals in idtac "There are" n "goals".



(* Definition DePoolContract_Ф_Constructor6 ( Л_minStake : XInteger64 )
                                         ( Л_validatorAssurance : XInteger64 )   
										                     ( Л_proxyCode :  TvmCell )
                                         ( Л_validatorWallet : XAddress )
                                         ( Л_association : XAddress )
                                         ( Л_participantRewardFraction : XInteger8 )
                                         ( Л_validatorRewardFraction : XInteger8 )
                                         ( Л_minimumBalance : XInteger64 )										                    
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
Require2 {{ tvm_hash (! $ Л_proxyCode !) ?== ↑ε12 DePoolContract_ι_PROXY_CODE_HASH , ↑ε7 Errors_ι_BAD_PROXY_CODE }} ; 

(*require(validatorWallet.isStdAddrWithoutAnyCast(), Errors.VALIDATOR_IS_NOT_STD);*)
Require2 {{ ($ Л_validatorWallet) ->isStdAddrWithoutAnyCast() , ↑ε7 Errors_ι_VALIDATOR_IS_NOT_STD }} ;  

(* require(association.isStdAddrWithoutAnyCast(), Errors.ASSOCIATION_IS_NOT_STD); *)
Require2 {{ ($ Л_association) ->isStdAddrWithoutAnyCast() , ↑ε7 Errors_ι_ASSOCIATION_IS_NOT_STD }} ; 

(* require(participantRewardFraction > 0, Errors.BAD_PART_REWARD); *)
Require2 {{ $ Л_participantRewardFraction ?> $xInt0, ↑ε7 Errors_ι_BAD_PART_REWARD }} ; 

(*   require(validatorRewardFraction > 0, Errors.BAD_VALID_REWARD); *)
Require2 {{ $ Л_validatorRewardFraction ?> $xInt0, ↑ε7 Errors_ι_BAD_VALID_REWARD }} ; 

(*require(uint(participantRewardFraction) + validatorRewardFraction <= 100,
                Errors.PERCENT_NOT_EQ_100);*)
Require2 {{ $ Л_participantRewardFraction !+ 
            $ Л_validatorRewardFraction ?<= $xInt100, ↑ε7 Errors_ι_PERCENT_NOT_EQ_100 }} ;

(*  uint8 associationRewardFraction = 100 - participantRewardFraction - validatorRewardFraction;
        bool isFractionZero = associationRewardFraction == 0;
        bool isAddressZero = association == address(0);
        require(isFractionZero == isAddressZero, Errors.BAD_ASSOCIATION_AND_PERCENT); // both are set or both are equal to zero
        require(minimumBalance >= 2 * CRITICAL_MIN_BALANCE, Errors.BAD_MINIMUM_BALANCE);
 *)

 U0! Л_associationRewardFraction := $xInt100 !- $ Л_participantRewardFraction !- $ Л_validatorRewardFraction ; 
 U0! Л_isFractionZero := $ Л_associationRewardFraction ?== $ xInt0 ; 
 U0! Л_isAddressZero := $ Л_association ?== $ xInt0 ;  
 Require2 {{ $Л_isFractionZero ?== $ Л_isAddressZero, ↑ε7 Errors_ι_BAD_ASSOCIATION_AND_PERCENT }} ; 
 
 Require2 {{ $Л_minimumBalance ?>= $xInt2 !* (↑ε12 DePoolContract_ι_CRITICAL_MIN_BALANCE) , ↑ε7 Errors_ι_BAD_MINIMUM_BALANCE }} ;

 (* require(address(this).balance >=
                    minimumBalance + 2 * (DePoolLib.MIN_PROXY_BALANCE + DePoolLib.PROXY_CONSTRUCTOR_FEE),
                Errors.BAD_MINIMUM_BALANCE);
 *)
 Require2 {{ tvm_balance () ?>= $Л_minimumBalance !+ 
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
U0! Л_publicKey := tvm_hash (! ($ Л_b) ->toCell !); 
U0! Л_data := tvm_buildEmptyData (! $ Л_publicKey !); 
U0! Л_stateInit := tvm_buildStateInit (!  $Л_proxyCode ,  $Л_data !);  
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

(*  m_associationRewardFraction = associationRewardFraction; *)
(↑12 U1! DePoolContract_ι_m_associationRewardFraction := $ Л_associationRewardFraction) >>

(*  m_association = association; *)
(↑12 U1! DePoolContract_ι_m_association := $ Л_association) >>

(*  m_minimumBalance = minimumBalance; *)
(↑12 U1! DePoolContract_ι_m_minimumBalance := $ Л_minimumBalance) >> 


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
 *)
    
(*     Definition DePoolContract_Ф_addOrdinaryStake ( Л_stake : XInteger64 ) : LedgerT ( XErrorValue True XInteger ) := 
    do r ← DePoolContract_Ф_addOrdinaryStake' Л_stake ;
    return! (xErrorMapDefaultF (xValue ∘ fromValueValue) r xError).  *)
       
(* 
    constructor(
        uint64 minStake,
        uint64 validatorAssurance,
        TvmCell proxyCode,
        address validatorWallet,
        uint8 participantRewardFraction,
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
        require(participantRewardFraction > 0 && participantRewardFraction < 100, Errors.BAD_PART_REWARD);
        uint8 validatorRewardFraction = 100 -  participantRewardFraction;
        require(balanceThreshold >= CRITICAL_THRESHOLD, Errors.BAD_BALANCE_THRESHOLD);

        require(address(this).balance >=
                    balanceThreshold +
                    DePoolLib.DEPOOL_CONSTRUCTOR_FEE +
                    2 * (DePoolLib.MIN_PROXY_BALANCE + DePoolLib.PROXY_CONSTRUCTOR_FEE),
                Errors.BAD_ACCOUNT_BALANCE);

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
(* 
 Check xIsError. *)

Check 0.
Lemma constructor6_eval: forall  (minStake 
                                  validatorAssurance: Z)
                                 (proxyCode: TvmCell) 
                                 (validatorWallet : Z)
                                 (participantRewardFraction 
                                  balanceThreshold: Z)
                                 (l: Ledger),
eval_state (DePoolContract_Ф_Constructor6 minStake validatorAssurance 
                                          proxyCode validatorWallet 
                                          participantRewardFraction 
                                          balanceThreshold) l = 
(* require(address(this).wid == 0, Errors.NOT_WORKCHAIN0); *)
let address := eval_state tvm_address l in
let wid := addressWid address in
    let wid0 := wid =? 0 in
(* require(msg.pubkey() == tvm.pubkey(), Errors.IS_NOT_OWNER); *)    
let tvm_pubkey := eval_state tvm_pubkey l in
let msg_pubkey := eval_state msg_pubkey l in
    let pubkeys :=  msg_pubkey =? tvm_pubkey in
(* require(tvm.pubkey() != 0, Errors.CONSTRUCTOR_NO_PUBKEY); *)
    let tvm_pubkey0 := negb (tvm_pubkey =? 0) in
    (* require(minStake >= 1 ton, Errors.BAD_STAKES); *)
    let minstake1 := minStake >=? x1_ton in
    (* require(minStake <= validatorAssurance, Errors.BAD_STAKES); *)
    let minStakeValidator := minStake <=? validatorAssurance in
    (* require(tvm.hash(proxyCode) == PROXY_CODE_HASH, Errors.BAD_PROXY_CODE); *)
let proxy_code_hash := tvm_hash proxyCode in
let PROXY_CODE_HASH := eval_state (↑ε12 DePoolContract_ι_PROXY_CODE_HASH) l in
    let proxyCodeSame := proxy_code_hash =? PROXY_CODE_HASH in 
    (* require(validatorWallet.isStdAddrWithoutAnyCast(), Errors.VALIDATOR_IS_NOT_STD); *)
    let validatorStdAddrWithoutAnyCast := isStdAddrWithoutAnyCast validatorWallet in
    (* require(validatorWallet.isStdAddrWithoutAnyCast(), Errors.VALIDATOR_IS_NOT_STD); *)
    let associationStdAddrWithoutAnyCast := isStdAddrWithoutAnyCast validatorWallet in 
    (* require(participantRewardFraction > 0 && participantRewardFraction < 100, Errors.BAD_PART_REWARD); *)
    let participantRewardFraction0 := ( ( participantRewardFraction >? 0 ) && 
                                        ( participantRewardFraction <? 100 ) )%bool in
    (* uint8 validatorRewardFraction = 100 -  participantRewardFraction; *)
let validatorRewardFraction := 100 - participantRewardFraction in
    (* require(balanceThreshold >= CRITICAL_THRESHOLD, Errors.BAD_BALANCE_THRESHOLD); *)
let CRITICAL_THRESHOLD := eval_state ( ↑ε12 DePoolContract_ι_CRITICAL_THRESHOLD ) l in
    let if1 : bool := balanceThreshold >=? CRITICAL_THRESHOLD in

                  (* require(address(this).balance >=
                                  balanceThreshold +
                                  DePoolLib.DEPOOL_CONSTRUCTOR_FEE +
                                  2 * (DePoolLib.MIN_PROXY_BALANCE + DePoolLib.PROXY_CONSTRUCTOR_FEE),
                              Errors.BAD_ACCOUNT_BALANCE); *)
let balance := eval_state tvm_balance l in 
let DEPOOL_CONSTRUCTOR_FEE := eval_state ( ↑ε9 DePoolLib_ι_DEPOOL_CONSTRUCTOR_FEE ) l in
let MIN_PROXY_BALANCE := eval_state (↑ε9 DePoolLib_ι_MIN_PROXY_BALANCE) l in 
let PROXY_CONSTRUCTOR_FEE := eval_state (↑ε9 DePoolLib_ι_PROXY_CONSTRUCTOR_FEE) l in 
    let balance2 := balance >=? balanceThreshold + DEPOOL_CONSTRUCTOR_FEE + 
                                2 * ( MIN_PROXY_BALANCE + PROXY_CONSTRUCTOR_FEE ) in

    let roundTimeParams := eval_state ConfigParamsBase_Ф_roundTimeParams l in
    let curValidatorData := eval_state ConfigParamsBase_Ф_getCurValidatorData l in
    let prevValidatorHash := eval_state ConfigParamsBase_Ф_getPrevValidatorHash l in
if (wid0) then 
    if (pubkeys) then 
        if (tvm_pubkey0) then  
            if (minstake1) then 
                if (minStakeValidator) then  
                    if (proxyCodeSame) then 
                        if (validatorStdAddrWithoutAnyCast) then 
                            if (associationStdAddrWithoutAnyCast) then 
                                if (participantRewardFraction0) then 
                      if if1 then
                                    (* if (validatorRewardFraction0) then  *)
                                        (* if (fraction100) then *) 
                                            (* if (assFractionZero: bool) then *)  
                                                (* if (minimumBalance2) then  *)
                                                    if (balance2) then 
                                                        if (errorValueIsValue roundTimeParams) then 
                                                            if (errorValueIsValue curValidatorData) then 
                                                                if (errorValueIsValue prevValidatorHash) then Value I
                                                                else errorMapDefaultF (fun _ => Value I) prevValidatorHash (fun er => Error er)
                                                            else errorMapDefaultF (fun _ => Value I) curValidatorData (fun er => Error er) 
                                                        else errorMapDefaultF (fun _ => Value I) roundTimeParams (fun er => Error er)  
                                                    else Error (eval_state (↑ε7 Errors_ι_BAD_ACCOUNT_BALANCE) l )
                                                (* else Error (eval_state (↑ε7 Errors_ι_BAD_MINIMUM_BALANCE) l) *)
                                           (*  else Error (eval_state (↑ε7 Errors_ι_BAD_ASSOCIATION_AND_PERCENT) l) *)
                                        (* else  Error (eval_state (↑ε7 Errors_ι_PERCENT_NOT_EQ_100) l) *)  
                                    (* else Error (eval_state (↑ε7 Errors_ι_BAD_VALID_REWARD) l) *)  
                                else Error (eval_state (↑ε7 Errors_ι_BAD_BALANCE_THRESHOLD) l)
                      else Error (eval_state (↑ε7 Errors_ι_BAD_PART_REWARD) l)
                            else Error (eval_state (↑ε7 Errors_ι_VALIDATOR_IS_NOT_STD) l) 
                        else Error (eval_state (↑ε7 Errors_ι_VALIDATOR_IS_NOT_STD) l)
                    else Error (eval_state (↑ε7 Errors_ι_BAD_PROXY_CODE) l) 
                else Error (eval_state (↑ε7 Errors_ι_BAD_STAKES) l)   
            else Error (eval_state (↑ε7 Errors_ι_BAD_STAKES) l)   
        else Error (eval_state (↑ε7 Errors_ι_CONSTRUCTOR_NO_PUBKEY) l)       
    else Error (eval_state (↑ε7 Errors_ι_IS_NOT_OWNER) l)    
else  Error (eval_state (↑ε7 Errors_ι_NOT_WORKCHAIN0) l) .                                                

Proof.
  intros.
  destruct l. 
  destruct Ledger_ι_DebugDePool, Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ConfigParamsBase, Ledger_ι_ParticipantBase, 
  Ledger_ι_DePoolHelper, Ledger_ι_Errors, Ledger_ι_InternalErrors, Ledger_ι_DePoolLib, Ledger_ι_DePoolProxyContract, 
  Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_DePool, Ledger_ι_Participant, Ledger_ι_TestElector, 
  Ledger_ι_VMState, Ledger_ι_LocalState.

  compute. idtac.


  Time  repeat (
  
  time match goal with

    | |- ?x =>
      match x with
       
     
      | context [if ?b then _ else _] =>  idtac "if..." b; 
                                          repeat rewrite ifSimpleState ; 
                                          repeat rewrite ifFunApply ;
                                            (* compute ; *)
                                            (* let rem := fresh "rem" in  *)
                                            (* set (rem:= b) ;  *)
                                          case_eq b ; 
                                          simpl ; intros     
(*         | context  [match RoundsBase_Ф__addStakes ?a ?b ?c ?d ?e ?f
                  with
                  | SimpleState s => s
                  end ?m] => idtac "found RoundsBase_Ф__addStakes ..."  a b c d e f; 
                             let p := fresh"p" in
                             destruct (RoundsBase_Ф__addStakes a b c d e f) as (p);
                             let v := fresh"v" in
                             let l := fresh"l" in 
                             destruct (p m) as [v l]; 
                             destruct l ; 
                             destruct v ;
                             simpl   *)                                 
       | context [let (x, t) := ?f in @?g x t] => idtac "let..." f g; 
                                                 replace (let (x, t) := f in g x t) with (g (fst f) (snd f)) 
                                                          by (symmetry; apply fstsndImplies) ;
                                                 destruct (snd f);          
                                                 simpl                                                                  
      | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
      end

 
  end) . 

Qed.

(* Lemma addOrdinaryStake_eval: forall (Л_stake: Z) (l: Ledger), 
eval_state (DePoolContract_Ф_addOrdinaryStake' Л_stake) l = 

let sender := eval_state msg_sender l in 
let isExtMsg : bool := negb (sender =? 0) in 
let isPoolClosed : bool := eval_state (↑12 ε DePoolContract_ι_m_poolClosed) l in 
let minStake := eval_state (↑12 ε DePoolContract_ι_m_minStake) l in 
let STAKE_FEE := eval_state (↑12 ε DePoolContract_ι_STAKE_FEE) l in
let msg_value := eval_state msg_value l in 
let feeSmall := msg_value <? Л_stake + STAKE_FEE in
let stakeSmall := Л_stake <? minStake in
if isExtMsg then 
 if isPoolClosed then Value (Error I) 
 else if feeSmall then Value (Error I)
 else if stakeSmall then Value (Error I)
 else Value (Value I)
else Error (eval_state (↑ε7 Errors_ι_IS_EXT_MSG) l).
Proof.
  intros.
  destruct l. 
  destruct Ledger_ι_DebugDePool, Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ConfigParamsBase, Ledger_ι_ParticipantBase, 
  Ledger_ι_DePoolHelper, Ledger_ι_Errors, Ledger_ι_InternalErrors, Ledger_ι_DePoolLib, Ledger_ι_DePoolProxyContract, 
  Ledger_ι_RoundsBase, Ledger_ι_DePoolContract, Ledger_ι_DePool, Ledger_ι_Participant, Ledger_ι_TestElector, 
  Ledger_ι_VMState, Ledger_ι_LocalState.

  compute. idtac.


  Time  repeat (
  
  time match goal with

    | |- ?x =>
      match x with
       
     
      | context [if ?b then _ else _] =>  idtac "if..." b; 
                                          repeat rewrite ifSimpleState ; 
                                          repeat rewrite ifFunApply ;
                                            (* compute ; *)
                                            (* let rem := fresh "rem" in  *)
                                            (* set (rem:= b) ;  *)
                                          case b ; 
                                          simpl(* ; intros *)    
        | context  [match RoundsBase_Ф__addStakes ?a ?b ?c ?d ?e ?f
                  with
                  | SimpleState s => s
                  end ?m] => idtac "found RoundsBase_Ф__addStakes ..."  a b c d e f; 
                             let p := fresh"p" in
                             destruct (RoundsBase_Ф__addStakes a b c d e f) as (p);
                             let v := fresh"v" in
                             let l := fresh"l" in 
                             destruct (p m) as [v l]; 
                             destruct l ; 
                             destruct v ;
                             simpl                                   
       | context [let (x, t) := ?f in @?g x t] => idtac "let..." f g; 
                                                 replace (let (x, t) := f in g x t) with (g (fst f) (snd f)) 
                                                          by (symmetry; apply fstsndImplies) ;
                                                 destruct (snd f);          
                                                 simpl                                                                  
      | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
      end

 
  end) . 

  all: pr_numgoals.

  
Qed. 
 *)


  
