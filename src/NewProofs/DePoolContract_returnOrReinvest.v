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
Module DePoolContract_Ф__returnOrReinvest (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.

Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair.

Definition DePoolContract_Ф__returnOrReinvest_while (Л_chunkSize Л_round1ValidatorsElectedFor: XInteger) : LedgerT (ErrorValue True XInteger) := 
    ( WhileE ( ( ↑17 D2! LocalState_ι__returnOrReinvest_Л_startIndex ?< $ Л_chunkSize ) !& 
    ( !¬ ( ( ↑17 D2! LocalState_ι__returnOrReinvest_Л_round2 ^^ RoundsBase_ι_Round_ι_stakes) ->empty ) ) ) 
 do 
 ( 
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
     fun r => return! (xProdSnd r).
 

Definition DePoolContract_Ф__returnOrReinvest_tailer ( Л_chunkSize Л_round1ValidatorsElectedFor: XInteger) : LedgerT (XErrorValue RoundsBase_ι_Round XInteger ) :=
    do _ ← DePoolContract_Ф__returnOrReinvest_while Л_chunkSize Л_round1ValidatorsElectedFor ?; 
    ( RoundsBase_Ф_setRound0 (! ↑17 D2! LocalState_ι__returnOrReinvest_Л_round0 !) ) >> 
( If ( ( ↑17 D2! LocalState_ι__returnOrReinvest_Л_round2 ^^ RoundsBase_ι_Round_ι_stakes ) ->empty ) 
then 
{ 
   (↑17 U1! LocalState_ι__returnOrReinvest_Л_round2 ^^ RoundsBase_ι_Round_ι_step := 
                      ξ$ RoundsBase_ι_RoundStepP_ι_Completed ) >> 

    this->sendMessage ( $ DePoolContract_Ф_ticktockF ) with {|| messageValue ::= $ DePool_ι_VALUE_FOR_SELF_CALL , 
                                       messageBounce ::= $ xBoolFalse||}  
   } ) >> 
return!! ( ↑17 D2! LocalState_ι__returnOrReinvest_Л_round2 ) .



Definition DePoolContract_Ф__returnOrReinvest_header ( Л_round2 : RoundsBase_ι_Round ) ( Л_chunkSize : XInteger8 ) : LedgerT ( XErrorValue RoundsBase_ι_Round XInteger ) :=    

( declareInit LocalState_ι__returnOrReinvest_Л_round2   := $ Л_round2 ) >> 
tvm_accept () >> 
( declareGlobal! LocalState_ι__returnOrReinvest_Л_round0 :>: RoundsBase_ι_Round := RoundsBase_Ф_getRound0 () ) >> 
 U0! Л_round := ( RoundsBase_Ф_getRound1 () ) ; 
 declareLocal Л_round1ValidatorsElectedFor :>: XInteger32 :=  $ Л_round ->> RoundsBase_ι_Round_ι_validatorsElectedFor ; 
( declareGlobal! LocalState_ι__returnOrReinvest_Л_startIndex :>: XInteger := $ xInt0 ) >> 
If!! ( !¬ ( ↑17 D1! ( D2! LocalState_ι__returnOrReinvest_Л_round2 ) ^^ 
            RoundsBase_ι_Round_ι_isValidatorStakeCompleted ) ) 
then 
{ 
  ( ↑17 U1! LocalState_ι__returnOrReinvest_Л_round2 ^^ 
        RoundsBase_ι_Round_ι_isValidatorStakeCompleted := $ xBoolTrue ) >> 
  declareLocal Л_optStake :>: (XMaybe RoundsBase_ι_StakeValue) := (D1! (↑17 D2! LocalState_ι__returnOrReinvest_Л_round2 ^^ 
                                                                           RoundsBase_ι_Round_ι_stakes) 
         ->fetch ( ↑2 D2! ValidatorBase_ι_m_validatorWallet ) ) ; 
   If! ( ( $ Л_optStake ) ->hasValue ) 
   then  
   { 
    declareLocal Л_stake :>: RoundsBase_ι_StakeValue := ( $ Л_optStake ) ->get ; 
    ( ↑17 U1! LocalState_ι__returnOrReinvest_Л_startIndex := $ xInt1 ) >> 
    ( ↑↑17 U2! delete LocalState_ι__returnOrReinvest_Л_round2 ^^ 
             RoundsBase_ι_Round_ι_stakes [[ ↑2 D2! ValidatorBase_ι_m_validatorWallet ]] ) >> 
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
} ;  DePoolContract_Ф__returnOrReinvest_tailer Л_chunkSize Л_round1ValidatorsElectedFor .

Lemma DePoolContract_Ф__returnOrReinvest_eq: 
DePoolContract_Ф__returnOrReinvest = DePoolContract_Ф__returnOrReinvest_header.
Proof.
    unfold DePoolContract_Ф__returnOrReinvest.
    unfold DePoolContract_Ф__returnOrReinvest_header.
    unfold DePoolContract_Ф__returnOrReinvest_while.
    auto.
Qed.


Opaque DePoolContract_Ф__returnOrReinvest_while DePoolContract_Ф__returnOrReinvestForParticipant DePoolContract_Ф__returnOrReinvest_tailer.

Lemma DePoolContract_Ф__returnOrReinvest_header_exec : forall (Л_round2 : RoundsBase_ι_Round ) ( chunkSize : XInteger8 ) 
                                                        (l: Ledger) , 
let round2 := Л_round2 in                                  
let la := exec_state tvm_accept l in
let round0 := eval_state (↓ RoundsBase_Ф_getRound0) la in
let round1 := eval_state (↓ RoundsBase_Ф_getRound1) la in
let round1ValidatorsElectedFor := round1 ->> RoundsBase_ι_Round_ι_validatorsElectedFor in
let if1 := negb (round2 ->> RoundsBase_ι_Round_ι_isValidatorStakeCompleted) in
let m_validatorWallet := eval_state (↑2 ε ValidatorBase_ι_m_validatorWallet) la in
let stakes :=  round2 ->> RoundsBase_ι_Round_ι_stakes in
let optStake := stakes ->fetch m_validatorWallet in
let if2 := isSome optStake in
let stake := maybeGet optStake in 
let startIndex := if if1 then if if2 then 1 else 0 else 0 in
let stakes := if if1 then if if2 then stakes ->delete m_validatorWallet else stakes else stakes in
let round2 := if if1 then if if2 then 
            {$round2 with (RoundsBase_ι_Round_ι_isValidatorStakeCompleted, true);
                          (RoundsBase_ι_Round_ι_stakes, stakes) $} else 
            {$round2 with (RoundsBase_ι_Round_ι_isValidatorStakeCompleted, true) $} else
            round2 in                                     
let newl := {$la With (LocalState_ι__returnOrReinvest_Л_round2, round2);
                      (LocalState_ι__returnOrReinvest_Л_round0, round0);
                      (LocalState_ι__returnOrReinvest_Л_startIndex, startIndex)  $} in
                      
let (erounds, newl) := if if1 then 
                            if if2 then 
                            run (↓ DePoolContract_Ф__returnOrReinvestForParticipant round2 round0 m_validatorWallet stake true round1ValidatorsElectedFor) newl
                            else (Value (round0, round2), newl)
                      else (Value (round0, round2), newl) in 
let ml1 := newl in                      
let bRounds := errorValueIsValue erounds in                      
let (round0, round2)  := errorMapDefault Datatypes.id erounds (round0, round2) in                     
let newl := {$newl With (LocalState_ι__returnOrReinvest_Л_round2, round2);
                        (LocalState_ι__returnOrReinvest_Л_round0, round0) $} in 
let (eWhile, newl) := run (DePoolContract_Ф__returnOrReinvest_tailer chunkSize round1ValidatorsElectedFor) newl   in
let bl := exec_state (DePoolContract_Ф__returnOrReinvest_tailer chunkSize round1ValidatorsElectedFor) {$la With (LocalState_ι__returnOrReinvest_Л_startIndex, 0);
                                (LocalState_ι__returnOrReinvest_Л_round2, round2);
                                (LocalState_ι__returnOrReinvest_Л_round0, round0)  $} in
exec_state (DePoolContract_Ф__returnOrReinvest_header Л_round2 chunkSize) l =
if if1 then 
    if if2 then 
        if bRounds then newl 
        else ml1
    else bl      
else bl .
Proof.

    intros.
    destructLedger l. 
    compute. idtac.
  
    Time repeat destructIf_solve2. idtac.
    all: try destructFunction6 DePoolContract_Ф__returnOrReinvestForParticipant; auto. idtac. 
    all: try case_eq x; intros; auto. idtac.
    destructFunction2 DePoolContract_Ф__returnOrReinvest_tailer; auto. idtac. 
    case_eq x0; intros; auto. idtac.
    destructFunction2 DePoolContract_Ф__returnOrReinvest_tailer; auto. idtac. 
    destructFunction2 DePoolContract_Ф__returnOrReinvest_tailer; auto. idtac. 
    destructFunction2 DePoolContract_Ф__returnOrReinvest_tailer; auto. 

Qed.


Lemma DePoolContract_Ф__returnOrReinvest_header_eval : forall (Л_round2 : RoundsBase_ι_Round ) ( chunkSize : XInteger8 ) 
                                                        (l: Ledger) , 
let round2 := Л_round2 in                                  
let la := exec_state tvm_accept l in
let round0 := eval_state (↓ RoundsBase_Ф_getRound0) la in
let round1 := eval_state (↓ RoundsBase_Ф_getRound1) la in
let round1ValidatorsElectedFor := round1 ->> RoundsBase_ι_Round_ι_validatorsElectedFor in
let if1 := negb (round2 ->> RoundsBase_ι_Round_ι_isValidatorStakeCompleted) in
let m_validatorWallet := eval_state (↑2 ε ValidatorBase_ι_m_validatorWallet) la in
let stakes :=  round2 ->> RoundsBase_ι_Round_ι_stakes in
let optStake := stakes ->fetch m_validatorWallet in
let if2 := isSome optStake in
let stake := maybeGet optStake in 
let startIndex := if if1 then if if2 then 1 else 0 else 0 in
let stakes := if if1 then if if2 then stakes ->delete m_validatorWallet else stakes else stakes in
let round2 := if if1 then if if2 then 
            {$round2 with (RoundsBase_ι_Round_ι_isValidatorStakeCompleted, true);
                          (RoundsBase_ι_Round_ι_stakes, stakes) $} else 
            {$round2 with (RoundsBase_ι_Round_ι_isValidatorStakeCompleted, true) $} else
            round2 in                                     
let newl := {$la With (LocalState_ι__returnOrReinvest_Л_round2, round2);
                      (LocalState_ι__returnOrReinvest_Л_round0, round0);
                      (LocalState_ι__returnOrReinvest_Л_startIndex, startIndex)  $} in
                      
let (erounds, newl) := if if1 then 
                            if if2 then 
                            run (↓ DePoolContract_Ф__returnOrReinvestForParticipant round2 round0 m_validatorWallet stake true round1ValidatorsElectedFor) newl
                            else (Value (round0, round2), newl)
                      else (Value (round0, round2), newl) in 
let ml1 := newl in                      
let bRounds := errorValueIsValue erounds in                      
let (round0, round2)  := errorMapDefault Datatypes.id erounds (round0, round2) in                     
let newl := {$newl With (LocalState_ι__returnOrReinvest_Л_round2, round2);
                        (LocalState_ι__returnOrReinvest_Л_round0, round0) $} in 
let (eWhile, newl) := run (DePoolContract_Ф__returnOrReinvest_tailer chunkSize round1ValidatorsElectedFor) newl   in
let br := eval_state (DePoolContract_Ф__returnOrReinvest_tailer chunkSize round1ValidatorsElectedFor) {$la With (LocalState_ι__returnOrReinvest_Л_startIndex, 0);
                                (LocalState_ι__returnOrReinvest_Л_round2, round2);
                                (LocalState_ι__returnOrReinvest_Л_round0, round0)  $} in

eval_state (DePoolContract_Ф__returnOrReinvest_header Л_round2 chunkSize) l =
if if1 then 
    if if2 then 
        if bRounds then eWhile 
        else errorMapDefaultF (fun _ => Value default) erounds (fun e => Error e)
    else br   
else br .
Proof.

    intros.
    destructLedger l. 
    compute. idtac.
  
    Time repeat destructIf_solve2. idtac.
    all: try destructFunction6 DePoolContract_Ф__returnOrReinvestForParticipant; auto. idtac. 
    all: try case_eq x; intros; auto. idtac.
    destructFunction2 DePoolContract_Ф__returnOrReinvest_tailer; auto. idtac. 
    case_eq x0; intros; auto. idtac.
    destructFunction2 DePoolContract_Ф__returnOrReinvest_tailer; auto. idtac. 
    destructFunction2 DePoolContract_Ф__returnOrReinvest_tailer; auto. idtac. 
    destructFunction2 DePoolContract_Ф__returnOrReinvest_tailer; auto. 

Qed.

Transparent DePoolContract_Ф__returnOrReinvest_tailer.

Lemma DePoolContract_Ф__returnOrReinvest_tailer_exec : forall (chunkSize round1ValidatorsElectedFor : XInteger8 ) 
                                                        (l: Ledger) ,
let (eWhile, newl) := run (DePoolContract_Ф__returnOrReinvest_while chunkSize round1ValidatorsElectedFor) l in 
let bWhile := errorValueIsValue eWhile in    
let ml2 := newl in 
let round0 := eval_state (↑17 ε LocalState_ι__returnOrReinvest_Л_round0) newl in
let round2 := eval_state (↑17 ε LocalState_ι__returnOrReinvest_Л_round2) newl in 
let if3 : bool := xHMapIsNull (round2 ->> RoundsBase_ι_Round_ι_stakes)  in 

let newl := exec_state (↓ RoundsBase_Ф_setRound0 round0) newl in 
let round2 := if if3 then {$ round2 with (RoundsBase_ι_Round_ι_step, RoundsBase_ι_RoundStepP_ι_Completed) $}
                     else round2 in 

let oldMessages := VMState_ι_messages ( Ledger_ι_VMState newl ) in
let newMessage  := {| contractAddress :=  0 ;
                      contractFunction := DePoolContract_Ф_ticktockF  ;
                      contractMessage := {| messageValue :=  DePool_ι_VALUE_FOR_SELF_CALL ;
                                            messageFlag  := 0 ; 
                                            messageBounce := false
                                            |} |} in  
let newl := if if3 then {$newl With (LocalState_ι__returnOrReinvest_Л_round2, round2);
                                    (VMState_ι_messages, newMessage :: oldMessages) $} else newl in                                                  
exec_state (DePoolContract_Ф__returnOrReinvest_tailer chunkSize round1ValidatorsElectedFor) l = 
if bWhile then newl
else ml2.
Proof.       
    
    intros.
    destructLedger l. 
    compute. idtac.
  
    Time repeat destructIf_solve2. idtac.
    destructFunction2 DePoolContract_Ф__returnOrReinvest_while; auto. idtac. 
    case_eq x; intros; auto. idtac.
    Time repeat destructIf_solve2. 
   
Qed.    

Lemma DePoolContract_Ф__returnOrReinvest_tailer_eval : forall (chunkSize round1ValidatorsElectedFor : XInteger8 ) 
                                                        (l: Ledger) ,
let (eWhile, newl) := run (DePoolContract_Ф__returnOrReinvest_while chunkSize round1ValidatorsElectedFor) l in 
let bWhile := errorValueIsValue eWhile in    
let ml2 := newl in 
let round0 := eval_state (↑17 ε LocalState_ι__returnOrReinvest_Л_round0) newl in
let round2 := eval_state (↑17 ε LocalState_ι__returnOrReinvest_Л_round2) newl in 
let if3 : bool := xHMapIsNull (round2 ->> RoundsBase_ι_Round_ι_stakes)  in 

let newl := exec_state (↓ RoundsBase_Ф_setRound0 round0) newl in 
let round2 := if if3 then {$ round2 with (RoundsBase_ι_Round_ι_step, RoundsBase_ι_RoundStepP_ι_Completed) $}
                     else round2 in 

let oldMessages := VMState_ι_messages ( Ledger_ι_VMState newl ) in
let newMessage  := {| contractAddress :=  0 ;
                      contractFunction := DePoolContract_Ф_ticktockF  ;
                      contractMessage := {| messageValue :=  DePool_ι_VALUE_FOR_SELF_CALL ;
                                            messageFlag  := 0 ; 
                                            messageBounce := false
                                            |} |} in  
let newl := if if3 then {$newl With (LocalState_ι__returnOrReinvest_Л_round2, round2);
                                    (VMState_ι_messages, newMessage :: oldMessages) $} else newl in                                                  
eval_state (DePoolContract_Ф__returnOrReinvest_tailer chunkSize round1ValidatorsElectedFor) l = 
if bWhile then Value round2
else errorMapDefaultF (fun _ => Value default) eWhile (fun e => Error e).
Proof.       
    
    intros.
    destructLedger l. 
    compute. idtac.
  
    Time repeat destructIf_solve2. idtac.
    destructFunction2 DePoolContract_Ф__returnOrReinvest_while; auto. idtac. 
    case_eq x; intros; auto. idtac.
    Time repeat destructIf_solve2. 
   
Qed.    


End DePoolContract_Ф__returnOrReinvest.