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
Module DePoolContract_Ф_onSuccessToRecoverStake (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.

Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair.

Opaque DePoolContract_Ф_startRoundCompleting DePoolContract_Ф_acceptRewardAndStartRoundCompleting.

Lemma DePoolContract_Ф_onSuccessToRecoverStake_exec : forall  ( Л_queryId : XInteger64 ) 
                                                              ( Л_elector : XAddress ) 
                                                              ( l: Ledger ) ,  
let optRound := eval_state ( ↓ ( RoundsBase_Ф_fetchRound Л_queryId ) ) l in
let req1 : bool := isSome optRound in  
let round := maybeGet optRound in
let req2 : bool := eval_state msg_sender l =?  round ->> RoundsBase_ι_Round_ι_proxy  in
let req3 : bool := Л_elector =? round ->> RoundsBase_ι_Round_ι_elector in
let value := ( eval_state msg_value l) + DePoolLib_ι_PROXY_FEE in
let if1 : bool := eqb (round ->> RoundsBase_ι_Round_ι_step) RoundsBase_ι_RoundStepP_ι_WaitingIfValidatorWinElections in
let if2 : bool := value <? round ->> RoundsBase_ι_Round_ι_stake in
let if3 : bool := eqb ( round ->> RoundsBase_ι_Round_ι_step ) RoundsBase_ι_RoundStepP_ι_WaitingReward in
let if4 : bool := value >=? ( ( round ->> RoundsBase_ι_Round_ι_stake ) - ( round ->> RoundsBase_ι_Round_ι_unused ) ) in
let la :=  exec_state (↓ tvm_accept) l in                                                           

let (round', l') := if if1 then 
                        if if2 then ({$ round with ( RoundsBase_ι_Round_ι_step , RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze ) ;
                                                   ( RoundsBase_ι_Round_ι_unused , value ) $}, la) else
                        ({$ round with ( RoundsBase_ι_Round_ι_step , RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze ) ;
                                       ( RoundsBase_ι_Round_ι_completionReason , RoundsBase_ι_CompletionReasonP_ι_ElectionsAreLost ) $}, la)
                           else if if3 then 
                                        let r' := {$ round with ( RoundsBase_ι_Round_ι_recoveredStake , value ) $} in
                                        if if4 then  
                                             run ( ↓ ( DePoolContract_Ф_acceptRewardAndStartRoundCompleting r'  value ) ) la 
                                               else 
                                             run ( ↓ ( DePoolContract_Ф_startRoundCompleting r' RoundsBase_ι_CompletionReasonP_ι_ValidatorIsPunished ) ) la
                           else (round, injEmbed (VMState_ι_savedDePoolContracts (Ledger_ι_VMState l)) la) in 

exec_state ( ↓ DePoolContract_Ф_onSuccessToRecoverStake Л_queryId Л_elector ) l =
if req1 then 
        if req2 then 
                if req3 then 
                        if if1 then 
                                if if2 then exec_state ( ↓ ( RoundsBase_Ф_setRound Л_queryId round' ) ) l' 
                                       else exec_state ( ↓ ( RoundsBase_Ф_setRound Л_queryId round' ) ) l' 
                               else
                        if if3 then 
                                if if4 then exec_state ( ↓ ( RoundsBase_Ф_setRound Л_queryId round' ) ) l' 
                                       else exec_state ( ↓ ( RoundsBase_Ф_setRound Л_queryId round' ) ) l'
                                else l'
                         else l
                else l
        else l. 
 Proof. 

        intros.
        destructLedger l. 
        compute.
      
        Time repeat destructIf_solve. idtac.
        all: try rewrite H0 in H4; try discriminate. idtac.
        all: try destructFunction2 DePoolContract_Ф_acceptRewardAndStartRoundCompleting; auto. idtac.
        all: try rewrite H1 in H5; try discriminate. idtac.
        all: try destructFunction2 DePoolContract_Ф_startRoundCompleting; auto. 
Qed. 


Lemma DePoolContract_Ф_onSuccessToRecoverStake_eval : forall ( Л_queryId : XInteger64 ) 
                                                              ( Л_elector : XAddress ) 
                                                              (l: Ledger) , 
let optRound := eval_state ( ↓ ( RoundsBase_Ф_fetchRound Л_queryId ) ) l in
let req1 : bool := isSome optRound in  
let round := maybeGet optRound in
let req2 : bool := eval_state msg_sender l =?  round ->> RoundsBase_ι_Round_ι_proxy  in
let req3 : bool := Л_elector =? round ->> RoundsBase_ι_Round_ι_elector in
let la :=  exec_state (↓ tvm_accept) l in         
let value := ( eval_state msg_value l) + DePoolLib_ι_PROXY_FEE in
let if1 : bool := eqb (round ->> RoundsBase_ι_Round_ι_step) RoundsBase_ι_RoundStepP_ι_WaitingIfValidatorWinElections in
let if2 : bool := value <? round ->> RoundsBase_ι_Round_ι_stake in
let if3 : bool := eqb ( round ->> RoundsBase_ι_Round_ι_step ) RoundsBase_ι_RoundStepP_ι_WaitingReward in
let if4 : bool := value >=? ( ( round ->> RoundsBase_ι_Round_ι_stake ) - 
                                                           ( round ->> RoundsBase_ι_Round_ι_unused ) ) in
eval_state ( ↓ DePoolContract_Ф_onSuccessToRecoverStake Л_queryId Л_elector ) l = 

if req1 then 
        if req2 then 
                if req3 then 
                        if if1 then 
                                if if2 then Value I 
                                       else Value I 
                               else
                        if if3 then 
                                if if4 then Value I 
                                       else Value I 
                                else Error InternalErrors_ι_ERROR521
                         else Error Errors_ι_IS_NOT_ELECTOR
                else Error Errors_ι_IS_NOT_PROXY
        else Error InternalErrors_ι_ERROR513 . 
                                                             
 Proof. 
        intros.
        destructLedger l. 
        compute.
      
        Time repeat destructIf_solve. idtac.
        all: try destructFunction2 DePoolContract_Ф_acceptRewardAndStartRoundCompleting; auto. idtac.
        all: try destructFunction2 DePoolContract_Ф_startRoundCompleting; auto. 
        
 Qed.    
 
 End DePoolContract_Ф_onSuccessToRecoverStake.