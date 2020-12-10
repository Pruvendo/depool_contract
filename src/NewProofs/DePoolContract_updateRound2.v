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
Module DePoolContract_Ф_updateRound2 (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.



Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo.
Opaque DePoolContract_Ф_startRoundCompleting ProxyBase_Ф__recoverStake.

Lemma DePoolContract_Ф_updateRound2_exec : forall ( Л_round2 : RoundsBase_ι_Round ) 
                                                  ( Л_prevValidatorHash : XInteger256 ) 
                                                  ( Л_curValidatorHash : XInteger256 ) 
                                                  ( Л_validationStart : XInteger32 )                                                  
                                                  (l: Ledger) ,                                                    
let round2 := Л_round2 in
let if1 : bool  :=  eqb ( round2 ->> RoundsBase_ι_Round_ι_step )  RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest in
let if2 : bool  :=  eqb ( round2 ->> RoundsBase_ι_Round_ι_completionReason )  RoundsBase_ι_CompletionReasonP_ι_Undefined in
let if3 : bool  :=  eqb (round2 ->> RoundsBase_ι_Round_ι_step )  RoundsBase_ι_RoundStepP_ι_Completing in 
let round2 := if if1 then 
                      if if2 then {$ round2 with (RoundsBase_ι_Round_ι_step, RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze);
                                                 (RoundsBase_ι_Round_ι_completionReason, RoundsBase_ι_CompletionReasonP_ι_NoValidatorRequest);
                                                 (RoundsBase_ι_Round_ι_unfreeze, 0) $}
                             else {$ round2 with (RoundsBase_ι_Round_ι_step, RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze);
                                                 (RoundsBase_ι_Round_ι_unfreeze, 0) $} 
                      else round2 in                     
let oldMessages := VMState_ι_messages ( Ledger_ι_VMState l ) in
let oldEvents := VMState_ι_events ( Ledger_ι_VMState l ) in
let newMessage  := {|  contractAddress :=  0 ;
                        contractFunction := DePoolContract_Ф_completeRoundWithChunkF round2->>RoundsBase_ι_Round_ι_id 1 ;
                        contractMessage := {| messageValue := 0 ;
                                              messageFlag  := 0 ; 
                                              messageBounce := false
                                                  |} |} in                      
let l' :=   if if1 then l
                   else if if3 then {$ l With (VMState_ι_messages, newMessage :: oldMessages ) $}
                               else l   
                      in                                             
let if4 : bool :=  ( ( negb ( eqb ( round2 ->> RoundsBase_ι_Round_ι_vsetHashInElectionPhase ) Л_curValidatorHash ) )  && 
                     ( negb ( eqb ( round2 ->> RoundsBase_ι_Round_ι_vsetHashInElectionPhase ) Л_prevValidatorHash ) )  && 
                     (  eqb (round2 ->> RoundsBase_ι_Round_ι_unfreeze) DePoolLib_ι_MAX_TIME ) )%bool   in
let round2 := if if4 then {$ round2 with (RoundsBase_ι_Round_ι_unfreeze, Л_validationStart + round2->>RoundsBase_ι_Round_ι_stakeHeldFor) $} 
                       else round2 in 
let if5 : bool  := ( eval_state tvm_now  l ) >=? ( (round2 ->> RoundsBase_ι_Round_ι_unfreeze) + 
                                                   DePoolLib_ι_ELECTOR_UNFREEZE_LAG ) in 
let if6 : bool := (( eqb (round2 ->> RoundsBase_ι_Round_ι_step) RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze ) &&
                     negb ( eqb (round2 ->> RoundsBase_ι_Round_ι_completionReason) RoundsBase_ι_CompletionReasonP_ι_Undefined ))%bool in
(* let if7 : bool := ( round2 ->> RoundsBase_ι_Round_ι_participantQty ) =? 0  in *)
let if8 : bool :=  ( ( eqb (round2 ->> RoundsBase_ι_Round_ι_step) RoundsBase_ι_RoundStepP_ι_WaitingValidationStart ) ||
                     ( eqb (round2 ->> RoundsBase_ι_Round_ι_step) RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze ))%bool in  
(* let round2' := if if5 then 
                            if if6 then 
                                   eval_state ( ↓ DePoolContract_Ф_startRoundCompleting round2 round2 ->> RoundsBase_ι_Round_ι_completionReason) l'
                                    else if if8 then {$ round2 with (RoundsBase_ι_Round_ι_step, RoundsBase_ι_RoundStepP_ι_WaitingReward) $} 
                                                else round2    
                     else round2 in    *)                   
let l'' := if if5 then if if6 then exec_state ( ↓ DePoolContract_Ф_startRoundCompleting round2 round2 ->> RoundsBase_ι_Round_ι_completionReason) l'
                              else if if8 then  exec_state ( ↓ ProxyBase_Ф__recoverStake round2 ->> RoundsBase_ι_Round_ι_proxy 
                                                                                         round2 ->> RoundsBase_ι_Round_ι_id 
                                                                                         round2 ->> RoundsBase_ι_Round_ι_elector ) l' 
                                          else l'     
                     else l' in 

exec_state ( ↓ DePoolContract_Ф_updateRound2 Л_round2 Л_prevValidatorHash Л_curValidatorHash Л_validationStart ) l = l''.

 Proof. 

  intros.

  destructLedger l. 
  destruct Л_round2.
  compute. idtac.

  Time do 3 destructIf_solve. idtac.

  -

  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash); 
  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash); 
  destruct (0 =? DePoolLib_ι_MAX_TIME); 
  try discriminate. idtac.

  time repeat destructIf_solve. idtac.
  destructFunction2 DePoolContract_Ф_startRoundCompleting; auto. 

  - idtac.

  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash); 
  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash); 
  destruct (0 =? DePoolLib_ι_MAX_TIME); 
  try discriminate. idtac.

  all: time repeat destructIf_solve. idtac.
  all: destructFunction2 DePoolContract_Ф_startRoundCompleting; auto. 

  - idtac.  

  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash); 
  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash); 
  destruct (0 =? DePoolLib_ι_MAX_TIME); 
  try discriminate. idtac.

  all: time repeat destructIf_solve. idtac.
  all: destructFunction2 DePoolContract_Ф_startRoundCompleting; auto. 

  - idtac.  

  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash); 
  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash); 
  destruct (0 =? DePoolLib_ι_MAX_TIME); 
  try discriminate. idtac.

  all: time repeat destructIf_solve. idtac.
  all: destructFunction2 DePoolContract_Ф_startRoundCompleting; auto.   

  - idtac.  

  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash); 
  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash); 
  destruct (RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME); 
  try discriminate. idtac.

  all: time repeat destructIf_solve. idtac.
  all: destructFunction2 DePoolContract_Ф_startRoundCompleting; auto.  

  - idtac.  

  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash); 
  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash); 
  destruct (RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME); 
  try discriminate. idtac.

  all: time repeat destructIf_solve. idtac.
  all: destructFunction2 DePoolContract_Ф_startRoundCompleting; auto.    

  - idtac.  

  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash); 
  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash); 
  destruct (RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME); 
  try discriminate. idtac.

  all: time repeat destructIf_solve. idtac.
  all: destructFunction2 DePoolContract_Ф_startRoundCompleting; auto.  

  - idtac.  

  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash); 
  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash); 
  destruct (RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME); 
  try discriminate. idtac.

  all: time repeat destructIf_solve. idtac.
  all: destructFunction2 DePoolContract_Ф_startRoundCompleting; auto.  

Qed. 


  

Lemma DePoolContract_Ф_updateRound2_eval : forall ( Л_round2 : RoundsBase_ι_Round ) 
                                                   ( Л_prevValidatorHash : XInteger256 ) 
                                                   ( Л_curValidatorHash : XInteger256 ) 
                                                   ( Л_validationStart : XInteger32 )                                                  
                                                   (l: Ledger) ,                                                    
let round2 := Л_round2 in
let if1 : bool  :=  eqb ( round2 ->> RoundsBase_ι_Round_ι_step )  RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest in
let if2 : bool  :=  eqb ( round2 ->> RoundsBase_ι_Round_ι_completionReason )  RoundsBase_ι_CompletionReasonP_ι_Undefined in
let if3 : bool  :=  eqb (round2 ->> RoundsBase_ι_Round_ι_step )  RoundsBase_ι_RoundStepP_ι_Completing in 
let round2 := if if1 then 
                      if if2 then {$ round2 with (RoundsBase_ι_Round_ι_step, RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze);
                                                 (RoundsBase_ι_Round_ι_completionReason, RoundsBase_ι_CompletionReasonP_ι_NoValidatorRequest);
                                                 (RoundsBase_ι_Round_ι_unfreeze, 0) $}
                             else {$ round2 with (RoundsBase_ι_Round_ι_step, RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze);
                                                 (RoundsBase_ι_Round_ι_unfreeze, 0) $} 
                      else round2 in                     
let oldMessages := VMState_ι_messages ( Ledger_ι_VMState l ) in
let newMessage  := {|  contractAddress :=  0 ;
                        contractFunction := DePoolContract_Ф_completeRoundWithChunkF round2->>RoundsBase_ι_Round_ι_id 1 ;
                        contractMessage := {| messageValue := 0 ;
                                              messageFlag  := 0 ; 
                                              messageBounce := false
                                                  |} |} in                      
let l' :=   if if1 then l
                   else if if3 then {$ l With (VMState_ι_messages, newMessage :: oldMessages ) $}
                               else l   
                      in                                             

let if4 : bool :=  (( negb ( eqb ( round2 ->> RoundsBase_ι_Round_ι_vsetHashInElectionPhase ) Л_curValidatorHash ) )  && 
                    ( negb ( eqb ( round2 ->> RoundsBase_ι_Round_ι_vsetHashInElectionPhase ) Л_prevValidatorHash ) )  && 
                    ( eqb (round2 ->> RoundsBase_ι_Round_ι_unfreeze) DePoolLib_ι_MAX_TIME  ) )%bool   in
let round2 := if if4 then {$ round2 with (RoundsBase_ι_Round_ι_unfreeze, Л_validationStart + round2->>RoundsBase_ι_Round_ι_stakeHeldFor) $} 
                       else round2 in 
let if5 : bool  := ( eval_state tvm_now  l ) >=? ( (round2 ->> RoundsBase_ι_Round_ι_unfreeze) + 
                                                   DePoolLib_ι_ELECTOR_UNFREEZE_LAG ) in 
let if6 : bool := (( eqb (round2 ->> RoundsBase_ι_Round_ι_step) RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze ) &&
                     negb ( eqb (round2 ->> RoundsBase_ι_Round_ι_completionReason) RoundsBase_ι_CompletionReasonP_ι_Undefined ))%bool in
let if8 : bool :=  ( ( eqb (round2 ->> RoundsBase_ι_Round_ι_step) RoundsBase_ι_RoundStepP_ι_WaitingValidationStart ) ||
                     ( eqb (round2 ->> RoundsBase_ι_Round_ι_step) RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze ))%bool in  
let round2 := if if5 then 
                            if if6 then 
                                   eval_state ( ↓ DePoolContract_Ф_startRoundCompleting round2 round2 ->> RoundsBase_ι_Round_ι_completionReason) l'
                                    else if if8 then {$ round2 with (RoundsBase_ι_Round_ι_step, RoundsBase_ι_RoundStepP_ι_WaitingReward) $} 
                                                else round2
                     else round2 in 

eval_state ( ↓ DePoolContract_Ф_updateRound2 Л_round2 Л_prevValidatorHash Л_curValidatorHash Л_validationStart ) l = round2.

Proof. 

  intros.

  destructLedger l. 
  destruct Л_round2.
  compute. idtac.

  Time do 3 destructIf_solve. idtac.

  - idtac.

  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash); 
  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash); 
  destruct (0 =? DePoolLib_ι_MAX_TIME); 
  try discriminate. idtac.

  time repeat destructIf_solve. idtac.
  destructFunction2 DePoolContract_Ф_startRoundCompleting; auto. 

  - idtac.

  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash); 
  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash); 
  destruct (0 =? DePoolLib_ι_MAX_TIME); 
  try discriminate. idtac.

  all: time repeat destructIf_solve. idtac.
  all: destructFunction2 DePoolContract_Ф_startRoundCompleting; auto. 

  - idtac.  

  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash); 
  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash); 
  destruct (0 =? DePoolLib_ι_MAX_TIME); 
  try discriminate. idtac.

  all: time repeat destructIf_solve. idtac.
  all: destructFunction2 DePoolContract_Ф_startRoundCompleting; auto. 

  - idtac.  

  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash); 
  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash); 
  destruct (0 =? DePoolLib_ι_MAX_TIME); 
  try discriminate. idtac.

  all: time repeat destructIf_solve. idtac.
  all: destructFunction2 DePoolContract_Ф_startRoundCompleting; auto.   

  - idtac.  

  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash); 
  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash); 
  destruct (RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME); 
  try discriminate. idtac.

  all: time repeat destructIf_solve. idtac.
  all: destructFunction2 DePoolContract_Ф_startRoundCompleting; auto.  

  - idtac.  

  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash); 
  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash); 
  destruct (RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME); 
  try discriminate. idtac.

  all: time repeat destructIf_solve. idtac.
  all: destructFunction2 DePoolContract_Ф_startRoundCompleting; auto.    

  - idtac.  

  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash); 
  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash); 
  destruct (RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME); 
  try discriminate. idtac.

  all: time repeat destructIf_solve. idtac.
  all: destructFunction2 DePoolContract_Ф_startRoundCompleting; auto.  

  - idtac.  

  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_curValidatorHash); 
  destruct (RoundsBase_ι_Round_ι_vsetHashInElectionPhase =? Л_prevValidatorHash); 
  destruct (RoundsBase_ι_Round_ι_unfreeze =? DePoolLib_ι_MAX_TIME); 
  try discriminate. idtac.

  all: time repeat destructIf_solve. idtac.
  all: destructFunction2 DePoolContract_Ф_startRoundCompleting; auto.  


 Qed.


End DePoolContract_Ф_updateRound2.