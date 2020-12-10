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
Module DePoolContract_Ф_completeRoundWithChunk (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.


Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair.
Opaque DePoolFuncs.DePoolContract_Ф__returnOrReinvest DePoolContract_Ф__returnOrReinvest DePoolContract_Ф_checkPureDePoolBalance.

Lemma DePoolContract_Ф_completeRoundWithChunk_eval : forall ( Л_roundId : XInteger64 ) ( Л_chunkSize : XInteger8 ) (l: Ledger) , 
let req : bool :=  eval_state msg_sender l =? eval_state tvm_address l in
let la := exec_state (↓ tvm_accept) l in
let if1 : bool :=  negb ( ( eval_state ( ↓ RoundsBase_Ф_isRound2 Л_roundId ) l )   || 
                          ( eval_state ( ↑12 ε DePoolContract_ι_m_poolClosed ) l ) )%bool  in
let (ifb, lb) :=  run (↓ DePoolContract_Ф_checkPureDePoolBalance ) la in                         
let optRound := eval_state ( RoundsBase_Ф_fetchRound Л_roundId ) lb in
let req1 : bool := isSome optRound  in
let round := maybeGet optRound in
let if2 : bool := negb ( eqb ( round ->> RoundsBase_ι_Round_ι_step ) RoundsBase_ι_RoundStepP_ι_Completing ) in
let round' := eval_state ( ↓ DePoolContract_Ф__returnOrReinvest round Л_chunkSize ) lb  in 

eval_state ( ↓ DePoolContract_Ф_completeRoundWithChunk Л_roundId Л_chunkSize ) l =        
if req then 
   if if1 then Value ( Error I )
      else if (negb ifb) then Value ( Error I )
          else if req1 then 
                if if2 then Value ( Error I ) else match round' with
                                                   | Value _ => Value (Value I)
                                                   | Error x => Error x
                                                   end   
                else Error InternalErrors_ι_ERROR519
    else Error Errors_ι_IS_NOT_DEPOOL .           
Proof. 

  intros.
  destructLedger l. 
  compute.

  Time repeat destructIf_solve. idtac.

  all: try destructFunction0 DePoolContract_Ф_checkPureDePoolBalance; auto. idtac.
  all: time repeat destructIf_solve. idtac.
  all: try destructFunction1 DePoolContract_Ф__returnOrReinvest; auto. idtac.
  all: try destruct x0; auto. idtac.
  all: time repeat destructIf_solve. 
Qed. 


Lemma DePoolContract_Ф_completeRoundWithChunk_exec : forall ( Л_roundId : XInteger64 ) 
                                                            ( Л_chunkSize : XInteger8 ) 
                                                            (l: Ledger) , 
let req : bool :=  eval_state msg_sender l =? eval_state tvm_address l in
let la := exec_state (↓ tvm_accept) l in
let if1 : bool :=  negb ( ( eval_state ( ↓ RoundsBase_Ф_isRound2 Л_roundId ) l )   || 
                          ( eval_state ( ↑12 ε DePoolContract_ι_m_poolClosed ) l ) )%bool  in
let (ifb, lb) :=  run (↓ DePoolContract_Ф_checkPureDePoolBalance ) la in                         
let optRound := eval_state ( RoundsBase_Ф_fetchRound Л_roundId ) lb in
let req1 : bool := isSome optRound  in
let round := maybeGet optRound in
let if2 : bool := negb ( eqb ( round ->> RoundsBase_ι_Round_ι_step ) RoundsBase_ι_RoundStepP_ι_Completing ) in
let (round', l__returnOrReinvest) := run ( ↓ DePoolContract_Ф__returnOrReinvest round Л_chunkSize ) lb  in 

let oldMessages := VMState_ι_messages ( Ledger_ι_VMState l__returnOrReinvest ) in
let newMessage1  := {|  contractAddress :=  0 ;
                        contractFunction := DePoolContract_Ф_completeRoundWithChunkF Л_roundId
                          ( if ( (2 * Л_chunkSize) <? DePool_ι_MAX_MSGS_PER_TR )
                            then (2 * Л_chunkSize)
                            else Л_chunkSize ) ;
                            contractMessage := {| messageValue := default ;
                                                  messageFlag  := 1 ; 
                                                  messageBounce := false
                                                  |} |} in
let newMessage2  := {| contractAddress :=  0 ;
                       contractFunction := DePoolContract_Ф_completeRoundWithChunkF Л_roundId Л_chunkSize  ;
                       contractMessage := {| messageValue := default ;
                                             messageFlag  := 1 ; 
                                             messageBounce := false
                                                  |} |} in
let l' :=  {$ l__returnOrReinvest With ( VMState_ι_messages , newMessage2 :: newMessage1 :: oldMessages ) $}  in                                               

exec_state ( ↓ DePoolContract_Ф_completeRoundWithChunk Л_roundId Л_chunkSize ) l =      

if req then 
   if if1 then la
      else if (negb ifb) then lb
          else if req1 then 
                if if2 then lb else match round' with
                                    | Value round'' =>         (* if (chunkSize < MAX_MSGS_PER_TR && !round.stakes.empty()) { *)
                                   let if3 : bool := ( ( Л_chunkSize <? DePool_ι_MAX_MSGS_PER_TR ) && 
                                                       ( negb ( xHMapIsNull (round'' ->> RoundsBase_ι_Round_ι_stakes) ) ) )%bool in

                                   if if3 then exec_state ( ↓ RoundsBase_Ф_setRound Л_roundId round'' ) l'
                                          else exec_state ( ↓ RoundsBase_Ф_setRound Л_roundId round'' ) l__returnOrReinvest                    
                                   | Error x => l__returnOrReinvest
                                    end   
                else lb
    else l . 

Proof.

  intros.
  destructLedger l. 
  compute.

  Time repeat destructIf_solve. idtac.

  all: try destructFunction0 DePoolContract_Ф_checkPureDePoolBalance; auto. idtac.
(*   all: time repeat destructIf_solve. idtac. *)
  all: try destructFunction2 DePoolContract_Ф__returnOrReinvest; auto. idtac.
  all: time repeat destructIf_solve. idtac.
  all: try rewrite <- Heqm0. idtac.
  all: try rewrite <- Heqr0. idtac.
  all: try destruct x0; auto. idtac.
  all: time repeat destructIf_solve. 
  
Qed.

End DePoolContract_Ф_completeRoundWithChunk.