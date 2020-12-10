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

Require Import depoolContract.Lib.CommonStateProofs.

Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope solidity_scope.
Require Import Lists.List.
Import ListNotations.
Local Open Scope list_scope.

Require Import depoolContract.DePoolConsts.
Module DePoolContract_Ф_cutWithdrawalValue (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.



Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair.


Lemma DePoolContract_Ф_cutWithdrawalValue_exec : forall ( Л_p : RoundsBase_ι_InvestParams ) 
                                               ( Л_doPunish : XBool) 
                                               (Л_punishInterval : XInteger32)
                                               (l: Ledger) ,                  
exec_state ( ↓ DePoolContract_Ф_cutWithdrawalValue Л_p Л_doPunish Л_punishInterval ) l = l .
Proof.
  intros.
  destructLedger l. 
  compute.

  repeat destructIf_solve2. 
Qed. 
 
Lemma DePoolContract_Ф_cutWithdrawalValue_eval : forall ( Л_p : RoundsBase_ι_InvestParams ) 
                                               ( Л_doPunish : XBool) 
                                               (Л_punishInterval : XInteger32)
                                               (l: Ledger) ,
let p_lastWithdrawalTime := if ( Л_doPunish ) then  Л_p ->> RoundsBase_ι_InvestParams_ι_lastWithdrawalTime + Л_punishInterval 
                                              else  Л_p ->> RoundsBase_ι_InvestParams_ι_lastWithdrawalTime in
let tonsForOwner := if ( Л_doPunish ) then intMin (intMulDiv Л_punishInterval 
                                                   ( Л_p ->> RoundsBase_ι_InvestParams_ι_withdrawalValue )
                                                   ( Л_p ->> RoundsBase_ι_InvestParams_ι_withdrawalPeriod ))  ( Л_p ->> RoundsBase_ι_InvestParams_ι_remainingAmount )
                                      else 0 in 

let p_remainingAmount := if ( Л_doPunish ) then ( Л_p ->> RoundsBase_ι_InvestParams_ι_remainingAmount ) - tonsForOwner
                                           else ( Л_p ->> RoundsBase_ι_InvestParams_ι_remainingAmount ) in 
                   
let if2 : bool := ( eval_state tvm_now l ) >? p_lastWithdrawalTime in
let periodQty := if if2  
  then ( ( eval_state tvm_now l ) - p_lastWithdrawalTime ) / ( Л_p ->> RoundsBase_ι_InvestParams_ι_withdrawalPeriod ) 
  else default in
let if3 : bool := ( if2 && ( periodQty >? 0 ) )%bool in
                    
let withdrawalTons := if if3  then intMin ( periodQty * ( Л_p ->> RoundsBase_ι_InvestParams_ι_withdrawalValue) )
                                             p_remainingAmount 
                                 else 0 in
let p_remainingAmount := if  if3  then p_remainingAmount - withdrawalTons
                                  else p_remainingAmount in 
let p_lastWithdrawalTime := 
  if  if3  
  then p_lastWithdrawalTime + ( periodQty * ( Л_p ->> RoundsBase_ι_InvestParams_ι_withdrawalPeriod) )
  else p_lastWithdrawalTime in

let if4 : bool := p_remainingAmount <? eval_state ( ↑12 ε DePoolContract_ι_m_minStake ) l in
let withdrawalTons := if if4 then withdrawalTons + p_remainingAmount 
                             else withdrawalTons in
let p_remainingAmount := if if4 then 0 else p_remainingAmount in 

let newp := {$Л_p with (RoundsBase_ι_InvestParams_ι_remainingAmount, p_remainingAmount);
                       (RoundsBase_ι_InvestParams_ι_lastWithdrawalTime, p_lastWithdrawalTime) $} in 

eval_state ( ↓ DePoolContract_Ф_cutWithdrawalValue Л_p Л_doPunish Л_punishInterval) l = (Some newp, withdrawalTons, tonsForOwner) .
Proof.
  intros.
  destructLedger l. 
  destruct Л_p.
  compute.

  repeat destructIf_solve2. 
Qed. 

End DePoolContract_Ф_cutWithdrawalValue.