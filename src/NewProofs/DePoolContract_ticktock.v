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
Module DePoolContract_Ф_ticktock (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.


Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair.

Opaque DePoolContract_Ф_updateRounds 
       DePoolContract_Ф_checkPureDePoolBalance 
       DePoolContract_Ф__returnChange.

Opaque DePoolFuncs.DePoolContract_Ф_updateRounds 
       DePoolFuncs.DePoolContract_Ф_checkPureDePoolBalance 
       DePoolFuncs.DePoolContract_Ф__returnChange.       

Definition DePoolContract_Ф_ticktock' :  LedgerT ( XErrorValue True XInteger ) :=
 Require2 {{ msg_sender () ?!= $xInt0, $ Errors_ι_IS_EXT_MSG }} ;  
 If! (DePoolContract_Ф_checkPureDePoolBalance () ) then 
 { U0! _ ?:= DePoolContract_Ф_updateRounds () ; $I } ;
 (If (msg_sender () ?!= tvm_address () ) then {
    DePoolContract_Ф__returnChange ()
 }).       

Definition DePoolContract_Ф_ticktock_header {X} (f: LedgerT (XErrorValue X XInteger)) 
                                            (g: LedgerT True):  LedgerT ( XErrorValue True XInteger ) :=
 Require2 {{ msg_sender () ?!= $ xInt0, $ Errors_ι_IS_EXT_MSG }} ;  
 If! (DePoolContract_Ф_checkPureDePoolBalance () ) then 
 { U0! _ ?:= f () ; $I } ; g.
 
Definition DePoolContract_Ф_ticktock_tailer: LedgerT True :=
 If (msg_sender () ?!= tvm_address () ) then {
    DePoolContract_Ф__returnChange ()
 }.       


Lemma DePoolContract_Ф_ticktock_tailer_exec : forall (l: Ledger),
let if1 : bool := negb ( eval_state msg_sender l =? eval_state tvm_address l) in

exec_state DePoolContract_Ф_ticktock_tailer l =
if if1 then exec_state (↓ DePoolContract_Ф__returnChange) l else l.
Proof.

intros. 
  
  destructLedger l. 
  compute. idtac.
  repeat destructIf_solve. 
Qed.

Lemma DePoolContract_Ф_ticktock_header_exec : forall X (l: Ledger) (f: LedgerT (XErrorValue X XInteger)) g, 
let req : bool := negb (eval_state msg_sender l =? 0)  in
let (if1, l_checkPureDePoolBalance) := run ( ↓ DePoolContract_Ф_checkPureDePoolBalance ) l in
let (r, l_updateRounds) := run ( ↓ f ) l_checkPureDePoolBalance in
let l' := if if1 then l_updateRounds else l_checkPureDePoolBalance in
exec_state (DePoolContract_Ф_ticktock_header f g ) l = 
if req then 
if if1 then errorMapDefaultF (fun _ =>  exec_state g l') r (fun _ => l')
       else exec_state g l_checkPureDePoolBalance
else l .
Proof. 

  intros. 
  
  destructLedger l. 
  compute. idtac.

  destructFunction0 DePoolContract_Ф_checkPureDePoolBalance; auto. idtac.
  destructFunction0 f; auto. idtac.
  repeat destructIf_solve. idtac.
  all: try rewrite <- Heqr; auto. idtac.
  all: try rewrite H0; auto. idtac.
  all: try rewrite <- Heqr0; auto. idtac.
  all: try rewrite H1; auto. idtac.
  all: try destructFunction0 g; auto. 
 Qed.


Lemma DePoolContract_Ф_ticktock_header_eval : forall X (l: Ledger) (f: LedgerT (XErrorValue X XInteger)) (g: LedgerT True), 
let req : bool := negb (eval_state msg_sender l =? 0)  in
let (if1, l_checkPureDePoolBalance) := run ( ↓ DePoolContract_Ф_checkPureDePoolBalance ) l in
let (r, l_updateRounds) := run ( ↓ f ) l_checkPureDePoolBalance in
let l' := if if1 then l_updateRounds else l_checkPureDePoolBalance in
eval_state (DePoolContract_Ф_ticktock_header f g ) l = 
if req then 
if if1 then errorMapDefaultF (fun _ =>  Value (eval_state g l')) r (fun e => Error e)
       else Value (eval_state g l_checkPureDePoolBalance)
else Error Errors_ι_IS_EXT_MSG .
Proof.
  intros.

  destructLedger l. 
  compute. idtac.

  destructFunction0 DePoolContract_Ф_checkPureDePoolBalance; auto. idtac.
  destructFunction0 f; auto. idtac.

  repeat destructIf_solve. idtac.
  all: try rewrite <- Heqr; auto. idtac.
  all: try rewrite H0; auto. idtac.
  all: try rewrite <- Heqr0; auto. idtac.
  all: try destructFunction0 g; auto. 

  destruct x0; auto. idtac.
  rewrite <- Heqr1.
  auto.
Qed.  

Lemma DePoolContract_Ф_ticktock_tailer_eval : forall (l: Ledger),
let if1 : bool := negb ( eval_state msg_sender l =? eval_state tvm_address l) in

eval_state DePoolContract_Ф_ticktock_tailer l = I.
Proof.
intros.   
  destructLedger l. 
  compute. idtac.
  repeat destructIf_solve. 
Qed.


Lemma DePoolContract_Ф_ticktock'_run_eq: forall (l: Ledger),
run DePoolContract_Ф_ticktock' l = 
run (DePoolContract_Ф_ticktock_header DePoolContract_Ф_updateRounds DePoolContract_Ф_ticktock_tailer) l.
Proof.
  intros.
  compute; auto.
Qed.

Lemma DePoolContract_Ф_ticktock'_eval_eq: forall (l: Ledger),
eval_state DePoolContract_Ф_ticktock' l = 
eval_state (DePoolContract_Ф_ticktock_header DePoolContract_Ф_updateRounds DePoolContract_Ф_ticktock_tailer) l.
Proof.
  intros.
  unfold eval_state.
  rewrite DePoolContract_Ф_ticktock'_run_eq.
  auto.
Qed.

Lemma DePoolContract_Ф_ticktock'_exec_eq: forall (l: Ledger),
exec_state DePoolContract_Ф_ticktock' l = 
exec_state (DePoolContract_Ф_ticktock_header DePoolContract_Ф_updateRounds DePoolContract_Ф_ticktock_tailer) l.
Proof.
  intros.
  unfold exec_state.
  rewrite DePoolContract_Ф_ticktock'_run_eq.
  auto.
Qed.


Opaque exec_state eval_state run.
Opaque DePoolContract_Ф_ticktock_header DePoolContract_Ф_ticktock_tailer.

Lemma DePoolContract_Ф_ticktock_exec : forall (l: Ledger), 
let req : bool := negb (eval_state msg_sender l =? 0)  in
let (if1, l_checkPureDePoolBalance) := run ( ↓ DePoolContract_Ф_checkPureDePoolBalance ) l in
let (r, l_updateRounds) := run ( ↓ DePoolContract_Ф_updateRounds ) l_checkPureDePoolBalance in
let l' := if if1 then l_updateRounds else l_checkPureDePoolBalance in

let if2' : bool := negb ( eval_state msg_sender l' =? eval_state tvm_address l') in
let l'' := if if2' then exec_state (↓ DePoolContract_Ф__returnChange) l' else l' in

let if2'' : bool := negb ( eval_state msg_sender l_checkPureDePoolBalance =? eval_state tvm_address l_checkPureDePoolBalance) in
let l''' := if if2'' then exec_state (↓ DePoolContract_Ф__returnChange) l_checkPureDePoolBalance else l_checkPureDePoolBalance in

exec_state DePoolContract_Ф_ticktock' l = 
if req then 
if if1 then errorMapDefaultF (fun _ => l'') r (fun _ => l')
       else l'''
else l .

Proof.
  intros.
  rewrite DePoolContract_Ф_ticktock'_exec_eq.
  remember (run (↓ DePoolContract_Ф_checkPureDePoolBalance) l).
  destruct p.
  remember (run (↓ DePoolContract_Ф_updateRounds) l0).
  destruct p.
  intros.

  remember (DePoolContract_Ф_ticktock_header_exec (XValueValue True) l DePoolContract_Ф_updateRounds DePoolContract_Ф_ticktock_tailer).
  clear Heqy.
  rewrite <- Heqp in y.
  compute in y. compute in Heqp0. 
  rewrite <- Heqp0 in y. 
  rewrite ?DePoolContract_Ф_ticktock_tailer_exec in y.

  setoid_rewrite y.  auto.
Qed.  


Lemma DePoolContract_Ф_ticktock_eval : forall (l: Ledger), 
let req : bool := negb (eval_state msg_sender l =? 0)  in
let (if1, l_checkPureDePoolBalance) := run ( ↓ DePoolContract_Ф_checkPureDePoolBalance ) l in
let (r, l_updateRounds) := run ( ↓ DePoolContract_Ф_updateRounds ) l_checkPureDePoolBalance in
let l' := if if1 then l_updateRounds else l_checkPureDePoolBalance in

(* let if2' : bool := negb ( eval_state msg_sender l' =? eval_state tvm_address l') in
let l'' := if if2' then exec_state (↓ DePoolContract_Ф__returnChange) l' else l' in

let if2'' : bool := negb ( eval_state msg_sender l_checkPureDePoolBalance =? eval_state tvm_address l_checkPureDePoolBalance) in
let l''' := if if2'' then exec_state (↓ DePoolContract_Ф__returnChange) l_checkPureDePoolBalance else l_checkPureDePoolBalance in *)

eval_state DePoolContract_Ф_ticktock' l = 

if req then 
if if1 then errorMapDefaultF (fun _ =>  Value I) r (fun e => Error e)
       else Value I
else Error Errors_ι_IS_EXT_MSG .


(* if req then 
if if1 then errorMapDefaultF (fun _ => l'') r (fun _ => l')
       else l'''
else l .
 *)
Proof.
  intros.
  rewrite DePoolContract_Ф_ticktock'_eval_eq.
  remember (run (↓ DePoolContract_Ф_checkPureDePoolBalance) l).
  destruct p.
  remember (run (↓ DePoolContract_Ф_updateRounds) l0).
  destruct p.
  intros.

  remember (DePoolContract_Ф_ticktock_header_eval (XValueValue True) l DePoolContract_Ф_updateRounds DePoolContract_Ф_ticktock_tailer).
  clear Heqy.
  rewrite <- Heqp in y.
  compute in y. compute in Heqp0. 
  rewrite <- Heqp0 in y. 
  rewrite ?DePoolContract_Ф_ticktock_tailer_eval in y.

  setoid_rewrite y. auto.
Qed.  

End DePoolContract_Ф_ticktock.