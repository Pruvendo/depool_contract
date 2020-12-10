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

(*
function terminator() public {
require(msg.pubkey() == tvm.pubkey(), Errors.IS_NOT_OWNER);
        require(!m_poolClosed, Errors.DEPOOL_IS_CLOSED);
        m_poolClosed = true;
        tvm.commit();
        tvm.accept();

        Round roundPre0 = getRoundPre0();
        Round round0 = getRound0();
        Round round1 = getRound1();

        roundPre0 = startRoundCompleting(roundPre0, CompletionReason.PoolClosed);
        round0 = startRoundCompleting(round0, CompletionReason.PoolClosed);
        if (round1.step == RoundStep.WaitingValidatorRequest) {
            round1 = startRoundCompleting(round1, CompletionReason.PoolClosed);
        }
        emit DePoolClosed();
        setRoundPre0(roundPre0);
        setRound0(round0);
        setRound1(round1);
    }
*)

Ltac remDestructIf :=
  match goal with
    | |- ?x =>
      match x with
        | context [if ?b then _ else _] => case_eq b ; intros
        | _ => idtac
      end
  end.

  Lemma letIf: forall X Y (b: bool) (f g: X*Ledger) (h: X -> Ledger -> Y), 
(let (x, t) := if b then f else g in h x t)=
if b then let (x, t) := f in h x t else
          let (x, t) := g in h x t .
Proof.
  intros.
  destruct b; auto.
Qed.

Lemma matchIf: forall X (b: bool) (f g: LedgerT X) (l: Ledger), 
(match (if b then f else g) with | SimpleState c => c end l)=
if b then match f with | SimpleState c => c end l else 
match g with | SimpleState c => c end l.
Proof.
  intros.
  destruct b; auto.
Qed.

Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair.


Import TVMModel.LedgerClass.
Opaque DePoolContract_Ф_startRoundCompleting roundStepEqb.


Definition DePoolContract_Ф_terminator_header f : LedgerT ( XErrorValue True XInteger ) := 
(*require(msg.pubkey() == tvm.pubkey() , Errors.IS_NOT_OWNER);*)	
Require2 {{ msg_pubkey () ?== tvm_pubkey () , ↑7 D2!  Errors_ι_IS_NOT_OWNER }} ; 
(*require(!m_poolClosed, Errors.DEPOOL_IS_CLOSED);*)
Require {{ !¬ ↑12 D2! DePoolContract_ι_m_poolClosed , ↑7 D2! Errors_ι_DEPOOL_IS_CLOSED }} ; 
(* m_poolClosed = true; *)
(↑12 U1! DePoolContract_ι_m_poolClosed := $xBoolTrue) >>
(* tvm.commit(); *)
tvm_commit () >>
(* tvm.accept(); *)
tvm_accept () >>


(* Round roundPre0 = getRoundPre0(); *)
U0! Л_roundPre0 := RoundsBase_Ф_getRoundPre0 ();
(* Round round0 = getRound0(); *)
U0! Л_round0 := RoundsBase_Ф_getRound0 ();
(*Round round1 = getRound1();*)
(↑↑17 U2! LocalState_ι_terminator_Л_round1 := RoundsBase_Ф_getRound1 () ) >>

(* roundPre0 = startRoundCompleting(roundPre0, CompletionReason.PoolClosed); *)
U0! Л_roundPre0 := DePoolContract_Ф_startRoundCompleting  (! $ Л_roundPre0 , 
														$ RoundsBase_ι_CompletionReasonP_ι_PoolClosed !) ;
(*round0 = startRoundCompleting(round0, CompletionReason.PoolClosed);*)
U0! Л_round0 := DePoolContract_Ф_startRoundCompleting  (! $ Л_round0 , 
														$ RoundsBase_ι_CompletionReasonP_ι_PoolClosed !) ;
(* if (round1.step == RoundStep.WaitingValidatorRequest) {
	round1 = startRoundCompleting(round1, CompletionReason.PoolClosed);
} *)
(If (↑17 D2! LocalState_ι_terminator_Л_round1 ^^ RoundsBase_ι_Round_ι_step ?== $ RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest) then {
	↑↑17 U2! LocalState_ι_terminator_Л_round1 := DePoolContract_Ф_startRoundCompleting (! ↑17 D2! LocalState_ι_terminator_Л_round1 , 
																						  $ RoundsBase_ι_CompletionReasonP_ι_PoolClosed !) 
}) >> f Л_roundPre0 Л_round0.


Definition DePoolContract_Ф_terminator_tailer Л_roundPre0 Л_round0 : LedgerT True := 
(* emit DePoolClosed(); *)
->emit $ DePoolClosed >>
(* setRoundPre0(roundPre0); *)
(RoundsBase_Ф_setRoundPre0 (! $ Л_roundPre0 !) ) >>
(*  setRound0(round0);  *)
(RoundsBase_Ф_setRound0 (! $ Л_round0 !)  ) >>
(* setRound1(round1); *)
(RoundsBase_Ф_setRound1 (! ↑17 D2! LocalState_ι_terminator_Л_round1 !) ) .


Lemma DePoolContract_Ф_terminator_eval : forall (l : Ledger),
eval_state DePoolContract_Ф_terminator l =

let isOwner := eval_state msg_pubkey l =? eval_state tvm_pubkey l in
let isNotClosed := negb (eval_state (↑12 ε DePoolContract_ι_m_poolClosed) l) in
                                       
if isOwner then 
   if isNotClosed then Value I
                  else Error  (eval_state ( ↑7 ε Errors_ι_DEPOOL_IS_CLOSED) l) 
           else Error (eval_state ( ↑7 ε Errors_ι_IS_NOT_OWNER) l).
Proof.     
  intros. destruct l. compute.

  repeat remDestructIf; auto.              

  match goal with 
  | |- ?x  => match x with 
              | context [DePoolContract_Ф_startRoundCompleting ?a ?b] => remember (DePoolContract_Ф_startRoundCompleting a b)
              end
  end. idtac.
  
  destruct l. idtac.
  
  match goal with 
  | |- ?x  => match x with 
              | context [p ?a] => remember (p a)
              end
  end. idtac.
  
  destruct p0. auto. idtac.

  match goal with 
  | |- ?x  => match x with 
              | context [DePoolContract_Ф_startRoundCompleting ?a ?b] => remember (DePoolContract_Ф_startRoundCompleting a b)
              end
  end. idtac.
  
  destruct l0. idtac.
  
  match goal with 
  | |- ?x  => match x with 
              | context [p0 ?a] => remember (p0 a)
              end
  end. idtac.
  
  destruct p1. auto. idtac.

  match goal with
  | |- ?x =>
    match x with
      | context [if ?b then _ else _] => remember b
      | _ => idtac
    end
  end.
  symmetry. idtac.

  destruct x; auto. 
  
  match goal with 
  | |- ?x  => match x with 
              | context [DePoolContract_Ф_startRoundCompleting ?a ?b] => remember (DePoolContract_Ф_startRoundCompleting a b)
              end
  end. idtac.
  
  destruct l1. idtac.
  
  match goal with 
  | |- ?x  => match x with 
              | context [p1 ?a] => remember (p1 a)
              end
  end. idtac.
  
  destruct p2. auto. 
  
Qed.  

(* Definition DePoolContract_Ф_terminator_tailer Л_roundPre0 Л_round0 : LedgerT True := 
(* emit DePoolClosed(); *)
->emit $ DePoolClosed >>
(* setRoundPre0(roundPre0); *)
(RoundsBase_Ф_setRoundPre0 (! $ Л_roundPre0 !) ) >>
(*  setRound0(round0);  *)
(RoundsBase_Ф_setRound0 (! $ Л_round0 !)  ) >>
(* setRound1(round1); *)
(RoundsBase_Ф_setRound1 (! ↑17 D2! LocalState_ι_terminator_Л_round1 !) ) . *)

Lemma DePoolContract_Ф_terminator_tailer_exec : forall Л_roundPre0 Л_round0 (l : Ledger),
exec_state (DePoolContract_Ф_terminator_tailer Л_roundPre0 Л_round0) l =

let oldEvents := eval_state (↑16 ε VMState_ι_events) l in
let l_emit := {$l With (VMState_ι_events ,  DePoolClosed :: oldEvents ) $} in
let l_setPre0 := exec_state (↓ RoundsBase_Ф_setRoundPre0 Л_roundPre0) l_emit in
let l_set0 := exec_state (↓ RoundsBase_Ф_setRound0 Л_round0) l_setPre0 in
let round1 := eval_state (↑17 ε LocalState_ι_terminator_Л_round1) l in
let l_set1 := exec_state (↓ RoundsBase_Ф_setRound1 round1) l_set0 in
l_set1.

Proof.
  intros. destruct l. compute. auto.
Qed.

Import LedgerClass.

Lemma DePoolContract_Ф_terminator_header_exec : forall f (l : Ledger),
exec_state (DePoolContract_Ф_terminator_header f) l =

let isOwner := eval_state msg_pubkey l =? eval_state tvm_pubkey l in
let isNotClosed := negb (eval_state (↑12 ε DePoolContract_ι_m_poolClosed) l) in

let closedDePool := {$ l With (DePoolContract_ι_m_poolClosed, true) $} in
let commited :=  exec_state (↓ tvm_commit) closedDePool in
let accepted :=  exec_state (↓ tvm_accept) commited in

let oldRoundPre0 := eval_state RoundsBase_Ф_getRoundPre0 l in
let oldRound0 := eval_state RoundsBase_Ф_getRound0 l in 
let oldRound1 := eval_state RoundsBase_Ф_getRound1 l in 

let round1ToBeUpdated : bool := eqb (RoundsBase_ι_Round_ι_step oldRound1) RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest in
let (srcPre0, l_pre0) := run (↓ DePoolContract_Ф_startRoundCompleting oldRoundPre0 RoundsBase_ι_CompletionReasonP_ι_PoolClosed) accepted in
let (src0, l_0) := run (↓ DePoolContract_Ф_startRoundCompleting oldRound0 RoundsBase_ι_CompletionReasonP_ι_PoolClosed) l_pre0 in
let (src1, l_1) := if round1ToBeUpdated then run (↓ DePoolContract_Ф_startRoundCompleting oldRound1 RoundsBase_ι_CompletionReasonP_ι_PoolClosed) l_0 
                                        else (oldRound1, l_0) in
let l' := exec_state (f srcPre0 src0) {$ l_1 With (LocalState_ι_terminator_Л_round1, src1) $} in                                        
if isOwner then 
    if isNotClosed then l'
                   else l else l.

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
                                          case_eq b ; 
                                          simpl ; intros                                                                                                   
      | _ =>  idtac "solving..." x; tryif solve [auto] then idtac "solved" else idtac "not solved"
      end

 
  end) . 

match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_startRoundCompleting ?a ?b] => remember (DePoolContract_Ф_startRoundCompleting a b)
            end
end. idtac.

destruct l. idtac.

match goal with 
| |- ?x  => match x with 
            | context [p ?a] => remember (p a)
            end
end.

destruct p0. auto.

match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_startRoundCompleting ?a ?b] => remember (DePoolContract_Ф_startRoundCompleting a b)
            end
end. idtac.

destruct l0. idtac.

match goal with 
| |- ?x  => match x with 
            | context [p0 ?a] => remember (p0 a)
            end
end.

destruct p1. auto.

Transparent roundStepEqb.

match goal with
| |- ?x =>
  match x with
    | context [if ?b then _ else _] => remember b
    | _ => idtac
  end
end.
rewrite H1. idtac.


symmetry. idtac.


match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_startRoundCompleting ?a ?b] => remember (DePoolContract_Ф_startRoundCompleting a b)
            end
end. idtac.

destruct l1. idtac.

match goal with 
| |- ?x  => match x with 
            | context [p1 ?a] => remember (p1 a)
            end
end.

destruct p2. auto. idtac.

match goal with 
| |- ?x  => match x with 
            | context [f ?a ?b] => remember (f a b)
            end
end. idtac.

destruct s. auto. idtac.

match goal with 
| |- ?x  => match x with 
            | context [p2 ?a] => remember (p2 a)
            end
end. idtac.


destruct p3. auto.

match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_startRoundCompleting ?a ?b] => remember (DePoolContract_Ф_startRoundCompleting a b)
            end
end. idtac.

symmetry. idtac.

destruct l. idtac.

match goal with 
| |- ?x  => match x with 
            | context [p ?a] => remember (p a)
            end
end. idtac.

destruct p0. auto. idtac.


match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_startRoundCompleting ?a ?b] => remember (DePoolContract_Ф_startRoundCompleting a b)
            end
end. idtac.

destruct l0. idtac.

match goal with 
| |- ?x  => match x with 
            | context [p0 ?a] => remember (p0 a)
            end
end. idtac.

destruct p1. auto. idtac.

symmetry. idtac.

rewrite matchIf. idtac.
repeat rewrite letIf. idtac.

rewrite H1. idtac.


match goal with 
| |- ?x  => match x with 
            | context [f ?a ?b] => remember (f a b)
            end
end. idtac.

destruct s. auto. idtac.

match goal with 
| |- ?x  => match x with 
            | context [p1 ?a] => remember (p1 a)
            end
end. idtac.


destruct p2. auto.

symmetry. idtac.

match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_startRoundCompleting ?a ?b] => remember (DePoolContract_Ф_startRoundCompleting a b)
            end
end. idtac.

destruct l. idtac.

match goal with 
| |- ?x  => match x with 
            | context [p ?a] => remember (p a)
            end
end. idtac.

destruct p0. auto. idtac.


match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_startRoundCompleting ?a ?b] => remember (DePoolContract_Ф_startRoundCompleting a b)
            end
end. idtac.

destruct l0. idtac.

match goal with 
| |- ?x  => match x with 
            | context [p0 ?a] => remember (p0 a)
            end
end. idtac.

destruct p1. auto. idtac.

match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_startRoundCompleting ?a ?b] => remember (DePoolContract_Ф_startRoundCompleting a b)
            end
end. idtac.

destruct l1. idtac.

match goal with 
| |- ?x  => match x with 
            | context [p1 ?a] => remember (p1 a)
            end
end. idtac.


destruct p2. auto. idtac.


symmetry. idtac.

match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_startRoundCompleting ?a ?b] => remember (DePoolContract_Ф_startRoundCompleting a b)
            end
end. idtac.

destruct l. idtac.

match goal with 
| |- ?x  => match x with 
            | context [p ?a] => remember (p a)
            end
end. idtac.

destruct p0. auto. idtac.


match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_startRoundCompleting ?a ?b] => remember (DePoolContract_Ф_startRoundCompleting a b)
            end
end. idtac.

destruct l0. idtac.

match goal with 
| |- ?x  => match x with 
            | context [p0 ?a] => remember (p0 a)
            end
end. idtac.

destruct p1. auto. idtac.

symmetry. idtac.

match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_startRoundCompleting ?a ?b] => remember (DePoolContract_Ф_startRoundCompleting a b)
            end
end. idtac.

destruct l. idtac.

match goal with 
| |- ?x  => match x with 
            | context [p ?a] => remember (p a)
            end
end. idtac.

destruct p0. auto. idtac.


match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_startRoundCompleting ?a ?b] => remember (DePoolContract_Ф_startRoundCompleting a b)
            end
end. idtac.

destruct l0. idtac.

match goal with 
| |- ?x  => match x with 
            | context [p0 ?a] => remember (p0 a)
            end
end. idtac.

destruct p1. auto. idtac.

match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_startRoundCompleting ?a ?b] => remember (DePoolContract_Ф_startRoundCompleting a b)
            end
end. idtac.

destruct l1. idtac.

match goal with 
| |- ?x  => match x with 
            | context [p1 ?a] => remember (p1 a)
            end
end. idtac.


destruct p2. auto. idtac.


symmetry. idtac.

match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_startRoundCompleting ?a ?b] => remember (DePoolContract_Ф_startRoundCompleting a b)
            end
end. idtac.

destruct l. idtac.

match goal with 
| |- ?x  => match x with 
            | context [p ?a] => remember (p a)
            end
end. idtac.

destruct p0. auto. idtac.


match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_startRoundCompleting ?a ?b] => remember (DePoolContract_Ф_startRoundCompleting a b)
            end
end. idtac.

destruct l0. idtac.

match goal with 
| |- ?x  => match x with 
            | context [p0 ?a] => remember (p0 a)
            end
end. idtac.

destruct p1. auto.

Qed.


