Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.
Require Import omega.Omega.
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

(* Existing Instance embeddedLocalState.
 
Existing Instance monadStateT.
Existing Instance monadStateStateT. *)

(* Existing Instance embeddedLocalState.
Existing Instance embeddedMultisig. *)

 (* function ticktock() public override {
require(msg.sender != address(0), Errors.IS_EXT_MSG);
        if (checkPureDePoolBalance()) {
            updateRounds();
        }

        if (msg.sender != address(this))
            _returnChange();  } *) 

Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair.

Opaque DePoolContract_Ф_updateRounds DePoolContract_Ф_checkPureDePoolBalance.


Ltac remDestructIf :=
  match goal with
    | |- ?x =>
      match x with
        | context [if ?b then _ else _] => case_eq b ; intros
        | _ => idtac
      end
  end.

Lemma DePoolContract_Ф_ticktock_exec : forall (l: Ledger) , 
    (*require(msg.sender != address(0), Errors.IS_EXT_MSG);*)
    exec_state ( ↓ DePoolContract_Ф_ticktock ) l = 

let req : bool := negb (eval_state msg_sender l =? 0)  in
let (if1, l_checkPureDePoolBalance) := run ( ↓ DePoolContract_Ф_checkPureDePoolBalance ) l in
let (r,  l_updateRounds) := run ( ↓ DePoolContract_Ф_updateRounds ) l_checkPureDePoolBalance in
let l' := if if1 then match r with
                      | Value _ => l_updateRounds
                      | Error _ => l_checkPureDePoolBalance 
                 end else  l_checkPureDePoolBalance  in
let if2 : bool := negb ( eval_state msg_sender l' =? eval_state tvm_address l') in
let l__returnChange := exec_state ( ↓ DePoolContract_Ф__returnChange ) l' in

if req then if if1 then match r with
                        | Value _ => if if2 then l__returnChange else l_updateRounds
                        | Error _ => l_updateRounds
                        end 
                   else if if2 then l__returnChange else l_checkPureDePoolBalance 
       else l.

 Proof. 
  intros. destruct l. compute.

  do 2 remDestructIf; auto.
  
  all: cycle 1.

match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_checkPureDePoolBalance] => remember (DePoolContract_Ф_checkPureDePoolBalance)
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
            | context [DePoolContract_Ф_updateRounds] => remember (DePoolContract_Ф_updateRounds)
            end
end. idtac.

destruct l0. idtac.

match goal with 
| |- ?x  => match x with 
            | context [p0 ?a] => remember (p0 a)
            end
end.

destruct p1. auto. idtac.

match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_checkPureDePoolBalance] => remember (DePoolContract_Ф_checkPureDePoolBalance)
            end
end. idtac.

destruct l. idtac.

match goal with 
| |- ?x  => match x with 
            | context [p ?a] => remember (p a)
            end
end.

destruct p0. auto.

case_eq x; intros; auto. idtac.

all: cycle 1.

match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_updateRounds] => remember (DePoolContract_Ф_updateRounds)
            end
end. idtac.

destruct l0. idtac.

match goal with 
| |- ?x  => match x with 
            | context [p0 ?a] => remember (p0 a)
            end
end.

destruct p1. auto. idtac.

remDestructIf; auto.

match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_updateRounds] => remember (DePoolContract_Ф_updateRounds)
            end
end. idtac.

destruct l0. idtac.

match goal with 
| |- ?x  => match x with 
            | context [p0 ?a] => remember (p0 a)
            end
end.

destruct p1. auto. idtac.

destruct x0; auto. idtac.

remDestructIf; auto.

 Qed.


Lemma DePoolContract_Ф_ticktock_eval : forall (l: Ledger) , 
eval_state ( ↓ DePoolContract_Ф_ticktock ) l = 

let req : bool := negb (eval_state msg_sender l =? 0)  in
let (if1, l_checkPureDePoolBalance) := run ( ↓ DePoolContract_Ф_checkPureDePoolBalance ) l in
let (r,  l_updateRounds) := run ( ↓ DePoolContract_Ф_updateRounds ) l_checkPureDePoolBalance in
let l' := if if1 then match r with
                      | Value _ => l_updateRounds
                      | Error _ => l_checkPureDePoolBalance 
                 end else  l_checkPureDePoolBalance  in
let if2 : bool := negb ( eval_state msg_sender l' =? eval_state tvm_address l') in
let l__returnChange := exec_state ( ↓ DePoolContract_Ф__returnChange ) l' in

if req then if if1 then match r with
                        | Value _ => Value I
                        | Error x => Error x
                        end 
                   else Value I 
       else Error ( eval_state ( ↑7 ε Errors_ι_IS_EXT_MSG ) l ).
  
 Proof. 
  intros. destruct l. compute.

  do 2 remDestructIf; auto.

  all: cycle 1.

match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_checkPureDePoolBalance] => remember (DePoolContract_Ф_checkPureDePoolBalance)
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
            | context [DePoolContract_Ф_updateRounds] => remember (DePoolContract_Ф_updateRounds)
            end
end. idtac.

destruct l0. idtac.

match goal with 
| |- ?x  => match x with 
            | context [p0 ?a] => remember (p0 a)
            end
end.

destruct p1. auto. idtac.

(***)

match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_checkPureDePoolBalance] => remember (DePoolContract_Ф_checkPureDePoolBalance)
            end
end. idtac.

destruct l. idtac.

match goal with 
| |- ?x  => match x with 
            | context [p ?a] => remember (p a)
            end
end.

destruct p0. auto.

case_eq x; intros; auto. idtac.

all: cycle 1.

match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_updateRounds] => remember (DePoolContract_Ф_updateRounds)
            end
end. idtac.

destruct l0. idtac.

match goal with 
| |- ?x  => match x with 
            | context [p0 ?a] => remember (p0 a)
            end
end.

destruct p1. auto. idtac.

remDestructIf; auto.

match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф_updateRounds] => remember (DePoolContract_Ф_updateRounds)
            end
end. idtac.

destruct l0. idtac.

match goal with 
| |- ?x  => match x with 
            | context [p0 ?a] => remember (p0 a)
            end
end.

destruct p1. auto. idtac.

destruct x0; auto. idtac.

remDestructIf; auto.



 Qed. 
