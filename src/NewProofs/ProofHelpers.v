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
 
Require Import depoolContract.DePoolFunc.
Require Import depoolContract.DePoolConsts.

Require Import depoolContract.Lib.CommonModelProofs.
Module CommonModelProofs := CommonModelProofs StateMonadSig.
Import CommonModelProofs. 
Require Import depoolContract.Lib.Tactics.
Require Import depoolContract.Lib.ErrorValueProofs.

Require Import depoolContract.Lib.CommonStateProofs.

Import DePoolSpec.LedgerClass.SolidityNotations. 

Local Open Scope solidity_scope.
Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope solidity_scope.
Require Import Lists.List.
Import ListNotations.
Local Open Scope list_scope.

Module ProofHelpers (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Import dc.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.

(* Set Typeclasses Iterative Deepening.
Set Typeclasses Depth 100.
 *)


Ltac pr_numgoals := let n := numgoals in idtac "There are" n "goals".


Lemma if_fromValueValue: forall X (b: bool) (x y: XValueValue X),
fromValueValue (if b then x else y) = if b then (fromValueValue x) else (fromValueValue y).
Proof.
  intros.
  destruct b; auto.
Qed.


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

Tactic Notation "destructLedger" constr(l) := 
let Ledger_ι_ValidatorBase := fresh "Ledger_ι_ValidatorBase" in
let Ledger_ι_ProxyBase := fresh "Ledger_ι_ProxyBase" in
let Ledger_ι_ParticipantBase := fresh "Ledger_ι_ParticipantBase" in
let Ledger_ι_DePoolProxyContract := fresh "Ledger_ι_DePoolProxyContract" in
let Ledger_ι_RoundsBase := fresh "Ledger_ι_RoundsBase" in
let Ledger_ι_DePoolContract := fresh "Ledger_ι_DePoolContract" in
let Ledger_ι_VMState := fresh "Ledger_ι_VMState" in
let Ledger_ι_LocalState := fresh "Ledger_ι_LocalState" in

destruct l as 
 [Ledger_ι_ValidatorBase Ledger_ι_ProxyBase Ledger_ι_ParticipantBase 
 Ledger_ι_DePoolProxyContract 
Ledger_ι_RoundsBase Ledger_ι_DePoolContract  
Ledger_ι_VMState Ledger_ι_LocalState]; 

destruct Ledger_ι_ValidatorBase, Ledger_ι_ProxyBase, Ledger_ι_ParticipantBase, 
Ledger_ι_DePoolProxyContract, 
Ledger_ι_RoundsBase, Ledger_ι_DePoolContract,  
Ledger_ι_VMState, Ledger_ι_LocalState.


Tactic Notation "destructFunction0" constr(f) := 
match goal with 
 | |- ?G => match G with 
            | context [f] => 
                  let m := fresh "m" in
                  let p := fresh "p" in
                  remember f  as m;
                  destruct m as (p) ;
                  let r := fresh "r" in 
                  match goal with 
                    | |- ?G1 => match G1 with 
                                 | context [p ?l] => remember (p l) as r;
                                                     let x := fresh "x" in 
                                                     let l := fresh "l" in
                                                     destruct r as [x l] 
                                end                     
                  end
            end      
end.

Tactic Notation "destructFunction1" constr(f) := 
 match goal with 
  | |- ?G => match G with 
             | context [f ?a] => 
                   let m := fresh "m" in
                   let p := fresh "p" in
                   remember (f a) as m;
                   destruct m as (p) ;
                   let r := fresh "r" in 
                   match goal with 
                     | |- ?G1 => match G1 with 
                                  | context [p ?l] => remember (p l) as r;
                                                      let x := fresh "x" in 
                                                      let l := fresh "l" in
                                                      destruct r as [x l] 
                                 end                     
                   end
             end      
end.


Tactic Notation "destructFunction2" constr(f) := 
 match goal with 
  | |- ?G => match G with 
             | context [f ?a ?b] => 
                   let m := fresh "m" in
                   let p := fresh "p" in
                   remember (f a b) as m;
                   destruct m as (p) ;
                   let r := fresh "r" in 
                   match goal with 
                     | |- ?G1 => match G1 with 
                                  | context [p ?l] => remember (p l) as r;
                                                      let x := fresh "x" in 
                                                      let l := fresh "l" in
                                                      destruct r as [x l] 
                                 end                     
                   end
             end      
end.


Tactic Notation "destructFunction3" constr(f) := 
 match goal with 
  | |- ?G => match G with 
             | context [f ?a ?b ?c] => 
                   let m := fresh "m" in
                   let p := fresh "p" in
                   remember (f a b c) as m;
                   destruct m as (p) ;
                   let r := fresh "r" in 
                   match goal with 
                     | |- ?G1 => match G1 with 
                                  | context [p ?l] => remember (p l) as r;
                                                      let x := fresh "x" in 
                                                      let l := fresh "l" in
                                                      destruct r as [x l] 
                                 end                     
                   end
             end      
end.

Tactic Notation "destructFunction4" constr(f) := 
 match goal with 
  | |- ?G => match G with 
             | context [f ?a ?b ?c ?d] => 
                   let m := fresh "m" in
                   let p := fresh "p" in
                   remember (f a b c d) as m;
                   destruct m as (p) ;
                   let r := fresh "r" in 
                   match goal with 
                     | |- ?G1 => match G1 with 
                                  | context [p ?l] => remember (p l) as r;
                                                      let x := fresh "x" in 
                                                      let l := fresh "l" in
                                                      destruct r as [x l] 
                                 end                     
                   end
             end      
end.

Tactic Notation "destructFunction5" constr(f) := 
 match goal with 
  | |- ?G => match G with 
             | context [f ?a ?b ?c ?d ?e] => 
                   let m := fresh "m" in
                   let p := fresh "p" in
                   remember (f a b c d e) as m;
                   destruct m as (p) ;
                   let r := fresh "r" in 
                   match goal with 
                     | |- ?G1 => match G1 with 
                                  | context [p ?l] => remember (p l) as r;
                                                      let x := fresh "x" in 
                                                      let l := fresh "l" in
                                                      destruct r as [x l] 
                                 end                     
                   end
             end      
end.


Tactic Notation "destructFunction6" constr(f) := 
 match goal with 
  | |- ?G => match G with 
             | context [f ?a ?b ?c ?d ?e ?g] => 
                   let m := fresh "m" in
                   let p := fresh "p" in
                   remember (f a b c d e g) as m;
                   destruct m as (p) ;
                   let r := fresh "r" in 
                   match goal with 
                     | |- ?G1 => match G1 with 
                                  | context [p ?l] => remember (p l) as r;
                                                      let x := fresh "x" in 
                                                      let l := fresh "l" in
                                                      destruct r as [x l] 
                                 end                     
                   end
             end      
end.

Tactic Notation "destructFunction7" constr(f) := 
 match goal with 
  | |- ?G => match G with 
             | context [f ?a ?b ?c ?d ?e ?g ?h] => 
                   let m := fresh "m" in
                   let p := fresh "p" in
                   remember (f a b c d e g h) as m;
                   destruct m as (p) ;
                   let r := fresh "r" in 
                   match goal with 
                     | |- ?G1 => match G1 with 
                                  | context [p ?l] => remember (p l) as r;
                                                      let x := fresh "x" in 
                                                      let l := fresh "l" in
                                                      destruct r as [x l] 
                                 end                     
                   end
             end      
end.

Tactic Notation "destructFunction8" constr(f) := 
 match goal with 
  | |- ?G => match G with 
             | context [f ?a ?b ?c ?d ?e ?g ?h ?i] => 
                   let m := fresh "m" in
                   let p := fresh "p" in
                   remember (f a b c d e g h i) as m;
                   destruct m as (p) ;
                   let r := fresh "r" in 
                   match goal with 
                     | |- ?G1 => match G1 with 
                                  | context [p ?l] => remember (p l) as r;
                                                      let x := fresh "x" in 
                                                      let l := fresh "l" in
                                                      destruct r as [x l] 
                                 end                     
                   end
             end      
end.


Tactic Notation "destructIf_solve" := 

time match goal with
      | |- ?G =>
        match G with
        | context [if ?b then _ else _] =>  idtac "if..." b; 
                                            repeat rewrite ifSimpleState ; 
                                            repeat rewrite ifFunApply ;
                                            case_eq b ; 
                                            simpl ; 
                                            intros                                                                
        | _ =>  idtac "solving..." G; 
                tryif solve [auto] then idtac "solved" else idtac "not solved"
        end
end.


Tactic Notation "destructIf_solve2" := 

time match goal with
      | |- ?G =>
        match G with
        | context [if ?b then _ else _] =>  idtac "if..." b; 
                                            repeat rewrite ifSimpleState ; 
                                            repeat rewrite ifFunApply ;
                                            match goal with 
                                            | H : b = _ |- _ => first [ (idtac "rewriting ->" ; rewrite H) | (idtac "destructing" ; case_eq b ; (* simpl ; *) intros) ]
                                            | H : _ = b |- _ => first [ (idtac "rewriting <-" ; rewrite <- H) | (idtac "destructing" ; case_eq b ; (* simpl ; *) intros) ]
                                            | _ => idtac "destructing" ; case_eq b ; (* simpl ; *) intros
                                            end
        | _ =>  idtac "solving..." G; 
                tryif solve [auto] then idtac "solved" else idtac "not solved"
        end
end.

(* repeat time match goal with
  | H : ?P |- _ =>
    match P with
    | context [ (if ?b then _ else _ ) = _ ] =>  let HH:=fresh"HH" in idtac "if..." b; case_eq b ; intros HH; rewrite HH in H ; try discriminate; try congruence

    end
  end. *)
End ProofHelpers.
