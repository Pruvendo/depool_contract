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
Module RoundsBase_Ф_getRounds (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.


 Lemma RoundsBase_Ф_getRounds_exec' : forall (l: Ledger) , 
   exists (ls: LocalState),
 	 exec_state RoundsBase_Ф_getRounds l = {$ l with Ledger_ι_LocalState := ls $} .  
 Proof. 
   intros.  
   Opaque fold_left.
   compute. idtac.
   match goal with
   | |- ?G => match G with
              | context [fold_left ?f _ _ ] => remember f
              end
   end. idtac.

   remember (fun
   s0 : LedgerP Z Z Z Z Z Z Z bool string string list option
          (fun X Y : Type => list (X * Y)) prod => (false, I, s0)).
   assert (forall l, exists ls b, p l = (b, {$l with Ledger_ι_LocalState := ls $} )) . idtac. 
   intros.
   exists (Ledger_ι_LocalState (snd (p l0))), (fst (p l0)).
   rewrite Heqp.
   simpl.
   destruct l0; auto.
   rewrite Heqp in  Heqs.
   clear Heqp.
   generalize dependent p.
   induction (listInfinite True); intros.

   remember (H {$ l with Ledger_ι_LocalState :=  {$ Ledger_ι_LocalState l with (LocalState_ι_getRounds_Л_rounds , default); 
                                        (LocalState_ι_getRounds_Л_pair , eval_state RoundsBase_Ф_minRound l)  $} $} ).
   clear Heqe. inversion_clear e. idtac.
   inversion_clear H0. idtac.  
   exists x.

   Transparent fold_left.
   compute. idtac. destruct l. 
   simpl in H1.
   destruct Ledger_ι_LocalState. idtac.
   compute in H1. rewrite H1. idtac.
   auto.

   simpl.
   remember (s (SimpleState p) a).
   destruct s0.

   match goal with
   | |- ?G => match G with
              | context [ match fold_left s l0 (SimpleState p0) with
              | SimpleState c => c
              end ?l ] => remember l
              end
   end. idtac.

   remember (IHl0 p0).
   clear Heqe.
   clear IHl0.
   assert (forall
   l : LedgerP Z Z Z Z Z Z Z bool string string list option 
             (fun X Y : Type => list (X * Y)) prod,
 exists
   (ls : LocalStateP Z Z Z Z Z Z bool list option 
                  (fun X Y : Type => list (X * Y)) prod) 
 (b : bool * True), p0 l = (b, {$l with Ledger_ι_LocalState := ls $})).

 intros.
 exists (Ledger_ι_LocalState (snd (p0 l2))), (fst (p0 l2)).
 rewrite Heqs in Heqs0. idtac.
 inversion_clear Heqs0. idtac.

 remember (H l2). idtac.
 inversion_clear e0.
 inversion_clear H0.
 rewrite ?H1.

 destruct x0. idtac.

 match goal with
    | |- ?x =>
      match x with
        | context [if ?b then _ else _] =>  repeat rewrite ifSimpleState ; 
                                            repeat rewrite ifFunApply ;
                                            (* let rem := fresh "rem" in  *)
                                            (* set (rem:= b) ;  *)
                                            time case b (* compute; auto *)
        | _ => auto
      end
 end. idtac.
 simpl. destruct l2 .  auto. 

 match goal with
 | |- ?x =>
   match x with
     | context [if ?b then _ else _] =>  repeat rewrite ifSimpleState ; 
                                         repeat rewrite ifFunApply ;
                                         (* let rem := fresh "rem" in  *)
                                         (* set (rem:= b) ;  *)
                                         time case b (* compute; auto *)
     | _ => auto
   end
end. idtac.
destruct l2. destruct x. compute. auto.
destruct l2. destruct x. compute. auto.

apply e. idtac.
intros.

exists (Ledger_ι_LocalState (snd (p0 l2))), (fst (p0 l2)).
 rewrite Heqs in Heqs0. idtac.
 inversion_clear Heqs0. idtac.

 remember (H l2). idtac.
 inversion_clear e0.
 inversion_clear H1.
 rewrite ?H2.

 destruct x0. idtac.

 match goal with
    | |- ?x =>
      match x with
        | context [if ?b then _ else _] =>  repeat rewrite ifSimpleState ; 
                                            repeat rewrite ifFunApply ;
                                            (* let rem := fresh "rem" in  *)
                                            (* set (rem:= b) ;  *)
                                            time case b (* compute; auto *)
        | _ => auto
      end
 end. idtac.
 simpl. destruct l2 .  auto. 

 match goal with
 | |- ?x =>
   match x with
     | context [if ?b then _ else _] =>  repeat rewrite ifSimpleState ; 
                                         repeat rewrite ifFunApply ;
                                         (* let rem := fresh "rem" in  *)
                                         (* set (rem:= b) ;  *)
                                         time case b (* compute; auto *)
     | _ => auto
   end
end. idtac.
destruct l2. destruct x. compute. auto.
destruct l2. destruct x. compute. auto.

Qed. 

Lemma RoundsBase_Ф_getRounds_exec : forall (l: Ledger) , 
 exec_state (↓ RoundsBase_Ф_getRounds) l = l .
 Proof.
   intros.
   Opaque  RoundsBase_Ф_getRounds.
   compute.
   remember (run RoundsBase_Ф_getRounds {$l with Ledger_ι_LocalState := DePoolFuncs.DePoolSpec.LedgerClass.local0 $} ).
   remember (RoundsBase_Ф_getRounds_exec' {$l with Ledger_ι_LocalState := DePoolFuncs.DePoolSpec.LedgerClass.local0 $} ).
   clear Heqe.
   inversion_clear e.
   assert (snd p = {$ l with Ledger_ι_LocalState := x $} ).
   rewrite Heqp.
   rewrite run_eval_exec.
   rewrite H.
   auto.
   compute in Heqp.
   rewrite <- Heqp.
   destruct p.
   simpl in H0.
   rewrite H0.
   destruct l. destruct x. auto.
 Qed.

Lemma RoundsBase_Ф_getRounds_eval : forall (l: Ledger) , 
eval_state (  RoundsBase_Ф_getRounds ) l = xHMapEmpty . 
Proof. 
intros. destruct l. auto. 
Abort. 

End RoundsBase_Ф_getRounds.
