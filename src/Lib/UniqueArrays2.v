Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.
Require Import Setoid.

Require Import Lists.List.
Import ListNotations.

Require Import FinProof.Common.
Require Import FinProof.CommonInstances.
Require Import FinProof.CommonProofs.
Require Import ZArith.
Require Import Psatz.

Require Import depoolContract.SolidityNotations.
Require Import depoolContract.ProofEnvironment.
Require Import depoolContract.Lib.Tactics.
Require Import depoolContract.Lib.CommonCommon.

(* Module SolidityNotations := SolidityNotations XTypesSig StateMonadSig. *)
Import SolidityNotations.
Import List.

Local Open Scope solidity_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Set Typeclasses Iterative Deepening.

Set Typeclasses Depth 100.

Fixpoint toUniqueArray' {X}`{XBoolEquable bool X} (n:Z) (m: listPair Z X) (l: list X) : listPair Z X :=
match l with
| nil => m
| x::xs => if (bIn eqb x (xHMapElems m)) then (toUniqueArray' (Z.succ n) m xs) else 
                                              (toUniqueArray' (Z.succ n) (hmapInsert eqb n x m) xs)
end.

Definition toUniqueArray2 {X}`{XBoolEquable bool X} := toUniqueArray' 1%Z (@nil (Z*X)%type).

Lemma toUniqueArray2Cons': forall {X}`{XBoolEquable bool X} (l: list X) (n:Z) (m:list (Z*X)) (a:X),
      (forall k, (k >= n) -> bIn Z.eqb k (List.map fst m) = false) ->
      toUniqueArray' n m (l ++ [a]) = 
      if (bIn eqb a (xHMapElems (toUniqueArray' n m l))) then 
      (toUniqueArray' n m l) else
      (n + (xListLength l), a) :: (toUniqueArray' n m l).
Proof.
 intros. generalize dependent a. generalize dependent n. generalize dependent m.
 induction l; intros.
 simpl. rewrite H0; auto.
 destruct (bIn eqb a (map snd m)); auto.
 replace (n+0) with n; try lia.
 auto. lia.

 simpl. remember (bIn eqb a (map snd m)).
 remember (bIn Z.eqb n (map fst m)).
 rewrite H0 in Heqb0; try lia; auto.
 rewrite Heqb0.
 destruct b.
 remember (bIn eqb a0 (map snd (toUniqueArray' (Z.succ n) m l))).
 rewrite IHl; auto.
 setoid_rewrite <- Heqb1.
 destruct  b; auto.
 replace (n + Z.pos (Pos.of_succ_nat (Datatypes.length l))) with
         (Z.succ n + xListLength l). auto.
 rewrite Zpos_P_of_succ_nat.
 unfoldList xListLength. lia.
 intros. apply H0. lia.
 unfold Datatypes.id.
 remember (bIn eqb a0 (map snd (toUniqueArray' (Z.succ n) ((n, a) :: m) l))).
 destruct b.
 rewrite IHl; auto.
 setoid_rewrite <- Heqb1. auto.
 intros. simpl. rewrite H0.
 replace (n =? k) with false. auto. symmetry.
 apply Z.eqb_neq. lia. lia.
 rewrite  IHl; auto.
 setoid_rewrite <- Heqb1.
 replace  (n + Z.pos (Pos.of_succ_nat (Datatypes.length l))) with 
          (Z.succ n + xListLength l). auto.
 rewrite Zpos_P_of_succ_nat.
 unfoldList xListLength. lia.
 intros. simpl. rewrite H0.
 replace (n =? k) with false. auto. symmetry.
 apply Z.eqb_neq. lia. lia.
Qed.


Lemma toUniqueArray2Cons: forall {X}`{XBoolEquable bool X} (l: list X) (a:X),
      toUniqueArray2 (l ++ [a]) = 
      if (bIn eqb a (xHMapElems (toUniqueArray2 l))) then 
      (toUniqueArray2 l) else
      (Z.succ (xListLength l), a) :: (toUniqueArray2 l).
Proof.
 intros.
 unfold toUniqueArray2.
 rewrite toUniqueArray2Cons'.
 replace (1 + xListLength l) with (Z.succ (xListLength l)).
 auto. lia.
 intros.  simpl.  auto.
Qed.
 

