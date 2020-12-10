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

Fixpoint toUniqueArray {X} (eqX: X -> X -> bool) (l: list X) (m: listPair Z X) : listPair Z X :=
match l with
| nil => m
| x::xs => if (bIn eqX x (xHMapElems m)) then (toUniqueArray eqX xs m) else 
                                              (toUniqueArray eqX xs (hmapPush x m))
end.

Lemma toUniqueArrayFalse_helper1: forall X (H: XBoolEquable bool X)  (x0: listPair Z X) a,
boolEquivalence eqb ->
hmapFindWithDefault false (@eqb bool X H) a
       (List.map (fun p : Z * X => (snd p, true)) x0) = false -> 
bIn eqb a (List.map snd x0) = false.
Proof.
 intros. induction x0.
 simpl. auto.
 simpl. simpl in H1. 
 unfold hmapFindWithDefault in H1.
 unfold hmapLookup in H1. simpl in H1.
 remember (eqb (snd a0) a).
 replace (eqb a (snd a0)) with y in H1.
 destruct y. simpl in H0. inversion H1.
 replace (bIn eqb a (List.map snd x0)) with false.
 auto. symmetry. apply IHx0.
 apply H1. rewrite Heqy. apply boolEqSym. auto.
Qed.

Lemma toUniqueArrayTrue_helper1: forall X (H: XBoolEquable bool X)  (x0: listPair Z X) a,
boolEquivalence eqb ->
hmapFindWithDefault false (@eqb bool X H) a
       (List.map (fun p : Z * X => (snd p, true)) x0) = true -> 
bIn eqb a (List.map snd x0) = true.
Proof.
 intros. induction x0.
 simpl in H1. inversion H1.
 simpl. simpl in H1. 
 unfold hmapFindWithDefault in H1.
 unfold hmapLookup in H1. simpl in H1.
 remember (eqb (snd a0) a).
 replace (eqb a (snd a0)) with y in H1.
 destruct y. simpl in H1. auto.
 rewrite IHx0. auto. auto. rewrite Heqy.
 apply boolEqSym. auto.
Qed.

Lemma toUniqueArrayFalse_helper2: forall X (H:XBoolEquable bool X)  x0 a,
bIn eqb a (List.map snd x0) = false ->
hmapIsMember Z.eqb (Z.of_nat (Datatypes.length x0)) x0 = false ->
(List.map (fun p : Z * X => (snd p, true)) x0) [a]← true =
List.map (fun p : Z * X => (snd p, true)) (hmapInsert Z.eqb (xHMapSize x0) a x0).
Proof.
 intros. unfold hmapInsert.
 simpl. 
 replace (bIn eqb a (map fst (map (fun p : Z * X => (snd p, true)) x0))) with false.
 replace (bIn Z.eqb (Z.of_nat (Datatypes.length x0)) (map fst x0)) with false.
 unfold Datatypes.id. simpl. auto.
 symmetry.
 replace (List.map fst (List.map (fun p : Z * X => (snd p, true)) x0)) with (List.map snd x0).
 auto.
 generalize x0. intros. induction x1.
 simpl. auto.
 simpl. rewrite IHx1. auto.
Qed.

Lemma toUniqueArrayFalse_helper3: forall X (x0: listPair Z X) a0,
(forall z, z >= (Z.of_nat (Datatypes.length x0)) ->
                        hmapIsMember Z.eqb z x0 = false) -> 
hmapIsMember Z.eqb (Z.of_nat (Datatypes.length (hmapPush a0 x0))) (hmapPush a0 x0) = false.
Proof.
 intros. unfold hmapIsMember.
 unfold hmapIsMember in H.
 remember (Z.of_nat (Datatypes.length x0)).
 remember (Z.of_nat (Datatypes.length (hmapPush a0 x0))).
 assert (z0 >= z). 
 rewrite Heqz. rewrite Heqz0. apply hmapSizePush.
 apply H in H0.
 unfold hmapPush. unfold hmapInsert.
 replace (hmapIsMember xIntEqb (xHMapSize x0) x0) with false.
 simpl. rewrite <- Heqz. 
 unfold  Datatypes.id.
 replace (z =? z0) with false.
 replace (bIn Z.eqb z0 (List.map fst x0)) with false.
 auto. symmetry. rewrite Heqz.
 rewrite Heqz0.
 unfold hmapPush. unfold hmapInsert.
 replace (hmapIsMember xIntEqb (xHMapSize x0) x0) with false.
 simpl.  unfold Datatypes.id.
 remember (Datatypes.length x0).
 apply Z.eqb_neq. rewrite Zpos_P_of_succ_nat. lia.
 symmetry. unfold hmapIsMember. apply H.
 rewrite Heqz. simpl. lia. symmetry. unfold hmapIsMember. apply H.
 rewrite Heqz. simpl. lia.
Qed.


Lemma toUniqueArrayFalse_helper3': forall X (x0: listPair Z X) a0 z,
(forall z, z >= (Z.of_nat (Datatypes.length x0)) ->
                        hmapIsMember Z.eqb z x0 = false) -> 
z >= Z.of_nat (Datatypes.length (hmapPush a0 x0)) ->
hmapIsMember Z.eqb z (hmapPush a0 x0) = false.
Proof.
 intros. unfold hmapIsMember.
 unfold hmapIsMember in H.
 remember (Z.of_nat (Datatypes.length x0)).
 remember (Z.of_nat (Datatypes.length (hmapPush a0 x0))).
 assert (z1 >= z0). 
 rewrite Heqz1. rewrite Heqz0. apply hmapSizePush.
 apply H in H1.
 unfold hmapPush. unfold hmapInsert.
 replace (hmapIsMember xIntEqb (xHMapSize x0) x0) with false.
 simpl. rewrite <- Heqz0. 
 unfold  Datatypes.id.
 replace (z0 =? z) with false.
 replace (bIn Z.eqb z (List.map fst x0)) with false.
 auto. symmetry. apply H.
 rewrite Heqz0. apply Zge_trans with (m:=z1). auto.
 rewrite Heqz1.
 unfold hmapPush. unfold hmapInsert.
 replace (hmapIsMember xIntEqb (xHMapSize x0) x0) with false.
 simpl.  unfold Datatypes.id.
 remember (Datatypes.length x0).
 rewrite Zpos_P_of_succ_nat. lia.
 symmetry. unfold hmapIsMember. apply H.
 rewrite Heqz0. simpl. lia. 
 symmetry.  apply Z.eqb_neq.
 assert (z1 = z0 + 1).
 rewrite Heqz1. rewrite Heqz0.
 unfold hmapPush.
 unfold hmapInsert. replace (hmapIsMember xIntEqb (xHMapSize x0) x0) with false.
 simpl. simpl. unfold Datatypes.id. remember (Datatypes.length x0).
 rewrite Zpos_P_of_succ_nat. lia.
 symmetry. unfold hmapIsMember. apply H.
 rewrite Heqz0. simpl. lia.
 lia. symmetry. unfold hmapIsMember. apply H.
 rewrite Heqz0. simpl. lia.
Qed.

Lemma toUniqueArrayFalse: forall {X}`{XBoolEquable bool X} 
(l: list X) x0 (a: X), 
boolEquivalence eqb -> 
(forall z, z >= (Z.of_nat (Datatypes.length x0)) ->
                        hmapIsMember Z.eqb z x0 = false) ->
(List.map (fun p => (snd p, true))
        (toUniqueArray eqb l x0)) [a] = false ->
hmapInsert eqb a true
  (List.map (fun p => (snd p, true)) (toUniqueArray eqb l x0)) =
List.map (fun p => (snd p, true))
  (toUniqueArray eqb (l ++ [a]) x0).
Proof.
 intros. generalize dependent x0. induction l; intros.
 simpl. simpl in H2. 
 remember (bIn eqb a (List.map snd x0)).
 destruct b. apply toUniqueArrayFalse_helper1 in H2.
 congruence. auto.
 apply toUniqueArrayFalse_helper1 in H2.
 unfold hmapPush. 
 setoid_rewrite toUniqueArrayFalse_helper2. auto. auto.
 apply H1. lia. auto.
 simpl.
 remember (bIn eqb a0 (List.map snd x0)).
 destruct b. apply IHl. auto.
 simpl in H2. rewrite <- Heqb in H2. auto.
 apply IHl. intros. apply toUniqueArrayFalse_helper3'.
 intros. apply H1. auto. auto.
 simpl in H2. rewrite <- Heqb in H2.
 apply H2.
Qed.

Lemma toUniqueArrayTrue: forall {X}`{XBoolEquable bool X} 
(l: list X) x0 (a: X), 
boolEquivalence eqb -> 
(forall z, z >= (Z.of_nat (Datatypes.length x0)) ->
                        hmapIsMember Z.eqb z x0 = false) ->
(List.map (fun p => (snd p, true))
        (toUniqueArray eqb l x0)) [a] = true ->
List.map (fun p => (snd p, true))
  (toUniqueArray eqb l x0) =
List.map (fun p => (snd p, true))
  (toUniqueArray eqb (l ++ [a]) x0).
Proof.
 intros. generalize dependent x0. induction l; intros.
 simpl. simpl in H2. 
 remember (bIn eqb a (List.map snd x0)).
 destruct b. auto. apply toUniqueArrayTrue_helper1 in H2.
 congruence. auto.
 simpl in H2. simpl. remember (bIn eqb a0 (List.map snd x0)).
 destruct b. apply IHl. auto. 
 auto. apply IHl.
 intros. unfold hmapPush.
 apply toUniqueArrayFalse_helper3'. intros.
 apply H1. auto. auto. auto.
Qed.

Lemma toUniqueArrayFalse2: forall {X}`{XBoolEquable bool X} 
(l: list X) x0 (a: X), 
boolEquivalence eqb -> 
(List.map (fun p => (snd p, true))
        (toUniqueArray eqb l x0)) [a] = false -> 
hmapInsert Z.eqb
  (Z.of_nat (Datatypes.length (toUniqueArray eqb l x0))) a
  (toUniqueArray eqb l x0) =
toUniqueArray eqb (l ++ [a]) x0.
Proof.
 intros. generalize dependent x0. induction l; intros.
 simpl in H1. simpl. remember (bIn eqb a (List.map snd x0)).
 destruct b. apply toUniqueArrayFalse_helper1 in H1.
 congruence. auto.
 apply toUniqueArrayFalse_helper1 in H1.
 unfold hmapPush. auto. auto.
 simpl. simpl in H1.
 remember (bIn eqb a0 (List.map snd x0)).
 destruct b. apply IHl.  auto.
 apply IHl. auto.
Qed.  

Lemma toUniqueArrayTrue2: forall {X}`{XBoolEquable bool X} 
(l: list X) x0 (a: X), 
boolEquivalence eqb -> 
(List.map (fun p => (snd p, true))
          (toUniqueArray eqb l x0)) [a] = true ->
toUniqueArray eqb l x0 =
toUniqueArray eqb (l ++ [a]) x0.
Proof.
 intros. generalize dependent x0. induction l; intros.
 simpl. simpl in H1. apply toUniqueArrayTrue_helper1 in H1.
 rewrite H1. auto. auto.
 simpl. simpl in H1. remember (bIn eqb a0 (List.map snd x0)).
 destruct b. apply IHl. auto.
 apply IHl. auto.
Qed.

Lemma toUniqueArrayFalse3: forall {X}`{XBoolEquable bool X} 
(l: list X) x0 (a: X), 
boolEquivalence eqb -> 
(forall z, z >= (Z.of_nat (Datatypes.length x0)) ->
                        hmapIsMember Z.eqb z x0 = false) ->
(List.map (fun p => (snd p, true))
        (toUniqueArray eqb l x0)) [a] = false -> 
Z.of_nat (Datatypes.length (toUniqueArray eqb l x0)) + 1 =
Z.of_nat (Datatypes.length (toUniqueArray eqb (l ++ [a]) x0)).
Proof.
 intros. generalize dependent x0. induction l; intros.
 simpl in H1. simpl. remember (bIn eqb a (List.map snd x0)).
 destruct b. apply toUniqueArrayFalse_helper1 in H2. simpl in H2.
 congruence. auto.
 apply toUniqueArrayFalse_helper1 in H2. simpl in H2.
 unfold hmapPush. unfold hmapInsert. 
 replace (bIn Z.eqb (Z.of_nat (Datatypes.length x0)) (map fst x0)) with false.
 simpl. unfold Datatypes.id. remember (Datatypes.length x0).
 rewrite Zpos_P_of_succ_nat. lia.
 symmetry. apply H1. lia. auto.

 simpl. remember (bIn eqb a0 (List.map snd x0)).
 destruct b. apply IHl.  auto. simpl in H2.
 rewrite <- Heqb in H2. auto.
 apply IHl. intros. 
 apply toUniqueArrayFalse_helper3'. intros.
 apply H1. auto. auto.
 simpl in H2. rewrite <- Heqb in H2.
 auto.
Qed.

Lemma toUniqueArrayTrue3: forall {X}`{XBoolEquable bool X} 
(l: list X) x0 (a: X), 
boolEquivalence eqb -> 
(List.map (fun p => (snd p, true))
          (toUniqueArray eqb l x0)) [a] = true ->
Z.of_nat
  (Datatypes.length (toUniqueArray eqb l x0)) =
Z.of_nat
  (Datatypes.length
     (toUniqueArray eqb (l ++ [a]) x0)).
Proof.
 intros. generalize dependent x0. induction l; intros.
 simpl. simpl in H1. apply toUniqueArrayTrue_helper1 in H1.
 rewrite H1. auto. auto.
 simpl. simpl in H1.
 remember (bIn eqb a0 (List.map snd x0)).
 destruct b. apply IHl. auto. apply IHl.
 auto.
Qed.


