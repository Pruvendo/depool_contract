Require Import ZArith.
Require Import Psatz.

Require Import SMTCoq.SMTCoq.
Require Import Bool.

Require Import ZArith.

Local Open Scope Z_scope.
(* Require Import Coq.QArith.Qfield.  *)
Compute 5/0.

Compute Z.pow 2 15.
Compute (Z.pow 2 2 - 1) mod 15.
Compute (Z.pow 2 3 - 1) mod 15.
Compute (Z.pow 2 4 - 1) mod 15.

Goal forall a b c, ((a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a)) = false.
Proof.
  verit_bool.
Qed.

Require Import Classical.
Require Import Btauto.
Goal forall (a b : Z) (P : Z -> bool) (f : Z -> Z),
  (negb (Z.eqb (f a) b)) || (negb (P (f a))) || (P b).
Proof.
    intros.
    Abort.

Goal forall b1 b2 x1 x2,
    implb
      (ifb b1
           (ifb b2 (Z.eqb (2*x1+1) (2*x2+1)) (Z.eqb (2*x1+1) (2*x2)))
           (ifb b2 (Z.eqb (2*x1) (2*x2+1)) (Z.eqb (2*x1) (2*x2))))
      ((implb b1 b2) && (implb b2 b1) && (Z.eqb x1 x2)).
Proof.
  Abort.

Lemma distr_right_inst a b (mult : Z -> Z -> Z) :
    (forall x y z, mult (x + y)  z =? mult x z + mult y z) ->
    (mult (3 + a) b =? mult 3 b + mult a b).
  Proof.
    intro H.
    verit H.
  Qed.

  Lemma zdiv1 : forall a : Z, 1 < a -> 1 / a > 2.
  Proof.
      smt.
      try nia.
      try lia.
      try nra.
      try lra.
      eauto with zarith.
  Qed.

Lemma foo : forall a b c : Z,0 < c < 5 -> a > 2 -> b > 3 -> a*b > c.
Proof.
    intros.

    psatz Z 4.
    try lia.
    try verit.
    try nia.
    sm
    smt.
    intros.
    try nia.
    try lia.
    try nra.
    try lra.
    eauto with zarith.
Qed


Hint Resolve Zdiv_1_l : zarith. 

Lemma zdiv1 : forall a : Z, 1 < a -> 1 / a = 0.
Proof.
    intros.
    try nia.
    try lia.
    try nra.
    try lra.
    eauto with zarith.
Qed.

Lemma foo1: forall c:Z,  c > 0 -> 1/c >= 0.
Proof.
    intros.
    zero_or_not (c-1). assert (c = 1) by lia.
    subst. compute. discriminate.
    assert (1 < c) by lia.
    assert (1/c = 0) by auto with zarith.
    rewrite H1. lia.
Qed.

Lemma bar: forall a b, a >=0 -> b > 0 -> a*b >=0.
Proof.
    intros.
    try lia.
    try nia.
Qed.    
