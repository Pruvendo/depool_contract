(*this file should be moved to FinProof common scope*)
Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.
Require Import Psatz.
Require Import Setoid.
Require Import Unicode.Utf8.

Require Import Lists.List.
Import ListNotations.

Require Import FinProof.Lists.
Require Import FinProof.Common.
Require Import FinProof.CommonInstances.
Require Import FinProof.CommonProofs.
Require Import ZArith.

Require Import depoolContract.SolidityNotations.
Require Import depoolContract.ProofEnvironment.

Require Import depoolContract.Lib.Tactics.

(* Module SolidityNotations := SolidityNotations XTypesSig StateMonadSig. *)
Import SolidityNotations.

Local Open Scope solidity_scope.
Local Open Scope list_scope.

Set Typeclasses Iterative Deepening.

Set Typeclasses Depth 100.

Existing Instance bfr.
Existing Instance ifr.
Existing Instance lfr.
Existing Instance pfr.
Existing Instance hmfr.

Fixpoint indexate' {X} (n:Z) (l: list X) :=
match l with
| [ ] => [ ]
| x :: xs => (n, x) :: (indexate' (n + 1)%Z xs)
end.

Definition indexate {X} := indexate' (X:=X) 0.
 
Lemma xHMapKeysSnoc: forall K V (m: listPair K V) x, xHMapKeys (m ++ [x]) = xHMapKeys m ++ [fst x].
Proof.
 intros. induction m.
 simpl. auto.
 simpl. simpl in IHm. rewrite IHm.
 auto.
Qed.

Fixpoint take {X} (n:nat) (l: list X) :=
match n, l with
| O,_ => [ ]
| _, [ ] => [ ]
| S n', x::xs => x::(take n' xs)
end.
 
Lemma takeMore: forall X n (l: list X),
(n >= length l)%nat ->
take n l = l.
Proof.
 intros. generalize dependent n.
 induction l. intros. destruct n; auto.
 intros. destruct n. inversion H.
 simpl. rewrite IHl. auto. simpl in H. 
lia.
Qed.


Lemma takeNil: forall X n,
 take n (@nil X) = [ ].
 Proof.
 intros. destruct n.
 simpl. auto.
 simpl. auto.
Qed.
 

Require Import omega.Omega.


Lemma takeLength: forall X n (l: list X),
(n>=0)%Z -> 
(n<=xListLength l)%Z ->
xListLength  (take (Z.to_nat n) l) = n.
Proof.
 intros. generalize  dependent n.
 induction l; intros.
 simpl. rewrite takeNil.
 simpl. simpl  in H0. lia. (*lia. *)
 destruct n.
 simpl. auto.
 remember (Z.pos p - 1)%Z.
 assert  (Z.to_nat (Z.pos p) = S (Z.to_nat z) ).
 replace z with (Z.pred (Z.pos p)); try lia.
(*  rewrite Z2Nat.inj_pred.
 rewrite Nat.succ_pred_pos. auto. 
 rewrite Z2Nat.inj_pos. 
 apply (Pos2Nat.is_pos p). *)
 rewrite H1.
 Opaque xListLength.
 simpl. Transparent  xListLength.
 unfoldList xListLength.
 Opaque Z.of_nat.
 simpl.  rewrite Nat2Z.inj_succ.
 setoid_rewrite IHl. lia.
 rewrite Heqz.
 remember (Pos2Z.is_pos p).
 lia.
 rewrite Heqz. simpl in  H0.
 rewrite Nat2Z.inj_succ in H0.
 unfoldList  xListLength.
 lia. 
 remember (Zlt_neg_0 p). lia. 
Qed.

Transparent Z.of_nat.
 
Lemma takeLess: forall X n (l l': list X), n <= length l ->
take n l = take n (l ++ l'). 
Proof.
 intros. generalize dependent l. generalize dependent l'.
 induction n; intros.
 simpl. auto.
 simpl. destruct l.
 destruct l'.
 simpl. auto.
 simpl. inversion  H.
 simpl. rewrite IHn with (l':=l').
 auto. simpl in H. lia.
 Qed.

Fixpoint dropWhile {X} (bf: X -> bool) (l: list X) :=
match l with
| [ ] => [ ]
| x::xs => if (bf x) then dropWhile bf xs else xs
end.

Fixpoint takeWhile {X} (bf: X -> bool) (l: list X) :=
match l with
| [ ] => [ ]
| x::xs => if (bf x) then x::(takeWhile bf xs) else [ ]
end.

Import List.
Local Open Scope Z_scope.

Definition keysFactorization {K V} (m: listPair K V) := 
forall p1 p2, In p1 m -> In p2 m -> fst p1 = fst p2 -> p1 = p2.

Inductive keysDistinct {K V} : listPair K V -> Prop :=
| distinct_nil : keysDistinct xHMapEmpty
| distinct_cons : forall k v m, keysDistinct m -> Forall (fun x => x<>k ) (xHMapKeys m) -> keysDistinct ((k,v)::m).
 
Lemma keysDistinct_In_False: forall K V a (m: listPair K V) p , 
keysDistinct (a :: m) -> In p m -> fst a = fst p -> False.
Proof.
 intros.
 induction m.
 inversion H0.
 inversion H0.
 inversion H.
 inversion H5.
 inversion H6.
 destruct a. destruct p. destruct a0.
 inversion H2. simpl in H13. inversion H7.
 simpl in *.
 subst. inversion H3. apply H13. auto.
 apply IHm. destruct a.
 constructor.
 inversion H. inversion H5. auto.
 inversion H. inversion H7. auto.
 auto.
Qed. 


Lemma distinctFactorization: forall K V (m: listPair K V), keysDistinct m -> keysFactorization m.
Proof.
 intros.
 induction m.
 unfold keysFactorization.
 intros.
 inversion H0.
 unfold keysFactorization.
 intros.
 inversion H0.
 inversion H1.
 inversion H.
 congruence.
 inversion H.
 exfalso.
 apply keysDistinct_In_False with (m:=m) (a:=a) (p:=p2); auto.
 rewrite <- H2.
 rewrite H3. auto.
 inversion H1.
 exfalso.
 apply keysDistinct_In_False with (m:=m) (a:=a) (p:=p1); auto.
 rewrite H2.
 rewrite H4. auto.
 assert ( keysFactorization m).
 apply IHm.
 inversion H. auto.
 unfold keysFactorization in H5.
 apply H5; auto.
Qed. 


Lemma sublist_cons: forall X (x:X) l l', sublist l l' -> sublist l (x::l').
Proof.
  intros.
  generalize dependent x.
  generalize dependent l'.
  induction l; intros.
  simpl. constructor.
  constructor.
  simpl. right.
  apply (inlist_trans (l':=a::l)). simpl. left.  auto. auto.
  apply IHl.
  inversion H. auto.
Qed.


Lemma delete_sub: forall V (m: listPair Z V) k,
sublist (xHMapKeys (deleteListPair Z.eqb k m)) (xHMapKeys m).
Proof.
 intros.
 induction m.
 simpl. constructor.
 simpl.
 destruct a.
 remember (k=?z).
 destruct b. simpl.
 apply sublist_cons.
 auto.
 simpl.
 constructor. simpl. left. auto. 
 simpl. apply Forall_oright.
 auto.
Qed.


Lemma deleteDistinct: forall V (m: listPair Z V) k, 
keysDistinct m ->
keysDistinct (deleteListPair Z.eqb k m).
Proof.
 intros.
 induction m.
 simpl. constructor.
 simpl. destruct a.
 remember (k =? z).
 destruct b.
 apply IHm.
 inversion H. auto.
 constructor.
 apply IHm.
 inversion H. auto.
 inversion H.
 apply (Forall_sub (l':=xHMapKeys m)); auto.
 apply delete_sub.
 Qed.

Lemma bInFalse: forall id l,
false = bIn eqb id l ->
Forall (λ x0 : Z, x0 ≠ id) l.
Proof.
intros.
induction l.
constructor.
constructor. 
simpl in H.
symmetry in H.
apply Bool.orb_false_iff in H.
inversion H.
apply Z.eqb_neq in H0. auto. 
apply IHl.
simpl in H.
symmetry in H.
apply Bool.orb_false_iff in H.
inversion H.
apply Z.eqb_neq in H0. auto. 
Qed.

Lemma filter_nil_Forall: forall X id (txs : listPair Z X),
filter (fun p => id =? fst p) txs = [ ] ->
Forall (fun x => x <> id) (map fst txs).
Proof.
intros.
induction txs.
constructor.
simpl.
constructor.
simpl in H.
remember (id =? fst a) as b.
destruct b.
inversion H.
apply Z.eqb_neq.
symmetry.
rewrite Z.eqb_sym.
auto.
apply IHtxs.
simpl in H.
remember (id =? fst a) as b.
destruct b.
inversion H.
auto.
Qed.

Lemma Forall_bIn_false: forall l z,
Forall (fun x : Z => x <> z) l ->
bIn Z.eqb z l = false.
Proof.
 intros.
 induction l.
 auto.
 inversion H.
 simpl.
 replace ((a =? z)) with false.
 apply IHl. auto.
 symmetry.
 apply Z.eqb_neq.
 unfold not.
 intros.
 apply H2.
 auto.
Qed. 

Lemma split_map: forall X Y (l: list (X*Y)%type),
fst (split l) = map fst l.
Proof.
intros.
induction l.
auto.
simpl.
destruct a.
remember ( split l ).
destruct p.
simpl.
rewrite <- IHl.
auto.
Qed.

Lemma adjustKeysEqual: forall V x m id,
xHMapKeys (adjustListPair Z.eqb (λ _ : V, x) id m) = xHMapKeys m.
Proof.
intros.
induction m.
simpl. auto.
simpl.
destruct a.
remember (id =? z) as b.
destruct b. simpl.
setoid_rewrite IHm.
symmetry in Heqb.
apply Z.eqb_eq in Heqb.
rewrite Heqb. auto.
simpl.
setoid_rewrite IHm.
auto.
Qed.

Lemma adjustDistinct: forall V (m: listPair Z V) (x: V) (id: Z) ,

keysDistinct m -> keysDistinct (adjustListPair Z.eqb (λ _ : V, x) id m).
Proof.

intros.
induction m.
intros.
constructor.
simpl.
destruct a.
remember (id =? z) as b.
destruct b.
constructor. apply IHm. inversion H. auto.
assert (keysDistinct (adjustListPair Z.eqb (λ _ : V, x) id m)).
apply IHm. inversion H. auto.
rewrite adjustKeysEqual.
inversion H. 
symmetry in Heqb.
apply Z.eqb_eq in Heqb.
rewrite Heqb. auto.

constructor.
apply IHm.  inversion H. auto.
rewrite adjustKeysEqual.
inversion H.
auto.
Qed. 


 Lemma insertDistinct: forall V (m m': listPair Z V) (x: V) (id: Z) ,

 m' =   m [id] ← x  ->
keysDistinct m -> keysDistinct m'.
Proof.
intros.
generalize dependent m'.
induction m.
intros.
rewrite H. simpl. unfold Datatypes.id. constructor. auto.
constructor.
intros.
rewrite H. unfold hmapInsert. unfoldBool xBoolIfElse.
unfold hmapIsMember.
remember ( xListIn eqb id (xHMapKeys (a :: m))) as b.
destruct b.
all: cycle 1.
unfoldHMap xHMapFromList.
unfoldList xListCons.
unfoldHMap xHMapToList.
unfold Datatypes.id.
constructor. auto.
unfoldList xListIn in Heqb.
apply bInFalse. auto.

unfoldHMap xHMapAdjust.
simpl.
destruct a.
simpl in Heqb.
remember (z =? id) as b.
destruct b.
rewrite Z.eqb_sym.
rewrite <- Heqb0.
constructor.
apply adjustDistinct.
inversion H0. auto.
rewrite adjustKeysEqual.
inversion H0.
symmetry in Heqb0.
apply Z.eqb_eq in Heqb0.
rewrite <- Heqb0.
auto.

rewrite Z.eqb_sym.
rewrite <- Heqb0.
constructor.
apply adjustDistinct.
inversion H0. auto.

assert (keysDistinct (m [id]← x) ).
apply IHm.
inversion H0. auto.
auto.

unfoldHMap hmapInsert in H1.
unfoldHMap hmapIsMember in H1.
unfoldBool xBoolIfElse in H1.
unfoldHMap xHMapAdjust  in H1.
unfoldHMap xHMapFromList  in H1.
unfoldList xListCons in H1.
unfold  Datatypes.id in H1.
unfoldList xListIn in H1.
simpl in Heqb.
setoid_rewrite <- Heqb in H1.
inversion H0.
rewrite adjustKeysEqual.
auto.
Qed.

Lemma keysFactorization_cons: forall X x (m:listPair Z X),
keysFactorization (x::m) -> keysFactorization m.
Proof.
  intros.
  unfold keysFactorization.
  intros.
  unfold keysFactorization in H.
  apply H; auto.
  simpl. right. auto.
  simpl. right. auto.
Qed.

Lemma fetch_old_fetch_some: forall K V`{XBoolEquable bool K}`{XDefault V} (m: listPair K V) k x,
hmapFetch m k = (true, x) <-> hmapFetchM m k = Some x .
Proof.
  intros.
  split; intros.
  unfold hmapFetchM.
  unfold hmapFetch in H1.
  remember (m [k] ?).
  setoid_rewrite <- Heqy.
  setoid_rewrite <- Heqy in H1.
  destruct y.
  simpl in H1.
  inversion H1. auto.
  simpl in H1. inversion H1.
  (*********)
  unfold hmapFetchM in H1.
  unfold hmapFetch.
  remember (m [k] ?).
  setoid_rewrite <- Heqy.
  setoid_rewrite <- Heqy in H1.
  rewrite H1. simpl. auto.
Qed.

Lemma fetch_old_fetch_none: forall K V`{XBoolEquable bool K}`{XDefault V} (m: listPair K V) k,
hmapFetch m k = (false, default) <-> hmapFetchM m k = None .
Proof.
  intros.
  split; intros.
  unfold hmapFetchM.
  unfold hmapFetch in H1.
  remember (m [k] ?).
  setoid_rewrite <- Heqy in H1.
  setoid_rewrite <- Heqy.
  destruct y.
  simpl in H1. inversion H1.
  auto.
  (*******************)
  unfold hmapFetchM in H1.
  unfold hmapFetch.
  remember (m [k] ?).
  rewrite H1.
  simpl.
  auto.
Qed.  

Lemma fetch_lookup: forall K V`{XBoolEquable bool K}`{XDefault V} (m: listPair K V) k,
hmapFetchM m k = m [ k ] ? .
Proof.
  intros.
  unfold hmapFetchM.
  auto.
Qed.  

Lemma fetchIn: forall X`{XDefault X} (m:listPair Z X) k, 
true = fst (hmapFetch m  k) ->
In (k, snd (hmapFetch m  k)) m.
Proof.
 intros.
 induction m.
 discriminate.
 unfold hmapFetch in H0.
 simpl in H0.
 remember (k =? fst a).
 destruct b.
 simpl in H0.
 unfold hmapFetch.
 simpl.
 rewrite<- Heqb.
 simpl.
 left.
 destruct a.
 simpl. simpl in Heqb.
 symmetry in Heqb. apply Z.eqb_eq in Heqb.
 congruence. apply IHm in H0.
 unfold hmapFetch.
 simpl.
 rewrite <- Heqb.
 right.
 auto.
Qed.

Lemma fetch_cons_false: forall X`{XDefault X} (m:listPair Z X) k t,
keysDistinct ((k, t) :: m) ->
false = fst (hmapFetch m k).
Proof.
 intros.
 generalize dependent t.
 induction m; intros.
 auto.
 unfold hmapFetch.
 simpl.
 remember (k =? fst a).
 destruct b.
 simpl.
 destruct a.
 simpl in Heqb.
 symmetry in Heqb.
 apply Z.eqb_eq in Heqb.
 rewrite Heqb in H0.
 exfalso.
 inversion H0.
 inversion H5.
 apply H8. auto.
 apply IHm with (t:=t).
 constructor.
 inversion H0.
 inversion H3.
 auto.
 inversion H0.
 inversion H5.
 auto.
Qed. 

(* Compute ([ (1,1), (2,2) ] ->next 1). *)

(* Compute (listIndexFirstLast' false 100 Z.eqb 2 ([ (2) , (2) , (2) , (2), (2) , (8), (0)  ])%list ). *)

Lemma listIndexFirstLast_n: forall b n k l z,
listIndexFirstLast' b n Z.eqb k l = Some z ->
z >= n - 1.
Proof.
 intros.
 generalize dependent z.
 generalize dependent n.
 generalize dependent b.
 induction l; intros.
 simpl in H.
 destruct b.
 inversion H.
 lia.
 inversion H.
 simpl in H.
 remember (a=?k).
 destruct b0.
 apply IHl in H.
 lia.
 destruct b.
 inversion H.
 lia.
 apply IHl in H.
 lia.
Qed.


Lemma to_nat0: forall z, Z.to_nat z = 0%nat -> z <= 0.
Proof.
 intros.
 destruct z. lia.
 rewrite Z2Nat.inj_pos in H.
 remember (Pos2Nat.is_pos p).
 lia.
 lia.
Qed.


Lemma listIndexFirstLast_Some: forall b n k k1 z l,  
n >= 0 ->
listIndexFirstLast' b n Z.eqb k l = Some z ->
nth_error l (Z.to_nat (z - n + 1)) = Some k1 ->
k1 <> k. 
Proof.
  intros.
  generalize dependent b.
  generalize dependent z.
  generalize dependent n.
  generalize dependent k1.
  induction l; intros.
  apply listIndexFirstLast_n in H0.
  remember (Z.to_nat (z - n + 1)).
  destruct n0; discriminate.
  remember H0.
  clear Heqe.
  apply listIndexFirstLast_n in e.
  remember (Z.to_nat (z - n + 1)).
  destruct n0.
  simpl in H1.
  simpl in H0.
  remember (a =? k).
  destruct b0.
  symmetry in Heqb0.
  apply Z.eqb_eq in Heqb0.
  apply listIndexFirstLast_n in H0.
  enough (z <= n - 1).
  lia.
  symmetry in Heqn0. apply to_nat0 in Heqn0.
  lia.
  destruct b.
  symmetry in Heqn0. apply to_nat0 in Heqn0.
  symmetry in Heqb0.
  apply Z.eqb_neq in Heqb0.
  inversion H1. lia.
  symmetry in Heqn0. apply to_nat0 in Heqn0.
  symmetry in Heqb0.
  apply Z.eqb_neq in Heqb0.
  inversion H1. lia.
  simpl in H1.
  simpl in H0.
  remember (a =? k).
  destruct b0.
  apply IHl  with (k1:=k1) in H0.
  auto.
  lia.
  rewrite  <- H1.
  replace n0 with (Z.to_nat (z - (n + 1) + 1)).
  auto.
  enough (n0 = Z.to_nat (z-n)).
  rewrite H2.
  lia.
  replace (z-n+1) with (Z.succ (z-n)) in Heqn0; try lia.
  destruct b.
  inversion H0.
  rewrite <- H3 in Heqn0.
  lia.
  apply IHl  with (k1:=k1) in H0.
  auto.
  lia.
  rewrite <- H1.
  replace n0 with (Z.to_nat (z - (n + 1) + 1)).
  auto.
  lia.
Qed.

Lemma nth_error_map_Some: forall X Y k (l:list X) x (f:X->Y), 
nth_error l k = Some x ->
nth_error (map f l) k = Some (f x).
Proof.
 intros.
 generalize dependent k.
 induction l; intros.
 destruct k; discriminate.
 destruct k.
 simpl. simpl in H.
 inversion H. auto.
 simpl in H.
 simpl.
 apply IHl. auto.
Qed. 

Lemma next_old_next_some: forall K V`{XBoolEquable bool K}`{XDefault V}`{XDefault K} (m: listPair K V) k p,
hmapNext m k = (p, true) <-> hmapNextM m k = Some p.
Proof.
  intros.
  split; intros.
  unfold hmapNextM.
  unfold hmapNext in H2.
  remember (xListIndexFirstLast eqb k (xHMapKeys m)).
  setoid_rewrite <- Heqy.
  setoid_rewrite <- Heqy in H2.
  destruct y.
  simpl in H2.
  simpl.
  remember (nth_error (Datatypes.id m) (Z.to_nat (z + 1))).
  setoid_rewrite <- Heqo.
  setoid_rewrite <- Heqo in H2.
  destruct o.
  simpl in H2.
  inversion H2.
  auto.
  simpl in H2. inversion H2.
  simpl.
  simpl in H2. inversion H2.
  (******************)
  unfold hmapNextM in H2.
  unfold hmapNext.
  remember (xListIndexFirstLast eqb k (xHMapKeys m)).
  setoid_rewrite <- Heqy.
  setoid_rewrite <- Heqy in H2.
  destruct y.
  simpl.
  simpl in H2.
  remember (nth_error (Datatypes.id m) (Z.to_nat (z + 1))).
  setoid_rewrite <- Heqo.
  setoid_rewrite <- Heqo in H2.
  destruct o.
  simpl.
  inversion H2.
  auto.
  discriminate.
  simpl in H2.
  discriminate.
Qed.

Lemma next_old_next_none: forall K V`{XBoolEquable bool K}`{XDefault V}`{XDefault K} (m: listPair K V) k (p: K*V),
hmapNext m k = (default, false) <-> hmapNextM m k = None.
Proof.
  intros.
  split; intros.
  unfold hmapNextM.
  unfold hmapNext in H2.
  remember (xListIndexFirstLast eqb k (xHMapKeys m)).
  setoid_rewrite <- Heqy.
  setoid_rewrite <- Heqy in H2.
  destruct y.
  simpl.
  simpl in H2.
  remember (nth_error (Datatypes.id m) (Z.to_nat (z + 1))).
  setoid_rewrite <- Heqo.
  setoid_rewrite <- Heqo in H2.
  destruct o.
  simpl in H2.
  inversion H2.
  auto.
  simpl.
  auto.
  (************)
  unfold hmapNextM in H2.
  unfold hmapNext.
  remember (xListIndexFirstLast eqb k (xHMapKeys m)).
  setoid_rewrite <- Heqy.
  setoid_rewrite <- Heqy in H2.
  destruct y.
  simpl in H2.
  simpl.
  remember (nth_error (Datatypes.id m) (Z.to_nat (z + 1))).
  setoid_rewrite <- Heqo.
  setoid_rewrite <- Heqo in H2.
  destruct o.
  discriminate.
  simpl.
  auto.
  simpl.
  auto.
Qed.

Lemma nextNotThis: forall V`{XDefault V} k (m: listPair Z V),
snd (hmapNext m  k) = true -> k <> fst (fst (hmapNext m  k)).
Proof.
 intros.
 unfold hmapNext in *.
 simpl in *.
 unfold Datatypes.id in *.
 unfold listIndexFirstLast in *.
 remember ((listIndexFirstLast' false 0 Z.eqb k (map fst m)) ).
 destruct o.
 all: cycle 1.
 simpl in H0. discriminate.
 simpl in H0.
 simpl.
 remember (nth_error m (Z.to_nat (z + 1))).
 setoid_rewrite <- Heqo0.
 setoid_rewrite <- Heqo0 in H0.
 destruct o.
 all: cycle 1.
 simpl in H0. discriminate.
 simpl.
 simpl in H0.
 symmetry in Heqo.
 apply listIndexFirstLast_Some with (k1:=fst p) in Heqo.
 lia. lia.
 symmetry in Heqo0.
 apply nth_error_map_Some with (f:=fst) in Heqo0.
 replace (z-0+1) with (z+1); try lia. auto.
Qed. 

(* (*not used*) (*BAD*) Axiom dropNext: forall X`{XDefault X} (l1 l2: list Z) (trans: listPair Z X) t' t, 
 t' = fst (fst (trans ->next t)) ->
 l1 = dropWhile (fun id : Z => negb (id =? t')%Z) (map fst trans) -> 
 l2 = dropWhile (fun id : Z => negb (id =? t )%Z) (map fst trans) -> 
 t' :: l1 = l2.

(*not used*) (*BAD*) Axiom nextFalseDrop: forall X`{XDefault X} (trans: listPair Z X) t, 
snd (trans ->next t) = false ->
(dropWhile (fun id : Z => negb (id =? t)) (map fst trans)) = [ ].

(*not used*) (*BAD*) Axiom nextFalseDefault: forall X`{XDefault X} (trans: listPair Z X) t, 
snd (trans ->next t) = false ->
fst (fst (trans ->next t)) = default.

(*not used*) (*BAD*) Axiom dropMin: forall X`{XDefault X} (trans: listPair Z X) min trId,
min = trans ->min ->
snd min = true ->
trId = fst (fst min) ->
dropWhile (fun id => negb (Z.eqb id trId)) (map fst trans) = tl (map fst trans). *)

Lemma deleteNonExisting: forall V`{XDefault V} k (m: listPair Z V),
fst (hmapFetch m k) = false ->
deleteListPair Z.eqb k m = m.
Proof.
  intros.
  induction m.
  simpl. auto.
  simpl.
  destruct a.
  remember (k =? z).
  unfold hmapFetch in H0.
  simpl in H0.
  setoid_rewrite <- Heqb in H0.
  destruct b.
  simpl in H0.
  discriminate.
  rewrite IHm.
  auto.
  auto.
Qed.


Lemma deleteFetch_false: forall V`{XDefault V} k (m: listPair Z V), 
fst (hmapFetch (deleteListPair Z.eqb k m) k) = false.
Proof.
 intros.
 induction m.
 compute. auto.
 simpl. destruct a.
 remember (k =? z).
 destruct b.
 auto.
 unfold hmapFetch.
 simpl.
 rewrite <- Heqb.
 auto.
Qed.

Lemma deleteLookup_None: forall V k (m: listPair Z V), 
hmapLookup Z.eqb k (deleteListPair Z.eqb k m) = None.
Proof.
 intros.
 induction m.
 compute. auto.
 simpl. destruct a.
 remember (k =? z).
 destruct b.
 auto.
 simpl.
 rewrite <- Heqb.
 auto.
Qed.

Lemma hmapMinFetch: forall V`{XDefault V} (m: listPair Z V), 
snd (hmapMin m) = true ->
hmapFetch m  (fst (fst (hmapMin m))) = (true, snd (fst (hmapMin m))).
Proof.
 intros.
 unfold hmapMin.
 unfold hmapMin in H0.
 simpl in H0.
 destruct m.
 simpl in H0.
 discriminate.
 simpl in H0.
 simpl.
 unfold hmapFetch.
 simpl.
 rewrite Z.eqb_refl.
 simpl.
 auto.
Qed. 

Lemma nthIn: forall X m k (x:X),  nth_error m k = Some x -> In x m. 
Proof.
 intros.
 generalize dependent k.
 induction m; intros.
 destruct k; discriminate.
 destruct k.
 simpl in H.
 inversion H.
 constructor. auto.
 simpl in H.
 apply IHm in H.
 simpl. right. auto.
Qed.

Lemma nthFilter_true: forall V k p m, 
keysFactorization m ->
Some p = nth_error m k ->
(hd_error (map snd (filter (fun p0 : (Z * V)%type => fst p =? fst p0) m))) = Some (snd p).
Proof.
  intros.
  generalize dependent k.
  induction m.
  intros.
  simpl. destruct k. discriminate. discriminate.
  intros.
  simpl.
  remember (fst p =? fst a).
  destruct b.
  symmetry in Heqb.
  apply Z.eqb_eq in Heqb.
  simpl.

  apply H in Heqb.

  rewrite Heqb. auto.
  symmetry in H0.
  apply nthIn in H0.
  auto.
  constructor. auto.
  destruct k.
  simpl in H0.
  inversion H0.
  rewrite H2 in Heqb.
  rewrite Z.eqb_refl in Heqb.
  discriminate.
  apply IHm with (k:=k).
  apply keysFactorization_cons with (x:=a); auto.
  simpl in H0. auto.
Qed.
 
(* Print hmapNext. *)

Lemma hmapNextFetch: forall V`{XDefault V} (m: listPair Z V) k, 
keysFactorization m ->
snd (hmapNext m k) = true ->
hmapFetch m (fst (fst (hmapNext m k))) = (true, snd (fst (hmapNext m k))).
Proof.
 intros.
 unfold hmapFetch.
 unfold hmapNext.
 unfold hmapNext in H1.
 remember ((xListIndexFirstLast eqb k (xHMapKeys m))).
 setoid_rewrite <- Heqy.
 destruct y.
 simpl in H1.
 setoid_rewrite <- Heqy in H1.
 simpl in H1.
 unfold Datatypes.id in H1.
 remember ((nth_error m (Z.to_nat (z + 1)))).
 setoid_rewrite <- Heqo in H1.
 simpl. unfold Datatypes.id.
 match goal with
 | |- ?G => match G with
            | context [optionMapDefault _ ?x _] => remember x
            end
 end.
 symmetry.
 match goal with
 | |- ?G => match G with
            | context [optionMapDefault _ ?x _] => remember x
            end
 end.
 setoid_rewrite <- Heqo in Heqo1.  
 rewrite Heqo0.
 rewrite Heqo1.
 destruct o.
 simpl in H1.
 simpl.
 rewrite nthFilter_true with (k:=Z.to_nat (z + 1)); auto.
 simpl in H1. discriminate.
 simpl in H1.
 setoid_rewrite <- Heqy in H1.
 simpl in H1.
 discriminate.
Qed. 

(* (*not used*) (*BAD*) Axiom deleteMinNext: forall X`{XDefault X} (k: Z) (v: X) (m: listPair Z X), 
m ->min = (k, v, true) ->
m ->next k = (deleteListPair Z.eqb k m) ->min. *)


Lemma deleteFetch_another: forall V`{XDefault V} (k z:Z) (m: listPair Z V),
k <> z -> 
hmapFetch  (deleteListPair Z.eqb k m)  z = hmapFetch m  z.
Proof.
 intros.
 induction m.
 compute. auto.
 simpl.
 destruct a.
 remember (k=?z0).
 destruct b.
 unfold hmapFetch.
 simpl.
 replace (z=?z0) with false.
 setoid_rewrite IHm. auto.
 symmetry in Heqb.
 apply Z.eqb_eq in Heqb.
 symmetry.
 apply Z.eqb_neq.
 lia.
 unfold hmapFetch.
 simpl.
 remember (z =? z0).
 destruct b.
 simpl. auto.
 auto.
Qed.

Lemma deleteFetchNext: forall V`{XDefault V} k (m: listPair Z V),
snd (hmapNext m  k) = true ->
hmapFetch (deleteListPair Z.eqb k m)  (fst (fst (hmapNext m k))) = 
hmapFetch m  (fst (fst (hmapNext m k))).
Proof.
 intros.
 remember (fst (fst (hmapNext m k))).
 apply nextNotThis in H0.
 rewrite <- Heqz in H0.
 apply deleteFetch_another; auto.
Qed.

Lemma deleteNotExisting: forall X`{XDefault X} k (m: listPair Z X), 
fst (hmapFetch m k) = false ->
deleteListPair Z.eqb k m = m.
Proof.
 intros.
 induction m.
 auto.
 unfold hmapFetch in H0.
 simpl in H0.
 remember (k =? fst a).
 destruct b.
 simpl in H0. discriminate.
 simpl.
 destruct a.
 simpl in Heqb.
 rewrite <- Heqb.
 rewrite IHm; auto.
Qed. 
 

Definition subMap {V} (m1 m2: XHMap Z V) :=
forall x id, hmapLookup Z.eqb id m1 = Some x -> 
             hmapLookup Z.eqb id m2 = Some x.

Lemma subMapRefl : forall V m, subMap (V:=V) m m.
Proof.
  intros.
  unfold subMap.
  intros.
  auto.   
Qed.

Lemma subMapTrans : forall V m1 m2 m3, subMap (V:=V) m1 m2 -> subMap (V:=V) m2 m3 -> subMap (V:=V) m1 m3.
Proof.
 intros.
 unfold subMap. intros.
 apply H in H1.
 apply H0 in H1.
 auto. 
Qed.

Lemma subMapDelete : forall V id m, subMap (V:=V) (deleteListPair Z.eqb id m) m.
Proof.
 intros.
 unfold subMap.
 intros.
 generalize dependent x.
 induction m; intros.
 simpl in H. discriminate.
 simpl in H. destruct a.
 remember (id =? z).
 destruct b.
 simpl.
 remember (id0 =? z).
 destruct b.
 simpl.
 symmetry in Heqb. symmetry in Heqb0.
 apply Z.eqb_eq in Heqb.
 apply Z.eqb_eq in Heqb0.
 rewrite Heqb in H.
 rewrite Heqb0 in H.
 setoid_rewrite deleteLookup_None in H. discriminate.
 apply IHm. auto.
 simpl.
 simpl in H.
 remember (id0 =? z).
 destruct b.
 simpl.
 simpl in H. auto.
 apply IHm. auto.
Qed.

Lemma fetchLookupFst: forall V`{XDefault V} m id,
fst (hmapFetch m  id) = true <->
exists (x: V), hmapLookup Z.eqb id m = Some x.
Proof.
 intros.
 split; intros.
 unfold hmapFetch in H0.
 remember (m [id] ?).
 destruct y.
 exists v.
 auto. simpl in H0. discriminate.
 inversion H0.
 unfold hmapFetch.
 remember (m [id] ?).
 setoid_rewrite H1 in Heqy.
 rewrite Heqy. simpl.
 auto.
Qed. 

Lemma fetchLookupSnd: forall V`{XDefault V} m id (x:V),
hmapLookup Z.eqb id m = Some x ->
snd (hmapFetch m  id) = x.
Proof.
 intros.
 unfold hmapFetch.
 remember (m [id] ?).
 setoid_rewrite H0 in Heqy.
 rewrite Heqy. simpl.
 auto.
Qed.

Lemma fetchLookupFull: forall V`{XDefault V} m id x,
fst (hmapFetch m  id) = true ->
snd (hmapFetch m  id) = x ->
hmapLookup Z.eqb id m = Some x.
Proof.
intros.
 apply fetchLookupFst in H0.
 inversion H0.
 rewrite H2.
 unfold hmapFetch in H1.
 setoid_rewrite H2 in H1.
 simpl in H1.
 congruence.
Qed. 

Lemma fetchLookup: forall V`{XDefault V} m id x,
hmapFetch m  id = (true, x) <->
hmapLookup Z.eqb id m = Some x.
Proof.
intros. split.
intros.
apply fetchLookupFull with (H:=H).
rewrite H0. auto.
rewrite H0. auto.
intros.
remember H0. clear Heqe.
apply fetchLookupSnd with (H:=H) in e.
remember (hmapFetch m  id).
destruct x0.
simpl in e.
rewrite e.
cut (x0 = true). 
intros.
rewrite H1.
auto.
replace x0 with (fst (hmapFetch m  id) ).
apply fetchLookupFst.
exists x. auto.
rewrite <- Heqx0.
auto.
Qed.

Lemma subMap_fetch_true: forall {V}`{XDefault V} (m1 m2: XHMap Z V) id,
fst (hmapFetch m1  id) = true ->
subMap m1 m2 ->
fst (hmapFetch m2  id) = true.
Proof.
 intros.
 apply fetchLookupFst  in  H0.
 inversion_clear H0.
 apply H1 in  H2.
 apply fetchLookupFst.
 exists x.
 auto.
Qed.

Lemma hmapLookup_bIn: forall X`{XBoolEquable bool X}`{boolEquivalence eqb} x k (m: listPair Z X),
hmapLookup Z.eqb k m = Some x ->
bIn eqb x (xHMapElems m) = true.
Proof.
 intros.
 generalize  dependent  x.
 induction  m;  intros.
 inversion H0.
 simpl in H0.
 remember  (k =? fst a).
 destruct b.
 simpl in H0.
 simpl.
 apply Bool.orb_true_intro.
 left.
 inversion H0.
 apply boolEquivalence0. auto.
 apply IHm in H0.
 simpl.
 apply Bool.orb_true_intro.
 right.
 apply  H0.
Qed.

Lemma hmapLookup_In: forall X id (m: listPair Z X) x,
hmapLookup Z.eqb id m = Some x ->
In (id, x) m.
Proof.
 intros.
 induction  m.
 simpl  in H. discriminate.
 simpl in H.
 remember (id  =? fst a).
 destruct b.
 simpl  in H.
 symmetry in Heqb.
 apply  Z.eqb_eq in Heqb.
 simpl.  left.
 destruct a.
 simpl  in Heqb.
 inversion H.
 rewrite Heqb.
 auto.
 simpl.
 right.
 apply IHm.
 auto. 
Qed.

Lemma subMap_cons: forall X (m1 m2: listPair Z X) x,
 keysFactorization (x::m1) ->
 subMap (x::m1) m2 -> subMap m1 m2.
 Proof.
  intros.
  unfold  subMap in  H0.
  unfold subMap.
  intros.
  apply  H0.
  unfold keysFactorization in  H.
  simpl.
  remember (id =? fst x).
  destruct b.
  all: cycle 1.
  auto.
  simpl. cut (snd x =  x0).
  intros. congruence.
  cut ((id, snd x) = (id, x0)).
  intros.
  inversion H2.
  auto.
  apply H; auto.
  simpl.
  symmetry in Heqb.
  apply  Z.eqb_eq in  Heqb.
  rewrite Heqb.
  left. destruct x. auto.
  simpl.
  right.
  apply hmapLookup_In.
  auto.
 Qed.
 
 
 Lemma bIn_false_subMap: forall X`{XBoolEquable bool X}`{boolEquivalence eqb} (l l': listPair Z X)  x,
 keysFactorization l' ->
 bIn eqb x (xHMapElems l) = false ->
 subMap l' l ->
 bIn eqb x (xHMapElems l') = false.
 Proof.
  intros.
  generalize dependent l.
  induction l'; intros.
  simpl. auto.
  unfold subMap in H2.
  simpl.
  apply Bool.orb_false_iff.
  split.
  simpl in H2.
  remember (eqb (snd a) x) as b.
  destruct b; auto.
  assert (bIn eqb x (xHMapElems l) = true).
  apply hmapLookup_bIn with (k:=fst a); auto.
  apply  H2.
  rewrite Z.eqb_refl.
  simpl.
  symmetry in Heqb.
  apply boolEquivalence0 in  Heqb.
  congruence.
  rewrite H1 in H3.
  discriminate.
 
  apply IHl' with  (l:=l); auto.
  all:cycle 1.
  apply subMap_cons with (x:=a); auto.
 
  apply keysFactorization_cons in H0; auto.
 Qed.   

Lemma subMap_insert_id: forall {V}`{XDefault V} (m1 m2 m3: XHMap Z V) id id0 x
(keyFact: keysFactorization  m2),
fst (hmapFetch m1  id) = false ->
fst (hmapFetch m3  id) = true -> 
subMap m2 m1 ->
m3 = m2 [id0]← x ->
id0 = id.
Proof.
 intros.
 generalize dependent m3.
 generalize dependent m1.
 induction m2; intros.
 simpl in H3.
 unfold Datatypes.id in H3.
 rews m3 in H1.
 unfold hmapFetch in H1.
 simpl in H1.
 remember (id =? id0).
 destruct b.
 symmetry in Heqb.
 apply Z.eqb_eq in Heqb.
 auto.
 simpl in H1.
 discriminate.
 simpl in H3.
 remember ((fst a =? id0) || bIn Z.eqb id0 (map fst m2))%bool.
 destruct b.
 all: cycle 1.
 unfold Datatypes.id in H3. 
 remember ((id0, x) :: m2) as m2'.
 apply IHm2 with (m1:=m1) (m3:=(id0, x) :: m2); auto.
 apply keysFactorization_cons in keyFact; auto.
 all: cycle 2.
 simpl.
 symmetry in Heqb.
 apply Bool.orb_false_iff in Heqb.
 inversion_clear Heqb.
 rewrite H5. auto.
 all: cycle 2.
 rewrite H3 in  H1.
 unfold hmapFetch in H1.
 simpl in  H1.
 symmetry in Heqb.
 apply Bool.orb_false_iff in Heqb.
 inversion_clear Heqb.
 unfold hmapFetch.
 simpl.
 remember (id =? id0).
 destruct b.
 symmetry in Heqb.
 apply  Z.eqb_eq in Heqb.
 simpl. auto.
 symmetry in Heqb.
 apply  Z.eqb_neq in Heqb.
 remember (id =? fst a).
 destruct b.
 apply Z.eqb_neq in H4.
 symmetry in Heqb0.
 apply Z.eqb_eq in  Heqb0.
 simpl in H1. 
 assert (fst (hmapFetch m1  id) = true).
 apply  (subMap_fetch_true (a::m2)); auto.
 unfold hmapFetch.
 simpl.
 rews id.
 rewrite Z.eqb_refl.
 simpl. auto.
 rewrite H0 in H6.
 discriminate.
 auto.
 all: cycle 1.
 apply  subMap_cons with (x:=a);auto.
 destruct a.
 simpl in Heqb.
 remember (id0 =? z).
 destruct b.
 remember (bIn Z.eqb id0 (map fst m2)).
 destruct b.
 all: cycle 1.
 apply  IHm2 with (m1:=m1) (m3:=(id0, x) :: m2); auto.
 all: cycle 3.
 simpl.
 rewrite <- Heqb1. auto.
 all: cycle 2.
 apply keysFactorization_cons in keyFact; auto.
 apply  subMap_cons with (x:=(z,v));auto.
 unfold  hmapFetch. simpl.
 remember (id =? id0).
 destruct b.
 simpl. auto.
 rews m3  in H1.
 apply fetchLookupFst in H1.
 inversion_clear H1.
 simpl in H4.
 rewrite <- Heqb2 in  H4.
 assert  (isSome (hmapLookup Z.eqb id (adjustListPair Z.eqb (λ _ : V, x) id0 m2)) = true).
 setoid_rewrite H4. auto.
 apply adjustSome in H1.
 remember (hmapLookup Z.eqb id m2).
 destruct y.
 apply fetchLookupFst.
 exists v0. auto.
 simpl in H1. discriminate.
 unfold boolEquivalence.
 intros.
 split; intros;
 apply Z.eqb_eq; auto.
 symmetry in Heqb0.
 remember (z =? id0).
 replace  b with false  in Heqb.
 simpl in Heqb.
 apply  IHm2 with (m1:=m1) (m3:=m2 [id0]← x); auto.
 apply keysFactorization_cons in keyFact; auto.
 apply  subMap_cons with (x:=(z,v));auto.
 rews m3 in H1.
 apply fetchLookupFst in H1.
 inversion_clear H1.
 simpl in  H4.
 remember (id =? z).
 destruct b0.
 symmetry in Heqb2.
 apply Z.eqb_eq in  Heqb2.
 assert (fst (hmapFetch m1 id) = true).
 rews id.
 apply (subMap_fetch_true ((z, v) :: m2)); auto.
 unfold hmapFetch.
 simpl.
 rewrite  Z.eqb_refl.
 simpl. auto.
 rewrite H1 in H0.
 discriminate.
 assert (isSome (hmapLookup Z.eqb id (adjustListPair Z.eqb (λ _ : V, x) id0 m2)) = true).
 setoid_rewrite  H4.
 auto.
 apply fetchLookupFst.
 remember (hmapLookup Z.eqb id m2 [id0]← x).
 destruct y.
 exists v0. auto.
 simpl in Heqy.
 rewrite <- Heqb in Heqy.
 setoid_rewrite <- Heqy in H1.
 simpl in  H1.
 discriminate.
 rews  b.
 symmetry .
 apply Z.eqb_neq.
 unfold not. intros.
 apply Z.eqb_neq in Heqb0.
 apply Heqb0. auto.
 symmetry in Heqb0.
 apply Z.eqb_eq in Heqb0.

 apply  IHm2 with (m1:=m1) (m3:=m2 [id0]← x); auto.
 apply keysFactorization_cons in keyFact; auto.
 apply  subMap_cons with (x:=(z,v));auto.
 rews m3 in H1.
 apply fetchLookupFst in H1.
 inversion_clear H1.
 simpl in  H4. rews id0 in  H4.
 remember (id =? z).
 destruct b.
 symmetry in Heqb2.
 apply Z.eqb_eq in  Heqb2.
 assert (fst (hmapFetch m1 id) = true).
 rews id.
 apply (subMap_fetch_true ((z, v) :: m2)); auto.
 unfold hmapFetch.
 simpl.
 rewrite  Z.eqb_refl.
 simpl. auto.
 rewrite H1 in H0.
 discriminate.
 assert (isSome (hmapLookup Z.eqb id (adjustListPair Z.eqb (λ _ : V, x) z m2)) = true).
 setoid_rewrite  H4.
 auto.
 apply fetchLookupFst.
 remember (hmapLookup Z.eqb id m2 [id0]← x).
 destruct y.
 exists v0. auto.
 simpl in Heqy.
 rews id0 in Heqb.
 rewrite <- Heqb1 in Heqy.
 rews id0 in Heqy.
 setoid_rewrite <- Heqy in H1.
 simpl in  H1.
 discriminate.
Qed. 

Lemma insertFetch: forall V`{XDefault V} (m:listPair  Z V) id x, 
hmapFetch (m [id]← x) id = (true, x).
Proof.
 intros.
 induction m.
 unfold hmapFetch.
 simpl.
 rewrite Z.eqb_refl.
 simpl. auto.
 unfold hmapFetch.
 simpl.
 unfold Datatypes.id.
 remember ((fst a =? id) || bIn Z.eqb id (map fst m))%bool.
 destruct b.
 destruct a.
 remember (id =? z).
 destruct b.
 simpl.
 rewrite Z.eqb_refl. simpl. auto.
 simpl in Heqb.
 replace (z =? id) with false in Heqb.
 simpl in Heqb.
 simpl.
 rewrite <- Heqb0.
 unfold hmapFetch in IHm.
 simpl in IHm.
 unfold Datatypes.id in IHm.
 rewrite <- Heqb in IHm.
 auto.
 symmetry in Heqb0.
 symmetry.
 apply Z.eqb_neq in Heqb0.
 apply Z.eqb_neq.
 unfold not. intros.
 apply Heqb0. auto.
 symmetry in Heqb.
 apply Bool.orb_false_iff in Heqb.
 inversion_clear Heqb.
 simpl.
 rewrite Z.eqb_refl.
 replace (id =? fst a) with false.
 simpl.  auto.
 symmetry.
 apply Z.eqb_neq in H0.
 apply Z.eqb_neq.
 unfold not. intros.
 apply H0. auto.
Qed. 

Lemma adjust_another: forall V (m:listPair Z V) f id0,
false = bIn Z.eqb id0 (map fst m) ->
adjustListPair Z.eqb f id0 m = m.
Proof.
 intros.
 induction m.
 simpl. auto.
 simpl in H.
 symmetry in H.
 apply Bool.orb_false_iff in H.
 inversion_clear H.
 simpl.
 destruct a.
 remember (id0 =? z).
 destruct b. simpl in H0.
 symmetry in Heqb.
 apply Z.eqb_eq in Heqb. rewrite Heqb in H0.
 rewrite Z.eqb_refl in H0.
 discriminate.
 rewrite IHm. auto. auto.
Qed. 


Lemma insertFetch_another: forall V`{XDefault V} (m:listPair Z V) id id0 x,
id0 <> id -> 
hmapFetch (m [id0]← x) id = hmapFetch m id. 
Proof.
 intros.
 induction m.
 simpl.
 unfold hmapFetch.
 simpl.
 replace (id =? id0) with false.
 auto.
 symmetry.
 apply Z.eqb_neq.
 unfold not. intros. apply H0. auto.
 (**********)
 unfold hmapFetch in IHm.
 simpl  in IHm.
 remember (bIn Z.eqb id0 (map fst m)).
 destruct b.
 (*true = bIn Z.eqb id0 (map fst m)*)
 unfold hmapFetch.
 simpl.
 setoid_rewrite <- Heqb.
 remember ((fst a =? id0) || true)%bool.
 replace b with true.
 destruct a. simpl.
 remember (id0 =? z).
 destruct b0.
 replace  (id =? z) with false.
 simpl.
 replace (id =? id0) with false.
 apply IHm.
 symmetry.
 apply Z.eqb_neq.
 unfold not.
 intros.
 apply H0. auto.
 symmetry. apply Z.eqb_neq.
 unfold not.  intros.
 symmetry in Heqb1.
 apply Z.eqb_eq  in Heqb1.
 apply H0.  rewrite Heqb1. rewrite H1. auto.
 remember (id =? z).
 destruct b0.
 unfold Datatypes.id.
 simpl.
 rewrite <- Heqb2. simpl. auto.
 unfold Datatypes.id. simpl.
 rewrite <- Heqb2. apply IHm.
 destruct b; auto.
 destruct (fst a =? id0).
 simpl in  Heqb0. discriminate. simpl in Heqb0. discriminate.
 (*****************)  
 (*false = bIn Z.eqb id0 (map fst m)*)
 unfold Datatypes.id in IHm.
 simpl  in IHm.
 replace (id =? id0) with false in  IHm.
 unfold  hmapFetch.
 simpl.
 rewrite <- Heqb.
 remember (fst a =? id0).
 destruct b.
 simpl. destruct a.
 simpl. simpl in Heqb0.
 replace  ( id0 =? z) with true.
 replace  ( id =? z) with false.
 simpl. replace (id =? id0) with false.
 rewrite adjust_another. auto. auto.
 symmetry. apply Z.eqb_neq.
 unfold not. intros.
 apply H0. auto.
 symmetry.
 symmetry in Heqb0.
 apply Z.eqb_eq in Heqb0.
 rewrite Heqb0.
 apply Z.eqb_neq. unfold not. intros.
 apply H0. auto.
 symmetry. apply Z.eqb_eq.
 symmetry in Heqb0. apply Z.eqb_eq in Heqb0. auto.
 simpl. replace  (id =? id0) with false.
 remember (id =? fst a).
 destruct b.
 auto. auto.
 all: symmetry.
 all: apply Z.eqb_neq.
 all: unfold not.
 all: intros.
 all: apply H0.
 all: auto.
Qed. 



Lemma pairEq: forall X Y (p p' : X*Y), fst p = fst p' ->
                                     snd p = snd p' ->
                                     p = p'.
Proof.
 intros. destruct p. destruct p'.             
 simpl in H. simpl in H0.
 congruence.
Qed. 

(*
Lemma subMap_insert_id: forall {V}`{XDefault V} (m1 m2 m3: XHMap Z V) id id0 x
(keyFact: keysFactorization  m2),
fst (m1 ->fetch id) = false ->
fst (m3 ->fetch id) = true -> 
subMap m2 m1 ->
m3 = m2 [id0]← x ->
id0 = id.
*)
Lemma subMap_insert_id_another: forall {V}`{XDefault V} (m1 m2 m3: XHMap Z V) id id0 x,
fst (hmapFetch m1  id) = true ->
fst (hmapFetch m3  id) = true -> 
subMap m2 m1 ->
m3 = m2 [id0]← x ->
id0 <> id ->
 (hmapFetch m3  id) = (hmapFetch m1  id).
Proof.
 intros.
 rewrite H3.
 rewrite  insertFetch_another; auto.
 assert (fst (hmapFetch m2  id) = true).
 rewrite <- H1.
 rewrite H3.
 rewrite  insertFetch_another; auto.
 apply pairEq.
 rewrite H5. rewrite H0. auto.
 apply fetchLookupFst in H5.
 apply fetchLookupFst in H0.
 inversion_clear H0.
 inversion_clear H5.
 rewrite fetchLookupSnd with (x:=x1); auto.
 rewrite fetchLookupSnd with (x:=x0); auto.
 cut (Some  x1 = Some x0).  intros.
 inversion_clear H5. auto.
 apply H2 in  H0.
 rewrite <- H6.
 rewrite <- H0.
 auto.
Qed. 


Lemma min_old_min_some: forall K V`{XBoolEquable bool K}`{XDefault V}`{XDefault K} (m: listPair K V) p,
hmapMin m = (p, true) <-> hmapMinM m = Some p.
Proof.
  intros.
  split; intros.
  unfold hmapMinM.
  unfold hmapMin in H2.
  remember (xListHead (xHMapToList m)).
  setoid_rewrite <- Heqy.
  setoid_rewrite <- Heqy in H2.
  destruct y.
  simpl in H2.
  destruct p0.
  inversion H2. auto.
  simpl in H2. inversion H2.
  (*******************)
  unfold hmapMinM in H2.
  unfold hmapMin.
  remember (xListHead (xHMapToList m)).
  setoid_rewrite <- Heqy.
  setoid_rewrite <- Heqy in H2.
  destruct y.
  simpl.
  inversion H2.
  destruct p. auto.
  discriminate.
Qed.


Lemma min_old_min_none: forall K V`{XBoolEquable bool K}`{XDefault V}`{XDefault K} (m: listPair K V),
hmapMin m = (default, false) <-> hmapMinM m = None.
Proof.
  intros.
  split; intros.
  unfold hmapMinM.
  unfold hmapMin in H2.
  remember (xListHead (xHMapToList m)).
  setoid_rewrite <- Heqy.
  setoid_rewrite <- Heqy in H2.
  destruct y.
  simpl in H2.
  inversion H2. auto.
  (*******************)
  unfold hmapMinM in H2.
  unfold hmapMin.
  remember (xListHead (xHMapToList m)).
  setoid_rewrite <- Heqy.
  setoid_rewrite <- Heqy in H2.
  destruct y.
  simpl. discriminate. auto.
Qed.


Lemma minPush: forall X`{XDefault X} (trans0 : listPair Z X)
                      (min : Z # X # bool) trId p,
(forall n, n >= (Z.of_nat (Datatypes.length p)) -> bIn Z.eqb n (map fst p) = false) ->
min = hmapMin trans0  ->
true = snd min ->
trId = fst (fst min) ->
fold_left (fun (acc : listPair Z Z) (x : Z) => hmapPush x acc)
   (tl (map fst trans0)) (hmapPush trId p)=
(rev (indexate' (Z.of_nat (length p)) (map fst trans0))) ++ p.
Proof.
 Opaque hmapPush Z.of_nat bIn Z.eqb Z.ge length map.
 induction trans0; intros.
 simpl. compute in H1.
 rewrite H1 in H2. inversion H2.
 simpl.
 destruct trans0.
 simpl.
 Transparent hmapPush.
 unfold  hmapPush. simpl.
 rewrite H0.
 unfold Datatypes.id.
 compute in H1. destruct a.
 rewrite H3. rewrite H1.
 simpl. auto. lia.
 Opaque hmapPush. simpl in IHtrans0.
 simpl.
 setoid_rewrite IHtrans0 with  (p:=hmapPush trId p).
 simpl.
 remember ((Z.of_nat (Datatypes.length p))).
 replace (Z.of_nat (Datatypes.length (hmapPush (H:=bfr) (H0:=pfr) (H2:=ifr) (H4:=lfr) (H6:=hmfr) trId p)) + 1) with (z+2).
 replace (Z.of_nat (Datatypes.length (hmapPush trId p))) with (z+1).
 Transparent hmapPush.
 simpl.
 rewrite H0.
 rewrite H3. rewrite H1.
 simpl. unfold Datatypes.id.
 rewrite <- Heqz.  
 Transparent map. simpl.
 rewrite ?app_ass. 
 replace (z+1+1) with (z+2). auto.
 lia.
 rewrite Heqz. lia.
 simpl. rewrite H0.
 Transparent Datatypes.length Z.of_nat.
 simpl.
 rewrite Zpos_P_of_succ_nat.
 setoid_rewrite <- Heqz. try lia.
 setoid_rewrite <- Heqz. try lia.
 simpl. rewrite H0. simpl. unfold Datatypes.id. 
 rewrite <- Pos2Z.add_pos_pos.
 rewrite Zpos_P_of_succ_nat.
 rewrite <- Heqz. lia. rewrite <- Heqz.
 lia. intros.
 simpl. rewrite H0.
 simpl. unfold Datatypes.id.
 Transparent bIn.  simpl.
 rewrite H0.
 replace (Z.of_nat (Datatypes.length p) =? n) with false.
 auto.
 symmetry. apply Z.eqb_neq.
 simpl in H4. rewrite H0 in H4.
 simpl in H4. rewrite Zpos_P_of_succ_nat in H4.
 unfold  Datatypes.id  in H4.
 try lia. try lia.
 simpl in H4. rewrite H0 in H4.
 simpl in H4. rewrite Zpos_P_of_succ_nat in H4.
 unfold  Datatypes.id  in H4.
 try lia. try lia.
 try lia.
 remember (hmapMin (p0 :: trans0) ).
 symmetry in Heqx.
 apply Heqx. compute. auto.
 compute. destruct p0. auto.
Qed.

Lemma fetchFind: forall X`{XDefault X} (m: listPair Z X) id,
       m [id] = snd (hmapFetch m id). 
Proof.
 intros.
 unfold hmapFetch. unfold hmapFindWithDefault.
 remember (m [id]?).
 destruct y. simpl.  destruct m.
 simpl. simpl in Heqy. inversion  Heqy.
 simpl. simpl in Heqy. setoid_rewrite <- Heqy.
 simpl. auto.
 setoid_rewrite <- Heqy.
 simpl. auto.
 Qed.


(* (*not used*) (*BAD*) Axiom deleteFetch_another: forall V`{XDefault V} k1 k2 (m: listPair Z V), 
k1 <> k2 ->
snd (deleteListPair Z.eqb k1 m ->fetch k2) =
snd (m ->fetch k2). *)

 
Lemma bIn_false_key_map: forall X`{XBoolEquable bool X}`{boolEquivalence eqb} 
                          (l: listPair Z X) (f: X -> Z) (x: X)
 (keysF: keysFactorization l) 
 (funkey: forall k x, hmapLookup Z.eqb k l = Some x -> f x = k)
 (xDist: Forall (fun x0 => fst x0 =? f x = false) l),
 bIn eqb x (xHMapElems l) = false ->
 bIn Z.eqb (f x) (map f (xHMapElems l)) = false.
 Proof.
  intros.
  induction l. simpl. auto.
  simpl in  H0.
  apply Bool.orb_false_elim in H0.
  inversion_clear  H0.
  simpl.
  apply Bool.orb_false_iff.
  split.
  assert (f (snd a) = fst a).
  apply funkey.
  simpl.
  rewrite  Z.eqb_refl.
  simpl. auto.
  rewrite H0.
  inversion xDist.
  auto.
  apply IHl.
  apply keysFactorization_cons in keysF; auto.
  intros.
  apply funkey.
  simpl.
  remember (k=? fst a).
  destruct b.
  simpl.
  cut (snd a = x0).
  intros. congruence.
  cut (a = (k, x0)). intros.
  destruct a. inversion H3. auto.
  apply keysF.
  simpl. left. auto.
  simpl. right.
  apply hmapLookup_In. auto.
  symmetry in Heqb.
  apply Z.eqb_eq in  Heqb.
  simpl.  auto.
  auto.
  inversion xDist.
  auto.
  auto.
 Qed.  
 
Lemma foldLoopRecordBreak: forall X (successLoop: X -> bool) f (l: list True) a,
successLoop a = false ->
(fold_left
     (fun (acc : X) (_ : True) =>
      if successLoop acc
      then f acc else acc) l
     a) = a.
Proof.
 intros. generalize dependent a.
 induction l. auto.
 intros. simpl. rewrite IHl.
 rewrite H. auto.
 rewrite H. auto.
Qed.

Lemma listIntFromToInc: forall n, 
 n >= 0 -> listIntFromTo 0 (n + 1) = (n + 1) :: listIntFromTo 0 n.
Proof.
 intros. induction n.
 compute. auto.
 simpl. unfold listIntFromTo.
 replace (Z.pos (p + 1) <? 0) with false.
 replace (Z.pos p <? 0) with false.
 replace (Z.pos (p + 1) - 0) with (Z.pos (p + 1)).
 replace (Z.pos p - 0) with (Z.pos p). 
 replace (Z.to_nat (Z.pos (p + 1))) with (S (Z.to_nat (Z.pos p))).
 simpl. replace (Z.pos (Pos.of_succ_nat (Pos.to_nat p))) with (Z.pos (p + 1)).
 auto. rewrite Pos2SuccNat.id_succ. rewrite Pplus_one_succ_l.
 replace ((p+1)%positive) with ((1+p)%positive).
 auto. apply Pos.add_comm.
 simpl. rewrite <- Pos2Nat.inj_succ.
 replace (Pos.succ p) with ((p + 1)%positive). auto. 
 rewrite Pos.add_1_r. auto. lia. lia. 
 symmetry. zbool2relG. lia. symmetry. zbool2relG. 
 apply Pos2Z.pos_is_nonneg.
 assert (Z.neg p <0). apply Pos2Z.neg_is_neg.
 lia.
Qed.

Lemma rangeInc: forall X (x: X) (l: list X), 
listRange (listLength (x :: l)) = 
((listRange (listLength l)) ++ [ (listLength l) ])%list.
Proof.
 intros. unfoldList listLength. 
 unfoldList xListLength. 
 Opaque Z.of_nat.
 simpl. destruct l. simpl. 
 Transparent Z.of_nat.
 compute. auto. remember (x0::l) as l'.
 unfold listRange. 
 remember (Datatypes.length l').
 replace (Z.of_nat (S n) - 1) with ((Z.of_nat n) - 1 + 1).
 rewrite listIntFromToInc. simpl.
 replace (Z.of_nat n - 1 + 1) with (Z.of_nat n).
 auto. lia.
 rewrite Heql' in Heqn. simpl in Heqn.
 rewrite Heqn. 
 rewrite Nat2Z.inj_succ. lia.
 rewrite Nat2Z.inj_succ. lia.
Qed.



Lemma rangeInc': forall X (x: X) (l: list X), 
listRange (listLength (l ++ [x])) = 
((listRange (listLength l)) ++ [ (listLength l) ])%list.
Proof.
 intros. replace (listLength (l ++ [x])) with (listLength (x::l)).
 apply rangeInc. unfoldList listLength. 
 unfoldList xListLength. rewrite <- snoc_app.
 rewrite lensnoc. auto.
Qed.


Lemma revcons: forall (A : Type) (l: list A) (a: A),
               rev (l ++ [a]) = a:: (rev l).
Proof.
 intros. induction l.
 simpl. auto. simpl. rewrite IHl.
 auto.
Qed.

Lemma revrev: forall (A : Type) (l: list A),
              rev (rev l) = l.
Proof.
 intros. remember (rev l). generalize dependent l0.
 induction l; intros.
 simpl in Heql0. rewrite Heql0. auto.
 rewrite Heql0. simpl. 
 replace (rev (rev l ++ [a])) with (a::(rev (rev l))).
 rewrite <- IHl with (l0:=rev l) at 2. auto.
 auto. rewrite revcons. auto.
Qed.


Lemma list_rev_prop: forall (A : Type) (P : list A -> Prop),
       (forall l : list A, P l) <-> (forall l : list A, P (rev l)).
Proof.
 intros. split; intros.
 apply H. replace l with (rev (rev l)).
 apply H. apply revrev.
Qed.

Lemma list_ind2: forall (A : Type) (P : list A -> Prop),
       P ([ ]% list) ->
       (forall (a : A) (l : list A), P l -> P (l ++ [ a ])) ->
       forall l : list A, P l.
Proof.
 intros. generalize dependent l. apply list_rev_prop.
 intros. induction l. auto.
 simpl. remember (H0 a (rev l)).
 auto.
Qed.

Lemma in_snoc: forall X l (i x: X), In i (l ++ [x]) <-> In i l \/ i = x.
Proof.
 intros. split. intros. induction l using list_ind.
 inversion H. right. auto.
 inversion H0. inversion H.
 left. constructor. auto.
 apply IHl in H0. inversion H0.
 left. simpl. right. auto.
 right. auto.
 intros. induction l. inversion H. inversion H0. simpl.
 left. auto. simpl. simpl in H. inversion H.
 inversion H0. left. auto.
 right. apply IHl. left. auto.
 right. apply IHl. right. auto.
Qed. 


Lemma lelteq: forall (i:Z) (m:nat), (i < Z.succ (Z.of_nat m))%Z -> 
              (i < (Z.of_nat m))%Z \/ i = (Z.of_nat m).
Proof.
 intros. lia.
Qed.

Lemma rangeLe: forall X i (l: list X), In i (listRange (listLength l)) <->
               (i < (listLength l) /\ i >= 0)%Z.
Proof.
 intros. split.
 intros. split. induction l using list_ind2.
 inversion H. rewrite rangeInc' in H.
 apply in_snoc in H. inversion H.
 apply IHl in H0.
 unfoldList listLength. unfoldList xListLength.
 rewrite <- snoc_app. rewrite lensnoc.
 unfoldList listLength in H0. 
 unfoldList xListLength in H0.
 rewrite Nat2Z.inj_succ. lia.
 unfoldList listLength. unfoldList xListLength.
 rewrite <- snoc_app. rewrite lensnoc.
 unfoldList listLength in H0. 
 unfoldList xListLength in H0. 
 rewrite Nat2Z.inj_succ. lia.
 induction l using list_ind2.
 inversion H. rewrite rangeInc' in H.
 apply in_snoc in H. inversion H.
 apply IHl in H0. auto. rewrite H0.
 unfoldList listLength. unfoldList xListLength.
 lia. intros. 
 induction l using list_ind2. 
 simpl in H.
 lia.
 inversion_clear H. rewrite rangeInc'.
 apply in_snoc. unfoldList listLength in H0. 
 unfoldList xListLength in H0.
 rewrite <- snoc_app in H0. rewrite lensnoc in H0.
 rewrite Nat2Z.inj_succ in H0.
 apply lelteq in H0. inversion H0.
 left. apply IHl. split. apply H. auto.
 right. apply H.
Qed.

Lemma rangeLeZ: forall i (n: Z), In i (listRange n) <-> (n >= 0 /\ i < n /\ i >= 0)%Z.
Proof.
 intros.
 split. intros.
 assert (n>=0)%Z.
 destruct n.
 lia.
 remember (Pos2Z.is_nonneg  p).
 lia.
 simpl in H. inversion H.
 auto.
 split. auto.
 assert (exists (l:list True), xListLength l  = n).
 exists (repeat (A:=True) I (Z.to_nat n)).
 unfoldList xListLength.
 rewrite repeat_length.
 apply Z2Nat.id. lia.
 inversion H1.
 rewrite <- H2.
 apply rangeLe.
 unfold listLength.
 rewrite H2. auto.
 intros. inversion H.
 assert (exists (l:list True), xListLength l  = n).
 exists (repeat (A:=True) I (Z.to_nat n)).
 unfoldList xListLength.
 rewrite repeat_length.
 apply Z2Nat.id. lia.
 inversion H2.
 rewrite <- H3.
 apply rangeLe.
 split; try lia.
 unfold listLength.
 rewrite  H3.
 apply H1.
Qed.

Lemma listNthDefaultIn: forall X i (l: list X) a d, In i (listRange (listLength l)) -> 
                          xListNthDefault i l d = xListNthDefault i (l ++ [a]) d.
Proof.
 intros. apply rangeLe in H. 
 unfoldList xListNthDefault.
 rewrite app_nth1. auto.
 inversion_clear H.
 unfoldList listLength in H0. 
 unfoldList xListLength in H0.
 remember (Datatypes.length l).
 replace n with (Z.to_nat (Z_of_nat n)).
 apply Z2Nat.inj_lt. lia. lia. lia.
 apply Nat2Z.id.
Qed.


Local  Open Scope Z_scope.


Lemma len_le_snoc: forall X len l (x:X), 
len <= xListLength (l ++ [x])  ->
(len <= xListLength l \/ len = Z.succ (xListLength l)).
Proof.
 intros.
 replace  (xListLength (l ++ [x])) with (Z.succ (xListLength l)) in H.
 apply Z.le_succ_r in H.
 tauto.
 unfoldList xListLength.
 rewrite app_length.
 remember (Datatypes.length l).
 simpl. 
 replace (n + 1)%nat with (S n).
 simpl. 
 rewrite Zpos_P_of_succ_nat. auto.
 lia.
 Qed.
  

Lemma listNthDefaultInTake: forall X i (l: list X) len d, 
In i (xListRange len) -> 
(len <= (xListLength l))%Z ->
xListNthDefault i l d = xListNthDefault i (take (Z.to_nat len) l) d.
Proof.
  intros.
  generalize dependent len.
  induction l using rev_ind; intros.
  rewrite  takeNil. auto.
  replace  (xListLength (l ++ [x])) with (Z.succ (xListLength l ))%Z in H0.
  assert (len = Z.succ (xListLength l) \/ len <= xListLength l)%Z.
  apply Z.le_succ_r in H0.
  tauto.
  inversion H1.
  rewrite H2 in H.
  replace (Z.succ (xListLength l)) with
          ((xListLength (d::l))) in H.
  rewrite rangeCons in H.
  apply in_snoc in H.
  inversion H.
  rewrite <- listNthDefaultIn; auto.
  rewrite takeMore.
  rewrite <- listNthDefaultIn; auto.
  rewrite H2. rewrite app_length.
  unfoldList xListLength.
  remember (Datatypes.length l).
  rewrite Z2Nat.inj_succ.
  rewrite Nat2Z.id.
  simpl. lia.
  apply Nat2Z.is_nonneg.
  rewrite  takeMore.
  auto.
  rewrite H2. rewrite app_length.
  unfoldList xListLength.
  remember (Datatypes.length l).
  rewrite Z2Nat.inj_succ.
  rewrite Nat2Z.id.
  simpl. lia.
  apply Nat2Z.is_nonneg.
  unfoldList xListLength.
  Opaque Z.of_nat.
  simpl.
  Transparent  Z.of_nat.
  rewrite Nat2Z.inj_succ.  auto.
  
  rewrite <- listNthDefaultIn; auto.
  rewrite IHl with (len:=len); auto.
  rewrite takeLess with (l':=[x]). auto.
  unfoldList xListLength  in H2.
  remember (Datatypes.length l).
  replace n with (Z.to_nat (Z.of_nat n)).
  apply Z2Nat.inj_le.
  destruct len.
  lia. apply Pos2Z.pos_is_nonneg.
  simpl in H. inversion H.
  apply Nat2Z.is_nonneg.
  auto. 
  apply Nat2Z.id.
  apply rangeLe.
  apply rangeLeZ in H.
  
  inversion_clear  H.
  inversion_clear  H4.
  split; auto; try lia.
  unfoldList listLength.
  remember (xListLength l).
  lia. 
  unfoldList xListLength.
  rewrite app_length.
  remember (Datatypes.length l).
  simpl. 
  Transparent Z.of_nat.
  replace (n + 1)%nat with (S n).
  simpl. 
  rewrite Zpos_P_of_succ_nat. auto.
   lia.
 Qed.



Lemma boolEqSym: forall X (eqX: X -> X -> bool),
boolEquivalence eqX -> forall x y, eqX x y = eqX y x.
Proof.
 intros. unfold boolEquivalence in H.
 remember (eqX x y). destruct b.
 symmetry in Heqb. apply H in Heqb.
 symmetry. apply H. auto.
 assert (x <> y). unfold not. intros.
 apply H in H0. congruence.
 remember (eqX y x). destruct b.
 symmetry in Heqb0. apply H in Heqb0.
 congruence. auto.
Qed.

Lemma hmapSizeAdjust: forall {V} (x0: listPair Z V) (a0: V) i,
xHMapSize (adjustListPair Z.eqb (fun _ : V => a0) i x0) =
xHMapSize x0.
Proof.
 intros. induction x0.
 simpl. auto. 
 simpl. destruct a. destruct (i =? z)%Z.
 simpl. simpl in IHx0. 
 remember ((Datatypes.length
            (adjustListPair Z.eqb (fun _ : V => a0) i x0))).
 assert (n = (Datatypes.length x0)).
 apply Nat2Z.inj in IHx0. auto. rewrite H. auto.
 simpl. simpl in IHx0. remember ((Datatypes.length
            (adjustListPair Z.eqb (fun _ : V => a0) i x0))).
 apply Nat2Z.inj in IHx0. rewrite IHx0. auto.
Qed.
 

Lemma hmapSizePush: forall {V} (x0: listPair Z V) (a0: V),
(xHMapSize (hmapPush a0 x0) >= xHMapSize x0)%Z.
Proof.
 intros. unfold hmapPush.
 unfold hmapInsert. destruct (hmapIsMember xIntEqb (xHMapSize x0) x0).
 simpl. setoid_rewrite hmapSizeAdjust. simpl. lia.
 simpl. unfold Datatypes.id. remember (Datatypes.length x0).
 rewrite Zpos_P_of_succ_nat. lia.
Qed.


Lemma listIntToNeg: forall n,
n < 0 -> listIntFromTo 0 n = @nil Z.
Proof.
 intros. unfold listIntFromTo.
 zrel2boolH.
 rewrite H. auto.
Qed.

Lemma listRangeNeg: forall n,
n < 0 -> listRange n = @nil Z.
Proof.
 intros. unfold listRange.
 rewrite listIntToNeg. auto. lia.
 Qed.

 Lemma fst_map_compose: forall X Y (m: list (X*Y)),
 map fst (map (fun ck => (snd ck, fst ck)) m) = 
 map snd m.
 Proof.
   intros. induction m.
   auto.
   simpl. rewrite IHm. auto.
 Qed.  

 Lemma nth_last: forall X`{XDefault X} (a:X) l,  
 a = xListNthDefault (xListLength l) (l ++ [a]) default.
 Proof.
  intros.
  generalize  dependent a.
  induction l; intros.
  simpl. auto.
  simpl.
  simpl in IHl.
  rewrite  Nat2Z.id in  IHl.
  remember (Datatypes.length l).
  assert (Pos.to_nat (Pos.of_succ_nat n) = S n).
  apply SuccNat2Pos.id_succ.
  rewrite H0.
  apply  IHl.
  Qed.

Lemma len_to_nat_le: forall X len (l: list X),
len <= xListLength l -> 
(Z.to_nat len <= Datatypes.length l)%nat.
Proof.
intros.
replace (Datatypes.length l) with
         (Z.to_nat (Z.of_nat  (Datatypes.length l))).
 assert (len < 0 \/ len >= 0).
 remember (Z.le_gt_cases 0 len).
 inversion o.
 right. lia.
 left. auto.
 inversion H0.
 destruct len.
 inversion H1.
 remember (Pos2Z.is_pos p). lia.
 rewrite Z2Nat.inj_neg. lia.
 apply Z2Nat.inj_le; auto. lia.
 apply Nat2Z.is_nonneg.
 apply Nat2Z.id.
 Qed.

 (*********************************************************************************)

 Inductive isListTail {X}: list X -> list X -> Prop :=
| isListTail_self: forall l, isListTail l l
| isListTail_cons: forall x l l', isListTail l l' -> isListTail l (x::l').

Lemma isListTail_correct1: forall X (l: list X) l' l'',
l'' = l ++ l' ->
isListTail l' l''.
Proof.
 intros. 
 generalize dependent l.
 generalize dependent l'.
 induction l''; intros.
 assert (l' = [ ]).
 destruct l'.
 auto.
 destruct l. discriminate.
 discriminate.
 rews l'.
 constructor.
 destruct l.
 rewrite H.
 constructor.
 inversion H.
 apply IHl'' in  H2.
 constructor.
 inversion H.
 rews l'' in H2.
 auto.
Qed.

Lemma isListTail_correct2: forall X (l': list X)  l'',
isListTail l' l'' ->
∃ (l:list X), l'' = l ++ l'.
Proof.
 intros.
 generalize  dependent l'.
 induction l''; intros.
 inversion H. exists [ ]. auto.
 inversion H.
 exists [ ]. auto.
 apply IHl'' in H2.
 inversion  H2.
 rews l''.
 exists (a::x0).
 auto.
Qed. 

Lemma isListTail_cons_in: forall X (a:X) l l',
isListTail (a::l) l' ->
In a l'.
Proof.
 intros.
 generalize dependent l.
 induction l'; intros.
 inversion H.
 inversion H.
 simpl.
 left.
 auto.
 apply IHl' in H2.
 simpl. right. auto.
Qed.

Lemma isListTail_cons_in_rev: forall X (a:X) l',
In a l' ->
∃ l,  isListTail (a::l) l'.
Proof.
 intros.
 induction l'.
 inversion H.
 inversion H.
 rewrite H0.
 exists l'.
 constructor.
 apply IHl'  in H0.
 inversion H0.
 exists x.
 constructor.
 auto.
Qed.


Inductive listDistinct: list Z -> Prop :=
| ldistinct_nil : listDistinct nil
| ldistinct_cons : forall x l, listDistinct l -> 
                               Forall (fun y => y<>x) l -> listDistinct (x::l).


Lemma Forall_fg: forall X (l: list X) (f g:X -> Prop),
Forall f l ->
(forall x, f x  -> g x) ->
Forall g l.
Proof.
 intros.
 induction l.
 auto.
 constructor.
 apply H0.
 inversion H.
 auto.
 apply IHl.
 inversion H.
 auto.
Qed. 


Lemma Forall_all_in: forall X (l: list X), 
Forall (λ x : X, In x l) l.
Proof.
 intros.
 induction l.
 auto.
 simpl.
 constructor. left. auto.
 apply Forall_fg with (f:=λ x : X, In x l).
 auto.
 intros.
 right. auto.
Qed. 


Lemma sublist_app: forall X (fl fl': list X),
sublist fl' (fl' ++ fl).
Proof.
 intros.
 induction fl'.
 constructor.
 simpl.
 constructor. 
 simpl. left. auto.
 apply Forall_fg with (f:=fun x => In x (fl'++fl)).
 apply  (Forall_sub (l':=fl'++fl)). auto.
 apply sublist_refl.
 intros.
 simpl. right. auto.
Qed.



Lemma consIf: forall X (b: bool) (x: X) (t e: list X),
x::(if b then t else e) = if b then x::t else x::e.
Proof. intros. destruct b; auto. Qed. 

Lemma doubleIf3: forall X (x y z: X) (b: bool),
(if b then x else (if b then y else z)) = 
if b then x else z.
Proof. 
 intros. destruct b; auto.
Qed.

Fixpoint mapFindFirst (v: Z) (l: listPair Z Z) : option Z := 
match l with
| [ ] => None
| (k, v')::l' => if (v =? v') then Some k else mapFindFirst v l'
end.


Fixpoint mapFindFirstIn (ids:list Z) (v: Z) (l: listPair Z Z) : option Z := 
match ids with
| [ ] => None
| k::ids' => let mv := hmapLookup Z.eqb k l in 
             match mv with
             | Some v' => if (v =? v') then Some k else mapFindFirstIn ids' v l
             | None => mapFindFirstIn ids' v l
             end
end.

Definition mapFindFirstBool (v: Z) (l: listPair Z Z) : bool*Z := 
match mapFindFirstIn (listRange (xHMapSize l)) v l with
| Some x => (true, x)
| None => (false, default)
end.

Lemma revnil: forall X (l: list X),
rev l = [ ] <-> l = [ ].
Proof.
 intros. split; intros.
 destruct l. auto. inversion H.
 destruct (rev l). inversion H1.
 inversion H1. subst. auto.
Qed.

Lemma listIntFromToNil: forall n,
n < 0 <-> listIntFromTo 0 n = [ ].
Proof.
 intros. split; intros.
 destruct n. lia.
 discriminate. unfoldList listIntFromTo.
 zrel2boolH. rewrite H. auto.
 destruct n. compute in H. inversion H.
 unfoldList listIntFromTo in H.
 replace (Z.pos p <? 0) with false in H.
 unfoldList listNatTo in H.
 remember (Z.to_nat (Z.pos p - 0)).
 destruct n. compute in H. inversion H.
 simpl in H. inversion H.
 symmetry. zbool2relG. apply Pos2Z.is_nonneg.
 apply Zlt_neg_0.
Qed.

Fixpoint cutLast {X} (l: list X) := 
match l with
| [ ] => [ ]
| [x] => [ ]
| x::xs => x::(cutLast xs)
end.

Lemma cutLastSnoc: forall {X} (l: list X) x,
cutLast (l ++ [x]) = l.
Proof.
 intros.
 induction l. auto.
 simpl. rewrite IHl.
 destruct l. auto. auto.
Qed. 

Lemma listRange0: forall n x y, 
x :: y = listRange n -> x = 0.
Proof.
 intros.
 unfoldList listRange in H.
 unfoldList listIntFromTo in H.
 remember (n - 1 <? 0).
 destruct b.
 inversion H.
 unfoldList listNatTo in H.
 remember (Z.to_nat (n - 1 - 0)).
 generalize dependent n.
 generalize dependent x. 
 generalize dependent y.
 induction n0; intros.
 simpl in H. inversion H. auto.
 simpl in H. apply IHn0 with (n:=n-1) (y:=cutLast y).
 match goal with
 | |- _ = ?m => remember m
 end.
 destruct l. inversion H.
 destruct n0. simpl in Heql. inversion Heql.
 simpl in Heql. destruct (rev
         (List.map (Z.add 0)
            (List.map Z.of_nat
               ((fix listNatTo (n : nat) : list nat :=
                   match n with
                   | 0%nat => [0%nat]
                   | S n' => n :: listNatTo n'
                   end) n0)))).
 inversion Heql. inversion Heql.
 inversion H. rewrite cutLastSnoc. auto.
 symmetry. zbool2relG.
 assert (n - 1 >= 1).
 replace (n-1) with (Z.of_nat (Z.to_nat (n-1))).
 replace 1 with (Z.of_nat (Z.to_nat 1)) at 2.
 apply inj_ge.  rewrite Z.sub_0_r in Heqn0.
 rewrite <- Heqn0. compute. lia.
 compute. auto. apply Z2Nat.id.
 symmetry in Heqb. zbool2relH. lia.
 lia. rewrite Z.sub_0_r in Heqn0.
 rewrite Z.sub_0_r.
 replace (n - 1 - 1) with (Z.pred (n-1)).
 rewrite Z2Nat.inj_pred. rewrite <- Heqn0.
 auto. lia.
Qed.

Lemma listIntFromTo_m: forall m,
listIntFromTo m m = [ m ].
Proof.
 intros. unfoldList listIntFromTo.
 replace (m <? m) with false.
 rewrite Z.sub_diag. simpl.
 rewrite Z.add_0_r. auto.
 symmetry. zbool2relG. lia.
Qed.

Lemma listIntFromTo_nil: forall m n,
m > n -> 
listIntFromTo m n = [ ].
Proof.
 intros.
 unfoldList listIntFromTo.
 replace (n <? m) with true. auto.
 symmetry. zbool2relG. lia.
Qed.

Lemma listIntFromTo_cons: forall m n,
m <= n -> 
listIntFromTo m n = (listIntFromTo (m+1) n) ++ [m].
Proof.
 intros.
 unfoldList listIntFromTo.
 replace (n <? m) with false.
 remember (n<?m+1). destruct b.
 assert (m = n).
 symmetry in Heqb. zbool2relH.
 lia. rewrite H0.
 rewrite Z.sub_diag.  simpl.
 rewrite Z.add_0_r. auto.
 remember (Z.to_nat (n - (m + 1))).
 assert ((Z.to_nat (n - m)) = S n0).
 replace (n - m) with (Z.succ (n - (m + 1))).
 rewrite Z2Nat.inj_succ.
 rewrite Heqn0.
 auto. symmetry in Heqb. zbool2relH.
 lia. 
 rewrite Zminus_succ_l.
 replace (Z.succ n) with (n+1).
 lia. lia. rewrite H0.
 generalize n0. intros.
 induction n1. simpl. rewrite ?Z.add_0_r. auto.
 simpl in IHn1. simpl. rewrite IHn1.
 assert (Z.pos (Pos.succ (Pos.of_succ_nat n1)) = 1 + Z.pos (Pos.of_succ_nat n1)).
 rewrite Pplus_one_succ_l. rewrite Pos2Z.inj_add. auto.
 rewrite H1. rewrite Z.add_assoc. auto.
 symmetry. zbool2relG. auto.
Qed.


Lemma mapFindFirstSnoc: forall x m x0, 
mapFindFirst x (m ++ [x0]) = 
match mapFindFirst x m with
| None => if (x =? snd x0) then Some (fst x0) else None
| Some v => Some v
end.
Proof.
 intros. generalize dependent x0. induction m; intros.
 simpl. destruct x0. simpl. auto.
 simpl. destruct a. destruct (x =? z0). auto.
 auto.
Qed.


Lemma optionMapIf: forall X (f: Z -> X) m x y,
optionMapDefault (fun i : Z => f i)
          (mapFindFirstIn (listRange (xHMapSize m)) x m) y = 
let (b, x) := mapFindFirstBool x m in 
if b then f x else y.
Proof.
 intros. remember (mapFindFirstBool x m).
 destruct p. destruct b.
 assert (mapFindFirstIn (listRange (xHMapSize m)) x m = Some z).
 unfold mapFindFirstBool in Heqp.
 remember (mapFindFirstIn (listRange (xHMapSize m)) x m).
 destruct o. inversion Heqp. auto.
 inversion Heqp. rewrite H. auto.
 unfold mapFindFirstBool in Heqp.
 remember (mapFindFirstIn (listRange (xHMapSize m)) x m).
 destruct o. inversion Heqp. auto.
Qed.

Lemma doubleIf4: forall X (b b1: bool) (x y z u: X),
(if b
 then
  (if b1
  then
   (if b
   then x else y) else z) else u) = 
if b then if b1 then x else z else u.
Proof.
 intros. destruct b; destruct b1; auto.
Qed.

Lemma doubleIf5: forall X (b b1: bool) (x y z u v: X),
(if b then
  if b1 then x else if b then y else z else
  if b then u else v) = if b then if b1 then x else y else v.
Proof.
 intros. destruct b; destruct b1; auto.
Qed.

Definition deleteLast {X} (l: listPair Z X) := 
deleteListPair Z.eqb (xHMapSize l - 1) l.


Lemma mapSizeEqAdjust : forall X (m: listPair Z X)
                        (n:Z) (f:X->X), 
 xHMapSize m = xHMapSize (xHMapAdjust Z.eqb f n m).
Proof.
 intros. induction m. simpl. auto.
 Opaque Z.of_nat.
 simpl. simpl in IHm. 
 rewrite Nat2Z.inj_succ.
 destruct a. destruct (n =? z).
 simpl. rewrite Nat2Z.inj_succ.
 rewrite IHm. auto.
 simpl. rewrite Nat2Z.inj_succ.
 rewrite IHm. auto.
Qed.

Lemma mapSizeEqBoth : forall X m (n:Z) (x:X), 
((hmapIsMember Z.eqb n m  = true -> 
 xHMapSize m = xHMapSize (m [n] ← x)) /\
 (hmapIsMember Z.eqb n m  = false -> 
 xHMapSize m + 1 = xHMapSize (m [n] ← x))).
Proof.
 intros. unfold hmapInsert.
 simpl. split; intros.
 rewrite H. apply mapSizeEqAdjust.
 rewrite H. simpl.
 rewrite Nat2Z.inj_succ. unfold Datatypes.id.
 lia.
Qed.

Lemma mapSizeEqTrue : forall X m (n:Z) (x:X), 
hmapIsMember Z.eqb n m  = true -> 
 xHMapSize m = xHMapSize (m [n] ← x).
Proof.
 intros. apply mapSizeEqBoth. auto.
Qed.

Transparent Z.of_nat.

(*********************************************************************************************************)



Lemma evalIf: forall S X (b: bool) (m: StateT S X) (s1 s2: S),  
      eval_state m (if b then s1 else s2) =
      if b then (eval_state m s1) else (eval_state m s2).
Proof.
 intros. destruct b; auto.
Qed. 

Lemma execIf: forall S X (b: bool) (m: StateT S X) (s1 s2: S),  
      exec_state m (if b then s1 else s2) =
      if b then (exec_state m s1) else (exec_state m s2).
Proof.
 intros. destruct b; auto.
Qed. 

Lemma negBoolIfThenElse: forall (b: bool), 
negb b = if b then false else true.
Proof.
 destruct b; auto.
Qed. 

Lemma doubleIf: forall X (x y z: X) (b: bool),
(if negb b then (if b then x else y) else z) = 
if b then z else y.
Proof. 
 intros. destruct b; auto.
Qed.

Lemma doubleIf2: forall X (x y z: X) (b: bool),
(if b then (if b then x else y) else z) = 
if b then x else z.
Proof. 
 intros. destruct b; auto.
Qed.

Lemma ifIrrel: forall X (x: X) (b: bool),
(if b then x else x) = x.
Proof.
 intros. destruct b; auto. Qed.

Lemma boolIfElseSimple: forall (b: bool), (if b then true else false) = b.
Proof.
 destruct b; auto.
Qed.

Lemma boolIfElseSimpleNot: forall (b: bool), (if b then false else true) = negb b.
Proof.
 destruct b; auto.
Qed.

