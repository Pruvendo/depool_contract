Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.
Require Import omega.Omega.
Require Import Setoid.

Require Import FinProof.Common.
Require Import FinProof.CommonInstances.
Require Import FinProof.StateMonad2.
Require Import FinProof.StateMonadInstances.
Require Import FinProof.ProgrammingWith.
(* Require Import MultiSigWallet.Lib.CPDT. *)

Require Import FinProof.CommonProofs.
Require Import depoolContract.ProofEnvironment.

Set Typeclasses Iterative Deepening.
(*Set Typeclasses Depth 1.
Set Typeclasses Strict Resolution. *)
(* Set Typeclasses Debug.  *)  
(* Set Typeclasses Unique Instances. 
Unset Typeclasses Unique Solutions. *)

(* Existing Instance monadStateT.
Existing Instance monadStateStateT. *)
(* Module MultiSigWalletSpecSig := MultiSigWalletSpecSig XTypesSig StateMonadSig. *)

(* Require Import MultiSigWallet.CommonModelProofs.
Module CommonModelProofs := CommonModelProofs StateMonadSig.
Import CommonModelProofs. *)

Require Import depoolContract.Lib.Tactics.


Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope solidity_scope.

Require Import Lists.List.
Import ListNotations.
Local Open Scope list_scope.

(* Existing Instance embeddedMultisig.
Existing Instance monadStateT.
Existing Instance monadStateStateT. *)



Lemma foldLeftAccOrProp: forall l a b,
                       (a <-> b) ->
                       fold_left or l a <-> fold_left or l b.
Proof.
 intros. split. generalize dependent a. generalize dependent b.
 induction l. intros. simpl. simpl in H0. apply H. auto.
 simpl. intros. apply IHl with (a:=or a0 a). 
 rewrite H. tauto. auto. intros.
 generalize dependent a. generalize dependent b.
 induction l. intros. simpl. simpl in H0. apply H. auto.
 simpl. intros. apply IHl with (b:=or b a). 
 auto. rewrite H. tauto.
 Qed.
 
Lemma foldLeftAccAndProp: forall l a b,
                       (a <-> b) ->
                       fold_left and l a <-> fold_left and l b.
Proof.
 intros. split. generalize dependent a. generalize dependent b.
 induction l. intros. simpl. simpl in H0. apply H. auto.
 simpl. intros. apply IHl with (a:=and a0 a). 
 rewrite H. tauto. auto. intros.
 generalize dependent a. generalize dependent b.
 induction l. intros. simpl. simpl in H0. apply H. auto.
 simpl. intros. apply IHl with (b:=and b a). 
 auto. rewrite H. tauto.
 Qed.
 
Lemma foldLeftOrProp: forall l a b,
                    fold_left or l (a \/ b)  <-> a \/ fold_left or l b.
Proof.
 intros. split; intros.
 generalize dependent a. generalize dependent b. 
 induction l.
 intros. simpl in H. simpl. tauto.
 intros. simpl in H. simpl.
 apply IHl. assert ((a0 \/ b) \/ a <-> a0 \/ b \/ a). 
 apply or_assoc. rewrite foldLeftAccOrProp. apply H. rewrite H0. tauto.
 generalize dependent a. generalize dependent b. 
 induction l.
 intros. simpl in H. simpl. tauto.
 intros. simpl in H. simpl. 
 assert ((a0 \/ b) \/ a <-> a0 \/ b \/ a). 
 apply or_assoc. rewrite foldLeftAccOrProp. apply IHl.
 apply H. apply H0.
Qed.

Lemma foldLeftPropOrFalse: forall l a,
                    fold_left or l a  <-> a \/ fold_left or l False.
Proof.
 intros. rewrite foldLeftAccOrProp with (b:= a \/ False).
 apply foldLeftOrProp. tauto.
Qed.

Lemma foldLeftAndProp: forall l a b,
                    fold_left and l (a /\ b)  <-> a /\ fold_left and l b.
Proof.
 intros. split; intros.
 generalize dependent a. generalize dependent b. 
 induction l.
 intros. simpl in H. simpl. tauto.
 intros. simpl in H. simpl.
 apply IHl. assert ((a0 /\ b) /\ a <-> a0 /\ b /\ a). 
 apply and_assoc. rewrite foldLeftAccAndProp. apply H. tauto.
 generalize dependent a. generalize dependent b. 
 induction l.
 intros. simpl in H. simpl. tauto.
 intros. simpl in H. simpl. 
 assert ((a0 /\ b) /\ a <-> a0 /\ b /\ a). 
 apply and_assoc. rewrite foldLeftAccAndProp. apply IHl.
 apply H. tauto.
Qed.

Lemma foldLeftPropAndTrue: forall l a,
                    fold_left and l a  <-> a /\ fold_left and l True.
Proof.
 intros. rewrite foldLeftAccAndProp with (b:= a /\ True).
 apply foldLeftAndProp. tauto.
Qed.

Lemma foldLeftAndProp2: forall l a b,
                    fold_left and l (a /\ b)  <-> b /\ fold_left and l a.
Proof.
 intros. split;intros.
 apply foldLeftPropAndTrue in H. 
 split. inversion H. inversion H0.
 auto. apply foldLeftPropAndTrue. 
 inversion H. split. inversion H0. auto.
 auto. inversion H. apply foldLeftPropAndTrue in H1.
 inversion H1. apply foldLeftPropAndTrue.
 split;tauto.
 Qed. 

Lemma ErrorValueFalse: forall X E l (x:X) (e:E) ,
           toErrorProp l x e -> toValueProp l x -> False.
Proof.
 intros. induction l.
 compute in H. compute in H0. auto.
 simpl in H. unfold toValueProp in H0.
 simpl in H0. unfold toErrorProp in H.
 simpl  in H. remember (a x).
 destruct p. simpl in H0.
 simpl in H. rewrite foldLeftPropOrFalse in H.
 inversion H. inversion_clear H1.
 rewrite foldLeftPropAndTrue in H2.
 inversion H2. rewrite foldLeftPropAndTrue in H0.
 inversion H0. unfold not  in H5. apply H5. auto.
 apply IHl. unfold toErrorProp.
 match goal with
 | H1: fold_left or ?h False |- _ => remember h
 end. destruct l0. simpl in H1. inversion H1.
 simpl in H1. rewrite foldLeftAccOrProp. apply H1.
 tauto. apply foldLeftPropAndTrue in H0.
 inversion  H0. unfold toValueProp.
 remember (List.map (fun p : X -> Prop * E => ~ fst (p x)) l).
 destruct l0. apply I. simpl in H3.
 rewrite foldLeftAccAndProp . apply H3.
 tauto.
 Qed.
 
Lemma forallEqEq: forall X (P:X -> Prop) Q A, 
           (forall x, P x -> A) -> 
           (forall x, P x <-> Q x) -> 
           (forall x, Q x -> A).
Proof.
 intros. apply X0 with (x:=x). apply H. apply H0. Qed.

 
Lemma ForallFoldEqProp: forall (l:list Prop) P,  
                        (Forall (@Datatypes.id Prop) l /\ P) <-> fold_left and l P.
Proof.
 intros. split. intros.
 generalize dependent P. induction l. intros.
 simpl. inversion H. auto. intros.
 inversion H. simpl. apply foldLeftAndProp2.
 inversion H0. unfold Datatypes.id in H4.
 split. auto. apply IHl. split.
 auto. auto.
 generalize dependent P. induction l; intros.
 split. constructor. tauto.
 split. constructor. simpl in H.
 apply foldLeftAndProp2 in H.
 inversion H. tauto. simpl in  H.
 apply foldLeftAndProp2 in H. inversion H.
 apply IHl in H1. inversion H1. auto.
 simpl in  H.
 apply foldLeftAndProp2 in H. inversion H.
 apply IHl in H1. inversion H1. auto.
 Qed.
 
Lemma toValueForall: forall X E (l: list (X -> (Prop * E)%type)) (x:X), toValueProp l x <-> 
                                       Forall not (List.map (fun p => fst (p x)) l).
Proof.
  intros. split; intros.
  induction l. simpl. compute in H. constructor.
  simpl. constructor. unfold toValueProp in  H.
  simpl in H. apply foldLeftPropAndTrue in H.
  inversion H. auto. apply IHl.
  unfold toValueProp in  H.
  simpl in H. apply foldLeftPropAndTrue in H.
  inversion H. unfold toValueProp.
  destruct l. simpl. auto. simpl. simpl in H1.
  apply foldLeftPropAndTrue in H1.
  apply foldLeftPropAndTrue. inversion_clear H1.
  inversion_clear H2. split; tauto.
  induction l. compute. auto.
  unfold toValueProp. simpl. simpl in  H.
  inversion H. apply IHl in H3.
  apply foldLeftPropAndTrue. split. auto.
  unfold toValueProp in H3. destruct l. simpl. auto.
  simpl. simpl in H3. apply foldLeftPropAndTrue.
  split. split. auto. apply foldLeftPropAndTrue in H3.
  inversion H3. auto. apply foldLeftPropAndTrue in H3.
  inversion H3. auto.
Qed.

Lemma ForallNotFoldEqProp: forall (l:list Prop) P,  
                        (Forall not l /\ ~P) <-> 
                        ~ fold_left or l P.
Proof.
 intros. split; intros.
 unfold not. intros.
 induction l. simpl in H0. inversion H. 
 apply H2. auto.  simpl in H0.
 inversion_clear H. inversion H1.
 apply foldLeftPropOrFalse in H0.
 inversion H0. inversion H6. 
 congruence. congruence.
 apply IHl. split. auto. auto.
 apply foldLeftPropOrFalse.  right. auto.
 induction l. split. constructor.
 simpl in H. auto.
 simpl in H. unfold  not in H.
 rewrite foldLeftPropOrFalse in H.
 apply Classical_Prop.not_or_and in H.
 inversion H. apply Classical_Prop.not_or_and in H0.
 inversion H0. split. constructor.
 auto. apply IHl. unfold not. intros.
 apply H1. rewrite foldLeftPropOrFalse in H4.
 inversion H4. congruence. auto. auto.
Qed.

Lemma ForallNotFoldEqProp2: forall (l:list Prop) P, 
                            fold_left and (List.map (fun p : Prop => ~ p) l) P <->
                            Forall not l /\ P.
Proof.
 intros. split; intros.
 induction l. simpl in H.
 split. constructor. auto.
 simpl in H. 
 apply foldLeftPropAndTrue in H.
 inversion H. inversion H0. 
 split. constructor. auto.
 apply IHl. apply foldLeftPropAndTrue.
 split. auto. auto. auto.
 induction l. simpl. inversion H.
 auto. simpl. apply foldLeftPropAndTrue.
 split. inversion H. inversion H0.
 split. auto. auto.
 inversion H. inversion H0.
 assert ( Forall not l /\ P). tauto.
 apply IHl in H6. apply foldLeftPropAndTrue in H6.
 apply H6.
 Qed.


Lemma ErrorPropCons1: forall X E (l:list (X -> Prop*E)) a (x:X), 
                     (forall e : E, ~ toErrorProp (a :: l) x e) ->
                     (forall e : E, ~ toErrorProp l x e).
Proof.
 intros. unfold not.
 intros. remember (H e).
 apply n. unfold toErrorProp.
 simpl. apply foldLeftPropOrFalse.
 right. unfold toErrorProp in H0.
 match goal with
 | |- fold_left or ?l False => remember l
 end. destruct l0.  simpl.  auto.
 simpl. apply  foldLeftOrProp.
 right. auto.
Qed.

 
Lemma  ErrorPropCons2_helper: forall X E (l:list (X -> Prop*E)) (x:X), 
(List.map (fun p : X -> Prop * E => fst (p x)) l)  = 
 (hd nil
     ((fix
       f (l0 : list (X -> Prop * E)) (x0 : X) {struct l0} :
         list (list Prop) :=
         match l0 with
         | nil => nil
         | cons p  ls =>
             cons (cons (fst (p x0)) (hd nil (f ls x0))) (f ls x0)
         end) l x)).
Proof.
 intros. induction l.
 simpl. auto.
 simpl. rewrite IHl. auto.
 Qed.

Lemma ErrorPropCons2: forall X E (l:list (X -> Prop*E)) a (x:X), 
                     (forall e : E, ~ toErrorProp (a :: l) x e) ->
                      ~(fst(a x) /\ Forall not (List.map (fun p  => fst (p x)) l)).
Proof.
 intros. unfold not. intros.
 apply H with (e:=snd (a x)).
 unfold toErrorProp. simpl.
 apply foldLeftPropOrFalse.
 left. split; auto.
 apply foldLeftPropAndTrue.
 split. apply H0.
 inversion H0. apply ForallNotFoldEqProp2.
 split. rewrite <- ErrorPropCons2_helper.
 apply H2. auto.
 Qed.
 
Lemma ErrorPropCons2': forall X E e (l:list (X -> Prop*E)) a (x:X), 
                      toErrorProp (a :: l) x e -> 
                      ~fst(a x) -> toErrorProp l x e.
Proof.
 intros.
 unfold toErrorProp in H.
 simpl in H. apply foldLeftPropOrFalse in H.
 inversion H. inversion H1.
 apply foldLeftPropAndTrue in H2.
 inversion H2.
 congruence. 
 unfold toErrorProp.
 match goal with
 | H1: fold_left or ?l False |- _ => remember l
 end. destruct l0. simpl in H1. auto.
 simpl  in H1. apply foldLeftOrProp in H1.
 inversion H1. inversion H2. auto.
 Qed.
 
                      
 
Lemma ErrorPropCons: forall X E (l:list (X -> Prop*E)) a (x:X), 
                     (forall e : E, ~ toErrorProp (a :: l) x e) ->
                     (forall e : E, ~ toErrorProp l x e) /\
                      ~(fst(a x) /\ Forall not (List.map (fun p  => fst (p x)) l)).
Proof.
 intros. split. apply ErrorPropCons1 with (a:=a). auto.
  apply ErrorPropCons2. auto.
  Qed.                  
  
Lemma ValueTrueErrorFalse: forall X E l (x:X), 
toValueProp l x -> (forall (e:E), ~(toErrorProp l x e)).
Proof.
 intros. unfold not.
 intros. apply toValueForall in H. induction l.
 simpl in H. unfold toErrorProp in H0. simpl in H0.
 auto. apply ErrorPropCons2' in H0.
 apply IHl. simpl in H. inversion H.
 auto. auto.  simpl in H. inversion H. auto.
 Qed.

Lemma ErrorPropCons3: forall X E (l:list (X -> Prop*E)) (a:X->Prop*E) (x:X),  
                      fst (a x) -> toValueProp l x -> toErrorProp (a :: l) x (snd (a x)).
Proof.
 intros. apply toValueForall in H0.
 unfold toErrorProp. simpl. apply foldLeftPropOrFalse.
 left. split; auto.  rewrite <- ErrorPropCons2_helper.
 apply foldLeftPropAndTrue. split; auto.
 apply ForallNotFoldEqProp2. split; auto.
Qed.
 
Theorem ErrorValueEquivalence1: forall X E l V (x:X) (f: X -> ErrorValue V E) ,
           (forall e, toErrorProp l x e <-> f x = Error e) -> 
           (toValueProp l x <-> exists v, f x = Value v).
Proof.
 intros. split; intros.
 intros.
 remember (f x) as y. destruct y.
 (*1st part - False*)
 assert False. assert (toErrorProp l x e).
 apply H. auto. apply ErrorValueFalse in H1.
 auto. auto. inversion H1.
 (*2nd part  - Value*)
 exists v. auto.
 inversion H0.
 assert (forall e, not (toErrorProp l x e)).
 intros. unfold not. intros. apply H in  H2. 
 rewrite H1 in  H2.
 discriminate.
 induction l. unfold toValueProp.
 simpl. auto.
 apply ErrorPropCons in H2.
 inversion_clear H2.
 apply toValueForall. simpl. constructor.
 apply Classical_Prop.not_and_or in H4.
 inversion H4. auto.
 unfold not. intros.
 unfold not in H2.
 assert (f x = Error (snd (a x))).
 apply H. unfold toErrorProp.
 simpl. apply foldLeftPropOrFalse.
 left. split; auto.
 rewrite <- ErrorPropCons2_helper.
 apply foldLeftPropAndTrue.
 split. auto.
 apply ForallNotFoldEqProp2. split.
 apply toValueForall. apply IHl; auto.
 split. intros.
 remember (H3 e). congruence.
 intros. congruence. auto.
 congruence. apply toValueForall.
 apply IHl; auto.
 split. intros.
 remember (H3 e). congruence.
 intros. congruence. 
Qed.

Lemma notForallCons: forall {X} (f:X->Prop) a l, ~ Forall f (a::l) <-> ~(f a) \/ ~ Forall f l.
Proof.
 intros. split. intros.
 apply Classical_Prop.not_and_or. unfold not.
 intros. apply H. constructor. apply H0. apply H0.
 intros. unfold not. intros.
 inversion H0. inversion H; auto.
 Qed.
 
Lemma ForallCons: forall {X} (f:X->Prop) a l, 
      Forall f (a::l) <-> (f a) /\ Forall f l.
Proof.
 intros. split. intros.
 inversion H. tauto.
 intros. inversion H. constructor; auto.
 Qed.
 
Lemma forallAnd: forall X (P:X->Prop) (Q:X->Prop), 
      (forall x, P x /\ Q x) <->
      ((forall x, P x) /\ (forall x, Q x)).
Proof.
 intros. split;intros. split; intros;
 apply H. split; apply H.
 Qed.
 

Lemma existsOrforall: forall X (P:X -> Prop),
      exists x, P x \/ forall x, ~ (P x).
Proof.
 intros. Abort.
 
Lemma ErrorPropCons4: forall E X (l: list (X->Prop*E)) x a (e:E), 
      toErrorProp l x e -> toErrorProp (a::l) x e.
Proof.
 intros.
 unfold toErrorProp. 
 simpl. apply foldLeftPropOrFalse.
 right. unfold toErrorProp in H.
 match goal with
 | |- fold_left or ?l _ => remember l
 end.
 destruct l0. inversion H.
 simpl. apply foldLeftOrProp.
 right. auto.
 Qed.
 

Lemma ValueOrErrorTrue: forall X E l (x:X),
     (forall x, Forall (fun p => fst (p x) \/ ~fst (p x)) l) ->
     toValueProp l x \/ exists (e:E), toErrorProp l x e.
Proof.
 intros. induction l.
 compute. left. auto.
 rewrite toValueForall. simpl.
 rewrite ForallCons.
 assert (forall x : X, (fst (a x) \/ ~ fst (a x)) /\
    Forall
      (fun p : X -> Prop * E => fst (p x) \/ ~ fst (p x))
      l).
 intros. 
 remember (ForallCons (X:=X->Prop*E) (fun p => fst (p x0) \/ ~ fst (p x0))).
 rewrite <- i. apply H. rewrite forallAnd in H0.
 inversion_clear H0.
 apply IHl in H2. remember (H1 x). clear Heqo.
 inversion o. right.
 inversion H2.
 exists (snd (a x)).
 apply  ErrorPropCons3; auto.
 inversion H3. inversion H3.
 apply ErrorPropCons4 with (a:=a) in H5.
 exists x1. auto.
 inversion H2. left.
 split; auto. apply toValueForall. auto.
 right. inversion H3.
 apply ErrorPropCons4 with (a:=a) in H4.
 exists x0. auto.
Qed.
  

Lemma ValuePropDecidable: forall (X:Type) E (l: list (X -> Prop*E)),
      (forall x, Forall (fun p => fst (p x) \/ ~fst (p x)) l) ->
      (forall x, ~toValueProp l x \/ toValueProp l x).
Proof.
 intros. rewrite toValueForall.
 induction  l.  simpl. right. constructor.
 simpl. rewrite ForallCons.
 assert (forall x : X, (fst (a x) \/ ~ fst (a x)) /\
    Forall
      (fun p : X -> Prop * E => fst (p x) \/ ~ fst (p x))
      l).
 intros. 
 remember (ForallCons (X:=X->Prop*E) (fun p => fst (p x0) \/ ~ fst (p x0))).
 rewrite <- i. apply H. 
 rewrite forallAnd in H0.
 inversion_clear H0. apply IHl in H2. 
 remember (H1 x). clear Heqo.
 inversion o. left.
 unfold not. intros.
 inversion H3. tauto.
 inversion H2.
 left.  unfold not. intros.
 inversion  H4. tauto.
 right. tauto.
Qed.

Lemma ValueFalseErrorTrue: forall X E l (x:X),
      (forall x, Forall (fun p => fst (p x) \/ ~fst (p x)) l) ->
     ~toValueProp l x -> exists (e:E), toErrorProp l x e.
Proof.  
intros.
assert (toValueProp l x \/ exists (e:E), toErrorProp l x e).
apply ValueOrErrorTrue. auto.
assert (~toValueProp l x \/ toValueProp l x).
apply ValuePropDecidable. auto.
inversion H1; inversion H2; try tauto.
Qed.


Theorem ErrorValueEquivalence2: forall X E l V (x:X) (f: X -> ErrorValue V E),
           (forall x, Forall (fun p => fst (p x) \/ ~fst (p x)) l) ->
           (toValueProp l x <-> exists v, f x = Value v) ->
           ((exists (e:E), toErrorProp l x e) <-> exists e0, f x = Error e0).
Proof.
 intros.
 assert (toValueProp l x \/ exists (e:E), toErrorProp l x e).
 apply ValueOrErrorTrue. auto.
 assert (~toValueProp l x \/ toValueProp l x).
 apply ValuePropDecidable. auto.
 remember (f x) as fx.
 split; intros.
 destruct fx. inversion_clear H2. inversion_clear H3. 
 (* try tauto. try assert_succeeds (exists e;  auto). exists e. auto. *)
 exists e. auto. exists e. auto. inversion_clear H2.
 assert False. apply H4. apply H0. exists v. auto. inversion H3.
 apply ErrorValueFalse in H5. inversion H2. apply H0. exists v. auto.
 destruct f. rewrite Heqfx. exists e. auto.
 inversion_clear H3. apply ErrorValueFalse in H2. inversion H2.
 apply H4.
 (* <- *)
 inversion_clear H2. inversion_clear H1. 
 assert False. apply H4. apply H2. inversion H1. apply H2.  
 apply H0 in H4.  
 inversion_clear H4. inversion_clear H3. destruct fx.
 congruence. congruence.
Qed.
 
Lemma orFalse: forall P, False \/ P <-> P.
Proof.
 intros. split. intros. inversion H. inversion H0.
 auto. intros. right. auto.
Qed.

Lemma andTrue: forall P, P /\ ~False <-> P.
Proof.
 intros. split. intros. inversion H. auto.
 intros. split. auto. unfold not. intros. auto.
Qed.