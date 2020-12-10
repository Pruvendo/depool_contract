(* Module Type ASig.
  Axiom A : Type.
End ASig.

Module a : ASig.
  Definition A := Set.
End a. *)

(* Inductive age : bool -> Type :=
| Z : age false
| S : age false -> age false
| D : age false -> age true.
 *)

Variable X : Type.
Variable Bar: X -> Prop.
Variable Baz: X -> Prop.

Definition Foo := forall x, Bar x -> Baz x.
Axiom foo : Foo.

Lemma barbaz: forall x, Bar x -> Baz x.
Proof.
 intros.
 apply foo in H.
 auto.
Qed.
  
Inductive D2 := X2 | Y2.
Inductive D3 := X3 | Y3 | Z3.

Inductive double_nat : D2 -> Type :=
| S20 : forall {c}, double_nat c
| S21 : forall {c}, double_nat c -> double_nat X2
| S22 : double_nat Y2 -> double_nat Y2.

Check S20.
Check (S21 S20).
Check (S21 (S21 S20)).
Check (S21 (S21 (S21 S20))).
Fail Check S22 (S21 (S21 (S21 S20))).
Check S21 (S22 (S22 (S22 S20))).
Fail Check S22 (S21 (S22 (S22 (S22 S20)))).


Inductive triple_nat : D3 -> Type :=
| S30 : triple_nat Z3
| S33 : triple_nat Z3 -> triple_nat Z3
| S32 : forall {c} {p: c = Z3 \/ c = Y3}, triple_nat c -> triple_nat Y3
| S31 : forall {c}, triple_nat c -> triple_nat X3.


Fixpoint double_nat_to_pair {c} (d: double_nat c): nat*nat :=
  match d with
  | S20 => (0,0)
  | S22 d' => let x := double_nat_to_pair d' in
             (fst x, S (snd x))
  | S21 d' => let x := double_nat_to_pair d' in
             (S (fst x), snd x)          
  end.  

Compute double_nat_to_pair (S21 (S21 (S20))).  
Check double_nat.
Check {c & double_nat c}.
Check existT double_nat Y2 S20.


Fixpoint y_to_double_nat (y: nat) : double_nat Y2 :=
  match y with
  | O => S20
  | S y' => S22 (y_to_double_nat y')
  end.


Fixpoint x_to_double_nat {c} (x: nat) (d: double_nat c) : double_nat match x with 
                                                                     | O => c
                                                                     | _ => X2
                                                                     end :=
  match x with
  | 0 => d
  | S x' => S21 (x_to_double_nat x' d)
  end.


Definition pair_to_double_nat (x y: nat) : double_nat match x,y with 
                                                    | 0, _ => Y2
                                                    | _, _ => X2
                                                    end :=
x_to_double_nat x (y_to_double_nat y).

Lemma double_nat_correct11: forall x c x' y' (d: double_nat c), 
      double_nat_to_pair d = (x', y') ->
      double_nat_to_pair (x_to_double_nat x d) = (x+x', y').
Proof.
  induction x; intros.
  simpl. auto.
  simpl.
  rewrite IHx with (x':=x') (y':=y'); auto.
Qed.

Lemma double_nat_correct12: forall y,
      double_nat_to_pair (y_to_double_nat y) = (0, y).
Proof.
   intros.
   induction y.
   auto.
   simpl. rewrite IHy. auto.
Qed.        


Lemma double_nat_correct1 : forall x y, double_nat_to_pair (pair_to_double_nat x y) = (x, y).
Proof.
  intros.
  replace (pair_to_double_nat x y) with (x_to_double_nat x (y_to_double_nat y)) by auto.
  remember (y_to_double_nat y) as d.
  remember (double_nat_to_pair d) as p.
  destruct p.
  rewrite double_nat_correct11 with (x':=n) (y':=n0).
  rewrite Heqd in Heqp.
  rewrite double_nat_correct12 in Heqp.
  inversion Heqp.
  auto.
  auto.
Qed.  

  
Lemma double_nat_correct2 : forall p, 
let (x,y) := double_nat_to_pair p in
pair_to_double_nat x y = p.


Fixpoint triple_nat_to_triple {c} (t: triple_nat c): nat*nat*nat :=
  match t with
  | S30 => (0,0,0)
  | S33 t' => let x := triple_nat_to_triple t' in
              (fst (fst x), snd (fst x), S (snd x))
  | S32 t' => let x := triple_nat_to_triple t' in
              (fst (fst x), S (snd (fst x)), snd x)
  | S31 t' => let x := triple_nat_to_triple t' in
              (S (fst (fst x)), snd (fst x), snd x)
  end. 



Compute triple_nat_to_triple (S31 (S31 (S32 (S33 (S33 S30))))).








Inductive raw_age : Set := Z | N: raw_age -> raw_age | D: raw_age ->raw_age. 

Inductive live  : raw_age -> Prop :=
| age0: live Z
| ageS : forall (a: raw_age), live a -> live (N a).

Inductive dead  : raw_age -> Prop :=
| ageD : forall (a: raw_age), live a -> dead (D a).

Definition feasible a := live a \/ dead a.

Fixpoint numD (a: raw_age) : nat := 
  match a with
  | N a' => numD a'
  | D a' => S (numD a')
  | Z => O
  end.

Require Import Psatz.  

Lemma foo: forall a, a<10 -> a <= 20.
Proof.
  lia.
Qed.


Lemma d1_feasible: forall a, feasible  a -> numD  a <= 1 .
Proof.
    intros.
    induction H.
    induction H.
    simpl. lia.
    simpl. auto.
    induction H.
    induction H.
    simpl. lia.
    simpl. simpl in IHlive. auto.
Qed.
  


Require Import List.
Check cons.
Import ListNotations.
Local Open Scope list_scope.

Inductive before {X} : X -> X -> list X -> Prop :=
| before_here: forall a b l, In b l -> before a b (a::l)
| before_next: forall x a b l , before a b l -> before a b (x::l).

Lemma before1 : before 1 2 [1; 3; 7; 2].
Proof.
  apply before_here. 
  right. right. constructor. auto.
  
Qed.

Lemma before2 : before 1 2 [8; 1; 3; 7; 2].
Proof.
  apply before_next.
  apply before_here.

  right. right. constructor. auto.
  
Qed.


Set Universe Polymorphism.
Set Printing Universes.
Require Import Unicode.Utf8.

Unset Cumulativity Weak Constraints.

(* Module MDefinition.

Universes i j k.
Constraint i <= k.
Constraint j <= k. 

Polymorphic Cumulative Inductive simpleState (S: Type@{i}) (X : Type@{j}) : Type@{k}:=
  | SimpleState : (S -> (X * S)) -> simpleState S X.

Print simpleState.

End MDefinition.
 *)
Module Type MModuleSig.

Section Sec1.

Universes i j k.
Constraint i <= k.
Constraint j <= k. 
Constraint i <= prod.u1.
Constraint j <= prod.u0.

(* Constraint i <= prod.u1. *)

Polymorphic Axiom M: Type@{i} -> Type@{j} -> Type@{k}.

End Sec1.

End MModuleSig.

(* Import MDefinition. *)

(* Print simpleState. *)

Module MModule <: MModuleSig.


(* Universes i j k.
Constraint i <= k.
Constraint j <= k.  *)

(* Constraint i <= k.
Constraint j <= k. *)

Polymorphic Cumulative Inductive simpleState(* @{i j k} *) (S: Type) (X : Type) : Type :=
  | SimpleState : (S -> (X * S)) -> simpleState S X.
  

(* Polymorphic Definition M := simpleState. *)


Polymorphic Definition M (S: Type) (X: Type) : Type. (* @{i j} (S: Type@{i}) (X: Type@{j}). *)
refine (simpleState S X).
Defined. 

End MModule.




Polymorphic Cumulative  Record L (M: Type  -> Type -> Type) :=  {
    data: nat;
    calculations: forall S, M S True} .

Definition ML := M (L M).
 

Module Type States.

Parameter G: Type. (*micro state, bigger type*)
Parameter L: Type. (*macro state, smaller type*)

Parameter ν: G -> L. (*projection from micro state to macro one*)
Definition Μ := forall (g: G), Prop. (*predicates over G*)
Parameter η : L -> Μ. (*characteric function of L *)

Axiom microProp: forall (g: G) (l: L), ν g = l <-> (η l) g. (*every local state can be characterized by some predicate which is deducible in G*)

Definition Τ := forall (g: G), G. (*transitions between global states*)

Definition stateSaving (τ: Τ) (l: L) := forall g, ν g = l -> ν (τ g) = l.  (*saves macro state in every case*)
Definition stateSavingWith (τ: Τ) (l: L) (p: Μ) := forall g, ν g = l -> p g -> ν (τ g) = l. (*saves macro state only if p holds*)
Definition macroFeasible l := exists g, ν g = l.

Lemma propDistinct: forall l l', macroFeasible l -> macroFeasible l' -> 
                                 (l = l' <-> forall g, (η l) g <-> (η l') g).
Proof.
    intros.
    split; intros.
    split; intros.
    rewrite <- H1.  auto.
    rewrite H1. auto.
    (**)
    inversion H. inversion H0.
    apply microProp in  H2.
    apply microProp in  H3.
    

    
Qed.




Lemma propTransition: forall g τ l l', ν g = l -> ν (τ g) = l' .
Proof.
    
Qed.





