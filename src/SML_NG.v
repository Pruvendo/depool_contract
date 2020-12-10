Require Import Coq.Program.Basics.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.
Require Import Coq.Unicode.Utf8.


Local Open Scope program_scope. 

Require Import FinProof.Common.
Require Import FinProof.ProgrammingWith.
Require Import FinProof.StateMonad2.
Require Import FinProof.StateMonadInstances.

Local Open Scope record.


Require Import depoolContract.DePoolClass. 
Require Import depoolContract.SolidityNotations.
Require Import depoolContract.ProofEnvironment. 
Require Import depoolContract.DePoolSpec.

(* Module SML (xt: XTypesSig) (sm: StateMonadSig). *)

Module DePoolSpec := DePoolSpec XTypesSig StateMonadSig.
Import DePoolSpec.
Import LedgerClass.
Import SolidityNotations.

Require Import ZArith.
Require Import Psatz.
Local Open Scope Z_scope.

Compute (xIntPlus 0%Z 1%Z).

(* Require Import Coq.QArith.Qfield. *)

(* Lemma foo1: forall c,  c > 0 -> 1/c > 0.
Proof.
    intros.
    try nia.
    try lia.
    try nra.
    try lra.
    field.
    psatz R 4.


Lemma foo: forall a b c, a >= 0 -> b >= 0 -> c > 0 -> a*(1/c) >= 0.
Proof.
    intros.
    nia.

    
Qed. *)



(*  Lemma foo : forall a y, let x := (Z.modulo a 13%Z) - (a + a) / (a +13) in  y <= y + x.
Proof.
    intros.
    match goal with
    | |- ?G => match G with 
              | context [y <= y + ?x] => remember x
              end
    end.
    zify.



    enough ( z >= 0).        
    lia.   *) 
 
(* Import xt. Import sm. *)

Local Open Scope solidity_scope.
Local Open Scope string_scope.

Inductive LedgerFunction : Type -> Type := 
 | LedgerFunction0: forall X, LedgerFunction (LedgerT X)
 | LedgerFunction_Next: forall X Y, LedgerFunction Y -> LedgerFunction (X -> Y).

 Class Ledgerable (X: Type) :=
 {
     ledgerable : LedgerFunction X ;
     ledgerFirstType : Type ;
     ledgerTailType : Type ;
     ledgerJoin : LedgerT X -> X ;
     sApply : X -> LedgerT ledgerFirstType -> ledgerTailType
 }.

 

(*  Notation "◯" := (LedgerFunction0) (at level 100).
 Notation " a ⇉ b " := (LedgerFunction1 a b) (at level 100, right associativity).

Check ◯ nat.
Check  nat ⇉ ◯ nat.
Check  nat ⇉ nat ⇉ ◯ nat. *)


Inductive SolidityExpression : Type -> Type := 
| SolidityScalar : forall {X}, LedgerT X -> SolidityExpression X
| SolidityState : forall {X U} {m: Ledger -> U}`{Accessor Ledger U m}`{EmbeddedType Ledger U} (f: U -> X)`{Accessor U X f} ,  SolidityExpression X
| SolidityField : forall {S U}`{Struct S} (f:S->U)`{Accessor _ _ f}, SolidityExpression S -> SolidityExpression U
| SolidityIndex : forall {K V}`{XBoolEquable XBool K}`{XDefault V}, SolidityExpression K -> SolidityExpression (XHMap K V) -> SolidityExpression V
(* | SolidityFunction: forall {X B}`{Ledgerable X B}, X -> SolidityExpression B *)
(* | SolidityFunctionCall: forall {X A B}`{Ledgerable X (A -> B)}, X -> SolidityExpression A -> SolidityExpression B
 *).


 Instance LedgerT_Ledgerable {X} : Ledgerable (LedgerT X) := {
    ledgerable := LedgerFunction0 X ;
    ledgerFirstType := True ;
    ledgerTailType :=  SolidityExpression X ;
    ledgerJoin := fun mx => mx >>= Datatypes.id ;
    (*sApply : X -> ledgerFirstType -> ledgerTailType*)
    sApply := fun f _ => SolidityScalar f
 }.


 Instance LedgerTNext_Ledgerable {X Y}`{Ledgerable Y} : 
                      Ledgerable (X -> Y) := {
    ledgerable := LedgerFunction_Next X Y ledgerable ;
    (* toLedgerBaseType := fun (f: X -> Y) => inject (fun (x: X) => toLedgerBaseType (f x))  *)
    ledgerFirstType := X ;
    ledgerTailType := Y ;
    (* LedgerT (X -> Y) -> X -> Y *)
    ledgerJoin := fun (mf: LedgerT (X -> Y)) => fun x => ledgerJoin (mf >>= fun f => return! (f x)) ;
    (*sApply : X -> ledgerFirstType -> ledgerTailType*)
    sApply := fun (f : X -> Y) (mx: LedgerT X) => ledgerJoin (mx >>= fun x => return! (f x)) 
 }.

(* Definition sApply {L} (f: L)`{Ledgerable L} (x: LedgerT ledgerFirstType) : ledgerTailType.
Proof.
    intros.
    remember (ledgerable_dec L ledgerFirstType ledgerTailType).
    assert (match ledgerable with
    | LedgerFunction0 _ => L = ledgerTailType
    | LedgerFunction_Next _ Y _ => L = (ledgerFirstType → ledgerTailType)
    end).
    apply y; auto. clear y Heqy.
    remember ledgerable.
    generalize dependent ledgerable.
    induction l; intros.
    rewrite <- H0.
    refine f.
    apply forall_dec in H0.
    inversion_clear H0.
    rewrite <- H2 in * |- *.
    assert (Ledgerable Y).
    apply ledgerableFunction with (X:=X); auto.
    assert (H = @LedgerTNext_Ledgerable X Y X0).
    apply instance_irr.
    rewrite H0 in * |- *.
    rewrite <- H1 in * |- *.

    remember (do x' ← x; return! (f x')).
    apply sJoin.
    refine l1.
Defined. *)

(*  := {
    ledgerable := LedgerFunction0 X ;
    ledgerFirstType := True ;
    ledgerTailType :=  LedgerT X
 }. *)

Check ledgerable (X:=nat -> nat -> LedgerT nat). 
Compute ledgerFirstType (X:=nat -> nat -> LedgerT nat).
Compute ledgerTailType (X:=nat -> nat -> LedgerT nat).
Compute ledgerFirstType (X:= LedgerT nat).
Compute ledgerTailType (X:= LedgerT nat).

(* (X -> LedgerT Y) --> (LedgerT (X -> Y)) *)


(* Fixpoint ledgerableDegree (X: Type)`{Ledgerable X} : nat := 
    match ledgerable with
    | LedgerFunction0 _ => 0
    | LedgerFunction_Next X Y L => S (@ledgerableDegree Y {| ledgerable  := L ; 
                                                             ledgerFirstType   
                                                               |})
    end. *)

Fixpoint ledgerableDegree {X} (a: LedgerFunction X) : nat := 
    match a with
    | LedgerFunction0 _ => 0
    | LedgerFunction_Next _ _ f => S (ledgerableDegree f)
    end.


(* Lemma ledgerable0_first: forall X, ledgerFirstType (X:=LedgerT X) = True.
Proof.
    intros.
    auto.
Qed.

Lemma ledgerable0_tail: forall X, ledgerTailType (X:=LedgerT X) = LedgerT X.
Proof.
    intros.
    auto.
Qed.  *)

(* Check (ledgerFirstType -> ledgerTailType).

Axiom instance_irr: forall X (i j: Ledgerable X), i = j.

Axiom forall_dec: forall (X Y A B: Type), ((forall (_:X), Y) = (forall (_:A), B)) -> 
(X = A) /\ (Y = B). 


Axiom ledgerableFunction : forall X Y`{ Ledgerable (X -> Y) } , Ledgerable Y.


Axiom ledgerable_dec: forall (L: Type)`{H: Ledgerable L} (f t: Type), 
f = @ledgerFirstType L H -> 
t = @ledgerTailType L H -> 
match @ledgerable L H with 
| LedgerFunction0 _ => (L = t)
| LedgerFunction_Next _ _ _ => (L = forall (a: f), t ) 
end. *)


(* Instance ledgerTailType_Ledgerable {L}`{Ledgerable L} : Ledgerable ledgerTailType.
remember (ledgerable_dec L ledgerFirstType ledgerTailType).
assert (match ledgerable with
| LedgerFunction0 _ => L = ledgerTailType
| LedgerFunction_Next _ Y _ => L = (ledgerFirstType → ledgerTailType)
end).
apply y; auto.
clear Heqy y.
induction ledgerable.
rewrite <- H0.
refine H.
destruct l.
apply forall_dec in H0 .
inversion_clear H0.
rewrite <- H2.
apply LedgerT_Ledgerable.
apply forall_dec in H0 .
inversion_clear H0.
rewrite <- H2.
assert (LedgerFunction (X0->Y)).
apply LedgerFunction_Next; auto.
refine {| ledgerable := X1 ;
          ledgerFirstType := X0 ;
          ledgerTailType := Y  |}.
Defined. *)


Check SolidityScalar ($ xInt0).
Check SolidityState DePoolContract_ι_m_association.
Check SolidityField contractAddress (SolidityScalar ($ default)).
Check SolidityIndex (SolidityScalar ($xInt0)) (SolidityScalar ($xHMapEmpty)).
(* Check SolidityFunction (fun x: nat => return! x : LedgerT nat).
Check SolidityFunction (fun (x: Z) (y: Z) => return! (x + y) : LedgerT Z).
Check SolidityFunction (fun (x: Z) (y: Z) => (x + y) : Z).
Check SolidityFunction (return! 0 : LedgerT Z). *)

Definition sReader {X} (e : SolidityExpression X): LedgerT X.
Proof.
    induction e.
    - exact l.
    - exact (↑ (ε f)).
    - exact (do r' ← IHe;
             $ (f r')).
    - exact (
        do k' ← IHe1;
        do m' ← IHe2;
        $ ( m' [ k' ] )
    ) . (* 
    - destruct H. exact (toLedgerBaseType0 x).
    - inversion e1.
     + exact (do x' ← IHe2;
              do f' ← X1;
              $ (f' x')).
     + exact (do x' ← IHe2;
              do f' ← IHe1;
              $ (f' x')). 
     + exact (do x' ← IHe2;
     do f' ← IHe1;
     $ (f' x')). 
     + exact (do x' ← IHe2;
     do f' ← IHe1;
     $ (f' x')). 
     + destruct H.   
     inversion ledgerable0.
     exact (do x' ← IHe2;
     do f' ← IHe1;
     $ (f' x')). *) 
Defined.

(* Definition sApply {X Y} (f: X -> LedgerT Y) (x: SolidityExpression X) :=
           do x' ← sReader x ;
           f x'. *)

(* (X -> M Y) -> M X -> M Y *) 



(* Axiom onlySimpleTypes: forall X Y (lf: LedgerFunction (LedgerT (X -> Y))),  False. *)



(* Definition sJoin {L}`{Ledgerable L} (a: LedgerT L) : L.
Proof.
    remember (ledgerable_dec L ledgerFirstType ledgerTailType).
    assert (match ledgerable with
    | LedgerFunction0 _ => L = ledgerTailType
    | LedgerFunction_Next _ Y _ => L = (ledgerFirstType → ledgerTailType)
    end).
    apply y; auto.
    clear Heqy y.
    remember ledgerable.
    generalize dependent ledgerable.
    induction l; intros.
    refine (a >>= Datatypes.id).
    apply forall_dec in H0.
    inversion_clear H0.
    intros.
    remember (a >>= fun f => return! (f X0)).
    assert (Ledgerable Y).
    rewrite H2.
    apply ledgerTailType_Ledgerable.
    remember (IHl X1 l1).
    clear Heqy IHl.
    apply y with  (l0:=l); auto.
    destruct l.
    symmetry.
    assert (X1 = LedgerT_Ledgerable ).
    apply instance_irr.
    rewrite H0.
(*     clear  y X1 Heql1 l1 X0 a. *)
    apply (ledgerable0_tail X2).
    remember (@ledgerTailType_Ledgerable (X2 → Y) X1).
    clear Heql2.
    remember (@ledgerable_dec (X2 → Y) X1 (@ledgerFirstType (X2 → Y) X1) (@ledgerTailType (X2 → Y) X1)).
    clear Heqy0.
    assert (match (@ledgerable (X2 → Y) X1) with
    | LedgerFunction0 _ => (X2 → Y) = @ledgerTailType (X2 → Y) X1
    | LedgerFunction_Next _ Y0 _ =>
        (X2 → Y) = (@ledgerFirstType (X2 → Y)  X1 → @ledgerTailType (X2 → Y) X1)
    end).
    apply y0; auto. clear y0.
    remember (@ledgerableFunction X2  Y X1).
    assert (X1 = @LedgerTNext_Ledgerable X2 Y l3).
    apply instance_irr.
    rewrite H3 in * |- *.
    compute.
    auto.
Defined.
 *)

(* Definition sApply {L} (f: L)`{Ledgerable L} (x: LedgerT ledgerFirstType) : ledgerTailType.
Proof.
    intros.
    remember (ledgerable_dec L ledgerFirstType ledgerTailType).
    assert (match ledgerable with
    | LedgerFunction0 _ => L = ledgerTailType
    | LedgerFunction_Next _ Y _ => L = (ledgerFirstType → ledgerTailType)
    end).
    apply y; auto. clear y Heqy.
    remember ledgerable.
    generalize dependent ledgerable.
    induction l; intros.
    rewrite <- H0.
    refine f.
    apply forall_dec in H0.
    inversion_clear H0.
    rewrite <- H2 in * |- *.
    assert (Ledgerable Y).
    apply ledgerableFunction with (X:=X); auto.
    assert (H = @LedgerTNext_Ledgerable X Y X0).
    apply instance_irr.
    rewrite H0 in * |- *.
    rewrite <- H1 in * |- *.

    remember (do x' ← x; return! (f x')).
    apply sJoin.
    refine l1.
Defined. *)    
    
    
(*     simpl in x.
    (* remember H as HL. clear HeqHL. *)
    destruct H.
    inversion ledgerable0.
    rewrite <- H in f.
    remember (SolidityScalar f). clear Heqs.
    rewrite <- ledgerable0_tail in s.
    
    refine s.

    rewrite ledgerable0_tail.
    (* refine (SolidityScalar f). *)
    assert (ledgerTailType (X:=L) (Ledgerable := HL) = SolidityExpression X).
    compute.
    destruct HL. 
    rewrite <- H in HL.
    refine (SolidityScalar f).
    
    setoid_rewrite <- H in x. *)



(*     match e with
    | SolidityScalar c =>  c
    | SolidityState m =>  ↑ (ε m)
    | SolidityField f r => do r' ← (sReader r);
                           $ (f r')
    | SolidityIndex k m =>  do k' ← (sReader k);
                            do m' ← (sReader m);
                            $ ( m' [ k' ] )                              
    | SolidityFunction f => toLedgerBaseType f  (* match ( ledgerable (X:=X) ) with
                            | LedgerFunction0 _ => f
                            | LedgerFunction_Next _ _ f => 
                            end *)
    | SolidityFunctionCall f x => do x' ← sReader x;
                                  do f' ← sReader f;
                                  $ (f' x')

    end. *)

Notation " # e " := (SolidityScalar e) (at level 100).
Notation " 'μ' e " := (SolidityState e) (at level 100).
Notation " r ^^ f " := (SolidityField f r) (at level 100).
Notation " m [[ i ]] " := (SolidityIndex i m) (at level 100).
(* Notation " 'ϕ' f " := (SolidityFunction f) (at level 100).*)
Notation " 'α' " := (sApply ) (at level 100). 



Check #$xInt0.
Check μ DePoolContract_ι_m_association.
Check (#$default) ^^ contractAddress.
Check (#$xHMapEmpty) [[ #$xInt0 ]].
Check (#$xHMapEmpty) [[ #$xInt0 ]] ^^ contractAddress. 
Check (#$xHMapEmpty) [[ μ DePoolContract_ι_m_association ]] ^^ contractAddress. 
Check @SolidityState.

 Check α. 

Existing Instance monadStateT.
Existing Instance monadStateStateT.

Check (α (fun (x y: XInteger) => $ (xIntPlus x y ) : LedgerT XInteger) ($xInt2)) : XInteger -> LedgerT XInteger.
Let a := (α (fun (x y: XInteger) => $ (xIntPlus x y ) : LedgerT XInteger) ($xInt2)) : XInteger -> LedgerT XInteger.
Let b := α a ($xInt100).


Lemma foo1:  eval_state b default  = 102 .
Proof.
    compute.
    auto.
Qed.    

(* Check (ϕ (fun (x y: XInteger) => $ (xIntPlus x y ) : LedgerT XInteger)).
Check  (ϕ (fun (x: XInteger) => (↑2 U1! ValidatorBase_ι_m_validatorWallet := $ x) : LedgerT True)).
 *)
Let g := sReader (α (α (fun (x: XInteger) => (↑2 U1! ValidatorBase_ι_m_validatorWallet := $ x): LedgerT True) ($xInt2)) ($I)).

Lemma foo2: eval_state (↑2 D2! ValidatorBase_ι_m_validatorWallet)  (exec_state g default) = 2.
Proof.
    compute.
    auto.
Qed.


Definition sWriter {X} (e : SolidityExpression X) (v : LedgerT X): LedgerT True.
Proof.
    intros.
    induction e. exact ($I).

    exact (do v' ← v; 
    modify (fun r => {$ r with m := {$ (r ->> m) with f := v' $} $} ) >> $ I).

    exact (do v' ← v;
    do o ← sReader e; 
    IHe ($ {$ o with f := v' $} )
    ).

    exact (do v' ← v;
    do k' ← sReader e1; 
    do m' ← sReader e2;
    IHe2 ($  (m' [k'] ← v') )
    ).
Defined.

Definition sAssign {X} (el er : SolidityExpression X) := 
    sWriter el (sReader er).


Check sAssign (μ DePoolContract_ι_m_association) (#$xInt0).
Check sAssign ((μ RoundsBase_ι_m_rounds) [[ μ DePoolContract_ι_m_association  ]] ^^ RoundsBase_ι_Round_ι_id ) 
              ((#$xHMapEmpty) [[ μ DePoolContract_ι_m_association ]] ^^ contractAddress).

(* Inductive foo : Type -> Type := | Foo: forall X, list X -> list X -> foo X.

Definition bar {X} (f g: foo X) : foo X.
Proof.
    intros.
    destruct f. destruct g.
    exact (Foo X l l2).
Defined.

Print bar.


Definition bar' {X} (f g: foo X) : foo X :=
    match f  with
    | Foo _ l1 _ =>
        fun g0  => match g0 with 
                    |  Foo _  _ l2 =>  fun l1 => Foo _ l1 l2
                   end l1 
    end g.

Definition bar' {X} (f g: foo X) : foo X :=
    match f (* in (foo T) return (foo T -> foo T) *) with
    | Foo _ l1 _ =>
    fun g0 (* : foo X0 *) => match g0 (* in foo T return (list T -> foo T ) *) with 
    |  Foo _  _ l2 =>  fun l1(* : list X1 *) => Foo _ l1 l2
    end l1 end g.

Set Asymmetric Patterns.

Arguments Foo {X} _ _. 
Print Implicit Foo.

Fixpoint bar {X} (f g: foo X) : foo X :=
    match f in (foo X), g in (foo X) return (foo X) with
    | Foo _ l1 _ , Foo _  _ l2 =>  @Foo  X l1 l2
    end.

Check bar.  *)   


Fail Fixpoint sWriter' {X} (e : SolidityExpression X) (v : LedgerT X): LedgerT True := 
    match e in SolidityExpression X with
    | SolidityScalar c => $I
    | @SolidityState _ _ m _ _ _ f _ _ => do v' ← v; 
                         modify ( fun r => {$ r with m := {$ (r ->> m) with f := v' $} $} ) >> $ I
    | _ => $I
    end. 



End SML.
