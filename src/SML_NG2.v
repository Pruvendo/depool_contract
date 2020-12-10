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
Local Open Scope Z_scope.

Compute (xIntPlus 0%Z 1%Z).

(* Import xt. Import sm. *)

Local Open Scope solidity_scope.
Local Open Scope string_scope.

Inductive LedgerFunction : Type -> Type := 
 | LedgerFunction0: forall X, LedgerFunction (LedgerT X)
 | LedgerFunction_Next: forall X Y, LedgerFunction Y -> LedgerFunction (X -> Y).


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
| SolidityPlus : SolidityExpression XInteger -> SolidityExpression XInteger -> SolidityExpression XInteger
| SolidityIfElse : forall {X},  SolidityExpression XBool -> SolidityExpression X -> SolidityExpression X -> SolidityExpression X
| SolidityIf : forall {X},  SolidityExpression XBool -> SolidityExpression X -> SolidityExpression True
(* | SolidityFunction: forall {X B}`{Ledgerable X B}, X -> SolidityExpression B *)
(* | SolidityFunctionCall: forall {X A B}`{Ledgerable X (A -> B)}, X -> SolidityExpression A -> SolidityExpression B
 *).

Notation " # e " := (SolidityScalar e) (at level 100).
Notation " 'μ' e " := (SolidityState e) (at level 100).
Notation " r ^^ f " := (SolidityField f r) (at level 100).
Notation " m [[ i ]] " := (SolidityIndex i m) (at level 100).


Definition sReader {X} (e : SolidityExpression X): LedgerT X.
Proof.
    induction e.
    - refine l.
    - refine (↑ (ε f)).
    - refine (do r' ← IHe;
             $ (f r')).
    - refine (
        do k' ← IHe1;
        do m' ← IHe2;
        $ ( m' [ k' ] )
    ) . 
    - refine (
        do x' ← IHe1;
        do y' ← IHe2;
        $ ( xIntPlus x' y' )
    ) .
    - refine (
        do b' ← IHe1;
        do x' ← IHe2;
        do y' ← IHe3;
        $ ( xBoolIfElse b' x' y' )
    ) .
    - refine (
        do b' ← IHe1;
        xBoolIf b' ( IHe2 >> $I )
    ) .
Defined.

 Class Ledgerable (X: Type) :=
 {
     ledgerable : LedgerFunction X ;
     ledgerFirstType : Type ;
     ledgerTailType : Type ;
     ledgerJoin : LedgerT X -> X ;
     sApply : X -> SolidityExpression ledgerFirstType -> ledgerTailType
 }.

 Notation " 'α' " := (sApply ) (at level 100). 

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
    sApply := fun (f : X -> Y) (sx: SolidityExpression X) => ledgerJoin (sReader sx >>= fun x => return! (f x)) 
 }.

(* Check ledgerable (X:=nat -> nat -> LedgerT nat). 
Compute ledgerFirstType (X:=nat -> nat -> LedgerT nat).
Compute ledgerTailType (X:=nat -> nat -> LedgerT nat).
Compute ledgerFirstType (X:= LedgerT nat).
Compute ledgerTailType (X:= LedgerT nat). *)


Fixpoint ledgerableDegree {X} (a: LedgerFunction X) : nat := 
    match a with
    | LedgerFunction0 _ => 0
    | LedgerFunction_Next _ _ f => S (ledgerableDegree f)
    end.

(* Check SolidityScalar ($ xInt0).
Check SolidityState DePoolContract_ι_m_association.
Check SolidityField contractAddress (SolidityScalar ($ default)).
Check SolidityIndex (SolidityScalar ($xInt0)) (SolidityScalar ($xHMapEmpty)). *)
(* Check SolidityFunction (fun x: nat => return! x : LedgerT nat).
Check SolidityFunction (fun (x: Z) (y: Z) => return! (x + y) : LedgerT Z).
Check SolidityFunction (fun (x: Z) (y: Z) => (x + y) : Z).
Check SolidityFunction (return! 0 : LedgerT Z). *)

(* Notation " 'ϕ' f " := (SolidityFunction f) (at level 100).*)


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

Check (α (fun (x y: XInteger) => $ (xIntPlus x y ) : LedgerT XInteger) (#$xInt2)) (* : XInteger -> LedgerT XInteger *).
Let a := (α (fun (x y: XInteger) => $ (xIntPlus x y ) : LedgerT XInteger) (#$xInt2)) : XInteger -> LedgerT XInteger.
Let b := α a (#$xInt100).
Check b :LedgerT XInteger.



Lemma foo1:  eval_state b default  = 102 .
Proof.
    compute.
    auto.
Qed.    

(* Check (ϕ (fun (x y: XInteger) => $ (xIntPlus x y ) : LedgerT XInteger)).
Check  (ϕ (fun (x: XInteger) => (↑2 U1! ValidatorBase_ι_m_validatorWallet := $ x) : LedgerT True)).
 *)
Let g := sReader (α (α (fun (x: XInteger) => (↑2 U1! ValidatorBase_ι_m_validatorWallet := $ x): LedgerT True) (#$xInt2)) (#$I)).

Lemma foo2: eval_state (↑2 D2! ValidatorBase_ι_m_validatorWallet) (exec_state g default) = 2.
Proof.
    compute.
    auto.
Qed.


Definition sWriter {X} (e : SolidityExpression X) (v : LedgerT X): LedgerT True.
Proof.
    intros.
    induction e. exact ($I).

    refine (do v' ← v; 
    modify (fun r => {$ r with m := {$ (r ->> m) with f := v' $} $} ) >> $ I).

    refine (do v' ← v;
    do o ← sReader e; 
    IHe ($ {$ o with f := v' $} )
    ).

    refine (do v' ← v;
    do k' ← sReader e1; 
    do m' ← sReader e2;
    IHe2 ($  (m' [k'] ← v') )
    ).

    exact ($I).
    exact ($I).
    exact ($I).
Defined.

Definition sAssign {X} (el er : SolidityExpression X) := 
    sWriter el (sReader er).



Check sAssign (μ DePoolContract_ι_m_association) (#$xInt0).
Check sAssign ((μ RoundsBase_ι_m_rounds) [[ μ DePoolContract_ι_m_association  ]] ^^ RoundsBase_ι_Round_ι_id ) 
              ((#$xHMapEmpty) [[ μ DePoolContract_ι_m_association ]] ^^ contractAddress).

Notation " a ':=' b " :=  ( sAssign a b ) (at level 100).

Check ((μ RoundsBase_ι_m_rounds) [[ μ DePoolContract_ι_m_association  ]] ^^ RoundsBase_ι_Round_ι_id ) := 
              ((#$xHMapEmpty) [[ μ DePoolContract_ι_m_association ]] ^^ contractAddress).

Notation " a ':=' b ; t" :=  ( let a :=  sReader b in t) (at level 100).

Check a :=  ((#$xHMapEmpty) [[ μ DePoolContract_ι_m_association ]] ^^ contractAddress) ; a.

Check b.
Check a := #b; a.




End SML.
