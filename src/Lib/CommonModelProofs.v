Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.

Require Import FinProof.Common.
Require Import FinProof.CommonInstances.
Require Import FinProof.StateMonad2.
Require Import FinProof.StateMonadInstances.
Require Import FinProof.ProgrammingWith.

Require Import FinProof.CommonProofs.

Require Import depoolContract.SolidityNotations.
Require Import depoolContract.ProofEnvironment.
Require Import depoolContract.DePoolSpec.
(* Require Import MultiSigWallet.Proofs.Tactics. *)

Require Import Lists.List.
Import ListNotations.
Local Open Scope list_scope.

Local Open Scope struct_scope.
Local Open Scope Z_scope.


Module CommonModelProofs (sm: StateMonadSig).
Export sm.
Existing Instance monadStateT.
Existing Instance monadStateStateT.

(*TODO: wrong module to import!*)

Module DePoolSpec := DePoolSpec ProofEnvironment.XTypesSig sm.
Import DePoolSpec.
Import LedgerClass.
Import SolidityNotations.

Local Open Scope solidity_scope.

Set Typeclasses Iterative Deepening.
(*Set Typeclasses Depth 1.
Set Typeclasses Strict Resolution. *)
(* Set Typeclasses Debug.  *)
(* Set Typeclasses Unique Instances. 
Unset Typeclasses Unique Solutions. *)

(* Existing Instance monadStateT.
Existing Instance monadStateStateT. *)

(* more generic proofs *)

Ltac destructMonads := compute; destruct monadStateStateT; destruct monadStateT.


(* Lemma requireOldM_eval_correct1: forall {S X} (b:bool) (f: StateT S  (option X)) l,
                         b = true ->
                         eval_state (requireOldM b f) l = eval_state f l.
Proof.
 intros. rewrite H. compute. auto.
Qed.

Lemma requireOldM_eval_correct2: forall {S X} (b:bool) (f: StateT S (option X)) l,
                         b = false ->  
                         eval_state (requireOldM b f) l = None.
Proof.
 intros. rewrite H. destructMonads. rewrite rununit. auto. 
Qed.

Lemma requireOld_eval_correct1: forall {S X} (b:bool) (f: StateT S  X) l,
                         b = true ->
                         eval_state (requireOld b f) l = Some (eval_state f l).
Proof.
 intros. rewrite H. destructMonads.
 rewrite runbind. remember (run X f l). destruct p. rewrite rununit. auto.
Qed.

Lemma requireOld_eval_correct2: forall {S X} (b:bool) (f: StateT S  X) l,
                         b = false ->
                         eval_state (requireOld  b f) l = None.
Proof.
 intros. rewrite H. destructMonads. rewrite rununit. auto. 
Qed.

Lemma requireOld_exec_correct1: forall {S X} (b:bool) (f: StateT S  X) l,
                         b = true ->
                         exec_state (requireOld b f) l = exec_state f l.
Proof.
 intros. rewrite H. destructMonads. 
 rewrite runbind. remember (run X f l). destruct p. rewrite rununit. auto.
Qed.

Lemma requireOld_exec_correct2: forall {S X} (b:bool) (f: StateT S X) l,
                         b = false ->  
                         exec_state (requireOld b f) l = l.
Proof.
 intros. rewrite H. destructMonads. rewrite rununit. auto. 
Qed.
*)
(* Check eval_state (do _ ← require _ _ ??; _) _. *)
Lemma requireE_eval_correct1: forall {S X E} (b:bool) (e: E) (f: StateT S (ErrorValue X E) ) l,
                         b = true ->
                         eval_state (do _ ← require b e ??; f) l = eval_state f l.
Proof.
 intros. rewrite H. unfold require. simpl. rewrite left_unit. simpl. auto.
Qed. 

Lemma requireE_eval_correct2: forall {S X E} (b:bool) (e: E) (f: StateT S (ErrorValue X E)) l,
                         b = false ->
                         eval_state (do _ ← require b e ??; f) l = Error e.
Proof.
 intros. rewrite H. unfold require. simpl. rewrite left_unit. simpl. rewrite eval_unit. auto.
Qed. 

Lemma requireE_eval_correct3: forall {S X E} (b:bool) (e x: E) (f: StateT S (ErrorValue X E)) l,
                         (b = false /\ (x = e))  \/ (b = true /\ eval_state f l = Error x) <->
                         eval_state (do _ ← require b e ??; f) l = Error x.
Proof.
 intros. split. intros. inversion H. rewrite requireE_eval_correct2.
 inversion H0. congruence. inversion H0. congruence.
 inversion H0. rewrite requireE_eval_correct1. auto. auto. 
 intros. destruct b. right. split. auto. rewrite requireE_eval_correct1 in H. auto.
 auto. left. rewrite requireE_eval_correct2 in H. split. auto. inversion H.  auto.
 auto.
Qed.

Lemma requireE_eval_correct4: forall {S X E} (b:bool) e (v: X) (f: StateT S (ErrorValue X E)) l,
                         (b = true /\ eval_state f l = Value v) <->
                         eval_state (do _ ← require b e ??; f) l = Value v.
Proof.
 intros. split. intros. inversion H.
 rewrite requireE_eval_correct1; auto.
 intros. split. destruct b. auto.
 rewrite requireE_eval_correct2 in H. inversion H. auto.
 destruct b. rewrite requireE_eval_correct1 in H. auto. auto.
 rewrite requireE_eval_correct2 in H. inversion H. auto.
Qed.

Lemma require_eval_correct1: forall {S X E} (b:bool) (e: E) (f: StateT S X) l,
                         b = true ->
                         eval_state (do _ ← require b e ?; f) l = Value (eval_state f l).
Proof.
 intros. rewrite H. unfold require. simpl. rewrite left_unit. simpl. 
 rewrite eval_bind2. rewrite eval_unit. 
 auto.
Qed. 


Lemma require_eval_correct2: forall {S X E} (b:bool) (e: E) (f: StateT S X) l,
                         b = false <->
                         eval_state (do _ ← require b e ?; f) l = Error e.
Proof.
 intros. split; intros. rewrite H.
 unfold require. simpl. rewrite left_unit. simpl. rewrite eval_unit. auto.
 intros. destruct b. rewrite require_eval_correct1 in H. inversion H.
 auto. auto.
Qed.

Lemma require_eval_correct2': forall {S X E} (b:bool) (x e: E) (f: StateT S X) l,
                         b = false /\ x = e <->
                         eval_state (do _ ← require b e ?; f) l = Error x .
Proof.
 intros. split; intros. inversion_clear H.
 rewrite (require_eval_correct2 (S:=S) (X:=X) (E:=E)) in H0.
 rewrite H0. congruence. remember b. destruct b0. 
 rewrite require_eval_correct1 in H.
 discriminate. auto. split. auto.
 rewrite Heqb0 in H. symmetry in Heqb0.
 rewrite (require_eval_correct2 (S:=S) (X:=X) (E:=E)) in Heqb0.
 rewrite H in Heqb0. congruence.
Qed.
 

Lemma require_exec_correct1: forall {S X E} (b:bool) (e: E) (f: StateT S X) l,
                            b = true ->
                            exec_state (do _ ← require b e ?; f) l = exec_state f l.
Proof.
 intros. rewrite H.
 unfold require. simpl. rewrite left_unit. simpl. 
  rewrite exec_bind. rewrite exec_unit. auto. 
Qed.

Lemma require_exec_correct2: forall {S X E} (b:bool) (e: E) (f: StateT S X) l,
                         b = false ->  
                         exec_state (do _ ← require b e ?; f) l = l.
Proof.
 intros. rewrite H.
 unfold require. simpl. rewrite left_unit. simpl. rewrite exec_unit. auto.
Qed.


Lemma requireE_exec_correct1: forall {S X E} (b:bool) (e: E) (f: StateT S (ErrorValue X E)) (l:S),
                         b = false ->  
                         exec_state (do _ ← require b e ??; f) l = l.
Proof.
 intros. rewrite H.
 unfold require. simpl. rewrite left_unit. simpl. rewrite exec_unit. auto.
Qed.

Lemma requireE_exec_correct2: forall {S X E} (b:bool) (e: E) (f: StateT S (ErrorValue X E)) l,
                            b = true ->
                            exec_state (do _ ← require b e ??; f) l = exec_state f l.
Proof.
 intros. rewrite H.
 unfold require. simpl. rewrite left_unit. simpl. auto.
Qed.


Lemma errorBindCorrect1: forall (S X Y E: Type) (f:StateT S (ErrorValue X E)) 
                                      (g: X -> StateT S Y) l n, 
eval_state f l = Error n ->
eval_state (do x ← f ?; g x) l = Error n.
Proof.
 intros. rewrite eval_bind2.
 rewrite H. simpl.
 rewrite eval_unit. auto.
Qed.

Lemma errorBindCorrect2: forall S X Y E (f:StateT S (ErrorValue X E)) 
                                (g: X -> StateT S Y) l x, 
eval_state f l = Value x ->
eval_state (do x ← f ?; g x) l = Value (eval_state (g x) (exec_state f l)).
Proof.
 intros. rewrite eval_bind2.
 rewrite H. simpl.
 rewrite eval_bind2. rewrite eval_unit. auto.
Qed.

Lemma errorBindCorrect3: forall S X Y E (f:StateT S (ErrorValue X E)) 
                                      (g: X -> StateT S (ErrorValue Y E)) l n, 
eval_state f l = Error n ->
eval_state (do x ← f ??; g x) l = Error n.
Proof.
 intros. rewrite eval_bind2.
 rewrite H. simpl. rewrite eval_unit. auto.
Qed.

Lemma errorBindCorrect4: forall S X Y E (f:StateT S (ErrorValue X E)) 
                                (g: X -> StateT S (ErrorValue Y E)) l x, 
eval_state f l = Value x ->
eval_state (do x ← f ??; g x) l = eval_state (g x) (exec_state f l).
Proof.
 intros. rewrite eval_bind2.
 rewrite H. simpl. auto.
Qed.

Lemma errorBindCorrect5: forall S X Y E (f:StateT S (ErrorValue X E)) 
                                (g: X -> StateT S (ErrorValue Y E)) l x, 
eval_state f l = Value x ->
exec_state (do x ← f ??; g x) l = exec_state (g x) (exec_state f l).
Proof.
 intros. rewrite exec_bind.
 rewrite H. simpl. auto.
Qed.

Lemma errorBindCorrect3': forall S X Y E (f:StateT S (ErrorValue X E)) 
                                      (g: X -> StateT S (ErrorValue Y E)) l n, 
eval_state (do x ← f ??; g x) l = Error n <->
(eval_state f l = Error n) \/
(exists v, eval_state f l = Value v /\ eval_state (g v) (exec_state f l) = Error n).
Proof.
 split. intros. 
rewrite eval_bind2 in H.
 remember (eval_state f l).
  destruct e. unfold xErrorMapDefaultF in H.
 unfold errorMapDefaultF in H. simpl in H. rewrite eval_unit in H.
  inversion H. left. auto.
 right.  exists x. split; auto.
 intros.
 inversion_clear H. apply errorBindCorrect3. apply H0.
 inversion_clear H0. inversion_clear H.
 rewrite <- H1.
 apply errorBindCorrect4. apply H0.
Qed.


(*TODO: define notModifedState by equalRelativeState*)
Definition notModifiedState {S X Y} (f: StateT S X) (m: StateT S Y) := forall s, 
                        eval_state f s = eval_state f (exec_state m s).

Lemma notModifiedState_correct: forall {S X Y} (f: StateT S X) (m: StateT S Y) s,
                 notModifiedState f m ->
                 eval_state f s = eval_state f (exec_state m s).
Proof. auto. Qed.

Definition equalRelativeState {S X Y1 Y2} (f: StateT S X) (m1: StateT S Y1) (m2: StateT S Y2) := forall s, 
                        eval_state f (exec_state m1 s) = eval_state f (exec_state m2 s).

Definition commuteRelativeState {S X Y1 Y2} (f: StateT S X) (m1: StateT S Y1) (m2: StateT S Y2) := forall s, 
                        eval_state f (exec_state (m1 >> m2)  s) = eval_state f (exec_state (m2 >> m1) s).

Lemma equalRelativeState_correct: forall {S X Y1 Y2} (f: StateT S X) (m1: StateT S Y1) (m2: StateT S Y2) s,
                 equalRelativeState f m1 m2 ->
                 eval_state f (exec_state m1 s) = eval_state f (exec_state m2 s).
Proof. auto. Qed.

Lemma equalRelativeState_sym: forall {S X Y1 Y2} (f: StateT S X) (m1: StateT S Y1) (m2: StateT S Y2),
                 equalRelativeState f m1 m2 -> equalRelativeState f m2 m1.
Proof.
 intros. unfold equalRelativeState. unfold equalRelativeState in H.
 intros. auto.
 Qed.

Lemma equalStatesRight: forall {S  X Y Y1} (f: StateT S X) 
                       (m1: StateT S Y1) (m: StateT S Y),
                       notModifiedState f m ->
                       equalRelativeState f (m1 >> m) m1.
Proof.
 intros. unfold equalRelativeState.
 intros. rewrite ?exec_bind'.
 unfold  notModifiedState in H.
 rewrite <- H. auto.
Qed.

Lemma equalStatesLeft: forall {S  X Y Y1} (f: StateT S X) 
                       (m1: StateT S Y1) (m: StateT S Y) s,
                       equalRelativeState f m1 (m >> m1) ->
                        eval_state f (exec_state m1 s) = 
                        eval_state f (exec_state m1 (exec_state m s)).
Proof.
 intros. rewrite (equalRelativeState_correct f  m1 (m>>m1)).
 rewrite exec_bind'. auto. apply H.
 Qed.

Lemma equalRelativeState_notModified: forall {S  X Y} (f: StateT S X) (m: StateT S Y),
                         notModifiedState f m <-> equalRelativeState f get m.
Proof.
 intros. split. unfold notModifiedState. unfold equalRelativeState.
 intros. unfold exec_state. rewrite runget.
 simpl. rewrite H. unfold exec_state. auto.
 unfold notModifiedState. unfold equalRelativeState.
 intros. unfold exec_state in H. unfold exec_state.
 rewrite <- H. rewrite runget. simpl. auto.
Qed.

Lemma notModifiedLeft: forall {S  X Y} (f: StateT S X) 
                       (m1: StateT S Y) (m2: StateT S Y) s,
               equalRelativeState f m2 (m1 >> m2) -> 
               eval_state f (exec_state (m1 >> m2) s) = eval_state f (exec_state m2 s).
Proof.
  intros. rewrite exec_bind'.
  unfold equalRelativeState in H.
  remember (H s). clear Heqe.
  rewrite exec_bind' in e.  auto.
  Qed.
(*
Lemma requireOldNotModifiedState {S  X} (f: StateT S X) (m: StateT S True) (b:bool): 
                              notModifiedState f m -> 
                              notModifiedState f (requireOld b m).
Proof.
 intros. destruct b. unfold notModifiedState. intros.
 rewrite requireOld_exec_correct1. apply H. auto.
 unfold notModifiedState. intros.
 rewrite requireOld_exec_correct2. auto. auto.
 Qed.
*)
Lemma notModifiedRequire {S E X} (f: StateT S X) (m: StateT S True) (b:bool) (e: E): 
                              notModifiedState f m -> 
                              notModifiedState f (do _ ← require b e ?; m).
Proof.
 intros. destruct b. unfold notModifiedState. intros.
 rewrite require_exec_correct1. apply H. auto.
 unfold notModifiedState. intros.
 rewrite require_exec_correct2. auto. auto.
 Qed.

Lemma notModifiedBind_: forall {S  X Y1 Y2} (f: StateT S X) (m1: StateT S Y1) (m2: StateT S Y2),
                       notModifiedState f m1 ->
                       notModifiedState f m2 ->
                       notModifiedState f (m1 >> m2).
Proof.
 intros. unfold notModifiedState in H. 
 unfold notModifiedState in H0. unfold notModifiedState.
 intros. rewrite exec_bind'. rewrite <-  H0.
 auto.
Qed.

Lemma notModifiedBind: forall {S  X Y1 Y2} (f: StateT S X) (m1: StateT S Y1) (m2: Y1 -> StateT S Y2),
                       notModifiedState f m1 ->
                       (forall y, notModifiedState f (m2 y)) ->
                       notModifiedState f (m1 >>= m2).
Proof.
 intros. unfold notModifiedState in H. 
 unfold notModifiedState in H0. unfold notModifiedState.
 intros. rewrite exec_bind. rewrite <-  H0.
 auto.
Qed. 


Lemma equalRelativeBind: forall {S  X Y1 Y2 U T} (f: StateT S X)  
                                (m1: StateT S Y1) (m2: Y1 -> StateT S Y2) (h: StateT S T) (g: StateT S U),
                       equalRelativeState f h g ->
                       equalRelativeState f (m1 >> h) g ->
                       (forall y, equalRelativeState f (m2 y >> h) g) ->
                       equalRelativeState f ((m1 >>= m2) >> h) g.
Proof.
 intros. 
 unfold equalRelativeState in H. 
 unfold equalRelativeState in H0. 
 unfold equalRelativeState.
 unfold equalRelativeState in H1. intros.
 rewrite exec_bind'. rewrite exec_bind.
 remember (H1 (eval_state m1 s) (exec_state m1 s)).
 clear Heqe. rewrite exec_bind' in e.
 rewrite e. rewrite <- ?H.
 rewrite <- exec_bind'. rewrite H0.
 rewrite H. auto.
 Qed.


Lemma equalRelativeBind_: forall {S  X Y1 Y2 U T} (f: StateT S X)  
                                (m1: StateT S Y1) (m2:StateT S Y2) (h: StateT S T) (g: StateT S U),
                       equalRelativeState f h g ->
                       equalRelativeState f (m1 >> h) g ->
                       equalRelativeState f (m2 >> h) g ->
                       equalRelativeState f (m1 >> m2 >> h) g.
Proof.
 intros. unfold bind_. apply equalRelativeBind.
 auto. auto. intros. auto.
Qed.

(*FIXME: find the less weak conditions*)
Lemma equalRelativeBind_': forall {S  X Y1 Y2 T} (f: StateT S X)  
                                (m1: StateT S Y1) (m2:StateT S Y2) (h: Y2 -> StateT S T),
                       notModifiedState m2 m1 ->
                       commuteRelativeState get m1 m2 -> 
                       equalRelativeState f (m1 >> m2 >>= h) (m2 >>= (fun x => m1 >> h x)).
Proof.
 intros. 
 intros. unfold commuteRelativeState in H.
 unfold equalRelativeState. intros. unfold bind_.
 rewrite ?exec_bind. rewrite eval_bind2.
 rewrite <- ?exec_bind'. rewrite <- H.
 rewrite <- ?bind_assoc_. 
 rewrite exec_bind'. symmetry. rewrite exec_bind'.
 unfold commuteRelativeState in H0.
 remember (H0 s). unfold eval_state in e. clear Heqe.
 rewrite ?runget in e. simpl in e. rewrite e. auto.
Qed.


Lemma notModifiedFold: forall {S  X A B} 
                              (f: StateT S X) (m: B -> StateT S A) (l:list B) (a0:StateT S A),
                       notModifiedState f a0 ->
                       (forall (x:B), notModifiedState f (m x)) -> 
                       notModifiedState f (fold_left (fun a i => a >> m i) l a0).
Proof.
 intros. generalize dependent a0. induction l;intros. simpl. auto.
 simpl. apply IHl. apply notModifiedBind_. auto. auto.
 Qed. 

Lemma notModifiedUnit: forall {S  X A} 
                               (f: StateT S X) (a: A),
                       notModifiedState f (return! a).
Proof.
 intros. destructMonads.
 intros. rewrite rununit. auto.
Qed.

Lemma notModifiedFold2: forall {S  X A B} 
                               (f: StateT S X) (m: (bool*A)%type -> B -> StateT S (bool*A)%type) 
                               (l:list B) (a0: StateT S (bool * A)%type),
                       notModifiedState f a0 -> 
                       (forall p (x:B), notModifiedState f (m p x)) -> 
                       notModifiedState f (fold_left (fun (a: StateT S (bool * A)%type) (i:B) => do p ← a;
                                                        if (fst p:bool) then return! p else (m p i)) l a0).
Proof.
 intros. generalize dependent a0. induction l;intros. simpl. auto.
 simpl. apply IHl. apply notModifiedBind. auto. intros. 
 destruct (fst y). apply notModifiedUnit. auto.
 Qed.

Lemma notModifiedEFoldLeftBreakable: forall {S X A B}
                               (f: StateT S  X) (m: B -> StateT S  (bool*A)%type) 
                               (l:list B) (a0: A),
                       (forall (x:B), notModifiedState f (m x)) -> 
                       notModifiedState f (listEFoldLeftBreakableM m l a0).
Proof.
 intros. unfold listEFoldLeftBreakableM. 
 apply notModifiedFold2. apply notModifiedUnit. 
 auto. 
Qed.


Lemma notModifiedFold': forall {S  X A B} 
                              (f: StateT S X) (m: B -> StateT S A) (l:list B) (a0:StateT S A),
                       notModifiedState f a0 ->
                       (forall (x:B), notModifiedState f (a0 >> m x)) ->
                       (forall (x y:B), notModifiedState f (m x >> m y)) -> 
                       notModifiedState f (fold_left (fun a i => a >> m i) l a0).
Proof.
 intros. generalize dependent a0. induction l; intros. simpl. auto.
 simpl. apply IHl. auto. intros. rewrite bind_assoc_. 
 apply notModifiedBind_. auto. auto.
 Qed.


Lemma notModifiedFold'': forall {S  X A B} 
                              (f: StateT S X) (m: B -> StateT S A) (l:list B) (a0:StateT S A),
                       notModifiedState f a0 ->
                       (forall (x:B), notModifiedState f (a0 >> m x)) ->
                       (forall (x y:B) s, eval_state f (exec_state (m x >> m y) s) = eval_state f (exec_state (m x) s)\/
                                          eval_state f (exec_state (m x >> m y) s) = eval_state f (exec_state (m y) s)) -> 
                       notModifiedState f (fold_left (fun a i => a >> m i) l a0).
Proof.
 intros. generalize dependent a0. induction l; intros. simpl. auto.
 simpl. apply IHl. auto. intros.
 rewrite bind_assoc_. unfold notModifiedState. intros.
 rewrite exec_bind'. 
 remember (H1 a x (exec_state a0 s)). clear Heqo. clear H1. 
 inversion o. rewrite H1. unfold notModifiedState in H0.
 rewrite H0 with (x:=a). rewrite exec_bind'. auto.
 rewrite H1. unfold notModifiedState in H0.
 rewrite H0 with (x:=x). rewrite exec_bind'. auto.
Qed.

Lemma equalRelativeFold: forall {S  X Y T A B} 
                              (f: StateT S X) (g: StateT S Y) (h: StateT S T) (m: B -> StateT S A) (l:list B) (a0:StateT S A),
                       equalRelativeState f h g -> 
                       equalRelativeState f (a0 >> h) g ->
                       (forall (x:B), equalRelativeState f (m x >> h) g) -> 
                       equalRelativeState f ((fold_left (fun a i => a >> m i) l a0) >> h) g.
Proof.
 intros. generalize dependent a0. induction l;intros. simpl. auto.
 simpl. apply IHl. apply equalRelativeBind_. auto. auto. auto. 
 Qed.

Lemma foldStateToAccumulator: forall {S  X Y A B} 
                              (f: StateT S X) (m: B -> StateT S A) (l:list B) (a0:StateT S A) (a: StateT S Y) (s:S),
                      eval_state f (exec_state (fold_left (fun a i => a >> m i) l a0) (exec_state a s)) = 
                      eval_state f (exec_state (fold_left (fun a i => a >> m i) l (a >> a0)) s).
Proof.
 intros. rewrite <- exec_bind'.
 generalize dependent a0. induction l; intros. simpl. auto.
 simpl. rewrite IHl. rewrite bind_assoc_. auto.
Qed.

Lemma notModifiedFoldWithProp: 
                      forall {S X A B} 
                      (f: StateT S X) (m: B -> StateT S A) (l:list B) 
                      (a0: StateT S A) (P: StateT S Prop),
                      notModifiedState f a0 ->
                      (forall s i, (eval_state P s: Prop) -> (eval_state P (exec_state (m i) s)): Prop) ->
                      (forall s, eval_state P (exec_state a0 s) : Prop) -> 
                      (forall s i, (eval_state P s: Prop) ->
                      eval_state f (exec_state (m i) s) = eval_state f s) ->
                       notModifiedState f (fold_left (fun a i => a >> m i) l a0).
Proof.
 intros. generalize dependent a0. induction l; intros.

 simpl. auto.
 simpl. apply IHl.
 unfold notModifiedState.
 intros. rewrite exec_bind'.
 rewrite H2. auto. auto.
 intros. rewrite exec_bind'.
 apply H0. auto.
Qed.

(* a > 0 -> a + 1 > 0
a >? 0 = true  -> a + 1 >?0 = true   *)

Lemma notModifiedFoldWithBool: 
                      forall {S X A B} 
                      (f: StateT S X) (m: B -> StateT S A) (l:list B) 
                      (a0: StateT S A) (P: StateT S bool),
                      notModifiedState f a0 ->
                      (forall s i, (eval_state P s = true) -> (eval_state P (exec_state (m i) s)) = true) ->
                      (forall s, eval_state P (exec_state a0 s) = true) -> 
                      (forall s i, (eval_state P s = true) ->
                      eval_state f (exec_state (m i) s) = eval_state f s) ->
                       notModifiedState f (fold_left (fun a i => a >> m i) l a0).
Proof.
 intros. generalize dependent a0. induction l; intros.

 simpl. auto.
 simpl. apply IHl.
 unfold notModifiedState.
 intros. rewrite exec_bind'.
 rewrite H2. auto. auto.
 intros. rewrite exec_bind'.
 apply H0. auto.
Qed.

Lemma notModifiedFoldWithBoolWeak: 
                      forall {S X A B} 
                      (f: StateT S X) (m: B -> StateT S A) (l:list B) 
                      (a0: StateT S A) (P: StateT S bool) s,
                      eval_state f (exec_state a0 s) =  eval_state f s ->
                      eval_state P (exec_state a0 s) =  true -> 
                      (forall s i, (eval_state P s = true) -> (eval_state P (exec_state (m i) s)) = true) ->
                      (forall s i, (eval_state P s = true) ->
                      eval_state f (exec_state (m i) s) = eval_state f s) ->
                       eval_state f (exec_state (fold_left (fun a i => a >> m i) l a0) s) = eval_state f s.
Proof.
 intros. generalize dependent a0. induction l; intros.

 simpl. apply H.
 simpl. apply IHl.
 rewrite exec_bind'.
 rewrite H2. apply H. apply H0. rewrite exec_bind'.
 rewrite H1. auto. apply H0.
Qed.

Lemma foldExecConj: forall {S X K} (s: S) (a0: StateT S X)
                           (f: K -> StateT S X) (l: list K) (x: K),
exec_state (fold_left (fun a0 (i : K) => a0 >> f i) (l ++ [ x ]) a0) s = 
exec_state (f x) 
           (exec_state (fold_left (fun a0  (i : K) => a0 >> f i) l a0) s).
Proof.
 intros. generalize dependent a0.
 induction l; intros.
 simpl. rewrite exec_bind'.
 auto.
 simpl. rewrite IHl. auto.
Qed.


Lemma foldExecEq: forall {S X K} (s: S) (a0: StateT S X)
                           (f g: K -> StateT S X) (l: list K),
(forall i, In i l -> f i = g i) ->
exec_state (fold_left (fun a0 (i : K) => a0 >> f i) l a0) s = 
exec_state (fold_left (fun a0  (i : K) => a0 >> g i) l a0) s.
Proof.
 intros. generalize dependent a0. induction l; intros.
 simpl. auto.
 simpl. rewrite <- IHl.
 replace (g a) with (f a). auto.
 apply H. constructor. auto.
 intros. apply H. simpl. right. auto.
Qed.


Lemma foldExecBreakableEq: forall {S X K} (s: S) (a0: StateT S X)
                           (f g: X -> K -> StateT S X) (l: list K),
(forall p i, In i l -> f p i = g p i) ->
exec_state (fold_left (fun a0 (i : K) => do p ← a0; f p i) l a0) s = 
exec_state (fold_left (fun a0  (i : K) => do p ← a0; g p i) l a0) s.
Proof.
 intros. generalize dependent a0. induction l; intros.
 simpl. auto.
 simpl. rewrite <- IHl.
 replace (do p ← a0; g p a) with (do p ← a0; f p a). auto.
 apply bind_eq. extensionality p.
 apply H. constructor. auto. intros.
 apply H. simpl. right. auto.
Qed.

Lemma foldEvalBreakableEq: forall {S X K} (s: S) (a0: StateT S X)
                           (f g: X -> K -> StateT S X) (l: list K),
(forall p i, In i l -> f p i = g p i) ->
eval_state (fold_left (fun a0 (i : K) => do p ← a0; f p i) l a0) s = 
eval_state (fold_left (fun a0 (i : K) => do p ← a0; g p i) l a0) s.
Proof.
 intros. generalize dependent a0. induction l; intros.
 simpl. auto.
 simpl. rewrite <- IHl.
 replace (do p ← a0; g p a) with (do p ← a0; f p a). auto.
 apply bind_eq. extensionality p.
 apply H. constructor. auto. intros.
 apply H. simpl. right. auto.
Qed.

Lemma foldRunBreakableEq: forall {S X K} (s: S) (a0: StateT S X)
                           (f g: X -> K -> StateT S X) (l: list K),
(forall p i, In i l -> f p i = g p i) ->
run (fold_left (fun a0 (i : K) => do p ← a0; f p i) l a0) s = 
run (fold_left (fun a0  (i : K) => do p ← a0; g p i) l a0) s.
Proof.
intros.
assert (forall X (f: StateT S X) (l: S), run f l = (eval_state f l, exec_state f l)).
intros. unfold exec_state. unfold eval_state. 
destruct (run f0 l0). auto.
rewrite 2H0. rewrite (foldEvalBreakableEq s a0 f g l).
rewrite (foldExecBreakableEq s a0 f g l). auto.
auto. auto.
Qed.

Lemma fold_left_cons: forall A B (f: A -> B -> A) x l a,
fold_left f (x::l) a = fold_left f l (f a x).
Proof.
 intros. simpl. auto.
Qed.

Lemma foldBreakableExec: forall S X Y y a0 (l:S) f, 
exec_state
  (fold_left
     (fun (a : StateT S X) (y0 : Y) => do p ← a; f p y0) y a0) l = 
exec_state
  (a0 >> fold_left
     (fun (a : StateT S X) (y0 : Y) => do p ← a; f p y0) y (return! (eval_state a0 l))) l.
Proof. 
 intros. generalize dependent a0.
 generalize dependent l.
 induction y; intros.
 Opaque unit bind bind_. simpl.
 rewrite exec_bind'. rewrite exec_unit. auto.
 rewrite 2fold_left_cons. 
 rewrite IHy. symmetry. rewrite exec_bind'.
 rewrite IHy. rewrite ?exec_bind'.
 rewrite eval_bind2. rewrite eval_unit.
 rewrite exec_unit. rewrite exec_bind.
 rewrite eval_unit. rewrite exec_unit.
 rewrite eval_bind2. rewrite exec_bind.
 auto.
 Transparent unit bind bind_.
Qed.

Lemma foldBreakableEval: forall S X Y y a0 (l:S) f, 
eval_state
  (fold_left
     (fun (a : StateT S X) (y0 : Y) => do p ← a; f p y0) y a0) l = 
eval_state
  (a0 >> fold_left
     (fun (a : StateT S X) (y0 : Y) => do p ← a; f p y0) y (return! (eval_state a0 l))) l.
Proof. 
 intros. generalize dependent a0.
 generalize dependent l.
 induction y; intros.
 Opaque unit bind bind_. simpl.
 rewrite eval_bind. rewrite eval_unit. auto.
 rewrite 2fold_left_cons. 
 rewrite IHy. symmetry. rewrite eval_bind.
 rewrite IHy. rewrite ?eval_bind.
 rewrite eval_bind2. rewrite eval_unit.
 rewrite exec_unit. rewrite exec_bind.
 rewrite eval_unit. rewrite exec_unit.
 rewrite eval_bind2. rewrite exec_bind.
 auto.
 Transparent unit bind bind_.
Qed.

Lemma foldBreakableRun: forall S X Y y a0 (l:S) f, 
run
  (fold_left
     (fun (a : StateT S X) (y0 : Y) => do p ← a; f p y0) y a0) l = 
run
  (a0 >> fold_left
     (fun (a : StateT S X) (y0 : Y) => do p ← a; f p y0) y (return! (eval_state a0 l))) l.
Proof. 
intros.
 assert (forall X (f: StateT S X) (l: S), run f l = (eval_state f l, exec_state f l)).
 intros. unfold exec_state. unfold eval_state. 
 destruct (run f0 l0). auto.
 rewrite 2H. rewrite foldBreakableEval.
 rewrite foldBreakableExec. auto.
 Qed.

Lemma foldBreakableExecConj: forall {S X K} (a0: StateT S X)
                           (f: X -> K -> StateT S X) (s: list K) (x: K) (l:S),
exec_state
  (fold_left
     (fun (a : StateT S X) (y0 : K) => do p ← a; f p y0) (s ++ [x]) a0) l  = 

exec_state
  (do p ← fold_left (fun (a : StateT S X) (y0 : K) => do p ← a; f p y0) s a0;
   f p x) l.

Proof.
 intros. generalize dependent a0.
 induction s; intros.
 simpl. rewrite ?exec_bind. auto.
 simpl. rewrite IHs. auto.
Qed.

Lemma foldBreakableEvalConj: forall {S X K} (a0: StateT S X)
                           (f: X -> K -> StateT S X) (s: list K) (x: K) (l:S),
eval_state
  (fold_left
     (fun (a : StateT S X) (y0 : K) => do p ← a; f p y0) (s ++ [x]) a0) l  = 

eval_state
  (do p ← fold_left (fun (a : StateT S X) (y0 : K) => do p ← a; f p y0) s a0;
   f p x) l.

Proof.
 intros. generalize dependent a0.
 induction s; intros.
 simpl. rewrite ?exec_bind. auto.
 simpl. rewrite IHs. auto.
Qed.

Lemma foldBreakableRunConj: forall {S X K} (a0: StateT S X)
                           (f: X -> K -> StateT S X) (s: list K) (x: K) (l:S),
run (fold_left
        (fun (a : StateT S X) (y0 : K) => do p ← a; f p y0) (s ++ [x]) a0) l  = 
run
(do p ← fold_left (fun (a : StateT S X) (y0 : K) => do p ← a; f p y0) s a0;
 f p x) l.
Proof.  
 intros.
 assert (forall X (f: StateT S X) (l: S), run f l = (eval_state f l, exec_state f l)).
 intros. unfold exec_state. unfold eval_state. 
 destruct (run f0 l0). auto.
 rewrite 2H. rewrite foldBreakableEvalConj.
 rewrite foldBreakableExecConj. auto.
 Qed.


(* Lemma foldExec2: forall S X Y y a0 (l:S) (b: X -> bool) f, 
exec_state
  (fold_left
     (fun (a : StateT S X) (y0 : Y) => do p ← a; if b p then a else f y0) y a0) l = 
exec_state
  (a0 >> fold_left
     (fun (a : StateT S X) (y0 : Y) => do p ← a; if b p then a else f y0) y (return! (eval_state a0 l))) l.
Proof. 
 intros. generalize dependent a0.
 generalize dependent l.
 induction y; intros.
 Opaque unit bind bind_. simpl.
 rewrite exec_bind'. rewrite exec_unit. auto.
 rewrite 2fold_left_cons. 
 rewrite IHy. symmetry. rewrite exec_bind'.
 rewrite IHy. rewrite ?exec_bind'.
 rewrite eval_bind2. rewrite eval_unit.
 rewrite exec_unit. rewrite ifEval.
 rewrite eval_unit. rewrite exec_bind.
 rewrite eval_unit. rewrite exec_unit.
 rewrite ifExec. rewrite exec_unit.
 rewrite eval_bind2. rewrite ifEval.
 rewrite exec_bind. rewrite ifExec.
 rewrite ?H. auto. 

 rewrite exec_bind. rewrite eval_unit.
 rewrite exec_unit. destructIf.
 rewrite exec_unit. auto.
 auto.
 Transparent unit bind bind_.
Qed. *)

Lemma foldBreakableBreakExec: forall S X l a y f, 
exec_state
  (fold_left
     (fun (mbx : StateT S (bool * True)) (y0 : X) =>
      do p ← mbx;
      if (fst p: bool) then (return! p) else (f y0)) y a) l =
if (fst (eval_state a l): bool) then exec_state a l else
exec_state
  (fold_left
     (fun (mbx : StateT S (bool * True)) (y0 : X) =>
      do p ← mbx;
      if (fst p: bool) then (return! p) else (f y0)) y (return! (false, I))) (exec_state a l).
Proof.
 intros. remember (eval_state a l) as p.
 rewrite foldBreakableExec. rewrite exec_bind'.
 rewrite <- Heqp.
 destruct p. destruct b; unfold fst; destruct t; auto.
 generalize dependent a. induction y; intros.
 simpl. rewrite exec_unit. auto.
 rewrite fold_left_cons. rewrite foldBreakableExec.
 rewrite exec_bind'. rewrite eval_bind2.
 rewrite eval_unit. rewrite eval_unit.
 rewrite exec_bind. rewrite eval_unit.
 rewrite exec_unit. rewrite exec_unit.
 rewrite IHy. auto.
 auto.
Qed.

Lemma foldBreakableBreakEval: forall S X l a y f, 
eval_state
  (fold_left
     (fun (mbx : StateT S (bool * True)) (y0 : X) =>
      do p ← mbx;
      if (fst p: bool) then (return! p) else (f y0)) y a) l =
if (fst (eval_state a l): bool) then (true, I) else
eval_state
  (fold_left
     (fun (mbx : StateT S (bool * True)) (y0 : X) =>
      do p ← mbx;
      if (fst p: bool) then (return! p) else (f y0)) y (return! (false, I))) (exec_state a l).
Proof.
 intros. remember (eval_state a l) as p.
 rewrite foldBreakableEval. rewrite eval_bind.
 rewrite <- Heqp.
 destruct p. destruct b; unfold fst; destruct t; auto.
 generalize dependent a. induction y; intros.
 simpl. rewrite eval_unit. auto.
 rewrite fold_left_cons. rewrite foldBreakableEval.
 rewrite eval_bind. rewrite eval_bind2.
 rewrite eval_unit. rewrite eval_unit.
 rewrite exec_bind. rewrite eval_unit.
 rewrite exec_unit. rewrite exec_unit.
 rewrite IHy. auto.
 auto.
Qed.

Lemma foldBreakableBreakRun: forall S X l a y f, 
run
  (fold_left
     (fun (mbx : StateT S (bool * True)) (y0 : X) =>
      do p ← mbx;
      if (fst p: bool) then (return! p) else (f y0)) y a) l =
if (fst (eval_state a l): bool) then ((true, I), exec_state a l) else
run
  (fold_left
     (fun (mbx : StateT S (bool * True)) (y0 : X) =>
      do p ← mbx;
      if (fst p: bool) then (return! p) else (f y0)) y (return! (false, I))) (exec_state a l).
Proof.
 intros. rewrite 2run_eval_exec.
 rewrite foldBreakableBreakEval.
 rewrite foldBreakableBreakExec. 
 destruct (fst (eval_state a l)); auto.
Qed.

 


(* Lemma foldExecEq2: forall {S X K} (s1 s2: S) (a0: StateT S (bool*X))
                         (f: K -> StateT S (bool*X)) (l1 l2: list K) (d: K) (t: K->K),
(l2 = List.map t l1) ->
exec_state a0 s1 = s1 ->
exec_state a0 s2 = s2 -> 
fst (eval_state a0 s1) = false ->
fst (eval_state a0 s2) = false -> 
(forall i, exec_state (f (nth i l1 d)) s1 = exec_state (f (nth i l2 d)) s2 /\ 
           (fst (eval_state (f (nth i l1 d)) s1) = true <-> fst (eval_state (f (nth i l2 d)) s2) = true)) -> 
exec_state (fold_left (fun (a0: StateT S (bool*X)) (i : K) => do p ← a0; if (fst p: bool) then (return! p) else f i) l1 a0) s1 = 
exec_state (fold_left (fun (a0: StateT S (bool*X)) (i : K) => do p ← a0; if (fst p: bool) then (return! p) else f i) l2 a0) s2.
Proof.
 intros. generalize dependent a0. 
 generalize dependent l2. induction l1; intros.
 simpl in H. rewrite H. simpl. auto.
 simpl in H. rewrite H. simpl.
 rewrite foldExec.
 rewrite exec_bind'. 
 rewrite eval_bind2. 
 rewrite exec_bind. rewrite H1.
 
 
Abort.  *)
 

Lemma notModifiedEmbed: forall{S T X Y}`{EmbeddedType S T}
                              (f: StateT S X) (m: T -> Y),
                        notModifiedState f (↑ (ε m)).
Proof.
 intros. compute. intros. repeat destructMonads.
 rewrite runbind. rewrite runget.
 rewrite runembed0. rewrite runbind.
 rewrite runput. rewrite rununit. destruct H.
 rewrite injproj. auto.
 Qed.
 
 
Lemma equalStateEmbed: forall{S T X Y U W}`{EmbeddedType S T}
                              (f: StateT S X) (m: T -> Y) (h: StateT S U) (g: StateT S W),
                        equalRelativeState f h g -> 
                        equalRelativeState f (↑ (ε m) >> h) g.
Proof.
 intros. unfold equalRelativeState in H0. compute in H0.
 repeat destructMonads. 
 intros.
 rewrite ?runbind. rewrite runget. 
 rewrite runembed0. rewrite runbind.
 rewrite runput. rewrite rununit. destruct H.
 rewrite injproj.  auto.
 Qed.

Lemma notModifiedLifted: forall {S T X Y}`{EmbeddedType S T}
                          (f: T -> X) (m: StateT T Y),
                          notModifiedState (ε f) m ->
                          notModifiedState (↑ (ε f)) (↑ m).
Proof.
 intros. unfold notModifiedState. intros.
 rewrite liftEmbeddedStateExec2.
 rewrite eval_bind. rewrite eval_embed.
 rewrite eval_lift_embed. unfold notModifiedState in H0.
 remember (H0 (projEmbed s)). clear Heqe.
 rewrite ?eval_embed in e. auto.
Qed.

Lemma notModifiedWithMap: forall {S T X Y A B}`{EmbeddedType S T}`{XBoolEquable bool A}`{XDefault B} 
                          (f: StateT S X) (g: B -> StateT S Y) (m: T -> listPair A B) (i:A),
                          (forall k, notModifiedState f (g k)) -> 
                          notModifiedState f (withEmbeddedMapDefault m i g).
Proof. intros.
  unfold withEmbeddedMapDefault.
  apply notModifiedBind.
  apply notModifiedEmbed. intros.
  apply H2.
  Qed.

Lemma notModifiedWithMap': forall {S T X Y A B}`{EmbeddedType S T}`{XBoolEquable bool A}`{XDefault B} 
                          (f: StateT S X) (g: B -> StateT S Y) (m: T -> listPair A B) (i:A) s,
                          (forall k, eval_state f (exec_state (g k) s) = eval_state f s) -> 
                          eval_state f (exec_state (withEmbeddedMapDefault m i g) s) = eval_state f s.
Proof.
 intros. unfold withEmbeddedMapDefault.
 rewrite exec_bind. rewrite exec_lift_embed.
 remember (eval_state (↑ (ε m)) s).
 setoid_rewrite <- Heql. apply H2.
Qed.
  
Lemma equalStatesWithMap: forall {S T X Y U W A B}`{EmbeddedType S T}`{XBoolEquable bool A}`{XDefault B} 
                          (f: StateT S X) (g: B -> StateT S Y) (m: T -> listPair A B) (i:A) (h: StateT S U) (r: StateT S W),
                          equalRelativeState f h r -> 
                          (forall k, equalRelativeState f (g k >> h) r) -> 
                          equalRelativeState f (withEmbeddedMapDefault m i g >> h) r.
Proof.
 intros. unfold withEmbeddedMapDefault.
 apply equalRelativeBind. auto. apply equalStateEmbed. auto.
 intros. apply H3.
 Qed.

Lemma withMapOnExecWeak: forall {S T X Y U A B}`{EmbeddedType S T}`{XBoolEquable bool A}`{XDefault B} 
                              (f: StateT S X) (m: T -> listPair A B) (i:A) (s:S) (a: StateT S Y) (g: B -> StateT S U),
                      notModifiedState (↑ (ε m)) a ->
                      eval_state f (exec_state (withEmbeddedMapDefault m i g) (exec_state a s)) = 
                      eval_state f (exec_state (withEmbeddedMapDefault m i (fun x => a >> g x)) s).
Proof.
 intros. rewrite <- exec_bind'.
 unfold withEmbeddedMapDefault. 
 apply equalRelativeState_correct. 
 unfold bind_. rewrite <- bind_assoc2.
 apply equalRelativeBind_' .
 auto. unfold commuteRelativeState.
 intros. rewrite ?exec_bind'.
 unfold exec_state. unfold liftEmbeddedState. rewrite ?runbind.
 rewrite ?runget.
 rewrite ?runembed. rewrite ?injproj.
 rewrite ?runbind'. remember (run a s0). destruct p. simpl.
 rewrite ?runput. rewrite ?rununit. simpl. rewrite <- Heqp. simpl.
 auto.
Qed.

Lemma ifBindCommute: forall {S  X Y} (m: StateT S X) (m1: StateT S Y) (m2: StateT S Y) (b:bool),
                       m >> (if b then m1 else m2) = if b then (m >> m1) else (m >> m2).
Proof.
 intros. destruct b; auto.
Qed.


Lemma notModifiedIf: forall {S  X Y} (f: StateT S X) (m1: StateT S Y) (m2: StateT S Y) (b:bool),
                       notModifiedState f m1 ->
                       notModifiedState f m2 ->
                       notModifiedState f (if b then m1 else m2).
Proof.
 intros. unfold notModifiedState in H. 
 unfold notModifiedState in H0. unfold notModifiedState.
 intros. destruct b; auto.
Qed.

Lemma notModifiedIf': forall {S  X Y} (f: StateT S X) (m1: StateT S Y) (m2: StateT S Y) (b:bool) s,
                       eval_state f (exec_state m1 s) = eval_state f s ->
                       eval_state f (exec_state m2 s) = eval_state f s ->
                       eval_state f (exec_state (if b then m1 else m2) s) = eval_state f s.
Proof.
 intros. destruct b; auto.
Qed.

Lemma notModifiedBreakBind_: forall {S  X} 
                       (f: StateT S X) (m1 m2: StateT S (bool*True)%type),
                       notModifiedState f m1 ->
                       notModifiedState f m2 ->
                       notModifiedState f (break_bind m1 m2).
Proof.
 intros. unfold notModifiedState in H. 
 unfold notModifiedState in H0. unfold notModifiedState.
 intros. unfold break_bind.
 rewrite exec_bind. simpl. 
 rewrite <- notModifiedIf. auto. auto. auto.
Qed.

Lemma equalRelativeIf: forall {S  X Y T U} (f: StateT S X) 
                       (m1: StateT S Y) (m2: StateT S Y) (g:StateT S T) (h: StateT S U) (b:bool),
                       equalRelativeState f (m1 >> h) g ->
                       equalRelativeState f (m2 >> h) g ->
                       equalRelativeState f ((if b then (m1) else (m2)) >> h) g.
Proof.
 intros. destruct b; auto.
 Qed.
 
Lemma ifExec: forall {S X}  
                     (m1: StateT S X) (m2: StateT S X) 
                     (s:S) (b:bool),
              exec_state (if b then m1 else m2) s = 
              if b then (exec_state m1 s) else (exec_state m2 s).
Proof.
 intros. destruct b; auto.
Qed. 

Lemma ifEval: forall {S X}  
                     (m1: StateT S X) (m2: StateT S X) 
                     (s:S) (b:bool),
              eval_state (if b then m1 else m2) s = 
              if b then (eval_state m1 s) else (eval_state m2 s).
Proof.
 intros. destruct b; auto.
Qed. 
(*
Lemma modifyMapCorrect: forall {S  X} 
                        (f: S -> listPair Z X) (l:S) (x:X) (n:Z) (i:listPair Z X -> S -> S),
                        (forall x l, f (i x l) = x) ->
       eval_state (do m ← ε f; 
                   return! hmapLookup Z.eqb n m)
       (exec_state (modifyXHMap1 f i n x) l) = Some x.
Proof.
 intros. unfold modifyXHMap1.
 unfold hmapInsert. 
 Opaque hmapIsMember get put run bind bind_ embed_fun unit modify exec_state.
 rewrite exec_bind.
 rewrite eval_bind2. unfold eval_state. rewrite rununit.
 rewrite runembed. 
 simpl fst.
 rewrite exec_bind'. rewrite exec_unit.
 Transparent exec_state. unfold exec_state. rewrite runembed. simpl.
 Transparent modify. unfold modify. unfold compose. 
 rewrite getput. rewrite runbind. rewrite runembed.
 rewrite runput. simpl.
 Transparent get put run bind bind_ embed_fun unit modify exec_state.
 rewrite H.
 Opaque hmapLookup hmapIsMember adjustListPair Z.eqb. compute.
 apply modifyMapCorrect_helper. unfold boolEquivalence. intros.
 apply intBoolEquivalence.  intros. apply zeqb_refl.
 Transparent hmapLookup hmapIsMember adjustListPair Z.eqb.
Qed.



Lemma modifyMapCorrect': forall {S T X}`{EmbeddedType T S}
                        (f: S -> listPair Z X) (l:T) (x:X) (n:Z) (i:listPair Z X -> S -> S),
                        (forall x l, f (i x l) = x) ->
       eval_state (do m ← ↑ (ε f); 
                   return! hmapLookup Z.eqb n m)
       (exec_state (↑ (modifyXHMap1 f i n x)) l) = Some x.
Proof.
 intros. rewrite liftEmbeddedStateBind.
 rewrite liftEmbeddedStateExec. rewrite  eval_bind.
 rewrite eval_embed_bind. apply modifyMapCorrect.
 auto.
Qed.

Lemma modifyMapDefaultCorrect': forall {S T X}`{EmbeddedType T S}
                        (f: S -> listPair Z X) (l:T) (x:X) (n:Z) (i:listPair Z X -> S -> S) d,
                        (forall x l, f (i x l) = x) ->
       eval_state (do m ← ↑ (ε f); 
                   return! hmapFindWithDefault d Z.eqb n m)
       (exec_state (↑ (modifyXHMap1 f i n x)) l) = x.
Proof.
 intros. unfold hmapFindWithDefault.
 rewrite eval_bind2. rewrite eval_unit.
 remember (modifyMapCorrect' f l x n i H0). clear Heqe.
 rewrite eval_bind2 in e. rewrite eval_unit in e.
 setoid_rewrite e. auto.
Qed. 
*)

Lemma modifyMapCorrect2: forall {S  X} 
                        (f: S -> listPair Z X) (l:S) (x:X) (n k:Z) (i:listPair Z X -> S -> S),
                        (forall x l, f (i x l) = x) ->
       n <> k ->
       eval_state (do m ← ε f; 
                   return! hmapLookup Z.eqb n m)
       (exec_state (modifyXHMap1 f i k x) l) = 
      eval_state (do m ← ε f; 
                   return! hmapLookup Z.eqb n m) l.
Proof.
 intros. unfold modifyXHMap1.
 unfold hmapInsert. 
 Opaque hmapIsMember get put run bind bind_ embed_fun unit modify exec_state.
 rewrite ?exec_bind. rewrite exec_embed. rewrite eval_embed. 
 rewrite ?eval_bind2. unfold eval_state. 
 rewrite ?rununit.
 rewrite ?runembed. simpl. 
 rewrite exec_bind'. rewrite exec_unit.
 Transparent exec_state. unfold exec_state. 
 Transparent modify. unfold modify. unfold compose. 
 rewrite getput. rewrite runbind. rewrite runembed.
 rewrite runput. simpl. Transparent hmapIsMember get put run bind bind_ embed_fun unit modify exec_state.
 rewrite H. unfold Datatypes.id. 
 apply modifyMapCorrect2_helper.
 unfold boolEquivalence. intros. apply intBoolEquivalence.
 auto.
Qed.

Lemma modifyMapCorrect2': forall {S T  X}`{EmbeddedType T S}
                        (f: S -> listPair Z X) (l:T) (x:X) (n k:Z) (i:listPair Z X -> S -> S),
                        (forall x l, f (i x l) = x) ->
                        n <> k ->
       eval_state (do m ← ↑ (ε f); 
                   return! hmapLookup Z.eqb n m)
       (exec_state (↑ (modifyXHMap1 f i k x)) l) = 
      eval_state (do m ← ↑ (ε f); 
                   return! hmapLookup Z.eqb n m) l.

Proof.
 intros. rewrite ?liftEmbeddedStateBind.
 rewrite ?liftEmbeddedStateExec. rewrite  ?eval_bind.
 rewrite ?eval_embed_bind.
 rewrite modifyMapCorrect2. rewrite ?eval_bind2.
 rewrite ?exec_embed. rewrite eval_embed.
 unfold eval_state. rewrite rununit.
 unfold embed_funInducted. rewrite runembed. simpl.
 unfold compose.
 auto. auto. auto.
Qed.

Lemma modifyMapDefaultCorrect2': forall {S T X}`{EmbeddedType T S}
                        (f: S -> listPair Z X) (l:T) (x:X) (n k:Z) (i:listPair Z X -> S -> S) d,
                        (forall x l, f (i x l) = x) ->
       n <> k -> 
       eval_state (do m ← ↑ (ε f); 
                   return! hmapFindWithDefault d Z.eqb n m)
       (exec_state (↑ (modifyXHMap1 f i k x)) l) = 
       eval_state (do m ← ↑ (ε f); 
                   return! hmapFindWithDefault d Z.eqb n m) l.
Proof.
 intros. unfold hmapFindWithDefault.
 rewrite eval_bind2. rewrite eval_unit.
 remember (modifyMapCorrect2' f l x n k i H0 H1). clear Heqe.
 rewrite eval_bind2 in e. rewrite eval_unit in e.
 setoid_rewrite e. symmetry.
 rewrite eval_bind2. rewrite eval_unit.
 rewrite eval_bind2. rewrite eval_unit.
 auto.
Qed.

(*
(fun r : PendingLimitP =>
              ProgrammingWith.wrapWith r votes_ι_PendingLimit
                (votes_ι_PendingLimit r) [sender]← xBoolFalse
                Struct_PendingLimit Acc_PendingLimit__votes)
                f [k] ^ g [n]
*)

Existing Instance xint_booleq.
(*
Lemma modifyMapFieldMapCorrect:  forall {S T X}`{XDefault X}`{XDefault T} 
                                 (f: S -> listPair Z T) (l:S)
                                 (x:X) (n k:Z) (i:listPair Z T -> S -> S)
                                 (g: T -> listPair Z X) (s:X) t z,
                                 hmapLookup Z.eqb k (f l) = Some z -> 
                                 g default = [ ] -> 
                                 (forall x l, f (i x l) = x) ->
                                 (forall r, ((t r) ->> g) [n] = s) ->
((eval_state (ε f)
    (exec_state
       ((modifyXHMapRecordByFun f i t k)) l)) [k] ->> g) [n] = s.
Proof.
 intros. unfold modifyXHMapRecordByFun.
 rewrite exec_bind.
 rewrite exec_embed.
 remember ((eval_state (ε f) l) [k] ?).
 setoid_rewrite <- Heqy.
 destruct y. simpl.
 unfold modify. rewrite exec_bind'.
 rewrite exec_unit.
 rewrite exec_bind.
 unfold compose.
 rewrite exec_get.
 rewrite eval_get.
 rewrite exec_put.
 rewrite 2eval_embed. rewrite eval_embed in Heqy.
 rewrite H3. unfold hmapFindWithDefault.
 unfold hmapInsert.
 assert (hmapIsMember Z.eqb k (f l) = true).
 apply memberLookup.
 unfold boolEquivalence. intros. apply intBoolEquivalence.
 exists t0. rewrite Heqy. simpl. auto.
 setoid_rewrite H5. simpl.
 rewrite lookupAdjust2.
 simpl. unfold Datatypes.id.
 unfold hmapFindWithDefault in H4.
 unfold Datatypes.id in H4.
 rewrite H4. auto.
 unfold boolEquivalence. intros. apply intBoolEquivalence.
 auto.  simpl.
 rewrite eval_embed. rewrite exec_unit.
 unfold hmapFindWithDefault.
 assert (hmapLookup Z.eqb k (f l) = None).
 rewrite  eval_embed in Heqy.
 rewrite Heqy.
 simpl. auto.
 rewrite H5. simpl. unfold get_field.
 rewrite H2.
 unfold  hmapLookup.
 simpl. congruence.
Qed.

Lemma modifyMapFieldMapCorrect2:  forall {S T X}`{XDefault X}`{XDefault T} 
                                 (f: S -> listPair Z T) (l:S)
                                 (x:X) (n k:Z) (i:listPair Z T -> S -> S)
                                 (g: T -> listPair Z X) (s:X) t,
                                 (* hmapLookup Z.eqb k (f l) = Some z ->  *)
                                 g default = [ ] -> 
                                 (forall x l, f (i x l) = x) ->
                                 (forall r, ((t r) ->> g) [n] = s) ->
((eval_state (ε f)
    (exec_state
       ((modifyXHMapRecordByFunDefault f i t k)) l)) [k] ->> g) [n] = s.
Proof.
intros. unfold modifyXHMapRecordByFunDefault.
 rewrite exec_bind.
 rewrite exec_embed.
 rewrite ?eval_embed.
 unfold modify. rewrite exec_bind'.
 rewrite exec_unit.
 rewrite exec_bind.
 unfold compose.
 rewrite exec_get.
 rewrite eval_get.
 rewrite exec_put.
 rewrite H2.
 unfold hmapFindWithDefault.
 unfold hmapInsert. simpl.
 remember (hmapIsMember Z.eqb k (f l)).
 setoid_rewrite <- Heqb.
 destruct b.
 rewrite lookupAdjust2.
 simpl. unfold Datatypes.id.
 assert (exists y, hmapLookup Z.eqb k (f l) = Some y).
 apply memberLookup.
 unfold boolEquivalence. intros. apply intBoolEquivalence.
 auto. inversion H4. setoid_rewrite H5.
 simpl. unfold hmapFindWithDefault in H3. 
 rewrite H3. auto.
 unfold boolEquivalence. intros. apply intBoolEquivalence.
 auto. unfold Datatypes.id.
 unfold hmapLookup.
 simpl. assert (k =? k = true).
 apply Z.eqb_eq. auto.
 rewrite H4. simpl.
 unfold Datatypes.id.
 match goal with
 | |- optionMapDefault (fun x0 : X => x0)
  (hd_error ?m) default = s => remember m
 end. unfold get_field in Heql0.
 unfold hmapFindWithDefault in H3.
 match goal with
 | H: l0 = List.map snd
          (filter (fun p : Z * X => n =? fst p)
             (g
                (t ?r))) |- _ => remember r
 end.
 rewrite Heql0.
 unfold Datatypes.id in H3.
 unfold hmapLookup in H3.
 simpl in H3.
 unfold Datatypes.id in H3.
 unfold get_field in H3.
 rewrite H3. auto.
Qed.

Lemma modifyMapFieldMapCorrectLift: forall {S T L X}`{XDefault X}`{XDefault T}`{EmbeddedType L S}
                                 (f: S -> listPair Z T) (l:L)
                                 (x:X) (n k:Z) (i:listPair Z T -> S -> S)
                                 (g: T -> listPair Z X) (s:X) t z,
                                 hmapLookup Z.eqb k (f (projEmbed l)) = Some z -> 
                                 g default = [ ] -> 
                                 (forall x l, f (i x l) = x) ->
                                 (forall r, ((t r) ->> g) [n] = s) ->
((eval_state (↑(ε f))
    (exec_state
       (↑ (modifyXHMapRecordByFun f i t k)) l)) [k] ->> g) [n] = s.
Proof.
 intros.
 rewrite liftEmbeddedStateExec2.
 rewrite eval_bind. 
 apply (modifyMapFieldMapCorrect f (projEmbed l) x n k i g s t z).
 auto. auto. auto. auto.
Qed.

Lemma modifyMapFieldMapCorrect3:  forall {S T X}`{XDefault X}`{XDefault T} 
                                 (f: S -> listPair Z T) (l:S)
                                 (x:X) (k:Z) (i:listPair Z T -> S -> S)
                                 (s:T) t z,
                                 hmapLookup Z.eqb k (f l) = Some z -> 
                                 (forall x l, f (i x l) = x) ->
                                 t z = s ->
((eval_state (ε f)
    (exec_state
       ((modifyXHMapRecordByFun f i t k)) l)) [k]) = s.
Proof.
 intros.
 unfold modifyXHMapRecordByFun.
 rewrite exec_bind.
 rewrite exec_embed.
 remember ((eval_state (ε f) l) [k] ?).
 setoid_rewrite <- Heqy.
 destruct y. simpl.
 unfold modify. rewrite exec_bind'.
 rewrite exec_unit.
 rewrite exec_bind.
 unfold compose.
 rewrite exec_get.
 rewrite eval_get.
 rewrite exec_put.
 rewrite 2eval_embed. rewrite eval_embed in Heqy.
 assert (Some t0 = Some z).
 rewrite Heqy. rewrite <- H1. simpl. auto.
 inversion H4.  
 rewrite H3. unfold hmapFindWithDefault.
 unfold hmapInsert.
 assert (hmapIsMember Z.eqb k (f l) = true).
 apply memberLookup.
 unfold boolEquivalence. intros. apply intBoolEquivalence.
 exists t0. rewrite Heqy. simpl. auto.
 setoid_rewrite H5. simpl.
 unfold Datatypes.id. rewrite H2.
 rewrite lookupAdjust2. simpl. auto.
 unfold boolEquivalence. intros. apply intBoolEquivalence.
 auto.  simpl.
 rewrite eval_embed. rewrite exec_unit.
 unfold hmapFindWithDefault.
 assert (hmapLookup Z.eqb k (f l) = None).
 rewrite  eval_embed in Heqy.
 rewrite Heqy.
 simpl. auto.
 rewrite H4. simpl.  congruence.
Qed.


Lemma modifyMapFieldMapCorrect3':  forall {S T X}`{XDefault X}`{XDefault T} 
                                 (f: S -> listPair Z T) (l:S)
                                 (x:X) (k:Z) (i:listPair Z T -> S -> S)
                                  t,
                                 hmapLookup Z.eqb k (f l) = None -> 
                                 (forall x l, f (i x l) = x) ->
((eval_state (ε f)
    (exec_state
       ((modifyXHMapRecordByFun f i t k)) l)) [k]) = default.
Proof.
 intros.
 unfold modifyXHMapRecordByFun.
 rewrite exec_bind.
 rewrite exec_embed.
 remember ((eval_state (ε f) l) [k] ?).
 setoid_rewrite <- Heqy.
 destruct y. rewrite eval_embed in Heqy.
 simpl in Heqy.
 congruence. simpl.
 rewrite eval_embed. rewrite exec_unit.
 unfold hmapFindWithDefault.
 rewrite H1. compute. auto.
Qed.
*)
Lemma modifyMapCorrect3: forall {X}`{XDefault X}
                        (m: listPair Z X) (k:Z) (x:X),
                        (m [k]← x) [k] = x.
Proof.
 intros. unfold hmapFindWithDefault.
 remember (m [k]← x [k] ?).
 destruct y. symmetry in Heqy.
 assert (exists z : X, hmapLookup Z.eqb k (m [k]← x) = Some z).
 exists x0. auto.
 apply memberLookup in H0.
 remember ((hmapIsMember eqb k m)).
 unfold hmapInsert in H0.  unfold hmapInsert in Heqy.
 destruct y. rewrite <- Heqy0 in H0.
 rewrite <- Heqy0 in Heqy. simpl in H0.
 remember (adjustListPair Z.eqb (fun _ : X => x) k m).
 remember Heql.
 symmetry in Heqy0. apply memberLookup in Heqy0.
 inversion Heqy0. clear Heqe.
 apply (lookupAdjust1  (z:=x1) (k:=k)) in e.
 inversion_clear e. inversion_clear H3.
 simpl. unfold Datatypes.id.
 apply H4 in H1. unfold hmapInsert in Heqy.
 simpl in Heqy.
 rewrite <- Heql in Heqy. setoid_rewrite Heqy in H1.
 inversion H1. auto.
 unfold boolEquivalence. intros. apply intBoolEquivalence.
 unfold boolEquivalence. intros. apply intBoolEquivalence.
 simpl. rewrite <- Heqy0 in  H0. rewrite <- Heqy0 in  Heqy.
 simpl in H0. simpl in Heqy.
 unfold Datatypes.id in Heqy. unfold Datatypes.id in H0.
 unfold hmapLookup in Heqy. simpl in Heqy.
 rewrite Z.eqb_refl in Heqy. 
 simpl in Heqy. inversion Heqy. compute. auto.
 unfold boolEquivalence. intros. apply intBoolEquivalence.
 unfold hmapInsert in Heqy.
 remember (hmapIsMember eqb k m).
 simpl. destruct y. simpl in Heqy.
 remember (adjustListPair Z.eqb (fun _ : X => x) k m).
 symmetry in Heqy0. apply memberLookup in Heqy0. inversion Heqy0.
 apply (lookupAdjust1  (z:=x0) (k:=k)) in Heql.
 inversion_clear Heql. inversion_clear H2. 
 apply H3 in H0. setoid_rewrite <- Heqy in H0.
 inversion H0. 
 unfold boolEquivalence. intros. apply intBoolEquivalence.
 unfold boolEquivalence. intros. apply intBoolEquivalence.
 simpl in Heqy. unfold hmapLookup in Heqy.
 simpl in Heqy. rewrite Z.eqb_refl in Heqy.  simpl in Heqy.
 inversion Heqy.
Qed.

Lemma modifyMapFieldMapCorrect3Default:  forall {S T X}`{XDefault X}`{XDefault T} 
                                 (f: S -> listPair Z T) (l:S)
                                 (x:X) (k:Z) (i:listPair Z T -> S -> S)
                                 (s:T) t,
                                 (forall x l, f (i x l) = x) ->
                                 t (f l) [k] = s ->
((eval_state (ε f)
    (exec_state
       ((modifyXHMapRecordByFunDefault f i t k)) l)) [k]) = s.
Proof.
 intros.
 unfold modifyXHMapRecordByFunDefault.
 rewrite exec_bind.
 rewrite exec_embed.
 (* remember ((eval_state (ε f) l) [k] ?). 
 setoid_rewrite <- Heqy.
 destruct y. simpl.*)
 unfold modify. rewrite exec_bind'.
 rewrite exec_unit.
 rewrite exec_bind.
 unfold compose.
 rewrite exec_get.
 rewrite eval_get.
 rewrite exec_put.
 rewrite 2eval_embed. 
 rewrite ?H1.
 rewrite modifyMapCorrect3.
 auto.
 Qed.

Lemma modifyStateCorrect: forall {S T X}`{EmbeddedType S T} (f:T->X) (l:S) m, 
eval_state (↑ (ε f)) (exec_state (↑ (modify m)) l) = f (m (projEmbed l)).
Proof.
 intros. rewrite liftEmbeddedStateExec2.
 rewrite eval_bind. unfold modify.
 rewrite exec_bind. unfold compose.
 rewrite exec_put. rewrite eval_embed.
 rewrite eval_get. auto.
Qed.


Lemma adjustListPairDouble:
forall X x y k m,
adjustListPair Z.eqb (fun _ : X => y) k
  (adjustListPair Z.eqb (fun _ : X => x) k m) =
adjustListPair Z.eqb (fun _ : X => y) k m.
Proof.
 intros. induction m.
 simpl. auto.
 simpl. destruct a.
 remember (k =? z).
 destruct  b.
 simpl. rewrite Z.eqb_refl.
 rewrite IHm. auto.
 simpl. rewrite <- Heqb. rewrite IHm.  auto.
 Qed.
(*
Lemma memberFalseAdjust:
forall X x k m, hmapIsMember eqb k m = false ->
      adjustListPair Z.eqb (fun _ : X => x) k m = m.
Proof.
 intros.
 induction m.
 simpl. auto.
 simpl. destruct a.
 replace (k =? z) with false.
 rewrite IHm. auto. 
 simpl in H. apply memberLookup2.
 unfold boolEquivalence. intros. apply intBoolEquivalence.
 apply memberLookup2 in H.
 unfold  hmapLookup in H.
 simpl in H.
 remember (k=?z). destruct b.
 simpl in H. inversion H.
 apply H.
 unfold boolEquivalence. intros. apply intBoolEquivalence.
 apply memberLookup2 in H.
 unfold  hmapLookup in H.
 simpl in H.
 remember (k=?z). destruct b.
 simpl in H. inversion H. auto.
 unfold boolEquivalence. intros. apply intBoolEquivalence.
 Qed.

Lemma modifyMapCorrect4: forall {X}`{XDefault X}
                        (m: listPair Z X) (k:Z) (x y:X),
                        (m [k]← x) [k] ← y = 
                        (m [k]← y).
Proof.
 intros.
 unfold hmapInsert.
 remember (hmapIsMember eqb k m).
 destruct  y0.
 simpl.
 replace (hmapIsMember Z.eqb k
    (adjustListPair Z.eqb (fun _ : X => x) k m)) with true.
 apply adjustListPairDouble.
 symmetry.
 apply memberLookup.
 unfold boolEquivalence. intros. apply intBoolEquivalence.
 exists x.
 apply lookupAdjust2.
 unfold boolEquivalence. intros. apply intBoolEquivalence.
 auto.
 simpl. unfold Datatypes.id.
 rewrite Z.eqb_refl.
 replace (hmapIsMember Z.eqb k ((k, x) :: m)) with true.
 rewrite memberFalseAdjust.
 auto. auto.  symmetry.
 apply memberLookup.
 unfold boolEquivalence. intros. apply intBoolEquivalence.
 exists x.
 unfold hmapLookup.
 simpl. rewrite Z.eqb_refl.
 simpl.  auto.
Qed.

Lemma modifyMapFieldsCommute:
forall {S T}`{XDefault T} 
(f: S -> listPair Z T) i (n: Z) (s: S) t1 t2, 
(forall x l, f (i x l) = x) ->
(forall x y l, i x (i y l) = i x l) ->
(forall t, t1 (t2 t) = t2 (t1 t)) ->
exec_state
  (modifyXHMapRecordByFunDefault f i t1 n)
  (exec_state
     (modifyXHMapRecordByFunDefault f i t2 n) s) =
exec_state
  (modifyXHMapRecordByFunDefault f i t2 n) 
  (exec_state
     (modifyXHMapRecordByFunDefault f i t1 n) s).
Proof.
 intros.
 unfold modifyXHMapRecordByFunDefault.
 rewrite ?exec_bind.
 rewrite ?eval_embed.
 unfold modify.
 rewrite ?exec_embed.
 rewrite ?exec_bind'.
 rewrite ?exec_bind.
 unfold compose.
 rewrite ?exec_get.
 rewrite ?exec_unit.
 rewrite ?exec_put.
 rewrite ?eval_get.
 rewrite ?H0.
 remember (f s).
 remember (l [n]).
 setoid_rewrite <- Heqt.
 rewrite ?modifyMapCorrect3.
 rewrite ?H1.
 rewrite ?modifyMapCorrect4.
 rewrite H2.
 auto.
Qed.
 
Lemma hmapDoubleInsert: forall X m (k: Z) (x y: X),
(m [k] ← x) [k] ← y = m [k] ← y.
Proof.
 intros. unfold hmapInsert.
 simpl. unfold Datatypes.id.
 remember (hmapIsMember Z.eqb k m). destruct b.
 replace (hmapIsMember Z.eqb k
    (adjustListPair Z.eqb (fun _ : X => x) k m)) with true.
 rewrite adjustListPairDouble. auto.
 symmetry. 
 apply memberLookup.
 unfold boolEquivalence. intros. apply intBoolEquivalence.
 symmetry in Heqb. remember Heqb. clear Heqe.
 apply memberLookup in Heqb. inversion Heqb.
 exists x. 
 apply lookupAdjust2.
 unfold boolEquivalence. intros. apply intBoolEquivalence.
 auto. unfold boolEquivalence. intros. apply intBoolEquivalence.
 simpl. rewrite Z.eqb_refl.
 unfold hmapIsMember. simpl. rewrite Z.eqb_refl. simpl.
 rewrite memberFalseAdjust. auto. auto.
Qed.

Lemma hmapDoubleInsertNeq: forall X`{XDefault X} (m: listPair Z X) (k n: Z) (x y: X),
k <> n  ->
(((m [k] ← x) [n] ← y) [k]) = x.
Proof.
 intros.
 remember (m [k]← x)  as m'.
 remember (modifyMapCorrect2_helper (K:=Z) (V:=X) (m:=m') (x:=y)  (n:=k) (k:=n)  (eqK := Z.eqb)).
 apply e in H0. clear Heqe.
 unfold hmapFindWithDefault.
 unfold hmapInsert. 
 remember(hmapIsMember Z.eqb n m').
 setoid_rewrite <- Heqb.
 unfold xBoolIfElse.
 unfold xiBoolFunRec.
 unfold xlIntFunRec.
 unfold xhmListFunRec.
 unfold hmfr.
 unfold hmapFunRec.
 unfold listFunRec.
 unfold intFunRec.
 unfold boolFunRec.
 setoid_rewrite H0.
 rewrite Heqm'. apply modifyMapCorrect3.
 unfold boolEquivalence. intros. apply intBoolEquivalence.
Qed.



Lemma hmapDeleteInsert: forall X (k:Z) (x: X) m,
deleteListPair Z.eqb k (m [k] ← x) =
deleteListPair Z.eqb k m.
Proof.
 intros. induction m.
 simpl. rewrite Z.eqb_refl. auto.
 simpl. destruct a.
 unfold hmapInsert.
 simpl. unfold hmapIsMember. simpl.
 remember (z=?k).
 replace (k=?z) with b.
 unfold Datatypes.id.
 unfold hmapInsert in IHm.
 simpl in IHm. unfold Datatypes.id  in IHm.
 unfold hmapIsMember in IHm.
 destruct b. simpl. rewrite Z.eqb_refl.
 remember (xListIn Z.eqb k (xHMapKeys m)).
 destruct b. 
 auto. rewrite memberFalseAdjust. auto.
 unfold hmapIsMember. auto.
 simpl. remember (bIn Z.eqb k (List.map fst m)).
 destruct b. setoid_rewrite <- Heqb0 in IHm.
 rewrite <- IHm. simpl.
 replace (k=?z) with false. auto.
 symmetry. rewrite Z.eqb_sym. auto. 
 simpl. rewrite Z.eqb_refl.
 replace (k=?z) with false.
 auto. rewrite Z.eqb_sym. auto.
 rewrite Z.eqb_sym. auto.
Qed.
*)
Lemma hmapIsMemberDelete: forall X (k:Z) m,
hmapIsMember (V:=X) Z.eqb k (deleteListPair Z.eqb k m) = false.
Proof.
 intros.
 induction m.
 simpl. auto.
 simpl. destruct a. remember (k =? z).
 destruct b. auto.
 unfold hmapIsMember. simpl.
 replace (z =? k) with false.
 simpl. apply IHm.
 symmetry. rewrite Z.eqb_sym. auto.
Qed.




End CommonModelProofs.

