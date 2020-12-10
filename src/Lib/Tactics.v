Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.
Require Import omega.Omega.
Require Import Setoid.

Require Import FinProof.Common.
Require Import FinProof.CommonInstances.
Require Export FinProof.CommonTactics.
Require Import FinProof.StateMonad2.
Require Import FinProof.StateMonadInstances.
Require Import FinProof.ProgrammingWith.

Require Import depoolContract.ProofEnvironment.
Require Import depoolContract.SolidityNotations.

Module SolidityNotations := SolidityNotations.SolidityNotations XTypesSig StateMonadSig.
Import SolidityNotations.

Local Open Scope struct_scope.
Local Open Scope Z_scope.

Import ListNotations.
Local Open Scope list_scope. 

Tactic Notation "start_proof" reference(f) reference(m) := 
unfold m; unfold f; intros.

Tactic Notation "unfoldInt" reference(f):=
unfold f; unfold ifr; unfold intFunRec.

Tactic Notation "unfoldInt" reference(f) "in" hyp(H):=
unfold f in H; unfold ifr in H; unfold intFunRec in H.

Tactic Notation "unfoldBool" reference(f):=
unfold f; unfold bfr; unfold boolFunRec.

Tactic Notation "unfoldBool" reference(f) "in" hyp(H):=
unfold f in H; unfold bfr in H; unfold boolFunRec in H.

Tactic Notation "unfoldError" reference(f):=
unfold f; unfold evfr; unfold errorFunRec.

Tactic Notation "unfoldError" reference(f) "in" hyp(H):=
unfold f in H; unfold evfr in H; unfold errorFunRec in H.

Tactic Notation "unfoldHMap" reference(f):=
unfold f; unfold hmfr; unfold hmapFunRec.

Tactic Notation "unfoldHMap" reference(f) "in" hyp(H):=
unfold f in H; unfold hmfr in H; unfold hmapFunRec in H.

Tactic Notation "unfoldList" reference(f):=
unfold f; unfold lfr; unfold listFunRec.

Tactic Notation "unfoldList" reference(f) "in" hyp(H):=
unfold f in H; unfold lfr in H; unfold listFunRec in H.

Tactic Notation "unfoldProd" reference(f):=
unfold f; unfold pfr; unfold prodFunRec.

Tactic Notation "unfoldProd" reference(f) "in" hyp(H):=
unfold f in H; unfold pfr in H; unfold prodFunRec in H.

Tactic Notation "rews" constr(x) := 
match goal with 
| H: x = _ |- _ => rewrite H 
end.

Tactic Notation "rews" constr(x) "<-" := 
match goal with 
| H: _ = x |- _ => rewrite <- H 
end.

Tactic Notation "rews" constr(x) "in"  hyp(G):= 
match goal with 
| H: x = _ |- _ => rewrite H in G
end.

Tactic Notation "rews" constr(x) "<-" "in"  hyp(G) := 
match goal with 
| H: _ = x |- _ => rewrite <- H in G
end.


(* https://github.com/tchajed/coq-tactical/blob/master/src/SimplMatch.v *)

Ltac simpl_match :=
  let repl_match_goal d d' :=
      replace d with d';
      lazymatch goal with
      | [ |- context[match d' with _ => _ end] ] => fail
      | _ => idtac
      end in
  let repl_match_hyp H d d' :=
      replace d with d' in H;
      lazymatch type of H with
      | context[match d' with _ => _ end] => fail
      | _ => idtac
      end in
  match goal with
  | [ Heq: ?d = ?d' |- context[match ?d with _ => _ end] ] =>
    repl_match_goal d d'
  | [ Heq: ?d' = ?d |- context[match ?d with _ => _ end] ] =>
    repl_match_goal d d'
  | [ Heq: ?d = ?d', H: context[match ?d with _ => _ end] |- _ ] =>
    repl_match_hyp H d d'
  | [ Heq: ?d' = ?d, H: context[match ?d with _ => _ end] |- _ ] =>
    repl_match_hyp H d d'
  end.

(** ** Find and destruct matches *)

Ltac destruct_matches_in e :=
  lazymatch e with
  | context[match ?d with | _ => _ end] =>
    destruct_matches_in d
  | _ => destruct e ; intros
  end.

Ltac destruct_all_matches :=
  repeat (try simpl_match;
          try match goal with
              | [ |- context[match ?d with | _ => _ end] ] =>
                destruct_matches_in d
              | [ H: context[match ?d with | _ => _ end] |- _ ] =>
                destruct_matches_in d
              end);
  subst;
  try congruence;
  auto.

Ltac destruct_nongoal_matches :=
  repeat (try simpl_match;
           try match goal with
           | [ H: context[match ?d with | _ => _ end] |- _ ] =>
             destruct_matches_in d
               end);
  subst;
  try congruence;
  auto.

Ltac destruct_goal_matches :=
  repeat (try simpl_match;
           match goal with
           | [ |- context[match ?d with | _ => _ end] ] =>
              destruct_matches_in d
           end);
  try congruence;
  auto.

Ltac destruct_tuple :=
  match goal with
  | [ H: context[let '(a, b) := ?p in _] |- _ ] =>
    let a := fresh a in
    let b := fresh b in
    destruct p as [a b]
  | [ |- context[let '(a, b) := ?p in _] ] =>
    let a := fresh a in
    let b := fresh b in
    destruct p as [a b]
  end.

Tactic Notation "destruct" "matches" "in" "*" := destruct_all_matches.
Tactic Notation "destruct" "matches" "in" "*|-" := destruct_nongoal_matches.
Tactic Notation "destruct" "matches" := destruct_goal_matches.

(****************************************************************************)
