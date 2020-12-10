Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.
Require Import ZArith.
Require Import Strings.String.

Require Import FinProof.Common.
Require Import FinProof.CommonInstances.
Require Import FinProof.StateMonad2.
Require Import FinProof.StateMonadInstances.
Require Import FinProof.ProgrammingWith.

Require Import depoolContract.SolidityNotations.
Require Import Lists.List.
Import ListNotations.
Local Open Scope list_scope.

Definition toErrorProp {E X} (l: list (X -> (Prop*E))) (x: X) (e:E):=
let fix f l x := match l with
| nil => [ ]
| p::ls => let p' := f ls x in
            ((fst (p x))::(hd (@nil Prop) p'))::p'
end  in
let l' := List.map (fun t => (hd True t) :: (List.map (fun (p:Prop) => ~p) (tl t))) (f l x) in
let l'':= List.map (fun t => match t with
                             | [ ] => True
                             | x::xs => fold_left and xs x
                             end) l'  in
let l''' :=  l'' in
let fix g m l := 
match m, l with 
| xm::ms, xl::ls => (xm /\ e = (snd xl)) :: (g ms ls)
| _, _ => [ ]
end in let l'''' := g l''' (List.map (fun p => p x) l) in
let l''''':= match l'''' with
| [ ] => False
| x::xs => fold_left or xs x
end in l'''''.

Definition toValueProp {X E} (l: list (X -> (Prop*E))) (x: X):=
let l' := List.map (fun p => ~ (fst (p x))) l in
match l' with
     | [ ] => True
     | x::xs => fold_left and xs x
end.


Definition toErrorList {E X} (l: list (X -> (Prop*E))) (x: X) :=
map (fun f => (snd (f x))) l.

Notation "$0"  := (prod_curry)       (at level 60, right associativity). 
Notation "$1"  := (prod_curry ∘ $0)  (at level 60, right associativity).
Notation "$2"  := (prod_curry ∘ $1)  (at level 60, right associativity).
Notation "$3"  := (prod_curry ∘ $2)  (at level 60, right associativity).
Notation "$4"  := (prod_curry ∘ $3)  (at level 60, right associativity).
Notation "$5"  := (prod_curry ∘ $4)  (at level 60, right associativity).
Notation "$6"  := (prod_curry ∘ $5)  (at level 60, right associativity).
Notation "$7"  := (prod_curry ∘ $6)  (at level 60, right associativity).

Notation "#0"  := (prod_uncurry)       (at level 60, right associativity). 
Notation "#1"  := ( prod_uncurry ∘ #0 )  (at level 60, right associativity).
Notation "#2"  := ( prod_uncurry ∘ #1 )  (at level 60, right associativity).
Notation "#3"  := ( prod_uncurry ∘ #2 )  (at level 60, right associativity).
Notation "#4"  := ( prod_uncurry ∘ #3 )  (at level 60, right associativity).
Notation "#5"  := ( prod_uncurry ∘ #4 )  (at level 60, right associativity).
Notation "#6"  := ( prod_uncurry ∘ #5 )  (at level 60, right associativity).
Notation "#7"  := ( prod_uncurry ∘ #6 )  (at level 60, right associativity).

Module XTypesSig <: SolidityNotations.XTypesSig.
Definition XBool := bool.
Definition XInteger := Z.

(*Definition XInteger256 := Z.*)
Definition XString := string. 
Definition XMaybe := option.
Definition XList := list.
Definition XProd := prod.
Definition XHMap := listPair.
Definition XErrorValue := ErrorValue.

(* constants used as literals *)
Definition xInt1000000000 := 1000000000%Z. 
Definition xInt10000000000 := 10000000000%Z.
Definition xInt104 := 104%Z.
Definition xInt100000000000 := 100000000000%Z.
Definition xInt103 := 103%Z.
Definition xInt4 := 4%Z.
Definition xInt18 := 18%Z.
Definition xInt2 := 2%Z.
Definition xInt100 := 100%Z.
Definition xInt64 := 64%Z.
Definition xInt102 := 102%Z.
Definition xInt101 := 101%Z.
Definition xInt1 := 1%Z.
Definition xInt17 := 17%Z.
Definition xInt15 := 15%Z.
Definition xInt32 := 32%Z.
Definition xInt34 := 34%Z.
Definition xInt0 := 0%Z.
Definition xInt65536 := 65536%Z.
Definition xInt3 := 3%Z.
Definition xInt1_000_000_000 := 1000000000%Z.
Definition xInt228_000_000 := 228000000%Z.
Definition xInt8 := 8%Z.
Definition x1_ton := 1000000000%Z.
Definition xInt1E9 := 1000000000%Z.
Definition xInt5 := 5%Z.
Definition xInt6 := 6%Z.
Definition xInt7 := 7%Z. 
Definition xInt9 := 9%Z. 
Definition xInt365 := 365%Z.
Definition x1_day := 86400%Z. 
Definition xInt128 := 128%Z.
Definition xInt200 := 200%Z.

(*funrec classes*)
Definition bfr := boolFunRec.
Definition pfr := prodFunRec.
Definition mfr := maybeFunRec.
Definition ifr := intFunRec.
Definition lfr := listFunRec.
Definition sfr := strFunRec.
Definition hmfr:= hmapFunRec.
Definition evfr:= errorFunRec. 
End XTypesSig.


(* Module Type A.

Set Universe Polymorphism.
Set Printing Universes.
Unset Cumulativity Weak Constraints.


Section UniSection.
Polymorphic Universes i j k.
Polymorphic Constraint i <= simpleState.u0.
Polymorphic Constraint j <= simpleState.u1.
Polymorphic Constraint i <= k.
Polymorphic Constraint j <= k. 

Polymorphic Axiom StateT: Type@{i} -> Type@{j} -> Type@{k}.

End UniSection.

(*Module*) Monomorphic Axiom monadStateT: forall S, Monad (StateT S).
Existing Instance monadStateT.
(*Module*) Monomorphic Axiom monadStateStateT : forall S, MonadState (M:=StateT S) S.
End A.  *)

Module StateMonadSig <: SolidityNotations.StateMonadSig. 

(* Polymorphic Definition StateT (S X: Type): Type.
 refine (simpleState S X).
 Defined. *)


 Definition StateT := simpleState.

(* 
 Check simpleStateMonad. *)

 Definition monadStateT := simpleStateMonad.

(*  Polymorphic Definition monadStateT : forall S, Monad (StateT S).
 refine (simpleStateMonad).
 Defined. *)

 Definition monadStateStateT := simpleStateMonadState.
(* 
 Polymorphic Definition monadStateStateT := simpleStateMonadState. *)

End StateMonadSig.

Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.
Require Import ZArith.
Require Import Lists.List.
Require Import Ascii.
Require Import Strings.String. 
Require Import Coq.Strings.Byte.

Require Import depoolContract.Lib.HexNotations.
Import HexNotations.
Require Import depoolContract.DePoolConsts.

Module DePoolConstsTypesSig <: DePoolConstsTypesSig XTypesSig StateMonadSig .

Module SolidityNotations := SolidityNotations XTypesSig StateMonadSig.

Local Open Scope solidity_scope_hex.
Local Open Scope solidity_scope_dec.

Local Notation "a 'e' b" := ( (a * 10^b)%Z )(at level 60, right associativity) . 
Local Notation "'0.09' '*' 'ton'" := (90000000%Z). 
Local Notation "'0.5' '*' 'ton'" := (500000000%Z). 

Definition ton := 1000000000%Z . 
Definition milliton := 1000%Z . 
Definition minutes := 60%Z . 
 
Definition Errors_ι_IS_NOT_OWNER := 101%Z . 
Definition Errors_ι_IS_NOT_PROXY := 107%Z . 
Definition Errors_ι_IS_EXT_MSG := 108%Z . 
Definition Errors_ι_IS_NOT_VALIDATOR := 113%Z . 
Definition Errors_ι_DEPOOL_IS_CLOSED := 114%Z . 
Definition Errors_ι_NO_SUCH_PARTICIPANT := 116%Z . 
Definition Errors_ι_IS_NOT_DEPOOL := 120%Z . 
Definition Errors_ι_INVALID_ROUND_STEP := 125%Z . 
Definition Errors_ι_INVALID_QUERY_ID := 126%Z . 
Definition Errors_ι_IS_NOT_ELECTOR := 127%Z . 
Definition Errors_ι_BAD_STAKES := 129%Z . 
Definition Errors_ι_CONSTRUCTOR_NO_PUBKEY := 130%Z . 
Definition Errors_ι_VALIDATOR_IS_NOT_STD := 133%Z . 
Definition Errors_ι_BAD_PART_REWARD := 138%Z . 
Definition Errors_ι_BAD_PROXY_CODE := 141%Z . 
Definition Errors_ι_NOT_WORKCHAIN0 := 142%Z . 
Definition Errors_ι_NEW_VALIDATOR_FRACTION_MUST_BE_GREATER_THAN_OLD := 143%Z . 
Definition Errors_ι_FRACTION_MUST_NOT_BE_ZERO := 144%Z . 
Definition Errors_ι_BAD_BALANCE_THRESHOLD := 145%Z . 
Definition Errors_ι_BAD_ACCOUNT_BALANCE := 146%Z . 
Definition InternalErrors_ι_ERROR507 := 507%Z . 
Definition InternalErrors_ι_ERROR508 := 508%Z . 
Definition InternalErrors_ι_ERROR509 := 509%Z . 
Definition InternalErrors_ι_ERROR511 := 511%Z . 
Definition InternalErrors_ι_ERROR513 := 513%Z . 
Definition InternalErrors_ι_ERROR516 := 516%Z . 
Definition InternalErrors_ι_ERROR517 := 517%Z . 
Definition InternalErrors_ι_ERROR518 := 518%Z . 
Definition InternalErrors_ι_ERROR519 := 519%Z . 
Definition InternalErrors_ι_ERROR521 := 521%Z . 
Definition InternalErrors_ι_ERROR522 := 522%Z . 
Definition InternalErrors_ι_ERROR523 := 523%Z . 
Definition InternalErrors_ι_ERROR524 := 524%Z . 
Definition InternalErrors_ι_ERROR525 := 525%Z . 
Definition InternalErrors_ι_ERROR526 := 526%Z . 
Definition InternalErrors_ι_ERROR527 := 527%Z . 
Definition InternalErrors_ι_ERROR528 := 528%Z . 
Definition DePoolLib_ι_PROXY_FEE := (0.09 * ton )%Z . 
Definition DePoolLib_ι_MIN_PROXY_BALANCE := (1 * ton )%Z . 
Definition DePoolLib_ι_PROXY_CONSTRUCTOR_FEE := (1 * ton )%Z . 
Definition DePoolLib_ι_DEPOOL_CONSTRUCTOR_FEE := (1 * ton )%Z . 
Definition DePoolLib_ι_ELECTOR_FEE := (1 * ton )%Z . 
Definition DePoolLib_ι_MAX_UINT64 := "FFFFFFFFFFFFFFFF" . 
Definition DePoolLib_ι_MAX_TIME := "FFFFFFFF" . 
Definition DePoolLib_ι_ELECTOR_UNFREEZE_LAG := (1 * minutes )%Z . 
Definition DePool_ι_STAKE_FEE := (0.5 * ton )%Z . 
Definition DePool_ι_RET_OR_REINV_FEE := (50 * milliton )%Z . 
Definition DePool_ι_MAX_MSGS_PER_TR := 25%Z . 
Definition DePool_ι_MAX_QTY_OF_OUT_ACTIONS := 250%Z . 
Definition DePool_ι_VALUE_FOR_SELF_CALL := (1 * ton )%Z . 
Definition DePool_ι_PROXY_CODE_HASH := "481d7f583b458a1672ee602f66e8aa8d2f99d3cd9ece2eaa20e25c7ddf4c7f4a". 
Definition DePool_ι_STATUS_SUCCESS := 0%Z . 
Definition DePool_ι_STATUS_STAKE_TOO_SMALL := 1%Z . 
Definition DePool_ι_STATUS_DEPOOL_CLOSED := 3%Z . 
Definition DePool_ι_STATUS_NO_PARTICIPANT := 6%Z . 
Definition DePool_ι_STATUS_PARTICIPANT_ALREADY_HAS_VESTING := 9%Z . 
Definition DePool_ι_STATUS_WITHDRAWAL_PERIOD_GREATER_TOTAL_PERIOD := 10%Z . 
Definition DePool_ι_STATUS_TOTAL_PERIOD_MORE_18YEARS := 11%Z . 
Definition DePool_ι_STATUS_WITHDRAWAL_PERIOD_IS_ZERO := 12%Z . 
Definition DePool_ι_STATUS_TOTAL_PERIOD_IS_NOT_DIVISIBLE_BY_WITHDRAWAL_PERIOD := 13%Z . 
Definition DePool_ι_STATUS_REMAINING_STAKE_LESS_THAN_MINIMAL := 16%Z . 
Definition DePool_ι_STATUS_PARTICIPANT_ALREADY_HAS_LOCK := 17%Z . 
Definition DePool_ι_STATUS_TRANSFER_AMOUNT_IS_TOO_BIG := 18%Z . 
Definition DePool_ι_STATUS_TRANSFER_SELF := 19%Z . 
Definition DePool_ι_STATUS_TRANSFER_TO_OR_FROM_VALIDATOR := 20%Z . 
Definition DePool_ι_STATUS_FEE_TOO_SMALL := 21%Z . 
Definition DePool_ι_STATUS_INVALID_ADDRESS := 22%Z . 
Definition DePool_ι_STATUS_INVALID_BENEFICIARY := 23%Z . 
Definition DePool_ι_STATUS_NO_ELECTION_ROUND := 24%Z . 
Definition DePool_ι_STATUS_INVALID_ELECTION_ID := 25%Z . 
Definition DePool_ι_CRITICAL_THRESHOLD := (10 * ton )%Z . 
Definition DePoolHelper_ι_TICKTOCK_FEE := 1 e 9 . 
Definition DePoolHelper_ι__timerRate := 400000%Z . 
Definition DePoolHelper_ι__fwdFee := 1000000%Z . 
Definition DePoolHelper_ι__epsilon := 1 e 9 . 
Definition DePoolProxyContract_ι_ERROR_IS_NOT_DEPOOL := 102%Z . 
Definition DePoolProxyContract_ι_ERROR_BAD_BALANCE := 103%Z . 

End DePoolConstsTypesSig. 

(* Module B (xt: XTypesSig) (sm: StateMonadSig).
(* Module LedgerClass := LedgerClass xt sm .
Import LedgerClass.
Import SolidityNotations. *)
(* 
Module Type DePoolSpecSig.
Import xt. Import sm. *)

End B.

Module B' := B XTypesSig StateMonadSig. *)

