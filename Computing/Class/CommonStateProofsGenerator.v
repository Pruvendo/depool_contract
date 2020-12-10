(*  Building CommonSateProofs's Lemmas  *)

Require Import Coq.Lists.List. 
Require Import Io.All.
Require Import Io.System.All.
Require Import ListString.All.
Require Import Ascii.
Require Import String.
Require Import Strings.String. 
Require Import ZArith.
Import ListNotations.
Import C.Notations.
Require Import CommonHelpers.
Require Import StringHelpers.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition proofer :=
"
Proof.
 intros. destruct l. destruct l'.
 simpl in H. simpl in * |-. 
 subst. auto.
Qed.
".
Fixpoint delete_last_symbol(s:string) :=
match s with
| "" => ""
| String a (String b "") => String a ""
| String a b => String a ( delete_last_symbol b )
end. 
Definition newline := "
" : string.
Definition types := [ "HM" ; "M" ; "L" ].
Definition split_string' (s:string)(sl:string):=
split_string sl s.
Fixpoint t2str(inp : LString.t):string :=
match inp with
| nil => EmptyString
| cons a b => String a ( t2str b) 
end. 
Fixpoint test_already_exists(s:string)(sl:list string) :=
match sl with
| nil => false
| h :: t => if (s =? h) then true
                        else test_already_exists s t
end.
Definition headS {X} (d: X)(x : list X)  :=
match (head x) with
| None => d
| Some x' => x'
end.
(* Pulling list elements to specified one *)
Fixpoint pulling_list_elements(s:string)(dl:list string) :=
match dl with
| nil => nil
| h :: t => if ( s =? h ) then nil
                          else h :: pulling_list_elements s t
end.

Fixpoint clear_string_easy (sl:list string) :=
match sl with
| nil => nil
| h :: t => match h with
            | "" => clear_string_easy t
            | " " => clear_string_easy t
            | "
" => clear_string_easy t
            | String "009"%char t' => t' :: clear_string_easy t
            | _ => h :: (clear_string_easy t)
            end 
end. 
Fixpoint get_member_list (sl:list string) :=
match sl with
| nil => nil
| "." :: t => nil
| name :: ":" :: t => if ( test_already_exists name types )
                      then get_member_list t
                      else name :: get_member_list t 
| h :: t => get_member_list t
end.
Fixpoint get_member_list_Ledger (sl:list string) :=
match sl with
| nil => nil
| "Record" :: "LedgerP" :: t => get_member_list t
| h :: t => get_member_list_Ledger t
end.
Fixpoint make_CSP_Lemma(sl:list string) :=
match sl with
| nil => nil
| h :: t => let q := headS "" t in
            if ( q =? "" ) 
            then h :: "l" :: "=" :: h :: "l'" :: "->" :: "l" :: "=" :: "l'" :: ["."]
            else
  h :: "l" :: "=" :: h :: "l'" :: "->" :: newline :: make_CSP_Lemma t
end.
Fixpoint find_record (s:string)(sl:list string) :=
match sl with
| nil => nil
| "Record" :: name :: t => if ( s =? name ) 
                           then pulling_list_elements "." t
                           else find_record s t
| h :: t => find_record s t
end.
Fixpoint make_All_CSP_Lemma(ml sl:list string) :=
match ml with
| nil => nil
| h :: t => let q := find_record h sl in 
            let w := get_member_list q in
            let r := delete_last_symbol h in
            let e := "Lemma" :: ( r++"Eq" )%string :: ":" :: "forall (l l': " :: r :: ") ,"::[newline] in
            e ++ ( make_CSP_Lemma w ) ++ proofer :: ( make_All_CSP_Lemma t sl ) 
end.
Fixpoint get_member_list_dog' (sl:list string) :=
match sl with
| nil => nil
| "." :: t => nil
| ":" :: "(@" :: name :: t => name :: get_member_list_dog' t
| h :: t => get_member_list_dog' t
end.
Fixpoint get_member_list_dog (sl:list string) :=
match sl with
| nil => nil
| "Record" :: "LedgerP" :: t => get_member_list_dog' t
| h :: t => get_member_list_dog t
end.

Definition header :=
"Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.
Require Import omega.Omega.
Require Import Setoid.

Require Import FinProof.Common.
Require Import FinProof.CommonInstances.
Require Import FinProof.StateMonad2.
Require Import FinProof.StateMonadInstances.
Require Import FinProof.ProgrammingWith.
(* Require Import MultiSigWallet.Proofs.CPDT. *)

Require Import FinProof.CommonProofs.
Require Import depoolContract.ProofEnvironment.
Require Import depoolContract.DePoolClass.
Require Import depoolContract.SolidityNotations.

(* Require Import MultiSigWallet.MultiSigWalletFunctions.
Module MultiSigWalletFunctions := MultiSigWalletFunctions XTypesSig StateMonadSig.
Import MultiSigWalletFunctions. *)


(*Set Typeclasses Strict Resolution. *)
(* Set Typeclasses Debug.  *)  
(* Set Typeclasses Unique Instances. 
Unset Typeclasses Unique Solutions. *)

(* Existing Instance monadStateT.
Existing Instance monadStateStateT. *)
(* Module MultiSigWalletSpecSig := MultiSigWalletSpecSig XTypesSig StateMonadSig. *)

Require Import depoolContract.Lib.CommonModelProofs.
Module CommonModelProofs := CommonModelProofs StateMonadSig.
Import CommonModelProofs.

Import DePoolSpec.
Import LedgerClass.
Import SolidityNotations.
Set Typeclasses Iterative Deepening.
Set Typeclasses Depth 10.

Require Import depoolContract.Lib.Tactics.


Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope solidity_scope.

Require Import Lists.List.
Import ListNotations.
Local Open Scope list_scope.

Existing Instance monadStateT.
Existing Instance monadStateStateT.


".

Definition shaper(s: string) := 
let sl:= split_string' " " s in 
let sl := clear_string_easy sl in 
let member_list_Ledger := get_member_list_Ledger sl in
let member_list        := get_member_list_dog    sl in

let q := 
( "

Lemma ledgerEq: forall (l l': Ledger) ,"++newline )%string :: 
( make_CSP_Lemma member_list_Ledger ) ++
[proofer] in

let q := q ++ make_All_CSP_Lemma member_list sl in

( header ++ (concat_with " " q) )%string.

Definition translator (argv : list LString.t) : C.t System.effect Datatypes.unit :=
  match argv with
  | [ _; file1 ] =>
    let! c1 := System.read_file file1 in
    match c1 with
    | Some c1' => System.log (LString.s (shaper (t2str c1') ) )
    | _ => System.log (LString.s "Cannot read the files.")
    end
  | _ => System.log (LString.s "Expected a parameter.")
  end. 
Definition main := Extraction.launch translator.

Extraction "./CommonStateProofsGenerator" main.



