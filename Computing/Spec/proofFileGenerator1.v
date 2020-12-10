(* Building proof-files *) 

Load "functions_services.v".


Definition header :=
"
Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.
Require Import omega.Omega.
Require Import Setoid.
Require Import ZArith.

Require Import FinProof.Common.
Require Import FinProof.CommonInstances.
Require Import FinProof.StateMonad2.
Require Import FinProof.StateMonadInstances.
Require Import FinProof.ProgrammingWith. 

Local Open Scope struct_scope.

Require Import FinProof.CommonProofs.
Require Import depoolContract.ProofEnvironment.
Require Import depoolContract.DePoolClass.
Require Import depoolContract.SolidityNotations.

Require Import depoolContract.DePoolFunc.
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.

(* Import SolidityNotations. *)
Set Typeclasses Iterative Deepening.
Set Typeclasses Depth 100.
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
Require Import depoolContract.Lib.Tactics.
Require Import depoolContract.Lib.ErrorValueProofs.
Require Import depoolContract.Lib.CommonCommon.

(* Require Import MultiSigWallet.Proofs.tvmFunctionsProofs. *)

Import DePoolSpec.LedgerClass.SolidityNotations. 

Local Open Scope solidity_scope.

(* Require Import MultiSigWallet.Specifications._validatelimit_inlineSpec.
Module _validatelimit_inlineSpec := _validatelimit_inlineSpec MultiSigWalletSpecSig.
Import _validatelimit_inlineSpec. *)

Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope solidity_scope.
Require Import Lists.List.
Import ListNotations.
Local Open Scope list_scope.

(* Existing Instance embeddedLocalState.
 
Existing Instance monadStateT.
Existing Instance monadStateStateT. *)

(* Existing Instance embeddedLocalState.
Existing Instance embeddedMultisig. *)

".


Definition string_plus (a b : string) := ( a ++ b )%string.

Fixpoint get_pure_name (f:bool)(s:string) :=
match f , s with
| _ , "" => ""
| false , String "164"%char ( String "_"%char t ) => get_pure_name true t
| false , String h t => get_pure_name f t
| true , String h t => String h (get_pure_name true t)
end.
Fixpoint to_two_lists (sl:list string) :=
    let fix tail'(sl:list string) :=
    match sl with
    | nil => nil
    | "(**" :: t => nil
    | h :: t => h :: tail' t
    end in
match sl with
| nil => [nil]
| "(**" :: name :: "*)" :: t => ( name :: tail' t ) :: to_two_lists t 
| h :: t => to_two_lists t 
end.
Check to_two_lists.
(* Find typelist in collect types *)
Fixpoint find_typelist(tl:list(string * list string))(s:string):=
match tl with
| nil => nil
| h :: t => if ( ( fst h ) =? s ) then snd h
                                  else find_typelist t s 
end.
Fixpoint set_constructors_numbers(n:nat)(sl:list string) :=
match sl with
| nil => nil
| "constructor" :: t => "function"::("Constructor"++(writeNat n))%string :: set_constructors_numbers (n+1) t
| h :: t => h :: set_constructors_numbers n t
end.
Fixpoint setSpace (s:string) :=
match s with
| "" => ""
| String "("%char t => String " "%char (String "("%char (String " "%char (setSpace t)))
| String "{"%char t => String " "%char (String "{"%char (String " "%char (setSpace t)))
| String "]"%char t => String " "%char (String "]"%char (String " "%char (setSpace t)))
| String ")"%char t => String " "%char (String ")"%char (String " "%char (setSpace t)))
| String "}"%char t => String " "%char (String "}"%char (String " "%char (setSpace t)))
| String "["%char t => String " "%char (String "["%char (String " "%char (setSpace t)))
| String ";"%char t => String " "%char (String ";"%char (String " "%char (setSpace t)))
| String ","%char t => String " "%char (String ","%char (String " "%char (setSpace t)))
| String "+"%char t => String " "%char (String "+"%char (String " "%char (setSpace t)))
| String "-"%char t => String " "%char (String "-"%char (String " "%char (setSpace t)))
| String "."%char t => String " "%char (String "."%char (String " "%char (setSpace t)))
| String "!"%char t => String " "%char (String "!"%char (String " "%char (setSpace t)))
| String ":"%char t => String " "%char (String ":"%char (String " "%char (setSpace t)))
(* | String "*"%char t => String " "%char (String "*"%char (String " "%char (setSpace t))) *)
| String "m"%char (String "s"%char (String "g"%char (String "."%char t))) =>
              String "m"%char (String "s"%char (String "g"%char (String "_"%char (setSpace t))))
| String "t"%char (String "v"%char (String "m"%char (String "."%char t))) =>
              String "t"%char (String "v"%char (String "m"%char (String "_"%char (setSpace t))))

| String ">"%char t => String " "%char (String ">"%char (String " "%char (setSpace t)))
| String "<"%char t => String " "%char (String "<"%char (String " "%char (setSpace t)))

| String h t => String h (setSpace t)
end.
Fixpoint out_tuple (tl:list(string * list string)) :=
match tl with
| nil => nil
| h :: t => ( ( fst h ) :: ( snd h ) ) :: out_tuple t
(* | h :: t => ( fst h ) :: out_tuple t *)
end.

Fixpoint approving_length (n:nat) (sl:list string) :=
match sl with
| nil => nil
| h :: t => let q := String.length h in
            let w := q + n in
            if ( w <? 52 ) then h :: approving_length w t
                           else h :: newline :: approving_length 0 t
end.

Fixpoint get_funcs_texts (sl : list string) :=
    let fix tail' (n:Z)(sl : list string) :=
    match n , sl with
    | _ , nil => nil
    | _ , "{" :: t => "{" :: tail' (n+1)%Z t
    | 0%Z , "}" :: t => "}" :: nil
    | _ , "}" :: t => "}" :: tail' (n-1)%Z t
    | _ , h :: t => h :: tail' n%Z t
    end in 
match sl with 
| nil => nil
| "function" :: name :: t => ( name , approving_length 0 ("function" :: name :: tail' (-1)%Z  t ) ) :: get_funcs_texts t
| h :: t => get_funcs_texts t
end.

Fixpoint get_type_list(sl:list string) :=
match sl with
| nil => nil
| ":" :: "LedgerT" :: t => ["_none_"]
| ":" :: t => get_type_list t
| "." :: t => nil
| "LedgerT" :: t => nil
| h :: "->" :: "LedgerT" :: t => [h]
| h :: "->" :: t => h :: get_type_list t
| "(" :: "XMaybe" :: h :: ")" :: "->" :: t => "(" :: "XMaybe" :: h :: ")" :: get_type_list t
| "(" :: "XHMap" :: h1 :: h2 :: ")" :: "->" :: t => "(" :: "XHMap" :: h1 :: h2 :: ")" :: get_type_list t
| h :: t => get_type_list t
end.

Fixpoint get_types (sl:list string):=
match sl with
| nil => nil
| "Parameter" :: name :: t => ( name , get_type_list t ) :: get_types t
| h :: t => get_types t
end.
 
Fixpoint get_args_list(sl:list string) :=
match sl with
| nil => nil
| "(" :: t => get_args_list t
| ")" :: t => nil
| h1 :: h2 :: ")" :: t => [( "Л_"++h2 )%string]
| h1 :: h2 :: "," :: t => ( "Л_"++h2 )%string :: get_args_list t
| h :: t => get_args_list t
end.
Fixpoint get_args (acc sl:list string) :=
match sl with
| nil => nil
| "function" :: name :: t => if ( test_already_exists name acc )
                             then get_args acc t
                             else ( name , get_args_list t ) :: get_args (name::acc) t
| h :: t => get_args acc t
end.
(* types lists and names lists *)
Fixpoint approving_both_lists(l1 l2 :list string) :=
match l1 , l2 with
| "(" :: "XMaybe" :: h1 :: ")" :: t1 , h2 :: t2  => 
  "(" :: h2 :: ":" :: "(" :: "XMaybe" :: h1 :: ")" :: ")" :: approving_both_lists t1 t2
| "(" :: "XHMap" :: h1 :: h1' :: ")" :: t1 , h2 :: t2 => 
  "(" :: h2 :: ":" :: "(" :: "XHMap" :: h1 :: h1' :: ")" :: ")" :: approving_both_lists t1 t2
| h1 :: t1 , h2 :: t2 => 
   "(" :: h2 :: ":" :: h1 :: ")" :: approving_both_lists t1 t2
| _ , _ => nil
end.
Fixpoint make_lemmas(l1 l2 origtext :list(string * list string)) :=
match l1 with
| nil => nil
| h :: t => let q := get_pure_name false ( fst h ) in 
            let w := find_typelist l2 q in
            let w' := find_typelist origtext q in
            let e := snd h in
            let r := fst h in ( "(**" :: ("./Proofs/"++r++"Proof.v")%string :: "*)" :: newline ::
                header :: newline ::
                "(*" :: w' ++ "*)" :: newline  ::
                   "Lemma" :: (r++"_exec")%string :: ":" :: "forall" :: 
                  (approving_both_lists e w) ++ "(l: Ledger)," :: newline ::
  "exec_state" :: "(" :: r :: w ++ ")" :: "l" :: "=" :: "l" :: "." :: newline ::
                    "Proof." :: newline :: "intros." :: "destruct l." :: "auto." :: 
                                newline ::
                    "Abort." ::
                     newline :: newline ::
                    "Lemma" :: (r++"_eval")%string :: ":" :: "forall" :: 
                  (approving_both_lists e w) ++ "(l: Ledger)," :: newline ::
  "eval_state" :: "(" :: r :: w ++ ")" :: "l" :: "=" :: "default" :: "." :: newline ::
                    "Proof." :: newline :: "intros." :: "destruct l." :: "auto." :: 
                                newline ::
                    "Abort." ::
                    newline :: newline :: [newline]) :: make_lemmas t l2 origtext
end.

(* Spes Sol *) 
Definition shaper(s1 s2 : string) := let s2 := setSpace s2 in

let sl1 := split_string' newline s1 in 
let sl1 := map (split_string' " ") sl1 in 

let sl1 := map clear_string_easy sl1  in
let sl1 := List.concat ( clear_list_easy sl1 ) in

let s2:= clearComment1 false ( clearComment false s2 ) in 

let sl2 := split_string' newline s2 in 
let sl2 := map (split_string' " ") sl2 in let sl2 := deleteComment sl2 in 

let sl2 := map clear_string_easy sl2  in
let sl2 := List.concat ( clear_list_easy sl2 ) in
 
let sl2 := set_constructors_numbers 1 sl2 in

let names := get_types sl1 in 
let args  := get_args [] sl2 in let sl := ( out_tuple names ) ++ ( out_tuple args ) in

let origtext := get_funcs_texts sl2 in

let qq := make_lemmas names args origtext in 

let qq := List.concat qq in (* concat_with " " *) qq.
Print fold_left.
Fixpoint map1 (sl:list(list string)):=
match sl with
| nil => System.log (LString.s "Done." )
| h :: t => let q := map1 t in

            let e := headS "" h in
            let r := LString.s ( concat_with " " ( tail h ) ) in
            let name := LString.s e in
            let! is_success :=  System.write_file name r in q
            (* if is_success 
            then q (* System.log (name ++ LString.s " generated.") *)
            else q (* System.log (name ++  LString.s " cannot generated." ) *)  *)  
end.

Check map1.

Definition translator (argv : list LString.t) :=
  match argv with 
  | [ _ ; file1 ; file2 ] =>
    let! c1 := System.read_file file1 in
    let! c2 := System.read_file file2 in
    match c1 , c2 with
    | Some c1' , Some c2' => let q := shaper (t2str c1') (t2str c2') in
                             let w := to_two_lists q in
                     map1 w 

    | _ , _ => System.log (LString.s "Cannot read the files.")
    end
  | _ => System.log (LString.s "Expected a parameter.")
  end. 

Definition main := Extraction.launch translator. 

Extraction "./proofFileGenerator" main.



