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

Load "./strAndListFunctions.v".

Fixpoint t2str(inp : LString.t):string :=
match inp with
| nil => EmptyString
| cons a b => String a ( t2str b) 
end. 
Definition split_string' (s:string)(sl:string):=split_string sl s.
(* Clearing a comment /**/  *)
Fixpoint clearComment(f:bool)(s:string):=
match f, s with
| _ , "" => ""
| false, String "/"%char (String "*"%char t) => clearComment true t
| true,  String "*"%char (String "/"%char t) => clearComment false t
| true,  String h t => clearComment true t
| false, String h t => String h (clearComment false t)
end.
(* Clearing a comment //  *)
Fixpoint clearComment1(f:bool)(s:string):=
match f, s with
| _ , "" => ""
| false, String "/"%char (String "/"%char t) => clearComment1 true t
| true,  String "010"%char t => clearComment1 false t
| true,  String h t => clearComment1 true t
| false, String h t => String h (clearComment1 false t)
end.
Fixpoint clear_string_easy (sl:list string) :=
match sl with
| nil => nil
| h :: t => match h with
            | "" => clear_string_easy t
            | " " => clear_string_easy t
            | String "009"%char _ => clear_string_easy t
            | _ => h :: (clear_string_easy t)
            end 
end.
Fixpoint clear_list_easy (sl:list (list string)) :=
match sl with
| nil => nil
| h :: t => match h with
            | nil => clear_list_easy t
            | _ => h :: (clear_list_easy t) 
            end 
end.
Fixpoint last_delete {X}(l:list X) :=
match l with
| nil => nil
| h :: nil => nil
| h' :: h'' :: nil => h' :: nil
| h :: t => h :: (last_delete t)
end.
Fixpoint set_constructors_numbers(n:nat)(sl:list string) :=
match sl with
| nil => nil
| "constructor" :: t => "function"::("Constructor"++(writeNat n))%string :: set_constructors_numbers (n+1) t
| h :: t => h :: set_constructors_numbers n t
end.
Fixpoint get_contracts(sl:list string) :=
match sl with
| nil => nil
| "library" :: name :: t => ( "library" :: name :: nil (* q *) ) :: get_contracts t
| "contract" :: name :: t => (* let q := last_delete (tail (find_braket_interior (-1) t)) in
                             let w := find_list_level_0 false 0 q in *)
                ( "contract" :: name :: nil (* q *) ) :: get_contracts t
| h :: t => get_contracts t
end.
Fixpoint get_modificators(contract_name:string)(sl:list string) :=
match sl with
| nil => nil
| "contract" :: name :: t => get_modificators name t
| "modifier" :: name :: "{" :: "require" ::  t => let q := find_braket_interior (-1) t in
               ( contract_name :: name :: "require" :: q ) :: get_modificators contract_name t
| h :: t => get_modificators contract_name t
end. 
Fixpoint get_functions(contract_name:string)(sl:list string) :=
match sl with
| nil => nil
| "contract" :: name :: t => get_functions name t
| "function" :: name :: t => let q := find_braket_interior (-1) t in
                             let w := pulling_list_elements "{" t in
                             let e := find_brace_interior (-1) t in
( contract_name :: name :: (* q ++  *)w ++ e ) :: get_functions contract_name t 
 
| h :: t => get_functions contract_name t
end.
Fixpoint get_structs(contract_name:string)(sl:list string) :=
match sl with
| nil => nil
| "contract" :: name :: t => get_structs name t
| "struct" :: name :: t => let q := find_brace_interior (-1) t in
  ( contract_name :: name :: q ) :: get_structs contract_name t 
| h :: t => get_structs contract_name t
end.
Fixpoint sol_type2coq_type(structs:list (list string))(sl:list string) :=
match sl with
| nil => ""
| h :: nil => type2type structs h
| h1 :: "." :: h2 :: nil => type2type structs h2
| _ => ""
end.
Fixpoint get_pure_args (structs:list (list string))(sl:list string) :=
match sl with
| type :: name :: nil => let q := sol_type2coq_type structs [type] in 
                          "(" :: ("Л_"++name)%string :: ":" :: q :: ")" :: nil
| type1 :: "." :: type2 :: name :: ")" :: nil  => let q := sol_type2coq_type structs [type1 ;".";type2] in 
                           "(" :: ("Л_"++name)%string :: ":" :: q :: ")" :: nil

| type :: name :: "," :: t  => let q := sol_type2coq_type structs [type] in 
                           "(" :: ("Л_"++name)%string :: ":" :: q :: ")" :: get_pure_args structs t

| type1 :: "." :: type2 :: name :: "," :: t  => let q := sol_type2coq_type structs [type1 ;".";type2] in 
                           "(" :: ("Л_"++name)%string :: ":" :: q :: ")" :: get_pure_args structs t
| _ => nil
end.
Fixpoint get_funcs_args (structs:list (list string))(sl:list string) := 
match sl with
| cn :: fn :: "(" :: ")" :: t => cn :: (cn++"_Ф_"++fn)%string :: nil
| cn :: fn :: t => let q := last_delete ( tail ( find_braket_interior (-1) t ) ) in
                   let w := get_pure_args structs q in
                   cn :: (cn++"_Ф_"++fn)%string :: w
| _ => nil
end.
Fixpoint get_names_args (sl:list string) :=
match sl with
| nil => nil
| "(" :: h :: t => h :: get_names_args t
| h :: t => get_names_args t
end.

Fixpoint make_lemmas (acc:list string) (sl:list(list string)) :=
match sl with
| nil => nil
| h :: t => match h with
            | nil => make_lemmas acc t
            | cn :: fn :: body => let q := get_names_args body in
                                       if ( test_already_exists cn acc )
                                       then (
 "Lemma" :: (fn++"_exec : forall")%string :: body ++ "," :: newline :: 
 tab :: "exec_state ( " :: fn :: q ++ ") l = l . 
 Proof. 
   intros. destruct l. auto. 
 Abort. 
" ::  newline :: 
 "Lemma" :: (fn++"_eval : forall")%string :: body ++ "," :: newline :: 
 tab :: "eval_state ( " :: fn :: q ++ ") l = default . 
 Proof. 
   intros. destruct l. auto. 
 Abort. 
" :: newline :: nil ) :: make_lemmas acc t
                                        else ( "(**" :: ("./Proofs/"++cn++"Proof.v")%string :: "*)" ::
newline ::
 "Lemma" :: (fn++"_exec : forall")%string :: body ++ "," :: newline :: 
 tab :: "exec_state ( " :: fn :: q ++ ") l = l . 
 Proof. 
   intros. destruct l. auto. 
 Abort. 
" ::  newline :: 
 "Lemma" :: (fn++"_eval : forall")%string :: body ++ "," :: newline :: 
 tab :: "eval_state ( " :: fn :: q ++ ") l = default . 
 Proof. 
   intros. destruct l. auto. 
 Abort. 
" :: newline :: nil ) :: make_lemmas (cn::acc) t 
            | _ => make_lemmas acc t
            end
end. 
Fixpoint to_two_lists (sl:list string) :=
    let fix tail'(sl:list string) :=
    match sl with
    | nil => nil
    | h :: t => if ( h =? "(**" ) then nil
                                  else h :: tail' t
    end in
match sl with
| nil => [nil]
| "(**" :: name :: "*)" :: t => ( name :: header :: newline :: newline :: tail' t ) :: to_two_lists t 
| h :: t => to_two_lists t 
end.
(*Axiom DePoolContract_ι_PART_FRACTION_const : forall  (l: Ledger), 
     eval_state (↑ ε DePoolContract_ι_PART_FRACTION) l = xInt0.*)
Fixpoint make_axioms ( sl:list (string * string) ) :=
match sl with
| nil => nil
| ( x , y ) :: t => 
      ( "Axiom "++x++"_const : forall  ( l: Ledger ), 
           eval_state ( ↑ ε "++x++" ) l = "++y++"."++newline )%string
                         :: make_axioms t
end.
 
Fixpoint get_scheme (sl:list string) :=
match sl with
| nil => nil
| "contract" :: name :: t => let q := pulling_list_elements "{" t in
                             let w := concat_with " " q in
                              ("contract "++name++" "++w)%string :: get_scheme t
| "interface" :: name :: t => let q := pulling_list_elements "{" t in
                             let w := concat_with " " q in
                              ("interface "++name++" "++w)%string :: get_scheme t
| "library" :: name :: t => let q := pulling_list_elements "{" t in
                             let w := concat_with " " q in
                              ("library "++name++w)%string :: get_scheme t
| "struct" :: name :: t => (tab++tab++"struct "++" "++name)%string :: get_scheme t
| "function" :: name :: t => (tab++"function "++name)%string :: get_scheme t
| "modifier" :: name :: t => (tab++tab++"modifier "++name)%string :: get_scheme t
| "receive" :: t => (tab++tab++tab++"receive ")%string :: get_scheme t
| "fallback" :: t => (tab++tab++tab++"fallback ")%string :: get_scheme t
| "constructor" :: t => (tab++"constructor ")%string :: get_scheme t
| "FILE" :: name :: t => (newline++"FILE "++name)%string :: get_scheme t
| h :: t => get_scheme t
end.

Definition shaper(s : string) := let s := setSpace s in
let s:= clearComment1 false ( clearComment false s ) in 

let sl := split_string' newline s in 
let sl := map (split_string' " ") sl in  

let sl := map clear_string_easy sl  in
let sl := unsetSpase ( List.concat ( clear_list_easy sl ) ) in
 
let sl := set_constructors_numbers 1 sl in

let contracts := get_contracts sl in 
let modifs := get_modificators "" sl in 
let funcs  := get_functions "" sl in
let structs := get_structs "" sl in
let scheme := get_scheme sl in

let constants := get_constants "" sl in

let funcs_args := map ( get_funcs_args structs ) funcs in

let lemmas := make_lemmas [] funcs_args in

let const_axs := make_axioms constants in

let z := lemmas in 

concat_with newline scheme (* const_axs *).

(* List.concat z . *)
(* concat_with newline ( map ( concat_with " " ) z ) . *)

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



(* Definition translator (argv : list LString.t) :=
  match argv with 
  | [ _ ; file ] =>
    let! c := System.read_file file in
    match c with
    | Some c' => let q := shaper (t2str c') in
                 let w := to_two_lists q in
                     map1 w 

    | _ => System.log (LString.s "Cannot read the file.")
    end
  | _ => System.log (LString.s "Expected a parameter.")
  end.  *)

 
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

Extraction "./generator" main.
