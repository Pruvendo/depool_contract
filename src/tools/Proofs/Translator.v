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
Require Import depoolContract.tools.CommonHelpers.
Require Import depoolContract.tools.StringHelpers.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition newline := "
" : string.
Definition tab := String "009"%char "".
Definition separators := [".";",";";";"(";")";"{";"}";"[";"]";">>";">>=";"!=";
"=";"-=";"+=";">";"<";"<=";">=";"==";"!";"=>";"||";"&&";"?";"delete"; "++"; "--";
"/=";"*=";"/";"+";"-";"*";"if";"while";"then";"require";"return";"else";"do";":=";":";""].
Definition assingment := ["-=";"+=";"/=";"*="].
Definition operations := ["-";"+";"*";"/"].
Definition add_exist_types (tl : list string) :=
 ["byte";"uint";"uint8";"uint16";"uint32";"uint64";"uint128";"uint256";"bool";"mapping"] ++ tl .
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

Load "src/tools/Proofs/function_finds.v".

Fixpoint difficult_types(lt:list(list string))(s:string) :=
match lt with
| nil => ""
| h :: t => match h with
            | h1 :: h2 :: t' => if ( s =? h2 ) 
                               then (h1++"_ι_"++h2)%string
                               else difficult_types t s
            | _ => difficult_types t s
            end
end. 
Definition type2type(lt:list(list string))(s:string) :=
match s with
| "uint" => "XInteger"
| "uint8" => "XInteger8"
| "uint16" => "XInteger16"
| "uint32" => "XInteger32"
| "uint64" => "XInteger64"
| "uint128" => "XInteger128"
| "uint256" => "XInteger256"
| "int" => "XInteger"
| "int8" => "XInteger8"
| "int16" => "XInteger16"
| "int32" => "XInteger32"
| "int64" => "XInteger64"
| "int128" => "XInteger128"
| "int256" => "XInteger256"
| "address" => "XAddress"
| "TvmCell" => "TvmCell"
| "bool" => "XBool"
| _ => difficult_types lt s
end.
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
               ( contract_name :: name :: "require" :: q ++ [";"]) :: get_modificators contract_name t
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
Check andb.
Fixpoint get_list_for_2_members (cn fn:string) (ot:list(list string)) :=
match ot with
| nil => nil
| h :: t => let q := headS "" h in
            let w := headS "" ( tail h ) in
            let e := tail ( tail h ) in
            if ( andb ( q =? cn ) ( w =? fn ) ) 
            then e
            else get_list_for_2_members cn fn t 
end.
Fixpoint make_lemmas (acc:list string)(ot:list(list string))(sl:list(list string)) :=
match sl with
| nil => nil
| h :: t => match h with
            | nil => make_lemmas acc ot t
            | cn :: fn :: body => let q := get_names_args body in
                                  let w := get_list_for_2_members cn fn ot in
                                       if ( test_already_exists cn acc )
                                       then ( w ++ newline ::
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
" :: newline :: nil ) :: make_lemmas acc ot t
                                        else ( "(**" :: ("./Proofs/"++cn++"Proof.v")%string :: "*)" ::
header :: newline :: newline :: newline :: w ++ newline ::
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
" :: newline :: nil ) :: make_lemmas (cn::acc) ot t 
            | _ => make_lemmas acc ot t
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
| "(**" :: name :: "*)" :: t => ( name :: newline :: newline :: tail' t ) :: to_two_lists t 
| h :: t => to_two_lists t 
end.
 
Fixpoint get_original_text(n:nat)(cn:string)(sl:list string) :=
match sl with
| nil => nil
| "contract" :: name :: t => get_original_text n name t
| "
contract" :: name :: t => get_original_text n name t
| "

contract" :: name :: t => get_original_text n name t

| "function" :: name :: t => let q := find_brace_interior_from_current (-1) t in
        ( cn :: name :: "function" :: (cn++"."++name)%string :: q ) :: get_original_text n cn t 

| "constructor" :: t => let q := find_brace_interior_from_current (-1) t in
        ( cn :: ("Constructor"++(writeNat n))%string :: "function" :: (cn++"."++("Constructor"++(writeNat n))%string)%string :: q ) :: get_original_text (n+1) cn t 
| h :: t => get_original_text n cn t
end. 

Definition shaper(s : string) := let s := setSpace s in
let s:= clearComment1 false ( clearComment false s ) in 

let sp := split_string' " " s in 

(* concat_with " " sp. *)

let original_text := get_original_text 1 "" sp in

let sl := split_string' newline s in 
let sl := map (split_string' " ") sl in  

let sl := map clear_string_easy sl  in
let sl := List.concat ( clear_list_easy sl ) in
  
let sl := set_constructors_numbers 1 sl in

let contracts := get_contracts sl in 
let modifs := get_modificators "" sl in 
let funcs  := get_functions "" sl in
let structs := get_structs "" sl in

let funcs_args := map ( get_funcs_args structs ) funcs in

let original_text := map ( set_modifier modifs ) original_text in

let lemmas := make_lemmas [] original_text funcs_args in 

let z := ( lemmas ) in 

 List.concat z . 
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

 

Definition translator (argv : list LString.t) :=
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
  end.

 
(* Definition translator (argv : list LString.t) : C.t System.effect Datatypes.unit :=
  match argv with
  | [ _; file1 ] =>
    let! c1 := System.read_file file1 in
    match c1 with
    | Some c1' => System.log (LString.s (shaper (t2str c1') ) )
    | _ => System.log (LString.s "Cannot read the files.")
    end
  | _ => System.log (LString.s "Expected a parameter.")
  end. *)

Definition main := Extraction.launch translator.

Extraction "./generator" main.

 
Compute (
let q := ["(";"B";"C";"1";")";"2";"3";"{";"D";"E";"{";"F";"J";"{";"I";"J";"}";"}";"K";"L";"}";"M";"N"] in
find_brace_interior_from_current (-1) q
).






