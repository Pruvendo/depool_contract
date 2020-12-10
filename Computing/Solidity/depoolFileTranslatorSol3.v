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

Definition newline := "
" : string.
Definition tab := String "009"%char "".

Definition split_string' (s:string)(sl:string):=
split_string sl s.
Fixpoint t2str(inp : LString.t):string :=
match inp with
| nil => EmptyString
| cons a b => String a ( t2str b) 
end. 
Fixpoint chars2str(l : list ascii) : string :=
match l with
| nil => EmptyString
| h :: t => String h ( chars2str t ) 
end. 
(* из строки первые два символа *)
Definition first2 (s:string):=
match s with
| "" => s
| String a "" => s
| String a (String b t) => String a (String b "")
end.
(* Чистит от строк // *)
Fixpoint deleteComment(sl:list(list string)):=
match sl with
| nil => nil
| h :: t => match h with
            | nil => deleteComment t
            | h' :: t' => match first2(h') with
                          | "" => t' :: (deleteComment t)
                          | "//" => deleteComment t
                          | _ => h :: (deleteComment t)
                          end 
            end 
end.
Definition headS {X} (d: X)(x : list X)  :=
match (head x) with
| None => d
| Some x' => x'
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
Compute (last_delete ["1"] ).
Fixpoint concat_with_3_level (sl:list (list (list string))):=
match sl with
| nil => nil
| h :: t => match h with
            | nil => concat_with_3_level t
            | h' :: t' => (map (concat_with " ") (h' :: t')) ::
                                                  concat_with_3_level t
            end 
end.

Fixpoint find_brace_interior (n:Z) (sl:list string) :=
match sl with
| nil => nil 
| "{" :: t => "{" :: find_brace_interior (n+1) t
| "}" :: t => if (Z.eqb n  0%Z) then "}" :: nil
                        else "}" :: find_brace_interior (n-1) t
| "" :: t => find_brace_interior n t
| h :: t => if (Z.eqb n (-1)%Z) then find_brace_interior n t
                             else h :: find_brace_interior n t 
end.
Fixpoint find_braket_interior (n:Z) (sl:list string) :=
match sl with
| nil => nil 
| "(" :: t => "(" :: find_braket_interior (n+1) t
| ")" :: t => if (Z.eqb n  0%Z) then ")" :: nil
                        else ")" :: find_braket_interior (n-1) t
| "" :: t => find_braket_interior n t
| h :: t => if (Z.eqb n (-1)%Z) then find_braket_interior n t
                             else h :: find_braket_interior n t 
end.
Fixpoint find_sq_braket_interior (n:Z) (sl:list string) :=
match sl with
| nil => nil 
| "[" :: t => "[" :: find_sq_braket_interior (n+1) t
| "]" :: t => if (Z.eqb n  0%Z) then "]" :: nil
                        else "]" :: find_sq_braket_interior (n-1) t
| "" :: t => find_sq_braket_interior n t
| h :: t => if (Z.eqb n (-1)%Z) then find_sq_braket_interior n t
                             else h :: find_sq_braket_interior n t 
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

| String h t => String h (setSpace t)
end.

(*************************************************************************************************)
(*  Анализ содержимого структуры  *)
Definition sol_types2coq_mini_types (t:string):=
match t with
| "uint"    => "I"
| "uint8"   => "I8"
| "uint16"  => "I16"
| "uint32"  => "I32"
| "uint64"  => "I64"
| "uint128" => "I128"
| "uint256" => "I256"
| "bytes"   => "I8"
| "bool"    => "B"
| "mapping" => "Arr"
| "address" => "A"
| _ => ""
end.
Definition cot_mini_types2coq_types (t:string):=
match t with
| "I" => "XInteger"
| "I8"   => "XInteger8"
| "I16"  => "XInteger16"
| "I32"  => "XInteger32"
| "I64"  => "XInteger64"
| "I128" => "XInteger128"
| "I256" => "XInteger256"
| "B"    => "XBool"
| "Arr"  => "XArray"
| "A" => "XAddress"
| _ => ""
end.
Fixpoint get_type_line(sl:list string):=
match sl with
| nil => nil
| ";" :: t => nil
| h :: t => h :: get_type_line t 
end.
Definition get_type_line'(prefix':string)(sl:list string):=
match sl with
| key_word :: name :: nil => 
(tab++prefix'++"·"++name)%string :: ":" :: (sol_types2coq_mini_types key_word) :: ";" :: newline :: nil
| key_word :: modif :: name :: nil => 
(tab++prefix'++"·"++name)%string :: ":" :: (sol_types2coq_mini_types key_word) :: ";" :: newline :: nil
| "mapping" :: "(" :: type1 :: "=>" :: type2 :: ")" :: name :: nil =>
(tab++prefix'++"·"++name)%string :: ":" :: "Arr" :: (sol_types2coq_mini_types type1) ::
                                          (sol_types2coq_mini_types type2) :: ";" :: newline :: nil
| _ => nil
end.
Definition get_type_lines(prefix':string)(sl:list string):=
let sl := concat_with  " " sl in
let sl := split_string' ";" sl in
let sl := map (split_string' " ") sl in
let sl := map get_type_line sl in     
let sl := map clear_string_easy sl in
let sl := clear_list_easy sl in 
let sl := map ( get_type_line' prefix' ) sl in  
let sl := [("{"++newline)%string] ++ (map (concat_with  " ")  sl) ++ [("}."++newline)%string] ++ nil in sl.
Fixpoint get_type_list'(sl:list string) :=
match sl with
| nil => nil
| h :: t => match (cot_mini_types2coq_types h) with
            | "" => get_type_list' t
            | _ => h :: get_type_list' t
            end 
end.
Fixpoint test_already_exists(s:string)(sl:list string) :=
match sl with
| nil => false
| h :: t => if (s =? h) then true
                        else test_already_exists s t
end.
Fixpoint list_of_uniq_types(acc s : list string) :=
match s with
| nil => acc
| h :: t => if (test_already_exists h acc) 
            then list_of_uniq_types acc t
            else list_of_uniq_types (acc++[h]) t
end.
Definition get_type_list (sl:list string) :=
let sl := map (split_string' " ") sl in 
let sl := map get_type_list' sl in 
let sl := List.concat sl in
list_of_uniq_types [] sl.

Compute (let x := get_type_lines 
"Prefix" ["uint";"qwerty";";";      "bool";"payable";"asdfghj";";"
;"mapping";"(";"uint64";"=>";"address";")"; "zxcvbnm";";";
"";"uint";"payable";"xru";";";"uint16";"d";";";"uint256";"qqq";";";"uint16";"ddd";";";"";"";"";"";"";"";"";""] in 
 (get_type_list x) ).

(* Работа с модификаторами mmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmm *)
Definition make_modifier_interior (modifier_name:string) (sl:list string) :=
let braket := find_braket_interior (-1) sl in
let brace  := find_brace_interior (-1) sl in
let x := "Modifier" :: modifier_name
               :: braket ++ last_delete ( List.tail brace ) in   x.
Definition get_modifier (contract_name:string) (sl:list string) :=
match sl with
| nil => nil
| h :: t => let modifier_name := 
     (contract_name++"·"++h)%string in make_modifier_interior modifier_name sl
end.
Fixpoint make_modifiers (contract_name:string)(sl:list string) :=
match sl with
| nil => nil
| "modifier" :: t => (get_modifier contract_name t) :: (make_modifiers contract_name t)
| h :: t => make_modifiers contract_name t
end.
(* Работа с констркутором ccccccccccccccccccccccccccccccccccccccccccccccccccccccc cccccccc*)
Definition make_constructor_interior (constructor_name:string) (sl:list string) :=
let braket := find_braket_interior (-1) sl in
let brace  := find_brace_interior (-1) sl in
let x := "Definition" :: constructor_name
               :: braket ++ last_delete ( List.tail brace ) in   x.
Definition get_constructor (contract_name:string) (sl:list string) :=
match sl with
| nil => nil
| h :: t => let constructor_name := 
     (contract_name++"·"++"constructor")%string in make_constructor_interior constructor_name sl
end.
Fixpoint make_constructors (contract_name:string)(sl:list string) :=
match sl with
| nil => nil
| "constructor" :: t => (get_constructor contract_name t) :: (make_constructors contract_name t)
| h :: t => make_constructors contract_name t
end.
(* Работа со функциями fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff*)
Definition make_function_interior (function_name:string) (sl:list string) :=
let braket := find_braket_interior (-1) sl in
let brace  := find_brace_interior (-1) sl in
let x := "Definition" :: function_name
               :: braket ++ last_delete ( List.tail brace ) in   x.
Definition get_function (contract_name:string) (sl:list string) :=
match sl with
| nil => nil
| h :: t => let function_name := 
     (contract_name++"·"++h)%string in make_function_interior function_name t
end.
Fixpoint make_functions (contract_name:string)(sl:list string) :=
match sl with
| nil => nil
| "function" :: t => (get_function contract_name t) :: (make_functions contract_name t)
| h :: t => make_functions contract_name t
end.
(* Работа со структурами ssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss*)
Definition make_struct_interior (struct_name:string) (sl:list string) :=
let x := find_brace_interior (-1) sl in
let x := last_delete ( List.tail x ) in   x.
Definition get_name_from_type_string(s:string) :=
     headS "" (split_string' " " s).
Definition make_line_for_Global_Instatce(s:string):=
match s with
| "" => ""
| "{" => ""
| "}" => ""
| " " => ""
| String "010"%char "" => ""
| String "010"%char " " => ""
| String " "%char (String "010"%char "") => ""
| String "010"%char (String "010"%char "") => ""
| _ => (tab++tab++"@existT _ _ _ "++(get_name_from_type_string s)++",")%string
end.
Fixpoint clear_some_symbols(s:string) :=
match s with
| "" => ""
| String "{"%char t => clear_some_symbols t
| String "}"%char t => clear_some_symbols t
| String "."%char t => clear_some_symbols t
| String "009"%char t => clear_some_symbols t
| String "010"%char t => clear_some_symbols t
| String h t => String h (clear_some_symbols t)
end.
 
Fixpoint make_pull_up_per_number(n:nat)(sl:list string) :=
match sl with
| nil => nil
| h :: t => let x := split_string' " "  h in let y := clear_some_symbols (headS "" x)
                                                        in match y with
                                                           | "" => make_pull_up_per_number n t
                        | String newline " " => make_pull_up_per_number n t
                                                           | _ =>
  ("Global Instance Acc_"++y++" : Accessor "++y++" := { acc := ·"++(writeNat n)++" }.")%string ::
                                make_pull_up_per_number (S n) t
                                                           end 
end.
Check make_pull_up_per_number.
Definition get_struct (contract_name:string) (sl:list string) :=
match sl with                                               (* get_type_list *)
| nil => nil
| h :: t => let struct_name := 
     (contract_name++"·"++h)%string in (*||||||||||||||||||||||||||||||||||||||||||||||||||||||||*)
            let x := make_struct_interior struct_name t in
            let x := get_type_lines struct_name x in
            let typelist := get_type_list x in
            let typestring := ("{" ++ (concat_with " " typelist) ++ "}")%string in
            let all := (typestring ++ " := " ++ struct_name ++ "C")%string in
        let natural_type_list := (concat_with " " (map cot_mini_types2coq_types typelist)) in

         (newline :: "Record" :: (struct_name++"P")%string :: all :: x) ++ [(
         "Arguments " ++ (struct_name ++ "C")%string ++
                " [ " ++ (concat_with " " typelist) ++" ] " ++ "." 

          ++newline++
          "Definition "++struct_name++" := @"++
                  struct_name++"P "++
                                         natural_type_list++"."
                                       ++ newline++
                  newline++"Global Instance Struct_"++struct_name++" : Struct "++struct_name++
                  " := {"++newline++
                  tab++"fields := ["++
                     (*concat_with newline x*)
              (concat_with newline (map make_line_for_Global_Instatce 
                                             (map clear_some_symbols x)))
                    ++tab++"];"++newline++
                 tab++"ctor := @"++struct_name++"C "++ natural_type_list 
                    ++" "++"}." ++ newline ++ newline ++
                    (concat_with newline (make_pull_up_per_number 0 x) )

)%string
]  
end.
Fixpoint make_structs (contract_name:string)(sl:list string) :=
match sl with
| nil => nil
| "struct" :: t => (get_struct contract_name t) :: (make_structs contract_name t)
| h :: t => make_structs contract_name t
end. 
Check make_structs.

(* Работа с контрактами ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc*)
Definition make_contract_interior (contract_name:string) (sl:list string) :=
let x := find_brace_interior (-1) sl in
let x := last_delete ( List.tail x ) in   
let ctrt := "Contract" in
let structs   :=  [ctrt ; contract_name] :: (make_structs contract_name x) in structs.
(* let functions := structs ++ (make_functions contract_name x) in  
let constructors := functions ++ (make_constructors contract_name x) in 
let modifiers := constructors ++ (make_modifiers contract_name x) in modifiers. *)

(* Первая строка - имя контракта *)
Definition get_contract (sl:list string) :=
match sl with
| nil => nil
| h :: t => let contract_name := h in make_contract_interior contract_name t
end.
Fixpoint make_contracts (sl:list string) :=
match sl with
| nil => [nil]
| "contract" :: t => (get_contract t) :: (make_contracts t)
| h :: t => make_contracts t
end.

Check make_contracts.

Definition shaper(s: string) := let s:= setSpace s in
let sl := split_string s newline in 
 let sl := map (split_string' " ") sl in 
 let sl := map clear_string_easy sl  in
let sl := clear_list_easy sl in
let sl := deleteComment sl in (* let sl := deleteComment2 sl in *)

let sl := List.concat sl in

let all := make_contracts sl in


let sl := concat_with_3_level all in
let sl := map (concat_with (newline++" ")%string) sl in
let sl := concat_with newline      sl       in 
               sl.




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

Extraction "./depoolFileTranslatorSol" main.

(* чистим от комментов косая-звёздочка *)
(* Fixpoint deleteComment2' (n:Z)(sl:list string) := 
match sl with
| nil => nil
| h :: t => match first2 h with
            | ""   => deleteComment2' n t 
            | "/*" => deleteComment2' (n+1) t 
            | "*/" => deleteComment2' (n-1) t 
            | _    => match n with
                      | 0%Z => h :: deleteComment2' n t
                      | _   => deleteComment2' n t
                      end 
            end 
end. *)
 
(* Definition deleteComment2 (sl:list(list string)):=
let sl := map (concat_with " " ) sl in 
let sl := concat_with newline sl in        
let sl := split_string sl " " in 

let sl := deleteComment2' 0 sl in 

let sl := concat_with " " sl in  
let sl := split_string sl newline in 
let sl := map (split_string' " ") sl in            sl.
 
Compute (deleteComment2 [ ["1";"2" ; "/*"] ;["22" ; "/*33" ; "44 ";"*/"]; ["3";"*/";"4"]])
 *)
