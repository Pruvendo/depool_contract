(* Building functions-file (i.e. solidity-coq translator for function sources ) *)

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
(* first two sybbols from string *)
Definition first2 (s:string):=
match s with
| "" => s
| String a "" => s
| String a (String b t) => String a (String b "")
end.
(* Clearing a comment /**/  *)
Fixpoint clearComment(f:bool)(s:string):=
match f, s with
| _ , "" => ""
| false, String "/"%char (String "*"%char t) => clearComment true t
| true,  String "*"%char (String "/"%char t) => clearComment false t
| true,  String h t => clearComment true t
| false, String h t => String h (clearComment false t)
end.

Fixpoint recoveryComments(s:string) :=
match s with
| "" => ""
| String "("%char (String " "%char (String "*"%char t)) => 
                 String "("%char (String "*"%char (recoveryComments t))
| String "*"%char (String " "%char (String ")"%char t)) => 
                 String "*"%char (String ")"%char (recoveryComments t))
  
| String h t => String h (recoveryComments t)
end.
Definition clear_forward (s:string) :=
match s with
| "" => ""
| String " "%char t => t
| String h t => s
end.
(* Clearing for comment // *)
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
(* get lines between arguments and brace *)
Fixpoint find_crotch_interior (f:bool) (sl:list string) :=
match f, sl with
| _, nil => nil
| false, ")" :: t => find_crotch_interior true t
| true,  "{" :: t => nil
| true,   h  :: t => h :: (find_crotch_interior true t) 
| false,  h  :: t => find_crotch_interior true t
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
| String "."%char t => String " "%char (String "."%char (String " "%char (setSpace t)))

| String h t => String h (setSpace t)
end.

(*************************************************************************************************)
(*  solidity type to coq alias type  *)
Definition sol_types2coq_mini_types (t:string):=
match t with
| "" => ""
| "uint"    => "I"
| "uint8"   => "I8"
| "uint16"  => "I16"
| "uint32"  => "I32"
| "uint64"  => "I64"
| "uint128" => "I128"
| "uint256" => "I256"
| "bytes"   => "I8"
| "bool"    => "B"
| "mapping" => "HM"
| "address" => "A"
| "TvmCell" => "C"
| _ => ("ι_" ++ t)%string
end.
Definition del_lead_2_symbolsι_(s:string):=
match s with
| "" => ""
| String a (String b (String c t)) => t
| _ => s
end.
(* Coq alias type to coq full type *)
Definition cot_mini_types2coq_types (t:string):=
match t with
| "" => ""
| "I" => "XInteger"
| "I8"   => "XInteger8"
| "I16"  => "XInteger16"
| "I32"  => "XInteger32"
| "I64"  => "XInteger64"
| "I128" => "XInteger128"
| "I256" => "XInteger256"
| "C"    => "TvmCell"
| "B"    => "XBool"
| "Arr"  => "XArray"
| "HM"   => "XHMap"
| "A" => "XAddress"
| _ =>  t
end.
Definition sol2coq_full_types(t:string):=cot_mini_types2coq_types (sol_types2coq_mini_types t).
(* Test for empty *)
Fixpoint isEmpty(s:string):bool :=
match s with
| "" => true
| String "010"%char t => isEmpty t
| String " "%char t => isEmpty t
| String "009"%char t => isEmpty t
| String "}"%char t => isEmpty t
| String "{"%char t => isEmpty t
| String ")"%char t => isEmpty t
| String "("%char t => isEmpty t
| String "]"%char t => isEmpty t
| String "["%char t => isEmpty t
| String ";"%char t => isEmpty t
| String ":"%char t => isEmpty t
| String "."%char t => isEmpty t

| String h t => false
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
(tab++prefix'++"_ι_"++name)%string :: ":" :: (sol_types2coq_mini_types key_word) :: ";" :: newline :: nil
| key_word :: modif :: name :: nil => 
(tab++prefix'++"_ι_"++name)%string :: ":" :: (sol_types2coq_mini_types key_word) :: ";" :: 
                ("(*"++modif++"*)")%string :: newline :: nil
| "mapping" :: "(" :: type1 :: "=>" :: type2 :: ")" :: name :: nil =>
(tab++prefix'++"_ι_"++name)%string :: ":" :: "HM" :: (sol_types2coq_mini_types type1) ::
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
let sl := [("{"++newline)%string] ++ (map (concat_with  " ")  sl) ++ [("}. "++newline)%string] ++ nil in sl.
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
Fixpoint test_already_exists_for_list(st sl:list string) :=
match st with
| nil => false
| h :: t => if (test_already_exists h sl) then true
                                          else test_already_exists_for_list t sl
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

(* Working with modifiers mmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmm *)
Definition make_modifier_interior (modifier_name:string) (sl:list string) :=
let braket := find_braket_interior (-1) sl in
let brace  := find_brace_interior (-1) sl in
let x := "Modifier" :: modifier_name
               :: braket ++ last_delete ( List.tail brace ) in   x.
Definition get_modifier (contract_name:string) (sl:list string) :=
match sl with
| nil => nil
| h :: t => let modifier_name := 
     (contract_name++"_ι_"++h)%string in make_modifier_interior modifier_name sl
end.
Fixpoint make_modifiers (contract_name:string)(sl:list string) :=
match sl with
| nil => nil
| "modifier" :: t => (get_modifier contract_name t) :: (make_modifiers contract_name t)
| h :: t => make_modifiers contract_name t
end.
(* Work with constructors ccccccccccccccccccccccccccccccccccccccccccccccccccccccc cccccccc*)
Definition make_constructor_interior (constructor_name:string) (sl:list string) :=
let braket := find_braket_interior (-1) sl in
let brace  := find_brace_interior (-1) sl in
let x := "Definition" :: constructor_name
               :: braket ++ last_delete ( List.tail brace ) in   x.
Definition get_constructor (contract_name:string) (sl:list string) :=
match sl with
| nil => nil
| h :: t => let constructor_name := 
     (contract_name++"_ι_"++"constructor")%string in make_constructor_interior constructor_name sl
end.
Fixpoint make_constructors (contract_name:string)(sl:list string) :=
match sl with
| nil => nil
| "constructor" :: t => (get_constructor contract_name t) :: (make_constructors contract_name t)
| h :: t => make_constructors contract_name t
end.
(* Work with functions fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff*)
Fixpoint make_function_returns (sl:list string) :=
match sl with
| nil => nil
| h :: nil      => [sol2coq_full_types h]
| h :: _ :: nil => [sol2coq_full_types h]
| h :: "," :: t => (sol2coq_full_types h) :: "#" :: (make_function_returns t)
| h :: _ :: "," :: t => (sol2coq_full_types h) :: "#" :: (make_function_returns t)
| _ => nil
end.

Fixpoint get_function_returns(contract_name:string) (sl:list string) :=
match sl with
| nil => ":" :: contract_name :: ["True"]
| "{" :: t => ":" :: contract_name :: ["True"]
| "returns" :: t => let x := last_delete (tail (find_braket_interior (-1) t)) in
                    let y := make_function_returns x in
                    match y with
                    | nil => ":" :: contract_name :: ["True"]
                    | _   => ":" :: contract_name ::  y
                    end
| h :: t => get_function_returns contract_name t
end.
Definition make_function_interior (function_name:string) (sl:list string) := 
let braket := find_braket_interior (-1)  sl in
let crotch := get_function_returns "XXX" (find_crotch_interior false sl) in
let brace  := find_brace_interior (-1)   sl in
let x := "Definition" :: function_name
               :: braket ++ crotch ++ brace in   x.
Definition get_function (contract_name:string) (sl:list string) :=
match sl with
| nil => nil 
| h :: t => let function_name := 
     (contract_name++"_Ф_"++h)%string in make_function_interior function_name t
end.

Fixpoint make_functions' (contract_name:string)(sl:list string) :=  
match sl with
| nil => nil
| "function" :: t => (get_function contract_name t) ::
                     (make_functions' contract_name t)
| h :: t => make_functions' contract_name t
end.
(* Argument preparing *)
Fixpoint get_argum (sl:list string) := 
match sl with
| nil => nil
| "(" :: ")" :: t => nil
| "(" :: t => "(" :: (get_argum t)
| typ :: name :: ")" :: t => name :: ":" :: (sol2coq_full_types typ) :: ")" :: nil
| typ :: name :: "," :: t => name :: ":" :: (sol2coq_full_types typ) :: ")(" :: (get_argum t)
| typ :: modif :: name :: "," :: t => name :: ":" :: (sol2coq_full_types typ) :: ")(" :: (get_argum t)
| typ :: modif :: name :: t   => name :: ":" :: (sol2coq_full_types typ) :: nil 
| typ :: name :: t => name :: ":" :: (sol2coq_full_types typ) :: nil 
| _ => nil
end.
Inductive type_of_name :=
| NUMBER : type_of_name
| LOCAL  : type_of_name
| VAR    : type_of_name
| FUNf   : type_of_name
| FUNdo  : type_of_name.
Definition isNum(s:string) := 
if (s =? "") then false
else
match num_of_string s with
| None => false
| Some x => true
end.

Definition who (s:string) := 
if ((first2 s) =? "m_") then VAR
else
match isNum s with
| true => NUMBER
| flase => LOCAL
end. 

Definition get_full_function(contract_name:string) (sl:list string) := 
[((headS "" sl)++" "++(headS "" (tail sl)))%string] ++ 
(get_argum (find_braket_interior (-1) sl)) ++ 
 [" := "]  ++  (find_brace_interior (-1) sl).

Definition make_functions(contract_name:string)(sl:list string) := 
let lines := make_functions' contract_name sl in 
let argums_list := map get_argum (map (find_braket_interior (-1)) lines) in
let x := map (get_full_function contract_name) lines in x .

(* Work with structs ssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss*)
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
  ("Global Instance Acc_"++y++" : Accessor "++y++" := { acc := ·"++(writeNat n)++" } ."++newline)%string ::
                                make_pull_up_per_number (S n) t
                                                           end 
end.
 
Definition get_struct_itself(struct_name:string) (sl:list string) :=
match sl with                                             
| nil => nil
| h :: t => let x := make_struct_interior struct_name t in
            let x := get_type_lines struct_name x in
            let typelist := get_type_list x in
            let typestring := ("{" ++ (concat_with " " typelist) ++ "}")%string in
            let all := (typestring ++ " := " ++ struct_name ++ "C")%string in
 let natural_type_list := (concat_with " " (map cot_mini_types2coq_types typelist)) in

        let rec := (newline :: "Record" :: (struct_name++"P")%string :: all :: x) in

        if (isEmpty (concat_with " " x)) then nil else rec 
end.

Definition get_struct_Arguments(struct_name:string) (sl:list string) :=
match sl with                                              
| nil => nil
| h :: t => let x := make_struct_interior struct_name t in
            let x := get_type_lines struct_name x in
            let typelist := get_type_list x in
            let typestring := ("{" ++ (concat_with " " typelist) ++ "}")%string in
            let all := (typestring ++ " := " ++ struct_name ++ "C")%string in
        let natural_type_list := (concat_with " " (map cot_mini_types2coq_types typelist)) in

         "Arguments " :: (struct_name ++ "C")%string ::
                " [ " :: (concat_with " " typelist) :: " ] " :: ["."]  
end.

Definition get_struct_DefinitionType (struct_name:string) (sl:list string) :=
match sl with                                               
| nil => nil
| h :: t => let x := make_struct_interior struct_name t in
            let x := get_type_lines struct_name x in
            let typelist := get_type_list x in
            let typestring := ("{" ++ (concat_with " " typelist) ++ "}")%string in
            let all := (typestring ++ " := " ++ struct_name ++ "C")%string in
        let natural_type_list := (concat_with " " (map cot_mini_types2coq_types typelist)) in
             "Definition " :: struct_name :: (" := @" ++
                  struct_name++"P ")%string :: natural_type_list :: ["."]
end.
Definition get_struct_existT (struct_name:string) (sl:list string) :=
match sl with                                               (* get_type_list *)
| nil => nil
| h :: t => let x := make_struct_interior struct_name t in
            let x := get_type_lines struct_name x in
            let typelist := get_type_list x in
            let typestring := ("{" ++ (concat_with " " typelist) ++ "}")%string in
            let all := (typestring ++ " := " ++ struct_name ++ "C")%string in
        let natural_type_list := (concat_with " " (map cot_mini_types2coq_types typelist)) in
             ("Global Instance Struct_"++struct_name)%string :: ":" :: ("Struct "++struct_name)%string
              :: ":=" :: "{" :: newline  :: tab :: "fields" :: ":=" :: "[" ::

              (concat_with newline (map make_line_for_Global_Instatce 
                                             (map clear_some_symbols x))) ::
                    tab :: "]" :: ";" :: newline ::
                 tab :: "ctor" :: ":=" :: ("@"++struct_name++"C")%string :: natural_type_list 
                   :: " " :: newline :: "}" :: ["."]
end.

Definition get_struct_Acc_ (struct_name:string) (sl:list string) :=
match sl with                                               (* get_type_list *)
| nil => nil
| h :: t => let x := make_struct_interior struct_name t in
            let x := get_type_lines struct_name x in
            make_pull_up_per_number 0 x
end.

Definition get_struct_BindScope (struct_name:string) (sl:list string) :=
match sl with                                               (* get_type_list *)
| nil => nil
| h :: t => "Bind" :: "Scope" :: "struct_scope" :: "with" :: struct_name :: ["."]
end.  
Fixpoint list_pass (l:list string) :=
match l with
| nil => ""
| "{
" :: t   => list_pass t
| "}.
" :: t  => list_pass t
| h :: t => if (isEmpty h) then list_pass t
                           else ("default" ++ " " ++ (list_pass t))%string
end.

Definition get_struct_default(struct_name:string) (sl:list string) :=
match sl with                                             
| nil => nil
| h :: t => let x := make_struct_interior struct_name t in
            let x := get_type_lines struct_name x in
            let typelist := get_type_list x in
            let typestring := ("{" ++ (concat_with " " typelist) ++ "}")%string in
            let all := (typestring ++ " := " ++ struct_name ++ "C")%string in
        let natural_type_list := (concat_with " " (map cot_mini_types2coq_types typelist)) in

         ("Instance" :: (struct_name++"_default")%string :: ":" :: "XDefault" :: struct_name ::
          ":=" :: "{" :: newline :: 
          tab :: "default" :: ":=" :: ( struct_name ++ "C")%string :: (list_pass x) :: newline 
          :: "}" :: ["."])   
end.

Definition get_struct (contract_name:string) (sl:list string) :=
match sl with                                               (* get_type_list *)
| nil => nil
| h :: t => let struct_name := (contract_name++"_ι_"++h)%string in 
           ( get_struct_itself struct_name sl )         ++ [newline] ++
           ( get_struct_Arguments struct_name sl )      ++ [newline] ++ 
           ( get_struct_DefinitionType struct_name sl ) ++ [newline] ++
           ( get_struct_existT struct_name sl )         ++ [newline] ++
           ( get_struct_Acc_ struct_name sl )           ++ [newline] ++
           ( get_struct_BindScope struct_name sl )      ++ [newline] ++
           ( get_struct_default struct_name sl )        ++ [newline]
end.
Fixpoint make_structs (contract_name:string)(sl:list string) :=
match sl with
| nil => nil
| "struct" :: t => (get_struct contract_name t) :: (make_structs contract_name t)
| h :: t => make_structs contract_name t
end. 

(***************    Work with rest stuff of contructs   *********                ********)
(* Pulling the chains of zero-level *)
Fixpoint make_list_level_0(f:bool)(n:nat)(sl:list string ) :=
match f, n, sl with
| _,     _,     nil  => nil 
| false, _, "{" :: t => make_list_level_0 false (n+1) t
| true,  _, "{" :: t => make_list_level_0 false  n    t
| _,  _, "}" :: t    => make_list_level_0 false (n-1) t
| _,  _,  "" :: t    => make_list_level_0 false  n    t
| _,  _,  "function" :: t => make_list_level_0 true (n+1) t
| _,  _,  "struct"   :: t => make_list_level_0 true (n+1) t
| _,  _,  "modifier" :: t => make_list_level_0 true (n+1) t
| false, 0, h :: t => h :: make_list_level_0 false 0 t
| _, _, h :: t =>   make_list_level_0 f n t
end.

Fixpoint make_elses' (prefix':string) (sl:list string) :=
match sl with
| nil => nil
| key_word :: name :: nil => 
(tab++prefix'++"_ι_"++name)%string :: ":" :: (sol_types2coq_mini_types key_word) :: ";" :: nil
| key_word :: modif :: name :: "=" :: xxx => 
(tab++prefix'++"_ι_"++name)%string :: ":" :: (sol_types2coq_mini_types key_word) :: ";" :: 
                ("(*"++modif++" := "++(headS "" xxx)++"*)")%string :: nil
| key_word :: modif :: name :: nil => 
(tab++prefix'++"_ι_"++name)%string :: ":" :: (sol_types2coq_mini_types key_word) :: ";" :: 
                ("(*"++modif++"*)")%string :: nil
| "mapping" :: "(" :: type1 :: "=>" :: type2 :: ")" :: name :: nil =>
(tab++prefix'++"_ι_"++name)%string :: ":" :: "Arr" :: (sol_types2coq_mini_types type1) ::
                                          (sol_types2coq_mini_types type2) :: ";" :: nil
| _ => nil
end.
Fixpoint get_type_list'' (w:list(list string)) :=
match w with
| nil => nil
| h :: t => match h with             
            | nil => (get_type_list'' t)
            | h' :: h'' :: h''' :: t' => h''' :: (get_type_list'' t)
            | h' :: t' => (get_type_list'' t)
            end 
end.
 
Definition make_elses (contract_name:string) (sl:list string) :=
let q := make_list_level_0 false 0 sl in 
let x := concat_with " " q in
let y := split_string' ";" x in 
let z := map clear_string_easy (map (split_string' " ") y) in 
let w := map (make_elses' contract_name) z in 
let type_list := concat_with " " (list_of_uniq_types [] (get_type_list'' w)) in
let natural_type_list := (concat_with " " (map cot_mini_types2coq_types 
                                                   (split_string' " " type_list))) in
let rec :=
    ["Record " ; (contract_name++"P"++"{"++ type_list ++"}")%string ; ":=" ; 
                (contract_name++"C"++" {")%string ] :: w ++  ["} ."] ::
     ["Arguments" ; (contract_name ++ "C")%string  ; "[" ; type_list ; "]" ; "." ] ::
     [ "Definition " ; contract_name ; (" := @" ++
                  contract_name++"P ")%string ; natural_type_list ; "." ] ::
    [("Global Instance Struct_"++contract_name++" : Struct "++contract_name++" := {"++
     newline++tab++"fields := [" ++ 
     newline++ (concat_with newline (map make_line_for_Global_Instatce 
                                             (map clear_some_symbols 
                                   (map (concat_with " ") w) )))  ++
     newline++tab++ "] ; "++
     newline++tab++"ctor := @"++contract_name++"C "++ natural_type_list ++
     newline ++"} .")%string]
     
     :: ( make_pull_up_per_number 0 (map clear_some_symbols 
                                   (map (concat_with " ") w) ) ) ::
        ("Instance" :: (contract_name++"_default")%string :: ":" :: "XDefault" :: contract_name ::
          ":=" :: "{" :: newline :: 
          tab :: "default" :: ":=" :: ( contract_name ++ "C")%string :: 
              (list_pass (map (concat_with " ") w)) :: newline :: "}" :: "." :: [newline])
     :: nil in 
 
         if (isEmpty (concat_with " "(map (concat_with " ") w))) then nil else rec. 

(* Workin of contructs ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc*)
Definition make_contract_interior (contract_name:string) (sl:list string) :=
let x := find_brace_interior (-1) sl in 
let x := last_delete ( List.tail x ) in   
let ctrt := "Сontract" in
let str := (make_structs contract_name x) in
let structs   :=  [ctrt ; (contract_name)%string] :: str in 
let elses := structs ++  (make_elses contract_name x) in        (*  elses. *)
let functions :=                                               (* structs ++ *) 
                 (make_functions contract_name x) in  functions.

(* let constructors := functions ++ (make_constructors contract_name x) in 
let modifiers := constructors ++ (make_modifiers contract_name x) in modifiers. *)

(* The first line is a name of contruct *)
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
(* Name contracts list ---------------------------------------------------------------*)
Fixpoint contracts_list (sl:list string) :=
match sl with
| nil => nil
| "contract" :: name :: t => name :: (contracts_list t) 
| h :: t => contracts_list t
end.
(* Name structs list *)
Fixpoint structs_list (s:string) (sl:list string) :=
match sl with
| nil => nil
| "contract" :: name :: t => structs_list name t 
| "struct" :: name :: t => (name, (name++"_ι_"++s)%string) :: structs_list s t
| h :: t => structs_list s t
end.
(* Name functions list *)
Fixpoint functions_list (s:string) (sl:list string) :=
match sl with
| nil => nil
| "contract" :: name :: t => functions_list name t 
(* | "function" :: name :: t => (name, (name++"_ι_"++s)%string) :: functions_list s t *)
| "function" :: name :: t => (name, (s++"_Ф_"++name)%string) :: functions_list s t
| h :: t => functions_list s t
end.
(* Testing for already exist in functions list *)
Fixpoint exists_function(s:string) (fl:list (string*string)) :=
match fl with
| nil => false
| h :: t => let fl' := fst h in if(s =? fl') then true
                                             else exists_function s t
end.
(* List of functions execute *)
Fixpoint execute_list (fl:list (string*string)) (s:string) (sl:list string) :=
match sl with
| nil => nil
| "function" :: name :: t => (name , "") :: (execute_list fl name t)
| h :: t => if(exists_function h fl) then (s , h) :: (execute_list fl s t)
                                     else execute_list fl s t
end.
(* Tuple outing *)
Fixpoint tuple_outing(fl:list (string*string)) :=
match fl with
| nil => ""
| h :: t => ((fst h) ++ " " ++ (snd h) ++ newline ++ (tuple_outing t) )%string
end.
Fixpoint functions_'(s:string)(acc1:list(list string))(acc2:list string)(fl:list (list string)) :=
match fl with
| nil => acc1
| h :: t => let x := (headS "" h) in 
            let y := headS "" (tail h) in 
            if(x =? s)
              then functions_' s acc1           (acc2++[y]) t
              else functions_' x (acc1++[acc2]) ([x;y])     t
end.
(* ================== Building a order of function running =================================================*)
(* Functions without running functions contain into top of list *)
Fixpoint function_order'(acc sl:list (list string)) :=
match sl with
| nil => acc
| h :: t => if (Nat.eqb (List.length h) 1) then h :: (function_order' acc t)
                                           else function_order' (acc(* ++[h] *)) t
end.
Fixpoint function_order''(n:nat)(already:list string) (sl:list (list string)) :=
match n, sl with
| 0, _ => nil
| _, nil => nil
| S n', h :: t => if(test_already_exists_for_list (tail h) already) 
                   then  h :: (function_order'' n' (already++[(headS "" h)]) t)
                   else  let t' := t ++ [h] in function_order'' n' (already++[(headS "" h)]) t'
end.
Definition function_order(sl:list string) :=
let x := functions_list "" sl in
let y := execute_list x "" sl in
let z := map (split_string' " " )(split_string' newline (tuple_outing y)) in
let t := clear_list_easy (map clear_string_easy (functions_' "" [] [] z)) in 
let tt := function_order' [] t in 
let f := tt ++ (function_order'' ((List.length t)+1) [] t) in
                                (* returning a list of functions in the correct sequence  *)
map (headS "") f.
(******************************************************)
Definition last'{A}(d : A) (l : list A)  := List.last l d.
Fixpoint get_function_line(s:string)(sl:list(list string)) :=
match sl with
| nil => nil
| h :: t => let q := headS "" h in
            let x := split_string' "_Ф_" q in
            let y := last' "" x in
            if(s =? y) then h
                       else get_function_line s t
end.
Fixpoint build_right_order(ord:list string) (sl:list(list string)) :=
match ord with
| nil => nil
| h :: t => (get_function_line h sl) :: (build_right_order t sl)
end.
Check functions_list.
(* find coq-name in tuple *)
Fixpoint find_coq_name(s:string)(tl:list (string * string)) := 
match tl with
| nil => ""
| h :: t => if(s =? (fst h)) then snd h
                             else find_coq_name s t
end.
(* rename from solidity mode to coq mode *)
Fixpoint rename_sol2coq(tl:list (string * string))(sl:list string) :=
match sl with
| nil => nil
| h :: t => let q := find_coq_name h tl in if(q =? "") 
                                           then h :: (rename_sol2coq tl t)
                                           else q :: (rename_sol2coq tl t)
end.
(*******************************************************************************************)

Definition shaper(s: string) := let s:= clearComment false (setSpace s) in 
let sl := split_string' newline s in 
let sl := map (split_string' " ") sl in 
let sl := map clear_string_easy sl  in
let sl := clear_list_easy sl in
let sl := deleteComment sl in 
let sl := List.concat sl in

let tuple_list := functions_list "" sl in

let right_order := function_order sl in 

let all := make_contracts sl in

let sl := List.concat all in
let qq := build_right_order right_order sl in
let qq := clear_list_easy qq in

let ww := map (rename_sol2coq tuple_list) qq in

concat_with newline (map (concat_with " ") ww).


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

Extraction "./functionsFileGenerator" main.
