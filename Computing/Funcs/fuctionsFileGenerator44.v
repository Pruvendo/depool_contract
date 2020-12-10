(* Building functions-file (i.e. solidity-coq translator for function sources ) *)

Load "functions_services.v".
Load "function_finds.v".

Load "functions_exchange.v".
Load "functions_types.v".
Load "functions_modifiers.v".
Load "functions_constructors.v". 

Load "functions_functions.v".
Load "functions_structs.v".
Load "functions_else.v".

Inductive type_of_name :=
| NUMBER : type_of_name
| LOCAL  : type_of_name
| VAR    : type_of_name
| FUNf   : type_of_name
| FUNdo  : type_of_name.

Definition who (s:string) := 
if (have_it_symbol "185"%char s) then VAR
else if (have_it_symbol "164"%char s) then FUNf  (* Ф *)
else if (have_it_symbol ")"%char s) then FUNf    (* ( *)
else if (have_it_symbol "155"%char s) then LOCAL (* Л *)
else if ( (first4 s) =? "msg_" ) then LOCAL
else if ( (first4 s) =? "tvm_" ) then FUNf
else
match isNum s with
| true => NUMBER
| flase => LOCAL
end.  


Fixpoint renaming_local_vars'(llv sl:list string) :=
match sl with
| nil => nil
| h :: t => if(test_already_exists h llv)
            then ("Л_"++h)%string :: (renaming_local_vars' llv t)
            else h :: (renaming_local_vars' llv t)
end.
Definition renaming_local_vars(sl:list string) :=
let xy :=  clear_string_easy (get_list_vars_function sl) in 
renaming_local_vars' xy sl.
Compute (first2 "Л_234567").
Fixpoint back_local_vars(sl:list string) :=
match sl with
| nil => nil
| "." :: h :: t => if((first2 h) =? "Л") 
                   then "." :: (del_lead_2_symbolsι_ h) :: (back_local_vars t)
                   else "." :: h :: (back_local_vars t)
| h :: t => h :: (back_local_vars t)
end.
(* pull out nested functions *)
Fixpoint func_name_to_inside'(sl:list string) :=
match sl with
| nil => nil
| h :: "(" :: t => if(have_it_symbol "164"%char h) 
            then "(" :: h :: (func_name_to_inside' t)
            else h :: "(" :: (func_name_to_inside' t)
| h :: t => h :: (func_name_to_inside' t)
end.
Fixpoint func_name_to_inside(sl:list string) :=
match sl with
| nil => nil
| "{" :: t => "{" :: (func_name_to_inside' t)
| h :: t => h :: (func_name_to_inside t)
end.

 (* for a + - / * *)
Load "functions_operations.v".
 Check make_contracts_v.



Fixpoint get_endline(sl:list string) :=
match sl with
| nil => nil
| ";" :: t => ";" :: newline :: get_endline t
| "{" :: t => newline ::"{" :: newline :: get_endline t
| "}" :: t => newline ::"}" :: newline :: get_endline t
| h :: t => h :: get_endline t
end. 

Fixpoint isElse (sl : list string) :=
let fix isElse' (n:nat)(sl:list string) :=
if ( Nat.eqb n 0 ) then let q := headS "" sl in ( if ( q =? "else" ) then true
                                                                     else false )
                   else 
match sl with
| nil => false
| "{" :: t => isElse' (n+1) t
| "}" :: t => isElse' (n-1) t
| h :: t => isElse' n t
end in 
match sl with
| nil => false
| "{" :: t => isElse' 1 t
| h :: t => isElse t
end.

Fixpoint get_to_sol(sl:list string) :=
match sl with
| nil => nil
| "(" :: ")" :: t => "()" :: get_to_sol t
| "if" :: "(" :: t => if (isElse t) then newline :: "Ife" :: "(" ::  get_to_sol t
                                    else newline :: "Ift" :: "(" ::  get_to_sol t
| "else" :: t => "else" :: get_to_sol t
| "(" :: t => "((" :: get_to_sol t
| ")" :: "{" :: t => ")" :: "{" :: get_to_sol t
| ")" :: t => "))" :: get_to_sol t
| "{" :: t => newline ::"{" :: newline :: get_to_sol t
| "}" :: t => newline ::"}" :: newline :: get_to_sol t
| ";" :: t => ">>" :: newline :: tab :: get_to_sol t
| a :: "." :: b :: t => if ((first2 a) =? "m_") then b :: get_to_sol t
                                                else  a :: "^^" :: b :: get_to_sol t
| "address(0)" :: t => "xInt0" :: get_to_sol t
| h :: t => h :: get_to_sol t
end. 

Definition if_who (a b : type_of_name) :=
match a, b with
| NUMBER, NUMBER => true
| LOCAL, LOCAL   => true
| VAR, VAR       => true
| FUNf, FUNf     => true
| FUNdo, FUNdo   => true
| _, _ => false
end.

Load "functions_operations1.v".

Fixpoint split_iterior_members_list(sl:list string):=
match sl with
| nil => nil
| h :: t => let q := split_string' " " h in
            let w := headS "" q in
            if ( w =? "Definition" ) then "Definition" :: (tail q) ++ split_iterior_members_list t
            else h :: split_iterior_members_list t
end.


Fixpoint is_msg_point (s:string)(sl:list string) :=
match sl with
| nil => false
| h :: t => if ( h =? s ) then true
            else is_msg_point s t
end.

Fixpoint repair_msg_point(s:string)(sl:list string):=
match sl with
| nil => nil
| "Definition" :: h1 :: "((" :: t => 
        let q := find_brace_interior (-1) t in  
        if (is_msg_point s q) 
        then "Definition" :: h1 :: "(" :: s :: ":" :: "XInteger" :: ")"::"(":: repair_msg_point s t
        else "Definition" :: h1 :: "(" :: repair_msg_point s t
| "Definition" :: h1 :: "(" :: t => 
        let q := find_brace_interior (-1) t in  
        if (is_msg_point s q) 
        then "Definition" :: h1 :: "(" :: s :: ":" :: "XInteger" :: ")"::"(":: repair_msg_point s t
        else "Definition" :: h1 :: "(" :: repair_msg_point s t
| "Definition" :: h1 :: ":" :: t => 
        let q := find_brace_interior (-1) t in
        if (is_msg_point s q) 
        then "Definition" :: h1 :: "(" :: s :: ":" :: "XInteger" :: ")"::":":: repair_msg_point s t
        else "Definition" :: h1 :: ":" :: repair_msg_point s t
| h :: t => h :: repair_msg_point s t
end.
 
Fixpoint delete_some (sl : list string) :=
match sl with
| nil => nil
| h1 :: "^^" :: h2 :: t => if(if_who (who h1) VAR) then h2 :: delete_some t
                                             else h1 :: "^^" :: h2 :: delete_some t
| h :: t => h :: delete_some t
end.  

Definition shaper(s: string) := let s:= clearComment1 false (clearComment false (setSpace s)) in 
let sl := split_string' newline s in 
let sl := map (split_string' " ") sl in 
let sl := map clear_string_easy sl  in
let sl := clear_list_easy sl in
let sl := deleteComment sl in 
let sl := List.concat sl in     

(* concat name [ ] *)
let sl := concat_sq_brakets sl in 
 
(* 'constructors' to 'function constructors'  *)
let sl := constructor_function 1 sl in
(* Adding modifier to functions's bodies *)
let sl := add_modifiers_to_functions sl in
(* Here are global vars from contracts including structs *)
let vars_list := List.concat (make_contracts_v sl) in 
let vars_list := clean_vars_list vars_list in
(* Building list of functions *) 
let funcs_list := functions_list "" sl in  
let struct_list := structs_list "" sl in
let consts_list := const_list "" sl in             (*  tuple_outing funcs_list.  *)

(* definition right order functions fo r eval *)
let right_order := function_order sl in  

let all := make_contracts sl in   

let sl :=  List.concat all in 
                                          
let sl := add_list_func_type sl in

let qq := build_right_order right_order sl in 
let qq := clear_list_easy qq in 
 
let ff := map (renaming_local_vars) qq in
let ff := map (back_local_vars) ff in
                                            
(* functions renaming *)
let ww := map (rename_sol2coq funcs_list)        ff in  
(* vars renaming *)
let aa := map (m_renaming vars_list) ww in
let aa' := map (else_renaming vars_list)         aa in    
(* Struct name as type renaming *) 
let bb := map (rename_sol2coq struct_list)       aa' in

let bb := map concat_op_equ bb in

let bb' := map (rename_sol2coq consts_list) bb in 
(* clearing for local variable declarations *)
let cc1 := map prepare_function_type_var bb' in  
let cc2 := map (delete_mapping false) cc1 in   let cc3 := map rename_tvm_some cc2 in
(* all numbers to Coq format *)   
let dd := map rename_numbers cc3 in

let dd := map split_iterior_members_list dd in

let dd := map get_to_sol dd in
let dd := map delete_some dd in
let dd := map set_assingment dd in
let dd := map set_plus_assingment dd in
let dd := map set_minus_assingment dd in
let dd := map set_mult_assingment dd in
let dd := map set_div_assingment dd in
let dd := map set_compare_eq dd in
let dd := map set_compare_ne dd in
let dd := map set_compare_le dd in
let dd := map set_compare_ge dd in
let dd := map set_compare_lt dd in
let dd := map set_compare_gt dd in

let dd := map (repair_msg_point "msg_sender") dd in
let dd := map (repair_msg_point "msg_value") dd in 

let dd := map all_end_prepare dd in let dd := map all_end_prepare dd in 

( concat_with newline  ( map ( concat_with " " )   dd  ) ).

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



(*Compute ( let s :=
"
   ;      
Definition RoundsBase_Ф__getOldestRound : RoundsBase ι_Round := { 
         return! ( RoundsBase_ι_m_rounds [ RoundsBase_ι_m_startIdx ] ; 
         } 
" in 
let q := split_string' " " s in
concat_with " " (work_with_return q) ).
*)

(* Fixpoint get_list_functions_to_temp (n:nat)(sl:list string) :=
match sl with
| nil => nil
| "Definition" :: h :: t => get_list_functions_to_temp n t 
| "if" :: "(" :: t => get_list_functions_to_temp n t 
| "while" :: "(" :: t => get_list_functions_to_temp n t 
| "return" :: "(" :: t => get_list_functions_to_temp n t 
| h :: "(" :: t => let q := find_braket_interior (-1) ("(" :: t) in
                     ( ("t"++writeNat n)%string , q ) :: get_list_functions_to_temp (S n) t
| h :: t => get_list_functions_to_temp n t
end.

Fixpoint set_list_functions_to_temp (n:nat)(sl:list string) :=
match sl with
| nil => nil
| "Definition" :: h :: t => get_list_functions_to_temp n t 
| "if" :: "(" :: t => get_list_functions_to_temp n t 
| "while" :: "(" :: t => get_list_functions_to_temp n t 
| "return" :: "(" :: t => get_list_functions_to_temp n t 
| h :: "(" :: t => let q := find_braket_interior (-1) ("(" :: t) in
                     ( ("t"++writeNat n)%string , q ) :: get_list_functions_to_temp (S n) t
| h :: t => get_list_functions_to_temp n t
end. *)
