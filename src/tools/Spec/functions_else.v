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
| key_word :: name :: nil => (name , (prefix'++"_ι_"++name)%string) :: nil
| key_word :: modif :: name :: "=" :: xxx => 
                             (name , (prefix'++"_ι_"++name)%string) :: nil
| key_word :: modif :: name :: nil => 
                             (name , (prefix'++"_ι_"++name)%string) :: nil
| "mapping" :: "(" :: type1 :: "=>" :: type2 :: ")" :: name :: nil =>
                             (name , (prefix'++"_ι_"++name)%string) :: nil
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
  
Definition make_elses_var_list (contract_name:string) (sl:list string) :=
let q := make_list_level_0 false 0 sl in 
let x := concat_with " " q in
let y := split_string' ";" x in 
let z := map clear_string_easy (map (split_string' " ") y) in 
let w := map (make_elses' contract_name) z in   List.concat w.
Check make_elses_var_list.
(* Working of contruct's variables ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc*)
Definition make_contract_interior_v (contract_name:string) (sl:list string) :=
let x := find_brace_interior (-1) sl in 
let x := last_delete ( List.tail x ) in   
let ctrt := "Сontract" in
let str := (make_structs_var_list contract_name x) in
let structs   :=  List.concat str in 
let list_names := structs ++ (make_elses_var_list contract_name x) in  list_names.
Check make_contract_interior_v. 

(* The first line is a name of contruct *)  
Definition get_contract_v (sl:list string) :=
match sl with 
| nil => nil
| h :: t => let contract_name := h in make_contract_interior_v contract_name t
end.  
Fixpoint make_contracts_v (sl:list string) :=
match sl with
| nil => [nil]
| "contract" :: t => (get_contract_v t) :: (make_contracts_v t)
| h :: t => make_contracts_v t
end. 
Check make_contracts_v.
(* Workin of contruct's functions ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc*)
Definition make_contract_interior (contract_name:string) (sl:list string) :=
let x := find_brace_interior (-1) sl in 
let x := last_delete ( List.tail x ) in   
let functions :=
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
| "struct" :: name :: t => (name, (s++"_ι_"++name)%string) :: structs_list s t
| h :: t => structs_list s t
end.
(* List of constants *)
Fixpoint const_list(s:string) (sl:list string) :=
match sl with
| nil => nil
| "contract" :: name :: t => const_list name t 
| typ :: "constant" :: name :: t => (name, (s++"_ι_"++name)%string) :: const_list s t
| h :: t => const_list s t
end.
(* Name functions list *)
Fixpoint functions_list (s:string) (sl:list string) :=
match sl with
| nil => nil
| "contract" :: name :: t => functions_list name t 
| "function" :: name :: t =>  (name, (s++"_Ф_"++name)%string) :: functions_list s t
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
(* Fixpoint function_order'(acc sl:list (list string)) :=
match sl with
| nil => acc
| h :: t => if (Nat.eqb (List.length h) 1) then h :: (function_order' acc t)
                                           else function_order' (acc(* ++[h] *)) t
end. *)
Fixpoint function_order'(sl:list (list string)) :=
match sl with
| nil => nil
| h :: t => if (Nat.eqb (List.length h) 1) then h :: (function_order' t)
                                           else function_order' t
end.
Fixpoint function_order''(n:nat)(already:list string) (sl:list (list string)) :=
match n, sl with
| 0, _ => nil
| _, nil => nil
| S n', h :: t => let h' := (headS "" h) in 
                     if(test_already_exists_for_list (tail h) already) 
                     then  h :: (function_order'' n' (already++[h']) t)
                     else  let t' := t ++ [h] in function_order'' n' (already++[h']) t'
end.
Definition function_order(sl:list string) :=
let x := functions_list "" sl in
let y := execute_list x "" sl in
let z := map (split_string' " " )(split_string' newline (tuple_outing y)) in 
let t := clear_list_easy (map clear_string_easy (functions_' "" [] [] z)) in  
let tt := function_order' t in 
let f := tt ++ (function_order'' ((List.length t)+400) [] t) in
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
(* The variables what are in functions *)
Fixpoint get_local_vars_list (sl:list string) :=
match sl with
| nil => nil
| h :: t => if(test_already_exists h separators) 
            then (get_local_vars_list t)
            else let h' := headS "" t in 
                 if (test_already_exists h' separators)
                 then (get_local_vars_list t)
                 else (h') :: (get_local_vars_list t)
end.
Fixpoint get_list_funcs_args (sl:list string) :=
match sl with
| nil => nil
| n1 :: ":" :: n2 :: t => n1 :: (get_list_funcs_args t)
| h :: t => (get_list_funcs_args t)
end.
Definition get_list_vars_function (sl:list string) :=
match sl with
| nil => nil
| _ => (get_list_funcs_args (last_delete(tail(find_braket_interior (-1) sl))))
    ++ (get_local_vars_list (last_delete(tail(find_brace_interior  (-1) sl))))
end.
(* Renaming the "m_" variables *)
Fixpoint m_renaming(vars_list:list(string*string))(sl:list string) :=
match sl with
| nil => nil
| h :: t => if((first2 h) =? "m_") then (find_coq_name h vars_list) :: (m_renaming vars_list t)
                                   else h :: (m_renaming vars_list t)
end.
(* Renaming the global variables *)
Fixpoint else_renaming(vars_list:list(string*string))(sl:list string) :=
match sl with
| nil => nil
| h :: t => let q := (find_coq_name h vars_list) in
                if (q =? "") then h :: (else_renaming vars_list t)
                             else q :: (else_renaming vars_list t)
end.

(* Delete construction as 'type variable;' and 'type variable =' to last only 'variable =' *)
Fixpoint prepare_function_type_var (sl : list string) :=
match sl with
| nil => nil
| h1 :: "." :: h2 :: "(" :: t => h1 :: "." :: h2 :: "(" :: (prepare_function_type_var t) 
| h1 :: "=" :: h2 :: "(" :: t => h1 :: "=" :: h2 :: "(" :: (prepare_function_type_var t) 
| h1 :: h2 :: "=" :: t => if(test_already_exists h1 separators) 
                          then h1 :: h2 :: "=" :: (prepare_function_type_var t)
                          else if(test_already_exists h2 separators)
                               then h1 :: h2 :: "=" :: (prepare_function_type_var t)
                               else h2 :: "=" :: (prepare_function_type_var t)
| h1 :: h2 :: "," :: t => if(test_already_exists h1 separators) 
                          then h1 :: h2 :: "," :: (prepare_function_type_var t)
                          else if (test_already_exists h2 separators) 
                               then h1 :: h2 :: "," :: (prepare_function_type_var t)
                               else h2 :: "," :: (prepare_function_type_var t)
| h1 :: h2 :: ")" :: t => if(test_already_exists h1 separators) 
                          then h1 :: h2 :: ")" :: (prepare_function_type_var t)
                          else if(test_already_exists h2 separators)
                               then h1 :: h2 :: ")" :: (prepare_function_type_var t)
                               else h2 :: ")" :: (prepare_function_type_var t)
| h1 :: h2 :: ";" :: t => if(test_already_exists h1 separators) 
                          then h1 :: h2 :: ";" :: (prepare_function_type_var t)
                          else if(test_already_exists h2 separators) 
                               then h1 :: h2 :: ";" :: (prepare_function_type_var t)
                               else (prepare_function_type_var t)
| h :: t => h :: (prepare_function_type_var t)
end.
Fixpoint delete_mapping (f:bool) (sl:list string) :=
match f, sl with
| _, nil => nil
| false, "mapping" :: "(" :: t => delete_mapping true t
| true, ")" :: t => delete_mapping false t
| true, h :: t => delete_mapping true t
| false, h :: t => h :: (delete_mapping false t)
end.
Fixpoint rename_numbers (sl:list string) :=
match sl with
| nil => nil
| h :: t => if (isNum h) then ("xInt"++h)%string :: (rename_numbers t)
                         else h :: (rename_numbers t)
end.
Fixpoint rename_tvm_some(sl:list string) :=
match sl with
| nil => nil
| "tvm" :: "." :: name :: t => ("tvm" ++ "_" ++ name)%string :: (rename_tvm_some t)
| h :: t => h :: (rename_tvm_some t) 
end.

Fixpoint clean_vars_list(vl:list(string * string)) :=
match vl with
| nil => nil
| (a,b) :: t => if(test_already_exists a separators) then clean_vars_list t
                else
                if(test_already_exists b separators) then clean_vars_list t
                else (a,b) :: (clean_vars_list t)
end.

Fixpoint get_list_func_type' (f:bool)(sl:list string) :=
match f, sl with
| _, nil => nil
| _, "(((" :: h :: t => h :: (get_list_func_type' true t)
| _, ":=" :: t => nil
| true, h :: t => h :: get_list_func_type' true t
| false, h :: t =>  get_list_func_type' false t
end.

Fixpoint get_list_func_type (sl:list(list string)) :=
match sl with
| nil => nil
| h :: t => match h with
            | nil => get_list_func_type t
            | "Definition" :: n :: t' => if( test_already_exists "(((" t' )
                            then (n , get_list_func_type' false t' ) :: (get_list_func_type t)
                            else get_list_func_type t
            | _ => get_list_func_type t
            end
end.

Fixpoint clear_list_func_type (sl:list(list string)) :=
match sl with
| nil => nil
| h :: t => match h with
            | nil => clear_list_func_type t
            | "Definition" :: t' => if( test_already_exists "(((" t' )
                            then clear_list_func_type t
                            else h :: clear_list_func_type t
            | _ => h :: clear_list_func_type t
            end
end.

Fixpoint adding (lst:list(string * (list string))) (n:string) :=
match lst with
| nil => [n]
| (n', l) :: t => if(n' =? n) then l
                              else adding t n
end.

Fixpoint add_list_func_type''(n:string)(lst:list(string * (list string))) (sl:list string) :=
match sl with
| nil => nil
| ":=" :: t => ( adding lst n ) ++ ":=" :: t
| h :: t => h :: add_list_func_type'' n lst t
end.

Definition add_list_func_type' (lst:list(string * (list string))) ( sl:list string) :=
let n := headS "" (tail (split_string' " " (headS "" sl))) in
add_list_func_type'' n lst sl.

Definition add_list_func_type (sl :list(list string)) := 
let lst := get_list_func_type (map clear_string_easy sl) in 
let x := clear_list_func_type (map clear_string_easy sl) in 
map (add_list_func_type' lst) x.

