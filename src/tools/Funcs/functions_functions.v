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
end .   

Fixpoint make_function_returns_for_return (sl:list string) :=
match sl with
| nil => nil
| _ :: nil      => [" "]
| _ :: h :: nil => "return" :: h :: [";"]
| _ :: "," :: t => [" "]
| _ :: h :: "," :: t => h :: "," :: (make_function_returns_for_return t)
| _ => nil
end .

Fixpoint get_function_returns_for_return(sl:list string) :=
match sl with
| nil => "return" :: [";"]
| "{" :: t => "return" :: [";"]
| "returns" :: t => let x := last_delete (tail (find_braket_interior (-1) t)) in
                    let y := make_function_returns_for_return x in
                    match y with
                    | nil   => "return" :: [";"]
                    | [" "] => nil
                    | _     => "return" :: "(" :: y ++ [")"]
                    end
| h :: t => get_function_returns_for_return t 
end .   

Definition make_function_interior (contract_name:string) (function_name:string) (sl:list string) := 
let braket := find_braket_interior (-1)  sl in
let crotch := "((("::(get_function_returns ((* contract_name *)"Ledger"++"T")%string (find_crotch_interior false sl)) in
let brace  := find_brace_interior (-1)   sl in  
let x := "Definition" :: function_name  :: 
              braket  ++  crotch ++ [":="] ++ brace in   x.

Definition get_function (contract_name:string) (sl:list string) :=
match sl with
| nil => nil 
| h :: t => let function_name := 
     (contract_name++"_Ф_"++h)%string in make_function_interior contract_name function_name t
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
| typ :: modif :: name :: t   => name :: ":" :: (sol2coq_full_types typ) :: ")" :: nil 
| typ :: name :: t => name :: ":" :: (sol2coq_full_types typ) :: nil 
| _ => nil
end.

Definition get_full_function(contract_name:string) (sl:list string) := 
[((headS "" sl)++" "++(headS "" (tail sl)))%string] ++ 
(get_argum (find_braket_interior (-1) sl)) ++ 
 [":="]  ++  (find_brace_interior (-1) sl).

Definition make_functions(contract_name:string)(sl:list string) := 
let lines := make_functions' contract_name sl in 
let argums_list := map get_argum (map (find_braket_interior (-1)) lines) in
let x := map (get_full_function contract_name) lines in x ++ lines.

Fixpoint make_functions_for_return (sl:list string) :=  
match sl with
| nil => nil
| "function" :: t => get_function_returns_for_return t
| h :: t => make_functions_for_return t
end.

(* Adding a modifier's reqiures ! *)
Fixpoint get_modif_from_list(m : list(string * (list string)))(name:string):=
match m with
| nil => nil
| (a,b) :: t => if(a =? name) then b
                              else get_modif_from_list t name
end.

Fixpoint add_modifiers_to_functions'(m : list(string * (list string)))(sl:list string):=
match sl with
| nil => nil
| h1 :: h :: "{" :: t => 
        if (h1 =? "modifier") 
        then  h1 :: h :: "{" :: (add_modifiers_to_functions' m t)
        else let mo := get_modif_from_list m h in
             if (Nat.eqb (List.length mo) 0)
             then h1 :: h :: "{" :: (add_modifiers_to_functions' m t)
             else "{" :: mo ++ (add_modifiers_to_functions' m t)

| h :: t => h :: (add_modifiers_to_functions' m t)
end.

Definition add_modifiers_to_functions(sl:list string) :=
let m := modifier_list_with_bodies sl in
add_modifiers_to_functions' m sl.



Fixpoint get_orig_text_funcs_list(n:string)(sl:list string):=
match sl with
| nil => nil
| "contract" :: name :: t => get_orig_text_funcs_list name t
| "function" :: name :: t => let q := pulling_list_elements "{" t in
                             let w :=  find_brace_interior (-1) (t++["}"]) in
                   ((n++"_Ф_"++name)%string , "function" :: name :: q ++ w ) ::
                                                          get_orig_text_funcs_list n t
| h :: t => get_orig_text_funcs_list n t
end.

Fixpoint add_orig_funcs_texts(tl:list(string*(list string)))(sl:list(list string)) :=
match sl with
| nil => nil
| h :: t => let q := headS "" (tail h) in
            let e := q in (* delete_first_symbols_include_determined_and_else_one (String "164"%char "") q in *)
            let w := "(*" :: (find_typelist tl e) ++ ["*)"] in
            let r := newstringing_for_length 0 w in
      [r] ++ h :: add_orig_funcs_texts tl t 
end.

(* List of all digits *)
Fixpoint get_digits_list' (acc:list string) (sl:list string) :=
match sl with
| nil => acc
| h :: t => if ( isNum h ) 
            then 
              if ( test_already_exists h acc ) 
              then get_digits_list' acc t
              else
                   if ( (first4 h) =? "xInt" )
                   then 
                        let acc := h :: acc in get_digits_list' acc t
                   else 
                        let acc := (h++"xInt")%string :: acc in get_digits_list' acc t
           else get_digits_list' acc t
end.
Fixpoint get_parameters_throw_digit (n:nat)(sl:list string) :=
match sl with
| nil => ""
| h :: t => let q := String.length h in
            let w := q + n in
            if ( w <? 52 ) 
            then ( ( get_parameters_throw_digit w t) ++ " " ++ h )%string
            else ( ( get_parameters_throw_digit 0 t) ++ newline ++ h )%string
end.
Fixpoint toPureDigit (s:string) :=
match s with
| "" => ""
| String h t => let q := String h "" in
                if ( isNum q ) then String h ( toPureDigit t )
                               else toPureDigit t
end.
Fixpoint get_definition_throw_digit (sl:list string) :=
match sl with
| nil => ""
| h :: t => ("Definition"++" "++h++" "++":="++" "++(toPureDigit h)++"%Z"++"."++
             newline++(get_definition_throw_digit t) )%string
end.
Definition get_digits_list(sl:list(list string)) :=
let q := List.concat sl in
let w := get_digits_list' [] q in
let e := get_parameters_throw_digit 0 w in
let r := get_definition_throw_digit w in
(
"

(* 
These lines need to place into 'SolidityNotation.v':

Parameters "++e++" : XInteger .

and these - into 'ProofEnvironment.v':

"++r++"
*)

"
)%string.


Fixpoint make_tuple_braket (sl:list string) :=
match sl with
| nil => nil
| "LedgerT" :: h :: t => let q := headS "" t in
                         if ( q =? "#" ) 
                         then "LedgerT" :: "(" :: h :: make_tuple_braket t
                         else "LedgerT" :: h :: make_tuple_braket t
| "#" :: h :: ":=" :: t => "#" :: h :: ")" :: ":=" :: make_tuple_braket t

| h :: t => h :: make_tuple_braket t
end.

Fixpoint analisys_for_returns' (sl:list string) :=
   let fix tail'' (sl:list string) :=
    match sl with
    | nil => nil
    | ")" :: t => ")" :: "XInteger" :: ")" :: analisys_for_returns' t 
    | h :: t => h :: tail'' t
    end in
    let fix tail' (sl:list string) :=
    match sl with
    | nil => nil
    | "LedgerT" :: "(" :: t => "LedgerT" :: "(" :: "XErrorValue" :: "(" :: tail'' t 
    | "LedgerT" :: h :: t => 
      "LedgerT" :: "(" :: "XErrorValue" :: h :: "XInteger" :: ")" :: analisys_for_returns' t 
    | h :: t => h :: tail' t
    end in
match sl with
| nil => nil
| "Definition" :: h :: t => "Definition" :: h :: tail' t 
| h :: t => h :: analisys_for_returns' t
end.

Definition analisys_for_returns (sl:list string) :=
let q := test_already_exists "require" sl in
analisys_for_returns' sl .

Fixpoint repair_require (sl:list string) :=
    let fix tail' (sl:list string) :=
    match sl with
    | nil => nil
    | ")" :: ">>" :: t => "}}" :: ";" :: repair_require t
    | h :: t => h :: tail' t
    end in
match sl with
| nil => nil
| "require" :: "(" :: t => "Require" :: "{{" :: tail' t 
| h :: t => h :: repair_require t
end.

Fixpoint set_return_I (sl:list string) :=
match sl with
| nil => newline :: "return!" :: "I" :: "." :: newline :: nil
| "return!" :: "I" :: t => newline :: "return!" :: "I" :: "." :: newline :: nil
| "return" :: t => newline :: "return!" :: "I" :: "." :: newline :: nil
| "." :: t => newline :: "return!" :: "I" :: "." :: nil
| ">>" :: nil => ">>" :: newline :: "return!" :: "I" :: "." :: newline :: nil
| ";" :: nil => ";" :: newline :: "return!" :: "I" :: "." :: newline :: nil
| h :: t => h :: set_return_I t
end.

Fixpoint repair_return (sl:list string) :=
    let fix tail' (sl:list string) :=
    match sl with
    | nil => nil
    | ")" :: ">>" :: t => ")" :: "." :: repair_return t
    | ";" :: t => "." :: repair_return t
    | h :: t => h :: tail' t
    end in
    let fix tail'' (sl:list string) :=
    match sl with
    | nil => nil
    | ")" :: ">>" :: t => "!)" :: "." :: repair_return t
    | h :: t => h :: tail'' t
    end in
    let fix tail''' (sl:list string) :=
    match sl with
    | nil => nil
    | h :: h1 :: h2 :: t => if ( ( first4 h2 ) =? "tvm_" ) 
                       then h1 :: ")}" :: ":=" :: h2 :: repair_return t
                       else if ( have_it_symbol "164"%char h2 ) (* Ф *)
                            then h1 :: ")}" :: ":=" :: h2 :: repair_return t
                            else h1 :: h2 :: tail''' t
    | h1 :: h2 :: t => if ( ( first4 h2 ) =? "tvm_" ) 
                       then h1 :: ")}" :: ":=" :: h2 :: repair_return t
                       else if ( have_it_symbol "164"%char h2 ) (* Ф *)
                            then h1 :: ")}" :: ":=" :: h2 :: repair_return t
                            else h1 :: h2 :: tail''' t
    | h :: t => h :: tail''' t
    end in
    let fix tail'''' (sl:list string) :=
    match sl with
    | nil => nil
    | "*)" :: t => "*)" :: repair_return t
    | h :: t => h :: tail'''' t
    end in

match sl with
| nil => nil
| "return!" :: "address" :: "^^" :: "makeAddrStd" :: "(" :: t => 
           "return!" :: "address" :: "->makeAddrStd" :: "(!" :: tail'' t 
| "return#" :: "(" :: t => "return#" :: "(" :: tail' t 
| "return!" :: "$" :: t => "$" :: tail' t
| "return!" :: "u1!" :: t => "u1!" :: tail' t
| "return!" :: "u2!" :: t => "u2!" :: tail' t
| "return!" :: "u3!" :: t => "u3!" :: tail' t
| "return!" :: "u4!" :: t => "u4!" :: tail' t
| "return!" :: h :: t => if (have_it_symbol "164"%char h) (* Ф *)
                         then h :: tail' t
                         else "return!" :: h :: repair_return t
| "return!" :: t => "return!" :: tail' t
| "
" :: "}" :: ">>" :: t => repair_return t 

| ":=" :: "{" :: t => ":=" :: newline :: repair_return t

| "LedgerT" :: "True" :: t => "LedgerT" :: "True" :: set_return_I t

| "(" :: "$" :: h :: "," :: t => "{(" :: "$" :: h :: "," :: tail''' t

| "(*" :: t => "(*" :: tail'''' t

| h :: t => h :: repair_return t
end.

(* " '{(' a ',' b ')}' ':=' q ';' t "  *)
