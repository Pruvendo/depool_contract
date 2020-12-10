(* Work with functions fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff*)
Fixpoint make_function_returns (sl:list string) :=
match sl with
| nil => nil

| h :: nil      => [sol2coq_full_types h]
| h :: _ :: nil => [sol2coq_full_types h]
| h :: "," :: t => (sol2coq_full_types h) :: "#" :: (make_function_returns t)
| h :: _ :: "," :: t => (sol2coq_full_types h) :: "#" :: (make_function_returns t)

| "mapping" :: "(" :: h1 :: "=>" :: h2 :: ")" :: nil => 
 "(" :: "XHMap" :: (sol2coq_full_types h1) :: (sol2coq_full_types h2) :: [")"] 

| "mapping" :: "(" :: h1 :: "=>" :: h2 :: ")" :: _ :: nil => 
        "(" :: "XHMap" :: ( sol2coq_full_types h1 ) :: ( sol2coq_full_types h2 ) :: [")"] 

| "mapping" :: "(" :: h1 :: "=>" :: h2 :: ")" :: "," :: t  => 
 "(" :: "XHMap" :: ( sol2coq_full_types h1 ) :: ( sol2coq_full_types h2 ) ::")" :: "#" :: make_function_returns t
 
| "mapping" :: "(" :: h1 :: "=>" :: h2 :: ")" :: _ :: "," :: t  => 
 "(" :: "XHMap" :: ( sol2coq_full_types h1 ) :: ( sol2coq_full_types h2 ) ::")" :: "#" :: make_function_returns t

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

Definition make_function_interior (contract_name:string) (function_name:string) (sl:list string) := 
let braket := find_braket_interior (-1)  sl in
let crotch := "((("::(get_function_returns (contract_name++"T")%string (find_crotch_interior false sl)) in
let brace  := find_brace_interior (-1)   sl in  
let x := "Definition" :: function_name
               :: braket ++ crotch ++ [":="] ++ brace in   x.
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

| "optional" :: "<" :: typ :: ">" :: name :: ")" :: t => name :: ":" :: "(" :: "XMaybe" :: (sol2coq_full_types typ) :: ")" :: ")" :: nil
| "optional" :: "<" :: typ :: ">" :: name :: "," :: t => name :: ":" :: "(" :: "XMaybe" :: (sol2coq_full_types typ) :: ")" :: ")" :: "(" :: (get_argum t)

| typ :: name :: "," :: t => name :: ":" :: (sol2coq_full_types typ) :: ")"::"(" :: (get_argum t)
| typ :: modif :: name :: "," :: t => name :: ":" :: (sol2coq_full_types typ) :: ")"::"(" :: (get_argum t)
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




















