(* Building spec-file (i.e. solidity-coq translator for spec-files ) *)

Load "functions_services.v".
Load "function_finds.v".
Load "functions_exchange.v".
Load "functions_types.v".
Load "functions_modifiers.v".
Load "functions_constructors.v". 

Load "functions_functions.v".
Load "functions_structs.v".
Load "functions_else.v".

Compute (sol2coq_full_types "uint64").

Inductive type_of_name :=
| NUMBER : type_of_name
| LOCAL  : type_of_name
| VAR    : type_of_name
| FUNf   : type_of_name
| FUNdo  : type_of_name.

Definition who (s:string) := 
if (have_it_symbol "185"%char s) then VAR
else if (have_it_symbol "164"%char s) then FUNf  (* Ф *)
else if (have_it_symbol "155"%char s) then LOCAL (* Л *)
else
match isNum s with
| true => NUMBER
| flase => LOCAL
end.  
Fixpoint work_delete(sl:list string) :=
match sl with
| nil => nil
| "delete" :: name1 :: "." :: name2 :: ";" :: t => 
     match who name1 with
     | LOCAL => "<!" :: name1 :: "^^" :: name2 :: "-->" :: "delete!" :: "!>" 
                 :: ")" :: ">>" :: (work_delete t)
     | VAR => "<!" :: name2 :: "-->" :: "delete!" :: "!>" 
                 :: ")" :: ">>" :: (work_delete t)
     | _ => nil
     end
| "delete" :: name :: "[" :: i :: "]" :: ";" :: t => 
    "(" :: "↑" :: "<!" :: name :: "-->" :: 
    "(" :: "delete!" :: i :: ")" :: "!>" :: ")" :: ">>" ::
     (work_delete t)
| "delete" :: name :: "[" :: i1 :: "." :: i2  :: "]" :: ";" :: t => 
    match who i1 with
    | LOCAL =>
      "(" :: "<-^l" :: i1 :: "^^" :: i2 :: ")" :: ">>=" :: "->l" :: "i" :: "in" :: newline ::
      "(" :: "↑" :: "<!" :: name :: "-->" :: 
      "(" :: "delete!" :: "i" :: ")" :: "!>" :: ")" :: ">>" ::
                                          (work_delete t)
    | VAR  => "(" :: "<-v" :: i2 :: ")" :: ">>=" :: "->l" :: "i" :: "in" :: newline ::
     "(" :: "↑" :: "<!" :: name :: "-->" :: 
     "(" :: "delete!" :: "i" :: ")" :: "!>" :: ")" :: ">>" ::
                                              (work_delete t)
    | _ => nil
    end
| "delete" :: name1 :: "." :: name2 :: "[" :: i1 :: "." :: i2  :: "]" :: ";" :: t => 
  ( match who i1 with
    | LOCAL =>
      "(" :: "<-^l" :: i1 :: "^^" :: i2 :: ")" :: ">>=" :: "->l" :: "i" :: "in" :: [newline] 
    | VAR  => "(" :: "<-v" :: i2 :: ")" :: ">>=" :: "->l" :: "i" :: "in" :: [newline]
    | _ => nil
    end  ) ++
  (
    match who name1 with
    | LOCAL => "(" :: "↑" :: "<!" :: name1 :: "^^" :: name2 :: "-->" :: 
     "(" :: "delete!" :: "i" :: ")" :: "!>" :: ")" :: [">>"]
    | VAR   => "(" :: "↑" :: "<!" :: name2 :: "-->" :: 
     "(" :: "delete!" :: "i" :: ")" :: "!>" :: ")" :: [">>"]
    | _ => nil
    end ) ++ (work_delete t)
| "delete" :: name1 :: "." :: name2 :: "[" :: i :: "]" :: ";" :: t => 
    (
    match who name1 with
    | LOCAL => "(" :: "↑" :: "<!" :: name1 :: "^^" :: name2 :: "-->" :: 
     "(" :: "delete!" :: i :: ")" :: "!>" :: ")" :: [">>"]
    | VAR   => "(" :: "↑" :: "<!" :: name2 :: "-->" :: 
     "(" :: "delete!" :: i :: ")" :: "!>" :: ")" :: [">>"]
    | _ => nil
    end ) ++ (work_delete t)
| h :: t =>  h :: (work_delete t)
end.

Definition work_with_objects(h1:string)(h1':type_of_name)(h2:string)(h2':type_of_name):=
match h1', h2' with
| LOCAL,  NUMBER => "(" :: "<-c" :: h2 :: ")" :: ">>=" :: "->l" :: h1 :: ["in"] 
| LOCAL,  LOCAL  => "(" :: "<-l" :: h2 :: ")" :: ">>=" :: "->l" :: h1 :: ["in"]  
| LOCAL,  VAR    => "(" :: "<-v" :: h2 :: ")" :: ">>=" :: "->l" :: h1 :: ["in"] 
| LOCAL,  FUNf   => "(" :: "<-f" :: h2 :: ")" :: ">>=" :: "->l" :: h1 :: ["in"] 
| LOCAL,  FUNdo  => "do" :: h1 :: "←" :: "↓" :: h2 :: ["??;;"]  
| VAR,  NUMBER => "(" :: "<-c" :: h2 :: ")" :: ">>=" :: "->v" :: h1 :: ["in"] 
| VAR,  LOCAL  => "(" :: "<-l" :: h2 :: ")" :: ">>=" :: "->v" :: h1 :: ["in"] 
| VAR,  VAR    => "(" :: "<-v" :: h2 :: ")" :: ">>=" :: "->v" :: h1 :: ["in"] 
| VAR,  FUNf   => "(" :: "<-f" :: h2 :: ")" :: ">>=" :: "->v" :: h1 :: ["in"] 
| VAR,  FUNdo  => "do" :: h1 :: "←" :: "↓" :: h2 :: ["??;;"] 

| _, _ => nil
end.
Fixpoint work_assignment_and_ect(sl:list string) :=
match sl with
| nil => nil
| h1 :: "." :: h1' :: "=" :: h2 :: "." :: h2' :: "[" :: n :: "]" :: t => 
                    match who h2 with
                    | LOCAL =>  "(" :: "<-^l" :: h2 :: "^^" :: h2' :: "[#" :: n :: "#]" :: ")" :: [">>="] 
                    | VAR   =>  "(" :: "<-" :: h2' :: "[#" :: n :: "#]" :: ")" :: [">>="] 
                    | _ => nil
                    end ++ (
                    match who h1 with 
                    | LOCAL  => "->^l" :: h1 :: "^^" :: h1' :: ["in"]
                    | VAR    => "->v"  :: h1' :: ["in"]
                    | _ => nil
                    end ) ++ (work_assignment_and_ect t)
| h1 :: "." :: h1' :: "=" :: h2 :: "[" :: n :: "]" :: t => 
                    match who h2 with
                    | LOCAL =>  "(" :: "<-^l" :: h2 :: "[#" :: n :: "#]" :: ")" :: [">>="] 
                    | VAR   =>  "(" :: "<-" :: h2 :: "[#" :: n :: "#]" :: ")" :: [">>="] 
                    | _ => nil
                    end ++ (
                    match who h1 with 
                    | LOCAL  => "->^l" :: h1 :: "^^" :: h1' :: ["in"]
                    | VAR    => "->v"  :: h1' :: ["in"]
                    | _ => nil
                    end ) ++ (work_assignment_and_ect t)
| h1 :: "[" :: n :: "]" :: "=" :: h2 :: ";" :: t =>
                    match who h1, who h2 with
                    | LOCAL, NUMBER => 
"(" :: "<-c" :: h2 :: ")" :: ">>=" :: "->l" :: h1 :: "[#" :: n :: "#]" :: ["in"]
                    | LOCAL, LOCAL => 
"(" :: "<-l" :: h2 :: ")" :: ">>=" :: "->l" :: h1 :: "[#" :: n :: "#]" :: ["in"]
                    | LOCAL, VAR => 
"(" :: "<-v" :: h2 :: ")" :: ">>=" :: "->l" :: h1 :: "[#" :: n :: "#]" :: ["in"]
                    | VAR, NUMBER => 
"(" :: "<-c" :: h2 :: ")" :: ">>=" :: "->" :: h1 :: "[#" :: n :: "#]" :: ["in"]
                    | VAR, LOCAL => 
"(" :: "<-l" :: h2 :: ")" :: ">>=" :: "->" :: h1 :: "[#" :: n :: "#]" :: ["in"]
                    | VAR, VAR => 
"(" :: "<-v" :: h2 :: ")" :: ">>=" :: "->" :: h1 :: "[#" :: n :: "#]" :: ["in"]
                    | _, _ => nil 
                    end 
| h1 :: "=" :: h2 :: "[" :: n :: "]" :: t => 
                    match who h2 with
                    | LOCAL =>  "(" :: "<-l" :: h2 :: "[#" :: n :: "#]" :: ")" :: [">>="] 
                    | VAR   =>  "(" :: "<-" :: h2 :: "[#" :: n :: "#]" :: ")" :: [">>="] 
                    | _ => nil
                    end ++ (
                    match who h1 with 
                    | LOCAL  => "->^l" :: h1 :: ["in"]
                    | VAR    => "->v"  :: h1 :: ["in"]
                    | _ => nil
                    end ) ++ (work_assignment_and_ect t)
| h1 :: "." :: h1' :: "=" :: h2 :: ";" :: t => 
                    match who h2 with
                    | NUMBER => "(" :: "<-c" :: h2 :: ")" :: [">>="]
                    | LOCAL =>  "(" :: "<-l" :: h2 :: ")" :: [">>="]
                    | VAR   =>  "(" :: "<-v" :: h2 :: ")" :: [">>="]
                    | FUNf  =>  "(" :: "<-f" :: h2 :: ")" :: [">>="]
                    | _ => nil
                    end ++ (
                    match who h1 with 
                    | LOCAL  => "->^l" :: h1 :: "^^" :: h1' :: ["in"]
                    | VAR    => "->v"  :: h1' :: ["in"]
                    | _ => nil
                    end ) ++ (work_assignment_and_ect t)
| h1 :: "=" :: h2 :: "." :: h2' :: ";" :: t => 
                    match who h2 with
                    | NUMBER => nil
                    | LOCAL =>  "(" :: "<-^l" :: h2 :: "^^" :: h2' :: ")" :: [">>="]
                    | VAR   =>  "(" :: "<-v" :: h2' :: ")" :: [">>="]
                    | FUNf  =>  "(" :: "<-f" :: h2 :: "." :: h2' :: ")" :: [">>="]
                    | _ => nil
                    end ++ (
                    match who h1 with 
                    | LOCAL  => "->l" :: h1 :: ["in"]
                    | VAR    => "->v" :: h1 :: ["in"]
                    | _ => nil
                    end ) ++ (work_assignment_and_ect t)
| h1 :: "." :: h1' :: "=" :: h2 :: "." :: h2' :: ";" :: t => 
                    match who h2 with
                    | NUMBER => nil
                    | LOCAL =>  "(" :: "<-^l" :: h2 :: "^^" :: h2' :: ")" :: [">>="]
                    | VAR   =>  "(" :: "<-v" :: h2' :: ")" :: [">>="]
                    | FUNf  =>  "(" :: "<-f" :: h2 :: "." :: h2' :: ")" :: [">>="]
                    | _ => nil
                    end ++ (
                    match who h1 with 
                    | LOCAL  => "->^l" :: h1 :: "^^" :: h1' :: ["in"]
                    | VAR    => "->v"  :: h1' :: ["in"]
                    | _ => nil 
                    end ) ++ (work_assignment_and_ect t)
| h1 :: "[" :: n :: "]" :: "." :: h1' :: "=" :: h2 :: ";" :: t =>
                   ( match who h2 with 
                     | NUMBER => "(" :: "<-c" :: h2 :: ")" :: [">>="]
                     | LOCAL  => "(" :: "<-l" :: h2 :: ")" :: [">>="]
                     | VAR =>    "(" :: "<-v" :: h2 :: ")" :: [">>="]
                     | FUNf => "(" :: "<-f" :: h2 :: ")" :: [">>="]
                     | _ => nil
                     end ) ++
                   ( match who h1 with
                    | LOCAL => "->^l" :: h1 :: "[#" :: n :: "#]" :: "^" :: h1' :: ["in"]
                    | VAR => "->" :: h1 :: "[#" :: n :: "#]" :: "^" :: h1' :: ["in"]
                    | _ => nil
                    end ) ++ (work_assignment_and_ect t)
| h1 :: "=" :: h2 :: ";" :: t => (work_with_objects h1 (who h1) h2 (who h2)) ++
                                 (work_assignment_and_ect t)
| h :: t => h :: (work_assignment_and_ect t) 
end.
(* work assingment and other operations: +=, -=, *= and /= *)
Fixpoint work_not_pure_assignment_and_ect(sl:list string) :=
match sl with
| nil => nil
| h1 :: "." :: h1' :: s :: h2 :: "[" :: n :: "]" :: t => if(test_already_exists s assingment) 
                  then 
                  ( match who h2, who h1 with
                    | LOCAL,LOCAL =>  "(" :: "<-^ll" :: h2 :: "[#" :: n :: "#]" :: s :: h1 ::")" :: [">>="] 
                    | VAR,LOCAL   =>  "(" :: "<-vl"  :: h2 :: "[#" :: n :: "#]" :: s :: h1 ::")" :: [">>="] 
                    | LOCAL,VAR =>  "(" :: "<-^lv" :: h2 :: "[#" :: n :: "#]" :: s :: h1 ::")" :: [">>="] 
                    | VAR,VAR   =>  "(" :: "<-vv"  :: h2 :: "[#" :: n :: "#]" :: s :: h1 ::")" :: [">>="] 
                    | _, _ => nil
                    end ) ++ (
                    match who h1 with 
                    | LOCAL  => "->^l" :: h1 :: "^^" :: h1' :: ["in"]
                    | VAR    => "->v"  :: h1' :: ["in"]
                    | _ => nil
                    end ) ++ (work_not_pure_assignment_and_ect t)
                   else h1 :: "." :: h1' :: s :: h2 :: "[" :: n :: "]" :: (work_not_pure_assignment_and_ect t)
| h1 :: "." :: h1' :: s :: h2 :: "." :: h2' :: "[" :: n :: "]" :: t => 
                  if(test_already_exists s assingment) 
                  then 
                    match who h2, who h1 with
                    | LOCAL,LOCAL =>  
"(" :: "<-^ll" :: h2 :: "^^" :: h2' :: "[#" :: n :: "#]" :: s :: h1 :: "^^" :: h1' :: ")" :: [">>="] 
                    | VAR,LOCAL   =>  
"(" :: "<-vl"  :: h2' :: "[#" :: n :: "#]" :: s :: h1 :: "^^" :: h1' :: ")" :: [">>="] 
                    | LOCAL,VAR =>  
"(" :: "<-^lv" :: h2 :: "^^" :: h2' :: "[#" :: n :: "#]" :: s :: h1 :: "^^" :: h1' :: ")" :: [">>="] 
                    | VAR,VAR   =>  
"(" :: "<-vv" :: h2' :: "[#" :: n :: "#]" :: s :: h1 :: "^^" :: h1' :: ")" :: [">>="] 
                    | _,_ => nil
                    end ++ (
                    match who h1 with 
                    | LOCAL  => "->^l" :: h1 :: "^^" :: h1' :: ["in"]
                    | VAR    => "->v"  :: h1' :: ["in"]
                    | _ => nil
                    end ) ++ (work_not_pure_assignment_and_ect t)
                  else h1 :: "." :: h1' :: s :: h2 :: "." :: h2' :: "[" :: n :: "]" :: (work_not_pure_assignment_and_ect t)
| h1 :: "." :: h1' :: s :: h2 :: ";" :: t => 
                  if(test_already_exists s assingment) 
                  then 
                    match who h2, who h1 with
                    | NUMBER,LOCAL => "(" :: "<-cl" :: h2 :: s :: h1 :: "^^" :: h1' :: ")" :: [">>="]
                    | LOCAL,LOCAL =>  "(" :: "<-ll" :: h2 :: s :: h1 :: "^^" :: h1' :: ")" :: [">>="]
                    | VAR,LOCAL   =>  "(" :: "<-vl" :: h2 :: s :: h1 :: "^^" :: h1' :: ")" :: [">>="]
                    | FUNf,LOCAL  =>  "(" :: "<-fl" :: h2 :: s :: h1 :: "^^" :: h1' :: ")" :: [">>="]

                    | NUMBER,VAR =>  "(" :: "<-cv" :: h2 :: s :: h1' :: ")" :: [">>="]
                    | LOCAL,VAR  =>  "(" :: "<-lv" :: h2 :: s :: h1' :: ")" :: [">>="]
                    | VAR,VAR    =>  "(" :: "<-vv" :: h2 :: s :: h1' :: ")" :: [">>="]
                    | FUNf,VAR   =>  "(" :: "<-fv" :: h2 :: s :: h1' :: ")" :: [">>="]
                    | _,_ => nil
                    end ++ (
                    match who h1 with 
                    | LOCAL  => "->^l" :: h1 :: "^^" :: h1' :: ["in"]
                    | VAR    => "->v"  :: h1' :: ["in"]
                    | _ => nil
                    end ) ++ (work_not_pure_assignment_and_ect t)
                  else h1 :: "." :: h1' :: s :: h2 :: ";" :: (work_not_pure_assignment_and_ect t)
| h1 :: s :: h2 :: "." :: h2' :: ";" :: t => 
                  if(test_already_exists s assingment) 
                  then 
                    match who h2, who h1 with
                    | NUMBER,_ => nil
                    | _,NUMBER => nil
                    | LOCAL,LOCAL =>  "(" :: "<-^ll" :: h2 :: "^^" :: h2' :: s :: h1 :: ")" :: [">>="]
                    | VAR,LOCAL   =>  "(" :: "<-vl" :: h2' :: s :: h1 ::")" :: [">>="]
                    | FUNf,LOCAL  =>  "(" :: "<-fl" :: h2 :: "." :: h2' :: s :: h1 :: ")" :: [">>="]
                    | LOCAL,VAR =>  "(" :: "<-^lv" :: h2 :: "^^" :: h2' :: s :: h1 :: ")" :: [">>="]
                    | VAR,VAR   =>  "(" :: "<-vv" :: h2' :: s :: h1 :: ")" :: [">>="]
                    | FUNf,VAR  =>  "(" :: "<-fv" :: h2 :: "." :: h2' :: s :: h1 :: ")" :: [">>="]
                    | _,_ => nil
                    end ++ (
                    match who h1 with 
                    | LOCAL  => "->l" :: h1 :: ["in"]
                    | VAR    => "->v" :: h1 :: ["in"]
                    | _ => nil
                    end ) ++ (work_not_pure_assignment_and_ect t)
                  else h1 :: s :: h2 :: "." :: h2' :: ";" :: (work_not_pure_assignment_and_ect t)
| h1 :: "." :: h1' :: s :: h2 :: "." :: h2' :: ";" :: t => 
                  if(test_already_exists s assingment) 
                  then 
                    match who h2, who h1 with
                    | NUMBER,_ => nil
                    | LOCAL,LOCAL =>  
     "(" :: "<-^ll" :: h2 :: "^^" :: h2' :: s :: h1 :: "^^" :: h1' :: ")" :: [">>="]
                    | VAR,LOCAL   =>  
     "(" :: "<-vl" :: h2' :: s :: h1 :: "^^" :: h1' :: ")" :: [">>="]
                    | FUNf,LOCAL  =>  
     "(" :: "<-fl" :: h2 :: "." :: h2' :: s :: h1 :: "^^" :: h1' :: ")" :: [">>="]
                    | LOCAL,VAR =>  
     "(" :: "<-^lv" :: h2 :: "^^" :: h2' :: s :: h1 :: "^^" :: h1' :: ")" :: [">>="]
                    | VAR,VAR   =>  
     "(" :: "<-vv" :: h2' :: s :: h1 :: "^^" :: h1' :: ")" :: [">>="]
                    | FUNf,VAR  =>  
     "(" :: "<-fv" :: h2 :: "." :: h2' :: s :: h1 :: "^^" :: h1' :: ")" :: [">>="]
                    | _,_ => nil
                    end ++ (
                    match who h1 with 
                    | LOCAL  => "->^l" :: h1 :: "^^" :: h1' :: ["in"]
                    | VAR    => "->v"  :: h1' :: ["in"]
                    | _ => nil
                    end ) ++ (work_not_pure_assignment_and_ect t)
                  else h1 :: "." :: h1' :: s :: h2 :: "." :: h2' :: ";" :: (work_not_pure_assignment_and_ect t)
| h1 :: s :: h2 :: ";" :: t =>   if( test_already_exists s assingment ) 
     then
     ( match who h1, who h2 with
      | LOCAL,  NUMBER => "(" :: "<-cl" :: h2 :: s :: h1 :: ")" :: ">>=" :: "->l" :: h1 :: ["in"] 
      | LOCAL,  LOCAL  => "(" :: "<-ll" :: h2 :: s :: h1 :: ")" :: ">>=" :: "->l" :: h1 :: ["in"]  
      | LOCAL,  VAR    => "(" :: "<-vl" :: h2 :: s :: h1 ::")" :: ">>=" :: "->l" :: h1 :: ["in"] 
      | LOCAL,  FUNf   => "(" :: "<-fl" :: h2 :: s :: h1 ::")" :: ">>=" :: "->l" :: h1 :: ["in"] 
      | VAR,  NUMBER => "(" :: "<-cv" :: h2 :: s :: h1 :: ")" :: ">>=" :: "->v" :: h1 :: ["in"] 
      | VAR,  LOCAL  => "(" :: "<-lv" :: h2 :: s :: h1 :: ")" :: ">>=" :: "->v" :: h1 :: ["in"] 
      | VAR,  VAR    => "(" :: "<-vv" :: h2 :: s :: h1 :: ")" :: ">>=" :: "->v" :: h1 :: ["in"] 
      | VAR,  FUNf   => "(" :: "<-fv" :: h2 :: s :: h1 :: ")" :: ">>=" :: "->v" :: h1 :: ["in"] 

      | _, _ => nil
      end ) ++ (work_not_pure_assignment_and_ect t)
     else h1 :: s :: h2 :: ";" :: (work_not_pure_assignment_and_ect t)
| h :: t => h :: (work_not_pure_assignment_and_ect t) 
end.

Compute (let q := "Definition OwnerBase_Ф_withdrawOwnerReward ( Л_amount : XInteger64 )  :=  { 
         require ( Л_amount <= OwnerBase_ι_m_owner . OwnerBase_ι_Owner_ι_reward , xInt105 ) ; 
         OwnerBase_ι_m_owner . OwnerBase_ι_Owner_ι_reward -= Л_amount ; 
         OwnerBase_ι_m_owner . OwnerBase_ι_Owner_ι_addr . transfer ( Л_amount , true , xInt3 ) ; 
         }
" in let t := split_string' " " q in concat_with " " (work_not_pure_assignment_and_ect t)).

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

(* for a + - / * *)
Load "functions_operations.v".
 Check make_contracts_v. 

Inductive way :=
| NOTHING : way
| REQUIRE : way
| IFF     : way
| RETURN  : way
| WHILE   : way.


Inductive Spec :=
| NOTH   : Spec
| COMMON : Spec
| LATTICE: Spec. 

Fixpoint to_spec (f:Spec)(sl:list string) :=
match f, sl with
| _, nil => nil
| NOTH, "Definition" :: name :: t => "Parameter" :: name :: ":" :: to_spec COMMON t
| NOTH, "
Definition" :: name :: t => "Parameter" :: name :: ":" :: to_spec COMMON t

| COMMON, ":" :: name :: type2 :: ":=" :: t => "LedgerT" :: type2 :: "." :: to_spec NOTH t

| COMMON, ":" :: name :: "(" :: "XHMap" :: n1 :: n2 :: ")" :: ":=" :: t =>
                       "LedgerT" :: "(" :: "XHMap" :: n1 :: n2 :: ")" :: "." :: to_spec NOTH t

| COMMON, ")" :: t => "->" ::  to_spec COMMON t

| COMMON , "(" :: name :: ":" :: "(" :: "XMaybe" :: typ :: ")" :: t =>
                               "(" :: "XMaybe" :: typ :: ")" :: to_spec COMMON t

| COMMON, "(" :: name :: ":" :: typ :: t => typ :: to_spec COMMON t

| COMMON, ":" :: n1 :: n2 :: "#" :: t => "LedgerT" :: "(" :: n2 :: "#" :: to_spec LATTICE t 

| LATTICE , "(" :: "XHMap" :: n1 :: n2 :: ")" :: ":=" :: t => 
            "(" :: "XHMap" :: n1 :: n2 :: ")" :: ")%sol" :: "." :: to_spec NOTH t

| LATTICE , "(" :: "XHMap" :: n1 :: n2 :: ")" :: "#" :: t => 
            "(" :: "XHMap" :: n1 :: n2 :: ")" :: "#" :: to_spec LATTICE t

| LATTICE, n :: ":=" :: t => n :: ")%sol" :: "." :: to_spec NOTH t

| LATTICE, n :: "#" :: t => n :: "#" :: to_spec LATTICE t


| _, h :: t => to_spec f t


end.

Fixpoint clear_double_functions (l:list string) (sl:list(list string)) :=
match sl with
| nil => nil
| h :: t => let q := headS "" h in
            let w := headS "" ( tail h ) in
            if ( test_already_exists w l ) 
            then clear_double_functions l t
            else h :: clear_double_functions ( w :: l ) t
end.

Definition head := "
Require Import (* depoolContract. *)DePoolClass. 
Require Import depoolContract.SolidityNotations.
Require Import depoolContract.ProofEnvironment.

Module DePoolSpec (xt: XTypesSig) (sm: StateMonadSig).
Module LedgerClass := LedgerClass xt sm .
Import LedgerClass.
Import SolidityNotations.

Module Type DePoolSpecSig.
Import xt. Import sm.


".

Definition foot := "


End DePoolSpecSig.

End DePoolSpec.
".

Fixpoint get_library_names(sl:list string) :=
match sl with
| nil => nil
| "library" :: name :: t => name :: get_library_names t
| h :: t => get_library_names t
end.
Fixpoint delete_library_names'(q sl:list string) :=
match sl with
| nil => nil
| h :: "." :: h1 :: t => if ( test_already_exists h q ) 
                   then ( h++"_ι_"++h1 )%string :: delete_library_names' q t
                   else h :: delete_library_names' q t
| h :: t => h :: delete_library_names' q t
end. 
(* This manipulations are only for spec-file!!! *)
Definition delete_library_names (sl:list string) :=
let q := get_library_names sl in
let w := delete_library_names' q sl in w.

Definition delete_symbol_P'(s:string) := split_string' "П" s.

Fixpoint delete_symbol_P(sl:list string) :=
match sl with
| nil => nil
| h :: t => ( delete_symbol_P' h ) ++ delete_symbol_P t
end.

Fixpoint qwerty(sl:list string) :=
match sl with
| nil => nil
| h :: t => ( split_string' " " h ) ++ qwerty t
end.

Definition shaper(s: string) := let s:= clearComment1 false ( clearComment false (setSpace s) ) in 
let sl := split_string' newline s in 
let sl := map (split_string' " ") sl in 
let sl := map clear_string_easy sl  in
let sl := clear_list_easy sl in
let sl := deleteComment sl in 
let sl := List.concat sl in     

let sl := delete_library_names sl in

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
let struct_list := structs_list "" sl in                   (*   tuple_outing struct_list. *)
let consts_list := const_list "" sl in             (*    tuple_outing funcs_list. *)
(* definition right order functions fo r eval *)
let right_order := function_order sl in               (* concat_with newline (map(concat_with " " ) right_order). *)

let all := make_contracts sl in                     (*    *)                                    

let sl :=  List.concat all in                       
                                                         (* + *)                        
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

let bb' := map qwerty bb in

let jj' := map (to_spec NOTH) bb' in
  
let kk := clear_double_functions []             jj'               in


( head ++ concat_with newline  ( map ( concat_with " " )  kk   ) ++ foot )%string .


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

Extraction "./specFileGenerator" main.



