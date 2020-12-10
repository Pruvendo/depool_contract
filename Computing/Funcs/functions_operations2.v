Fixpoint work_operations (sl:list string):=
match sl with
| nil => nil

| "Errors" :: "^^" :: t => work_operations t

| "))" :: "=" :: t => "))" :: ":=" :: work_operations t

| "==" :: t => "?==" :: work_operations t
| ">=" :: t => "?>=" :: work_operations t
| "<=" :: t => "?<=" :: work_operations t
| ">"  :: t => "?>"  :: work_operations t
| "<"  :: t => "?<"  :: work_operations t
| "!=" :: t => "?!=" :: work_operations t

| "+" :: t => "!+" :: work_operations t
| "-" :: t => "!-" :: work_operations t
| "*" :: t => "!*" :: work_operations t
| "/" :: t => "!/" :: work_operations t
| "%" :: t => "!%" :: work_operations t


| a :: "^^" :: p :: "[" :: n :: "]" :: "=" :: t =>
  "d3!" :: a :: "^^" :: p :: "[" :: n :: "]" :: ":=" :: work_operations t
| a :: "^^" :: p :: "=" :: t =>
  "d2!" :: a :: "^^" :: p :: ":=" :: work_operations t
| a :: "[" :: n :: "]" :: "=" :: t =>
  "d4!" :: a :: "[" :: n :: "]" :: ":=" :: work_operations t
| a :: "=" :: t => match who a with
                   | LOCAL  => "d0!" :: a :: ":=" :: work_operations t
                   | VAR    => "d1!" :: a :: ":=" :: work_operations t
                   | _ => work_operations t
                   end 

| a :: "^^" :: p :: "[" :: n :: "]" :: "+=" :: t =>
  "d3!" :: a :: "^^" :: p :: "[" :: n :: "]" :: "+=" :: work_operations t
| a :: "^^" :: p :: "+=" :: t =>
  "d2!" :: a :: "^^" :: p :: "+=" :: work_operations t
| a :: "[" :: n :: "]" :: "+=" :: t =>
  "d4!" :: a :: "[" :: n :: "]" :: "+=" :: work_operations t
| a :: "+=" :: t => match who a with
                   | LOCAL  => "d0!" :: a :: "+=" :: work_operations t
                   | VAR    => "d1!" :: a :: "+=" :: work_operations t
                   | _ => work_operations t
                   end 

| a :: "^^" :: p :: "[" :: n :: "]" :: "-=" :: t =>
  "d3!" :: a :: "^^" :: p :: "[" :: n :: "]" :: "-=" :: work_operations t
| a :: "^^" :: p :: "-=" :: t =>
  "d2!" :: a :: "^^" :: p :: "-=" :: work_operations t
| a :: "[" :: n :: "]" :: "-=" :: t =>
  "d4!" :: a :: "[" :: n :: "]" :: "-=" :: work_operations t
| a :: "-=" :: t => match who a with
                   | LOCAL  => "d0!" :: a :: "-=" :: work_operations t
                   | VAR    => "d1!" :: a :: "-=" :: work_operations t
                   | _ => work_operations t
                   end 

| a :: "^^" :: p :: "[" :: n :: "]" :: "*=" :: t =>
  "d3!" :: a :: "^^" :: p :: "[" :: n :: "]" :: "*=" :: work_operations t
| a :: "^^" :: p :: "*=" :: t =>
  "d2!" :: a :: "^^" :: p :: "*=" :: work_operations t
| a :: "[" :: n :: "]" :: "*=" :: t =>
  "d4!" :: a :: "[" :: n :: "]" :: "*=" :: work_operations t
| a :: "*=" :: t => match who a with
                   | LOCAL  => "d0!" :: a :: "*=" :: work_operations t
                   | VAR    => "d1!" :: a :: "*=" :: work_operations t
                   | _ => work_operations t
                   end 
 
| a :: "^^" :: p :: "[" :: n :: "]" :: "/=" :: t =>
  "d3!" :: a :: "^^" :: p :: "[" :: n :: "]" :: "/=" :: work_operations t
| a :: "^^" :: p :: "/=" :: t =>
  "d2!" :: a :: "^^" :: p :: "/=" :: work_operations t
| a :: "[" :: n :: "]" :: "/=" :: t =>
  "d4!" :: a :: "[" :: n :: "]" :: "/=" :: work_operations t
| a :: "/=" :: t => match who a with
                   | LOCAL  => "d0!" :: a :: "/=" :: work_operations t
                   | VAR    => "d1!" :: a :: "/=" :: work_operations t
                   | _ => work_operations t
                   end 

| a :: "^^" :: p :: "[" :: n :: "]" :: "%=" :: t =>
  "d3!" :: a :: "^^" :: p :: "[" :: n :: "]" :: "%=" :: work_operations t
| a :: "^^" :: p :: "%=" :: t =>
  "d2!" :: a :: "^^" :: p :: "%=" :: work_operations t
| a :: "[" :: n :: "]" :: "%=" :: t =>
  "d4!" :: a :: "[" :: n :: "]" :: "%=" :: work_operations t
| a :: "%=" :: t => match who a with
                   | LOCAL  => "d0!" :: a :: "%=" :: work_operations t
                   | VAR    => "d1!" :: a :: "%=" :: work_operations t
                   | _ => work_operations t
                   end 

| ")" :: ">>"  :: t => ")"  :: ">>" :: work_operations t
| "))" :: ">>" :: t => "))" :: ">>" :: work_operations t

(* | ">>" :: ">>" :: "
" :: ">>" :: t => ">>" :: work_operations t
| ">>" :: ">>" :: t => ")"  :: ">>" :: work_operations t *)

| ">>" :: t => ";" :: work_operations t  

| h :: ":" :: t => h :: ":" :: work_operations t

| h :: t => if ( if_who (who h) LOCAL ) then "$" :: h :: work_operations t 
                                        else        h :: work_operations t
end.

Fixpoint get_first_symbols_to_ ( s : string ) :=
match s with
| "" => ""
| String "_"%char t => ""
| String h t => String h ( get_first_symbols_to_ t )
end.

Fixpoint add_lift_to_vars( tl : list ( string * string ) ) (sl:list string) :=
match sl with
| nil => nil
| ":" :: h :: t => ":" :: h :: add_lift_to_vars tl t
| "LedgerT" :: h :: t => "LedgerT" :: h :: add_lift_to_vars tl t
| h1 :: t => (* if ( test_already_exists h2 ( ":=" :: assingment ) )
                   then h1 :: h2 :: add_lift_to_vars tl t
                   else *) if ( have_it_symbol "185"%char h1 )
                        then let q := get_first_symbols_to_ h1 in
                             let w := find_coq_name q tl in
                                 w :: h1 :: add_lift_to_vars tl t
                        else h1 :: add_lift_to_vars tl t
(* | h2 :: t => h2 :: add_lift_to_vars tl t *)
end.










