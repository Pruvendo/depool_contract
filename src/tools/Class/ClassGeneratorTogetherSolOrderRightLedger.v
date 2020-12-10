(*  Building Class-file: static and partially dinamic  *)

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

Definition separators := [".";",";";";"(";")";"{";"}";"[";"]";">>";">>=";"!=";
"=";"-=";"+=";">";"<";"<=";">=";"==";"!";"=>";"||";"&&";"?";"delete"; "++"; "--";
"/=";"*=";"/";"+";"-";"*";"if";"while";"then";"require";"return";"else";"do";":=";":";""].

Definition unacceptable_symbols := [".";",";";";"(";")";"{";"}";"[";"]";"=";">";"<";"!";"?";"
"; String "009"%char "" ;
"/";"+";"-";"*";":";" ";""].

Definition the_types := ["uint";"uint8";"uint16";"uint32";"uint64";"uint128";
"uint256";"int";"int8";"int16";"int32";"int64";"int128";
"int256";"bytes";"bool";"mapping";"address";"TvmCell"].

Definition arrow_types := [ ("HM","Type->Type->Type") ; ("L","Type->Type") ; ("M","Type->Type") ].

Definition newline := "
" : string.
Definition tab := String "009"%char "".
Definition split_string' (s:string)(sl:string):=
split_string sl s.
(* Splitting via s1 and adding s1: [ (spl1++s++s1)%string ; (spl2++s++s1)%string ; ... ] *)
Fixpoint split_string'''(s s1 : string) (sl:list string) :=
match sl with
| nil => nil
| h :: t => (h++s++s1)%string :: split_string''' s s1 t
end.
Check split_string'.
Definition split_string''(s s1 s2 : string) :=
let q := split_string' s1 s2 in
split_string''' s s1 q.


(* Clearing a comment //  *)
Fixpoint clearComment1(f:bool)(s:string):=
match f, s with
| _ , "" => ""
| false, String "/"%char (String "/"%char t) => clearComment1 true t
| true,  String "010"%char t => clearComment1 false t
| true,  String h t => clearComment1 true t
| false, String h t => String h (clearComment1 false t)
end.
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
(* First two symbols from string *)
Definition first2 (s:string):=
match s with
| "" => s
| String a "" => s
| String a (String b t) => String a (String b "")
end.
Definition delete_first_symbol(s:string) :=
match s with
| "" => ""
| String a "" => ""
| String a b => b
end.
Fixpoint delete_last_symbol(s:string) :=
match s with
| "" => ""
| String a (String b "") => String a ""
| String a b => String a ( delete_last_symbol b )
end.
Compute ( delete_last_symbol "1234" ).
Definition delete_first_and_last_symbols(s:string) :=
match s with
| "" => ""
| String a b => ( delete_last_symbol b )
end.
Check chars2str.
Fixpoint have_it_symbol(c:ascii)(s:string) :=
match s with
| "" => false
| String h t => if (Nat.eqb (nat_of_ascii h) (nat_of_ascii c)) then true
                            else have_it_symbol c t
end.
Fixpoint exchange(s:string) :=
match s with
| "" => ""
| String a b => let aa := String a "" in if ( aa =? "_" ) then String "x"%char b
                                                          else String a ( exchange b )
end.
Compute ( exchange  "1x234x56_987x65" ).   
(* Clearing comments: // *)
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
Fixpoint array_2_mapping(sl:list string) :=
match sl with
| nil => nil
| typ :: "[" :: "]" :: name :: t => 
          "mapping" :: "(" :: "int" :: "=>" :: typ :: ")" :: name :: array_2_mapping t 
| h :: t => h :: array_2_mapping t
end.
Fixpoint delete_angle_bracket(sl:list string) :=
match sl with
| nil => nil
| "<" :: h :: ">" :: t => h :: delete_angle_bracket t
| h :: t => h :: delete_angle_bracket t
end.
Fixpoint find_and_forward_symbol'(s:string)(sl:list string) :=
match sl with
| nil => nil
| h :: t => if ( h =? s ) then t
                          else h :: find_and_forward_symbol' s t
end.
Definition find_and_forward_symbol(s:string)(sl:list string) :=
let q := List.length sl in
let w := find_and_forward_symbol' s sl in
let e := List.length w in
if ( Nat.eqb q e ) then sl 
                   else s :: w.
(* Discard list elements to specified one *)
Fixpoint discard_list_elements(s:string)(dl:list string) :=
match dl with
| nil => nil
| h :: t => if ( s =? h ) then h :: t
                          else discard_list_elements s t
end.
(* Pulling list elements to specified one *)
Fixpoint pulling_list_elements(s:string)(dl:list string) :=
match dl with
| nil => nil
| h :: t => if ( s =? h ) then nil
                          else h :: pulling_list_elements s t
end.
(* Pulling list elements beetween specified ones *)
Fixpoint pulling_list_beetween(f:bool)(s e :string)(dl:list string) :=
match f, dl with
| _, nil => nil
| false, h :: t => if ( h =? s ) then pulling_list_beetween true s e t
                                 else pulling_list_beetween f s e t
| true, h :: t => if ( h =? e ) then nil
                                else h :: pulling_list_beetween f s e t
end.

Compute (find_and_forward_symbol "HM" [ "11" ;"22" ;"11" ;"44" ;"55" ;"66" ;"HM" ] ).
Compute (find_and_forward_symbol "L" [ "11" ;"22" ;"11" ;"L" ;"55" ;"66" ;"HM" ] ).
(* s1 includes before every element of s2 *)
Fixpoint PlusPlus { X } ( s1 s2 : list X ) :=
match s2 with
| nil => nil
| h :: t => s1 ++ h :: PlusPlus s1 t
end.

Compute (PlusPlus ["1";"3";"!"] ["2";"4";"5";"6"]).

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
| String "="%char ( String ">"%char t ) => String "="%char ( String ">"%char (setSpace t) )

| String ">"%char t => String " "%char (String ">"%char (String " "%char (setSpace t)))
| String "<"%char t => String " "%char (String "<"%char (String " "%char (setSpace t)))
| String "."%char t => String " "%char (String "."%char (String " "%char (setSpace t)))

| String h t => String h (setSpace t)
end.

(*************************************************************************************************)
(*  Interior struct analisis  *)
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
| "int"    => "I"
| "int8"   => "I8"
| "int16"  => "I16"
| "int32"  => "I32"
| "int64"  => "I64"
| "int128" => "I128"
| "int256" => "I256"
| "bytes"   => "I8"
| "bool"    => "B"
| "mapping" => "HM"
| "address" => "A"
| "TvmCell" => "C"
| "string" =>  "S"
| "list"  =>  "L"
| "optional" => "M"
| _ => t                    (* ("ι_" ++ t)%string *) (* for non-standard type *)
end.
Definition del_lead_2_symbolsι_(s:string):=
match s with
| "" => ""
| String a (String b (String c t)) => t
| _ => s
end.
(* Structs list for types *)
Fixpoint get_struct_list(name:string)(sl:list string) :=
match sl with
| nil => nil
| "contract" :: nam :: t => ( nam , nam ) :: get_struct_list nam t
| "library" :: nam :: t => ( nam , nam ) :: get_struct_list nam t
| "struct" :: nam :: t   => ( nam , ( name++"_ι_" ++ nam )%string ) :: get_struct_list name t
| "enum" :: nam :: t     => ( nam , ( name++"_ι_" ++ nam )%string ) :: get_struct_list name t
| h :: t => get_struct_list name t
end.
Fixpoint get_non_standard_type (tl:list(string*string)) (s:string) :=
match tl with
| nil => ""
| h :: t => if ((fst h) =? s ) then snd h
                               else get_non_standard_type t s
end.  
Definition cot_mini_types2coq_types (tl:list(string*string))(t:string) :=
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
| "A" =>    "XAddress"
| "S" =>    "XString"
| "L" =>    "XList"
| "M" =>    "XMaybe"
| typ => get_non_standard_type tl (del_lead_2_symbolsι_ typ)
end. 
Definition cot_mini_types2coq_types_1 (t:string) :=
match t with
| "" => ""
| "XInteger" =>     "I"
| "XInteger8" =>    "I8"
| "XInteger16" =>   "I16"
| "XInteger32" =>   "I32"
| "XInteger64" =>   "I64"
| "XInteger128" =>  "I128"
| "XInteger256" =>  "I256"
| "TvmCell" =>      "C"
| "XBool" =>        "B"
| "XArray" =>       "Arr"
| "XHMap" =>        "HM"
| "XAddress" =>     "A"
| "XString" =>      "S"
| "XList"   =>      "L"
| "XMaybe"  =>      "M"
| _ => ""
end. 
Definition sol2coq_full_types(tl:list(string*string))(t:string):=cot_mini_types2coq_types tl (sol_types2coq_mini_types t).
(* Easy construction test *)
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
| "mapping" :: "(" :: type1 :: "=>" :: type2 :: "." :: type3 :: ")" :: name :: nil =>
(tab++prefix'++"_ι_"++name)%string :: ":" :: "HM" :: (sol_types2coq_mini_types type1) ::
                                          (sol_types2coq_mini_types type3) :: ";" :: newline :: nil
| "optional" :: "<" :: typ :: ">" :: name :: t =>
      (tab++prefix'++"_ι_"++name)%string :: ":" :: "M" :: 
                                          (sol_types2coq_mini_types typ) :: ";" :: newline :: nil
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
Fixpoint get_type_list'(tl:list(string*string)) (sl:list string) :=
match sl with
| nil => nil
| h :: t => match (cot_mini_types2coq_types tl h) with
            | "" => get_type_list' tl t
            | _ => h :: get_type_list' tl t
            end 
end.
Fixpoint test_already_exists(s:string)(sl:list string) :=
match sl with
| nil => false
| h :: t => if (s =? h) then true
                        else test_already_exists s t
end.
(*compare two string lists*)
Fixpoint compare_two_string_lists(s l : list string) :=
match s , l with
| nil , nil => true
| nil , _ => false
| _ , nil => false
| h::t, m::n => if ( h =? m ) then compare_two_string_lists t n
                              else false
end.
(* For a list of types *)
Fixpoint list_of_uniq_types( acc s : list string ) := 
match s with
| nil => acc
| h :: t => if (test_already_exists h acc) 
            then list_of_uniq_types acc t
            else list_of_uniq_types (acc++[h]) t
end.
Definition get_type_list (sl:list string)(tl:list(string*string)) :=
let sl := map (split_string' " ") sl in 
let sl := map (get_type_list' tl) sl in 
let sl := List.concat sl in
list_of_uniq_types [] sl.
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
(* -------------------------- Making the local vars struct ----------------------------- *)
Fixpoint get_args (fn:string) (sl:list string) :=
match sl with
| nil => nil
| type :: name :: nil => ( type , ( fn++"_Л_"++name )%string ) :: nil
| type :: m :: name :: nil => ( type , ( fn++"_Л_"++name )%string ) :: nil
| type :: name :: "," :: t => ( type , ( fn++"_Л_"++name )%string ) :: get_args fn t
| type :: m :: name :: "," :: t => ( type , ( fn++"_Л_"++name )%string ) :: get_args fn t
| h :: t => get_args fn t
end.

Fixpoint test_of_unacceptable_symbols (s:string) :=
match s with
| "" => false
| String h t => let q := String h "" in 
                let w := test_already_exists q unacceptable_symbols in
                if ( w ) then true
                         else test_of_unacceptable_symbols t
end.

Definition test_off(s : string ) :=
let q := test_of_unacceptable_symbols s in
let w := test_already_exists s separators in
orb q w .

Fixpoint IFF( i : list string ) ( ot: (string * string ) ) :=
match i with
| nil => [ot]
| h :: t => if( test_off h ) then nil
                             else IFF t ot
end.
(* Buiding a local vars struct  *)
Fixpoint get_vars (fn:string) (sl:list string) :=
match sl with   
| nil => nil
| type :: name :: ";":: t => 
       ( IFF (type :: name :: nil) ( type , ( fn++"_Л_"++name )%string ) ) ++ get_vars fn t

| type :: m :: name :: ";":: t => 
       ( IFF (type :: m :: name :: nil ) ( type , ( fn++"_Л_"++name )%string ) ) ++ get_vars fn t

| type :: name :: "=":: t =>  
       ( IFF (type :: name :: nil ) ( type , ( fn++"_Л_"++name )%string )) ++ get_vars fn t

| type :: m :: name :: "=":: t =>  
       ( IFF (type :: m :: name :: nil) ( type , ( fn++"_Л_"++name )%string ) ) ++ get_vars fn t

| "(" :: type :: name :: ")" :: t =>  
       ( IFF (type :: name :: nil ) ( type , ( fn++"_Л_"++name )%string ) ) ++ get_vars fn t

| "(" :: type :: m :: name :: ")" :: t =>  
       ( IFF (type :: m :: name :: nil ) ( type , ( fn++"_Л_"++name )%string ) ) ++ get_vars fn t

| "(" :: type :: name :: "," :: t => 
       ( IFF ( type :: name :: nil ) ( type , ( fn++"_Л_"++name )%string ) ) ++ get_vars fn t

| "(" :: type :: m :: name :: "," :: t =>  
       ( IFF ( type :: m :: name :: nil ) ( type , ( fn++"_Л_"++name )%string ) ) ++ get_vars fn t

| type :: name :: ")" :: t => 
       ( IFF (type :: name :: nil ) ( type , ( fn++"_Л_"++name )%string ) ) ++ get_vars fn t

| type :: name :: "," :: t =>
       ( IFF (type :: name :: nil ) ( type , ( fn++"_Л_"++name )%string ) ) ++ get_vars fn t

| h :: t => get_args fn t
end.
Fixpoint get_local_variables (sl:list string) :=
match sl with
| nil => nil
| "function" :: name :: t => let arg := last_delete ( tail ( find_braket_interior (-1) t )) in
                             let body := last_delete ( tail ( find_brace_interior (-1) t )) in
                             ( get_args name arg ) ++ ( get_vars name body ) ++ get_local_variables t
| h :: t => get_local_variables t
end.
 
Fixpoint get_local_variables1 (tl:list string) ( l:list (string * string) ) :=
match l with
| nil => nil
| h :: t => let q := ( fst h ) in 
            let w := ( snd h ) in 
            if ( test_already_exists q tl ) 
            then
               ( if ( test_off w ) then get_local_variables1 tl t 
                                   else q :: w :: ";" :: get_local_variables1 tl t )
            else get_local_variables1 tl t
end.

Fixpoint delete_double_vars(acc:list string)(l:list (string * string)):=
match l with
| nil => nil
| h :: t => let q := snd h in if ( test_already_exists q acc ) 
                              then delete_double_vars acc t
                              else h :: delete_double_vars (q::acc) t
end.
Definition get_local_vars (tl:list (string * string)) (sl:list string) :=
let q := (* List.concat *) sl in

let w := get_local_variables q in 
let w := delete_double_vars [] w in

let e := get_local_variables1 ( ( map fst tl ) ++ the_types ) w in
"contract" :: "LocalState" :: "{" :: e ++ "}" :: nil.


(* Word with structs ssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssssss*)
Definition make_struct_interior (struct_name:string) (sl:list string) :=
let x := find_brace_interior (-1) sl in
let x := last_delete ( List.tail x ) in   x.
Definition get_name_from_type_string(s:string) :=  headS "" (split_string' " " s). 
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
Definition get_struct_itself(struct_name:string)(tl:list(string*string))(sl:list string) :=
match sl with                                             
| nil => nil
| h :: t => let x := make_struct_interior struct_name t in
            let x := get_type_lines struct_name x in
            let typelist := get_type_list x tl in
            (* let typestring := ("{" ++ (concat_with " " typelist) ++ "}")%string in *)
            let typestring := "{" :: typelist ++ ["}"] in
            let all := typestring ++ ":=" :: [(struct_name++"C")%string] in
 let natural_type_list := (concat_with " " (map (cot_mini_types2coq_types tl) typelist)) in

        let rec := (newline :: newline :: "Record" :: (struct_name++"P")%string :: all ++ x) in

        if (isEmpty (concat_with " " x)) then nil else rec 
end.

Definition get_struct_Arguments(struct_name:string)(tl:list(string*string))(sl:list string) :=
match sl with                                              
| nil => nil
| h :: t => let x := make_struct_interior struct_name t in
            let x := get_type_lines struct_name x in
            let typelist := get_type_list x tl in
            let typestring := ("{" ++ (concat_with " " typelist) ++ "}")%string in
            let all := (typestring ++ " := " ++ struct_name ++ "C")%string in
        let natural_type_list := (concat_with " " (map (cot_mini_types2coq_types tl) typelist)) in

         "Arguments" :: (struct_name ++ "C")%string ::
                "[" :: (concat_with " " typelist) :: "]" :: "." :: newline :: [newline]
end.
Definition get_struct_DefinitionType (struct_name:string)(tl:list(string*string))(sl:list string) :=
match sl with                                               
| nil => nil
| h :: t => let x := make_struct_interior struct_name t in
            let x := get_type_lines struct_name x in
            let typelist := get_type_list x tl in
            let typestring := ("{" ++ (concat_with " " typelist) ++ "}")%string in
            let all := (typestring ++ " := " ++ struct_name ++ "C")%string in
        let natural_type_list := (concat_with " " (map (cot_mini_types2coq_types tl) typelist)) in
             "Definition" :: struct_name :: ":=" :: ("@" ++struct_name++"P ")%string :: natural_type_list :: ["."]
end.
Definition get_struct_existT (struct_name:string)(tl:list(string*string))(sl:list string) :=
match sl with                                               (* get_type_list *)
| nil => nil
| h :: t => let x := make_struct_interior struct_name t in
            let x := get_type_lines struct_name x in
            let typelist := get_type_list x tl in
            let typestring := ("{" ++ (concat_with " " typelist) ++ "}")%string in
            let all := (typestring ++ " := " ++ struct_name ++ "C")%string in
        let natural_type_list := (concat_with " " (map (cot_mini_types2coq_types tl) typelist)) in
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
Definition get_struct_default(struct_name:string)(tl:list(string*string))(sl:list string) :=
match sl with                                             
| nil => nil
| h :: t => let x := make_struct_interior struct_name t in
            let x := get_type_lines struct_name x in
            let typelist := get_type_list x tl in
            let typestring := ("{" ++ (concat_with " " typelist) ++ "}")%string in
            let all := (typestring ++ " := " ++ struct_name ++ "C")%string in
        let natural_type_list := (concat_with " " (map (cot_mini_types2coq_types tl) typelist)) in

         ("Instance" :: (struct_name++"_default")%string :: ":" :: "XDefault" :: struct_name ::
          ":=" :: "{" :: newline :: 
          tab :: "default" :: ":=" :: ( struct_name ++ "C")%string :: (list_pass x) :: newline 
          :: "}" :: ["."])   
end.
Definition get_struct (contract_name:string)(tl:list(string*string))(sl:list string) :=
match sl with
| nil => nil
| h :: t => let struct_name := 
              if ( contract_name =? "localState" ) 
              then ""
              else (contract_name++"_ι_"++h)%string 
            in 
           ( get_struct_itself struct_name tl sl )         ++ [newline] ++
           ( get_struct_Arguments struct_name tl sl )      ++ [newline] ++ 
           ( get_struct_DefinitionType struct_name tl sl ) ++ [newline] ++
           ( get_struct_existT struct_name tl sl )         ++ [newline] ++
           ( get_struct_Acc_ struct_name sl )              ++ [newline] ++
           ( get_struct_BindScope struct_name sl )         ++ [newline] ++
           ( get_struct_default struct_name tl sl )        ++ [newline]
end.
Fixpoint make_structs (contract_name:string)(tl:list(string*string))(sl:list string) :=
match sl with
| nil => nil
| "struct" :: t => (get_struct contract_name tl t) :: (make_structs contract_name tl t)
| h :: t => make_structs contract_name tl t
end. 
(***************    Work with the contract stuffing rest    *****************)
(* Pulling the zero-level chains *)
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
| key_word :: name :: ";" :: nil => 
(tab++prefix'++"_ι_"++name)%string :: ":" :: (sol_types2coq_mini_types key_word) :: ";" :: nil

| key_word :: modif :: name :: "=" :: xxx => 
(tab++prefix'++"_ι_"++name)%string :: ":" :: (sol_types2coq_mini_types key_word) :: ";" :: 
                "(*" :: modif :: ":=" :: xxx ++ ["*)"]

| key_word :: modif :: name :: ";" :: nil =>  
(tab++prefix'++"_ι_"++name)%string :: ":" :: (sol_types2coq_mini_types key_word) :: ";" :: 
                "(*" :: modif :: "*)" :: nil
| "mapping" :: "(" :: type1 :: "=>" :: type2 :: ")" :: name :: ";" :: nil =>
(tab++prefix'++"_ι_"++name)%string :: ":" :: "HM" :: (sol_types2coq_mini_types type1) ::
                                          (sol_types2coq_mini_types type2) :: ";" :: nil
| "mapping" :: "(" :: type1 :: "=>" :: type2 :: "." :: type3 :: ")" :: name :: ";" :: nil =>
(tab++prefix'++"_ι_"++name)%string :: ":" :: "HM" :: (sol_types2coq_mini_types type1) ::
                                          (sol_types2coq_mini_types type3) :: ";" :: nil
| "optional" :: "<" :: typ :: ">" :: name :: ";" :: t =>
      (tab++prefix'++"_ι_"++name)%string :: ":" :: "M" :: 
                   (sol_types2coq_mini_types typ) :: ";" :: newline :: nil

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
Fixpoint get_legal_types (sl:list string) :=
match sl with
| nil => nil
| h :: t => ( cot_mini_types2coq_types_1 ( cot_mini_types2coq_types [] h ) ) :: get_legal_types t
end.
Definition make_elses (contract_name:string)(tl:list(string*string))(sl:list string) :=
let q := make_list_level_0 false 0 sl in 
let x := concat_with " " q in

let y := split_string'' " " ";" x in 

let z := map clear_string_easy (map (split_string' " ") y) in 

let w := map (make_elses' contract_name) z in 
let ww := get_type_list'' w in

let e := if ( contract_name =? "Ledger" ) then ww 
                                          else get_legal_types ( ww ) in

let type_list := concat_with " " ( list_of_uniq_types [] e ) in 
let natural_type_list := (concat_with " " (map (cot_mini_types2coq_types tl)
                                                   (split_string' " " type_list))) in 
let rec :=
    ["Record" ; (contract_name++"P"++"{"++ type_list ++"}")%string ; ":=" ; 
                (contract_name++"C"++" {")%string ] :: w ++  ["} ."] :: 
     ["Arguments" ; (contract_name ++ "C")%string  ; "[" ; type_list ; "]" ; "." ] :: [newline] ::
     [ "Definition" ; contract_name ; ":=" ; ("@" ++
                  contract_name++"P ")%string ; natural_type_list ; "." ] ::
    [("Global Instance Struct_"++contract_name++" : Struct "++contract_name++" := {"++
     newline++tab++"fields := [" ++ 
     newline++ (concat_with newline (map make_line_for_Global_Instatce 
                                             (map clear_some_symbols 
                                   (map (concat_with " ") w) )))  ++
     newline++tab++ "] ; "++
     newline++tab)%string ; "ctor" ; ":=" ; ("@"++contract_name++"C")%string ; natural_type_list ;
     newline ;"}" ; "."]
     :: ( make_pull_up_per_number 0 (map clear_some_symbols 
                                   (map (concat_with " ") w) ) ) ::
        ("Instance" :: (contract_name++"_default")%string :: ":" :: "XDefault" :: contract_name ::
          ":=" :: "{" :: newline :: 
          tab :: "default" :: ":=" :: ( contract_name ++ "C")%string :: 
              (list_pass (map (concat_with " ") w)) :: newline :: "}" :: "." :: [newline])
     :: nil in 
          if (isEmpty (concat_with " "(map (concat_with " ") w))) then nil else rec.
(* Работа с контрактами ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc*)
Definition make_contract_interior (contract_name:string)(tl:list(string*string))(sl:list string) :=
let x := find_brace_interior (-1) sl in 
let x := last_delete ( List.tail x ) in   
                let ctrt := "Сontract" in
                let str := (make_structs contract_name tl x) in
                let structs   :=  [ctrt ; (contract_name)%string] :: str in 
                let elses := structs ++  (make_elses contract_name tl x) in               elses.
(* The first line is the contruct name *)
Definition get_contract (tl:list(string*string)) (sl:list string) :=
match sl with
| nil => nil
| h :: t => let contract_name := h in make_contract_interior contract_name tl t
end.  
Fixpoint make_contracts (tl:list(string*string)) (sl:list string) (*l:list(list string)*) :=
match sl with
| nil => [nil]
| "contract" :: t => (get_contract tl t) :: (make_contracts tl t)
| "library" :: t => (get_contract tl t) :: (make_contracts tl t)
| h :: t => make_contracts tl t
end.
Definition clear_forward (s:string) :=
match s with
| "" => ""
| String " "%char t => t
| String h t => s
end. 
(*********************** Making enum types ********************************)
Fixpoint make_enum' (name:string)(sl:list string) :=
match sl with
| nil => [newline]
| h :: "," :: t => "|" :: ( name ++ "_ι_" ++ h )%string :: ":" :: name :: newline :: make_enum' name t
| h :: "}" :: t => "|" :: ( name ++ "_ι_" ++ h )%string :: ":" :: name :: "." :: newline :: [newline]
| h :: t => make_enum' name t
end.
Fixpoint make_enum (contract_name:string)(sl:list string) :=
match sl with
| nil => nil
| "contract" :: name :: t => make_enum name t
| "library" :: name :: t => make_enum name t
| "enum" :: name :: t => let q := find_brace_interior (-1) t in
                         let w := ( contract_name ++ "_ι_" ++ name ++ "P" )%string in
                         let e := "Inductive" :: w :: ":=" :: [newline] in
                         ( e ++ make_enum' w q ) :: make_enum contract_name t
| h :: t => make_enum contract_name t
end. 
(* Instance RoundsBase_ι_RoundStep_default : XDefault RoundsBase_ι_RoundStepP := {
default := RoundsBase_ι_RoundStepP_ι_Pooling }. *)
Check make_enum.
Fixpoint make_enum_default (sl:list string) :=
match sl with
| nil => nil
| "Inductive" :: w :: ":=" :: nl :: "|" :: yf :: t => "Instance" :: 
         ( w ++ "_default" )%string :: ":" :: "XDefault" :: w :: ":=" :: "{" :: newline ::
         "default" :: ":=" :: yf :: "}" :: "." :: newline :: newline :: make_enum_default t
| h :: t => make_enum_default t
end.
(********************************************************************************)
(* Clearing comments /**/ *)
Fixpoint clearComment(f:bool)(s:string):=
match f, s with
| _ , "" => ""
| false, String "/"%char (String "*"%char t) => clearComment true t
| true,  String "*"%char (String "/"%char t) => clearComment false t
| true,  String h t => clearComment true t
| false, String h t => String h (clearComment false t)
end.
(***************************** Work with order *****************************)
Fixpoint clear_forward_space (s:string) := 
match s with
| "" => ""
| String "010"%char (String " "%char (String " "%char t)) => String "010"%char (clear_forward_space t)
| String "010"%char (String " "%char t) => String "010"%char (clear_forward_space t)
| String h t => String h (clear_forward_space t)
end.
Fixpoint set_forward_space (s:string) := 
match s with
| "" => ""
| String "010"%char t => String "010"%char (String " "%char (set_forward_space t))
| String h t => String h (set_forward_space t)
end.
Inductive bool3 :=
| EMPTY : bool3
| RECORD : bool3
| ARGUMENTS  : bool3.
Fixpoint get_rec_arg (f:bool3) (sl:list string) :=
match f, sl with
| _, nil => nil
(* | EMPTY, "Record" :: t => (newline++"Record")%string :: (get_rec_arg RECORD t) *)
| EMPTY, "Record" :: t => newline::"Record" :: (get_rec_arg RECORD t) 
| RECORD, "Arguments" :: t => "Arguments" :: (get_rec_arg ARGUMENTS t)
| ARGUMENTS, "." :: t => "." :: (get_rec_arg EMPTY t)
| EMPTY, h :: t => (get_rec_arg EMPTY t)
| RECORD, h :: t => h :: (get_rec_arg RECORD t)
| ARGUMENTS, h :: t => h :: (get_rec_arg ARGUMENTS t)
end.
Inductive bool2 :=
| EMPTY' : bool2
| ELSE   : bool2.
(* Testing next is closing braket/brace/sq. braket *)
Fixpoint toBraket(sl:list string) :=
match sl with
| nil => false
| "}" :: t => true
| "]" :: t => true
| ")" :: t => true
| "
" :: t     => toBraket t
| " " :: t =>  toBraket t
| "" :: t =>  toBraket t
| (String "009"%char "") :: t => toBraket t
| _ => false
end.
(* Clearing "," & ";" before closing brace/braket *)
Fixpoint clear_before_brace_braket(sl:list string) :=
match sl with
| nil => nil
| "," :: t => if( toBraket t ) then clear_before_brace_braket t
                               else "," :: (clear_before_brace_braket t)
| ";" :: t => if( toBraket t ) then clear_before_brace_braket t
                               else ";" :: (clear_before_brace_braket t)
| h :: t => h :: (clear_before_brace_braket t)
end.
Fixpoint get_global (f:bool2) (sl:list string) :=
match f, sl with
| _, nil => nil
| EMPTY', "Global" :: t => (newline++"Global")%string :: (get_global ELSE t)
| ELSE, "." :: t => "." :: (get_global EMPTY' t)
| EMPTY', h :: t => (get_global EMPTY' t)
| ELSE, h :: t => h :: (get_global ELSE t)
end.
Fixpoint get_define (f:bool2) (sl:list string) :=
match f, sl with
| _, nil => nil
| EMPTY', "Definition" :: t => newline :: "Definition" :: (get_define ELSE t)
| ELSE, "." :: t => "." :: (get_define EMPTY' t)
| EMPTY', h :: t => (get_define EMPTY' t)
| ELSE, h :: t => h :: (get_define ELSE t)
end.
Fixpoint get_bind_scope (f:bool2) (sl:list string) :=
match f, sl with
| _, nil => nil
| EMPTY', "Bind" :: t => newline ::"Bind" :: (get_bind_scope ELSE t)
| ELSE, "." :: t => "." :: (get_bind_scope EMPTY' t)
| EMPTY', h :: t => (get_bind_scope EMPTY' t)
| ELSE, h :: t => h :: (get_bind_scope ELSE t)
end.
Fixpoint get_defau (f:bool2) (sl:list string) :=
match f, sl with
| _, nil => nil
| EMPTY', "Global" :: "Instance" :: t => (get_defau EMPTY' t)
| EMPTY', "Instance" :: t => (newline++"Instance")%string :: (get_defau ELSE t)
| ELSE, "." :: t => "." :: (get_defau EMPTY' t)
| EMPTY', h :: t => (get_defau EMPTY' t)
| ELSE, h :: t => h :: (get_defau ELSE t)
end.
Fixpoint clear_newline (s:string):=
match s with
| "" => ""
| String "010"%char t => clear_newline t
| String h t => String h (clear_newline t)
end.
Definition get_set_all (s:string) :=
let sl := split_string' " " s in let contract_name := clear_newline (headS "" (tail sl)) in
let recs_args := get_rec_arg EMPTY sl in 
let module := if(isEmpty (concat_with "" recs_args)) then ""
                   else "monadStateStateT" in
let sol :=  "" in
let define := get_define EMPTY' sl in
let global := get_global EMPTY' sl in
let bind_scope := get_bind_scope EMPTY' sl in
let defau := get_defau EMPTY' sl in
let done := if(isEmpty (concat_with "" recs_args)) 

then [""]
else (

if ( contract_name =? "Ledger" ) 
then
(newline++"Definition"++" "++contract_name++"T"++" := "++"StateT"++" "++contract_name ++" . ")%string ::
     newline :: "End" :: (contract_name++"Class")%string :: "." :: newline :: [newline]  
else
(newline++"(* Definition"++" "++contract_name++"T"++" := "++"StateT"++" "++contract_name ++" . *)")%string ::
     newline :: "End" :: (contract_name++"Class")%string :: "." :: newline :: [newline] 
) in 

clear_before_brace_braket (
recs_args ++ [module] ++ [newline] ++ [sol] ++ define ++ bind_scope ++ global ++ defau ++ done 
                           ).
Check get_set_all.
Fixpoint recoveryComments(s:string) :=
match s with
| "" => ""
| String "("%char (String " "%char (String "*"%char t)) => 
                 String "("%char (String "*"%char (recoveryComments t))
| String "*"%char (String " "%char (String ")"%char t)) => 
                 String "*"%char (String ")"%char (recoveryComments t))
  
| String h t => String h (recoveryComments t)
end.
(* Adding standard types *)
Definition add_exist_types (tl : list (string*string)) :=
 ("byte","") :: ("uint","") :: ("uint8","") :: ("uint16","") :: ("uint32","") :: ("uint64","") 
:: ("uint128","") :: ("uint256","") :: ("bool","") 
:: ("mapping","") :: tl .
(* Test for exist type *)
Fixpoint isExist(s:string)(tl : list (string*string)) :=
match tl with
| nil => false
| h :: t => if(s =? (fst h)) then true else isExist s t
end. 
Fixpoint out(tl : list (string*string)) :=
match tl with
| nil => ""
| h :: t => ( ((fst h) ++ " " ++ (snd h)) ++ newline ++ (out t) )%string
end.
 
(* puting a struct-types to struct-member types *)
Fixpoint set_different_types(tl:list (string * string))(sl:list string) :=
match sl with
| nil => nil
| ":" :: h :: h1 :: h2 :: t => if ( h =? "Struct" ) then ":" :: h :: h1 :: h2 :: set_different_types tl t
                     else 
                               if ( h =? "XDefault" ) then ":" :: h :: h1 :: h2 :: set_different_types tl t
                     else  
                     let q := get_non_standard_type tl h in
                     if ( q =? "" ) 
                     then 
                       let e := get_non_standard_type tl h1 in
                       if ( e =? "" ) 
                       then (                       
                         let w := get_non_standard_type tl h2 in
                         if ( w =? "" )
                         then ":" :: h :: h1 :: h2 :: set_different_types tl t
                         else ":" :: h :: h1 :: "(@" :: (w++"P")%string :: ")":: set_different_types tl t
                       )
                       else ":" :: h :: "(@" :: (e++"P")%string :: ")":: h2 :: set_different_types tl t
                     else ":" :: "(@" :: (q++"P")%string :: ")":: h1 :: h2 :: set_different_types tl t
| h :: t => h :: set_different_types tl t
end.
(* collect types of record interior  *)
Fixpoint find_types (sl:list string) :=
match sl with
| nil => nil
(*| "{" :: h :: t => h :: find_types t
| ":" :: h :: t => find_types t
| "}" :: t => find_types t
| "{" :: t => find_types t
| ":" :: t => find_types t
| "" :: t => find_types t
| " " :: t => find_types t *)
| h :: t => if ( test_of_unacceptable_symbols h ) then find_types t
            else h :: find_types t
end.
(* Fixpoint types_collect'(sl:list string) :=
match sl with 
| nil => nil 
| "Record" :: name :: t => let a := pulling_list_elements ":=" t in
                        let q := find_types a in
                        ( name , q ) :: types_collect' t

| h :: t => types_collect' t
end. *)
Fixpoint types_collect'(sl:list string) :=
match sl with 
| nil => nil
| "
Record" :: name :: t => let q := find_brace_interior (-1) t in
                           let w := tail q in
                           let e := last_delete w in
                           ( name , e ) :: types_collect' t
| h :: t => types_collect' t
end.
Definition types_collect (sl:list(list string)) :=
let q := List.concat sl in
types_collect' q.
 
(* Find typelist in collect types *)
Fixpoint find_typelist(tl:list(string * list string))(s:string):=
match tl with
| nil => nil
| h :: t => if ( ( fst h ) =? s ) then snd h
                                  else find_typelist t s 
end.
(* put type list to "(@" *)
Fixpoint put_type_list (tl:list(string * list string))(sl:list string) :=
match sl with
| nil => nil
| "(@" :: h :: t => let q := find_typelist tl h in
                    "(@" :: h :: q ++ put_type_list tl t
| h :: t => h :: put_type_list tl t
end.
Fixpoint out_tuple_2 (tl:list(string * nat)) :=
match tl with
| nil => nil
| h :: t => ( fst h ) :: ( writeNat ( snd h ) ) :: newline :: out_tuple_2 t
end.
Fixpoint out_tuple (tl:list(string * list string)) :=
match tl with
| nil => nil
| h :: t => ( ( fst h ) :: ( snd h ) ) :: [newline] :: out_tuple t
(* | h :: t => ( fst h ) :: out_tuple t *)
end.
(* Adding type list from (@ to record' parameters *)
Definition adding_parameters' (new cur : list string) :=
  list_of_uniq_types cur new.
Fixpoint find_brace_dog (sl:list string) :=
match sl with
| nil => nil
| ":" :: "(@" :: name :: t => t :: find_brace_dog t 
| ":" :: t1 :: "(@" :: name :: t => [t1] :: t :: find_brace_dog t 
| ":" :: t1 :: t2 :: "(@" :: name :: t => [ t1 ; t2 ] :: t :: find_brace_dog t 
| h :: t => find_brace_dog t
end. 
Fixpoint adding_parameters(tl:list(string * list string))(sl:list string) :=
let fix tail'(tl:list(string * list string)) (sl:list string) :=
match sl with
| nil => nil
| "]" :: t => adding_parameters tl t
| h :: t => tail' tl t
end in
match sl with
| nil => nil
| "Record" :: t => let name := headS "" t in
                let crotch := pulling_list_beetween false "}" "{" t in
                let param := last_delete ( tail ( find_brace_interior (-1) t )) in
                let t' := discard_list_elements "{" (tail (tail t)) in
                                   (* let body := last_delete ( tail ( find_brace_interior (-1) t' )) in *)
                let body := tail ( tail ( tail ( pulling_list_beetween false ":=" "}" t ) ) ) in
                let n := find_brace_dog body in
                let argu_name := pulling_list_beetween false "Arguments" "[" t in
                let argu_body := pulling_list_beetween false "[" "]" t in
                if ( Nat.eqb (List.length n) 0 ) 
                then newline :: "Record" :: adding_parameters tl t
                else 
                     let news := List.concat ( map ( pulling_list_elements ")" ) n ) in
                     let new_param := list_of_uniq_types param news in
                     newline :: "Record" :: name :: "{" :: new_param ++ "}" :: crotch ++ 
                     "{" :: body ++ "}" :: "." :: newline :: 
      "Arguments" :: argu_name ++ "[" :: new_param ++ ["]"] ++ newline :: tail' tl t
| h :: t => h :: adding_parameters tl t
end.

(* Fixpoint union_all_contructs' (s:string)(sl:list string) :=
match sl with
| nil => nil
| "contract" :: name :: t => union_all_contructs' name t
| "struct" :: name :: t => 
                    name :: (s++"_ι_"++name)%string :: ";" :: union_all_contructs' s t
| h :: t => union_all_contructs' s t
end. *)

Fixpoint union_all_contructs'(acc:list string)(s:string)(sl:list string) :=
match sl with
| nil => nil
(* | "contract" :: name :: t => (name++"P")%string :: ("type_"++name)%string :: ";" :: union_all_contructs' s t *)
| "contract" :: name :: t => 
         if ( test_already_exists name acc )
         then union_all_contructs' acc s t
         else (name++"P")%string :: name :: ";" :: union_all_contructs' (name::acc) s t
| "library" :: name :: t => 
         if ( test_already_exists name acc )
         then union_all_contructs' acc s t
         else (name++"P")%string :: name :: ";" :: union_all_contructs' (name::acc) s t
| h :: t => union_all_contructs' acc s t
end.
Check union_all_contructs'.

Definition union_all_contructs(sl:list string) := 
let q :=  union_all_contructs' [] "" sl in
"contract" :: "Ledger" :: "{" :: q ++ ["}"] . 

Fixpoint get_before_modules'(sl:list string):=
match sl with
| nil => nil
| "Record" :: t => let t' := pulling_list_elements "Arguments" t in
                     "Record" :: t' ++ [newline] ++ get_before_modules' t
| "Arguments" :: t => let t' := pulling_list_elements "." t in
                     "Arguments" :: t' ++ ["." ; newline] ++ get_before_modules' t
| h :: t => get_before_modules' t
end.
Fixpoint get_before_modules(sl:list(list string)):=
match sl with
| nil => nil
| h :: t => ( get_before_modules' h ) :: get_before_modules t
end.

Fixpoint get_after_modules'(sl:list string):=
match sl with
| nil => nil
| "monadStateStateT" :: t => let t' := pulling_list_elements "End" t in
                     t' ++ get_after_modules' t
| h :: t => get_after_modules' t
end.
Fixpoint get_after_modules(sl:list(list string)):=
match sl with
| nil => nil
| h :: t => ( get_after_modules' h ) :: get_after_modules t
end.

Fixpoint types_Ledger_list(sl:list string) :=
match sl with
| nil => nil
| "Record" :: name :: t => let q := last_delete ( tail ( find_brace_interior (-1) t ) ) in
                           ( name , q ) :: types_Ledger_list t
| h :: t => types_Ledger_list t
end.
Check types_Ledger_list.
Fixpoint put_types_to_Ledger_Record (f:bool)
                                    (w:list (string * list string))
                                    (sl:list string) :=
match f , sl with
| _ , nil => nil
| false , "Record" :: "LedgerP" :: t => "Record" :: "LedgerP" :: put_types_to_Ledger_Record true w t 
| true , h1 :: ":" :: name :: t => let q := find_typelist w name in
                                   if ( Nat.eqb ( List.length q ) 0 ) 
                                   then h1 :: ":" :: "True" :: put_types_to_Ledger_Record true w t
                                   else
                                   h1 :: ":" :: "(@" :: name :: q ++ ")" ::
                                      put_types_to_Ledger_Record true w t 

| true , "." :: t => "." :: put_types_to_Ledger_Record false w t

| true , h :: t => h :: put_types_to_Ledger_Record true w t

| false , h :: t => h :: put_types_to_Ledger_Record f w t 

end.
Fixpoint put_types_to_Ledger_Record' (f:bool)
                                    (w:list (string * list string))
                                    (sl:list string) :=
match f , sl with
| _ , nil => nil
| false , "Record" :: "LedgerP" :: "{" :: t => "Record" :: "LedgerP" :: "{" :: put_types_to_Ledger_Record' true w t 
| true , "}" :: t => "}" :: put_types_to_Ledger_Record' false w t
| true , name :: t => let q := find_typelist w name in
                                q ++ put_types_to_Ledger_Record' true w t 
| false , h :: t => h :: put_types_to_Ledger_Record' f w t 
end.
Fixpoint correct_Ledger_Arguments(w sl:list string) :=
let fix tail' (sl:list string) :=
match sl with
| nil => nil
| "." :: t => "." :: t
| h :: t => tail' t
end in
match sl with
| nil => nil
| "Arguments" :: "LedgerC" :: t => "Arguments" :: "LedgerC" :: "[" :: w ++ "]" :: tail' t 
| h :: t => h :: correct_Ledger_Arguments w t
end.
Fixpoint correct_types_to_Ledger_Record'(sl:list string) :=
let fix tail' (w sl:list string) :=
match sl with
| nil => nil
| "}" :: t => correct_Ledger_Arguments w t
| h :: t => tail' w t
end in
match sl with
|  nil => nil
| "Record" :: "LedgerP" :: "{" :: t => 
                  let q := last_delete ( tail ( find_brace_interior (-1) ( "{" :: t ) ) ) in
                  let w := list_of_uniq_types [] q in
                  "Record" :: "LedgerP" :: "{" :: w ++ "}" :: tail' w t                 
| h :: t => h :: correct_types_to_Ledger_Record' t 
end.

Definition make_Ledger_struct (sl:list(list string)) :=
let q := List.concat sl in
let w := types_Ledger_list q in
let e := map ( put_types_to_Ledger_Record  false w ) sl in
let r := map ( put_types_to_Ledger_Record' false w ) e in 
let t := map correct_types_to_Ledger_Record' r in t
.

Fixpoint HM_to_forward(sl:list string) :=
let fix tail' (sl:list string) :=
match sl with
| nil => nil
| "}" :: t => HM_to_forward t
| "]" :: t => HM_to_forward t
| ")" :: t => HM_to_forward t
| h :: t => tail' t
end in
match sl with
| nil => nil
| "Record" :: h :: t => let q := last_delete ( tail ( find_brace_interior (-1) t ) ) in
                        let w := find_and_forward_symbol "HM" q in
                        let e := headS "" w in
                        let r := tail w in
                        if ( e =? "HM" ) 
                        then "Record" :: h :: "{" :: "HM" :: ":" :: "Type" :: "->":: 
                        "Type" :: "->":: "Type" :: "}" :: "{" :: r ++ "}" :: tail' t
                        else "Record" :: h :: HM_to_forward t
| "Arguments" :: h :: t => 
                      let q := last_delete ( tail ( find_sq_braket_interior (-1) t ) ) in
                        let w := find_and_forward_symbol "HM" q in
                        let e := headS "" w in
                        let r := tail w in
                        if ( e =? "HM" ) 
                        then "Arguments" :: h :: "[" :: w ++ "]" :: tail' t
                        else "Arguments" :: h :: HM_to_forward t
| "(@" :: h :: t => 
                      let q := pulling_list_elements ")" t in
                        let w := find_and_forward_symbol "HM" q in
                        let e := headS "" w in
                        let r := tail w in
                        if ( e =? "HM" ) 
                        then "(@" :: h :: w ++ ")" :: tail' t
                        else "(@" :: h :: HM_to_forward t
| h :: t => h :: HM_to_forward t
end.

Fixpoint set_arrow_types (f:bool)(sl : list string) :=
match f, sl with
| _ , nil => nil
| false , "Record" :: n :: t => "Record" :: n :: set_arrow_types true t
| true , "}" :: t => "}" :: set_arrow_types false t
| true , "{" :: h :: t => let q := get_non_standard_type arrow_types h in
                          if ( q =? "" ) then "{" :: h :: set_arrow_types true t
                          else let w := headS "" t in
                               if ( w =? "}" ) then "{" :: h :: ":" :: q :: "}" :: set_arrow_types false t
                               else "{" :: h :: ":" :: q :: "}" :: "{" :: set_arrow_types true t
| true , h :: "}" :: t => let q := get_non_standard_type arrow_types h in
                          if ( q =? "" ) then h :: "}" :: set_arrow_types false t
                          else "}" :: "{" :: h :: ":" :: q :: "}" :: set_arrow_types false t
| true , h :: t => let q := get_non_standard_type arrow_types h in
                          if ( q =? "" ) then h :: set_arrow_types true t
                          else "}" :: "{" :: h :: ":" :: q :: "}" :: "{" :: set_arrow_types true t
| _ ,  h :: t => h :: set_arrow_types f t
end.

Fixpoint type_list(sl:list string) :=
match sl with
| nil => nil
| "Arguments" :: h :: t => let q:= last_delete ( tail ( find_sq_braket_interior (-1) t ) ) in
                           let w := map ( cot_mini_types2coq_types [] ) q in
                           let e := delete_last_symbol h in
                           ( e , w ) :: type_list t
| h :: t => type_list t
end.
Check find_typelist.
Fixpoint set_real_types_to_sites(tl:list(string * list string))(sl:list string) :=
let fix tail'(tl:list(string * list string))(sl:list string) :=
match sl with
| nil => nil
| "." :: t => set_real_types_to_sites tl t
| "}" :: t => set_real_types_to_sites tl t
| h :: t => tail' tl t
end in 
match sl with
| nil => nil
| "Definition" :: h :: ":=":: h1 :: t => let q := find_typelist tl h            in
                                       "Definition" :: h :: ":=" :: h1 :: q  ++ "." :: tail' tl t

| "ctor" :: ":=" :: h :: t => let q := delete_first_and_last_symbols h in
                              let w := find_typelist tl q              in
                       "ctor" :: ":=" :: h :: w ++ newline :: "}" :: ( tail' tl t )

| h :: t => h :: set_real_types_to_sites tl t 
end.
Definition set_real_types(sl:list(list string)) :=
let q := List.concat sl in
let w := type_list q in
let e := map ( set_real_types_to_sites w ) sl in     e. 

Fixpoint End_delete(sl:list string) :=
match sl with
| nil => nil
| "End" :: "LedgerClass" :: t => "End" :: "LedgerClass" :: t
| "End" :: n :: "." :: t => End_delete t
| h :: t => h :: End_delete t 
end.

Fixpoint owner_off(sl:list string) :=
match sl with
| nil => nil
| "Owner" :: t => owner_off t
| h :: t => h :: owner_off t
end.

Fixpoint get_member_of_Ledger_record'(f:bool)(sl:list string) :=
match f , sl with
| _, nil => nil
| false , "Record" :: "LedgerP" :: t => get_member_of_Ledger_record' true t
| true , "." :: t => get_member_of_Ledger_record' false t
| true , h1 :: ":" :: "(@" :: h2 :: t => 
                  ( delete_last_symbol h2 ) :: get_member_of_Ledger_record' true t
| true , h :: ":" :: t => get_member_of_Ledger_record' true t
| _ , h :: t => get_member_of_Ledger_record' f t
end.

(* Fixpoint get_member_of_Ledger_record'(f:bool)(sl:list string) :=
match sl with
| nil => nil
| "Record" :: name :: t => if ( have_it_symbol "185"%char name)
                           then get_member_of_Ledger_record' f t
                           else name :: get_member_of_Ledger_record' f t
| h :: t => get_member_of_Ledger_record' f t
end. *)

Fixpoint def_ti(n:nat)(sl:list string) :=
match sl with
| nil => nil
| h :: t => newline :: "Definition" :: ( "T"++(writeNat n) )%string :: ":=" :: h :: 
                                                 "." :: def_ti (n+1) t
end.
Definition get_member_of_Ledger_record(sl:list(list string)) :=
let q := List.concat sl in
let w := get_member_of_Ledger_record' false q in 
def_ti 1 w.
Fixpoint number_of_def'(n:nat)(f:bool)(sl:list string) :=
match f , sl with
| _ , nil => n
| false , "Definition" :: "T1" :: t => number_of_def' 1 true t
| true  , "Definition" :: t => number_of_def' (n+1) true t
| true  , "End" :: t => number_of_def' n true t
| _ , h :: t => number_of_def' n f t
end.
Definition number_of_def (sl:list (list string)) :=
let q:= List.concat sl in
number_of_def' 0 false q.

Fixpoint Ti_generator1 (nn n :nat) :=
match nn with
| 0 => nil
| S n' => let T := ("T"++(writeNat n))%string in newline ::newline ::newline ::
"Definition" :: ("projEmbed_"++T)%string :: ":" :: "Ledger" :: "->" :: T :: ":=" :: "projEmbed_Accessor" :: "." :: newline ::
"Definition" :: ("injEmbed_"++T)%string :: ":" :: T :: "->" :: "Ledger" :: "->" :: "Ledger" :: ":=" :: "injEmbed_Accessor" :: "." ::
newline ::newline ::
"Lemma" :: ("projinj_"++T)%string :: ":" :: "forall" :: "(" :: "t" :: ":" :: T :: ")" :: "(" :: "s" :: ":" :: "Ledger" :: ")" :: "," :: 
               newline :: ("projEmbed_"++T)%string :: "(" :: ("injEmbed_"++T)%string :: "t" :: "s" :: ")" :: "=" :: "t" :: "." ::
newline ::
"Proof.
 intros. compute. auto.
Qed." ::
newline ::newline ::
"Lemma" :: ("injproj_"++T)%string :: ":" :: "forall" :: "(" :: "s" :: ":" :: "Ledger" :: ")" :: "," :: 
      ("injEmbed_"++T)%string :: "(" :: ("projEmbed_"++T)%string :: "s" :: ")" :: "s" :: "=" :: "s" :: "." ::
"Proof.
 intros. destruct s. compute. auto.
Qed." ::newline ::

"Lemma" :: ("injinj_"++T)%string :: ":" :: "forall" :: "("::"t1":: "t2":: ":":: T::")" :: "(" :: "s" :: ":" :: "Ledger" :: ")" :: "," ::  
newline ::("injEmbed_"++T)%string :: "t1" :: "("::("injEmbed_"++T)%string:: "t2 s) =" ::
newline ::("injEmbed_"++T)%string :: "t1" :: "s" :: "." ::
newline ::
"Proof.
 intros. destruct s. compute. auto.
Qed." ::
newline ::newline ::
("Instance embedded"++T)%string :: (": EmbeddedType Ledger "++T)%string :: ":=" ::newline ::
("{
 projEmbed := projEmbed_"++T)%string :: ";"::newline ::
 ("injEmbed := injEmbed_"++T)%string :: ";"::newline ::
 ("projinj := projinj_"++T)%string :: ";"::newline ::
 ("injproj := injproj_"++T)%string :: ";"::newline :: 
 ("injinj  := injinj_"++T)%string :: ";"::newline ::
"}" :: "." :: newline :: Ti_generator1 n' (n+1)

end.
 
Fixpoint Ti_generator2 (nn n :nat)(cross s : string) :=
match nn with
| 0 => nil
| 1 => nil
| 2 => nil
| S n' =>  let T := ( "T" ++ ( writeNat n ) )%string in
           let t := ( "T" ++ ( writeNat (n-1) ) )%string in
           let c := ( ( exchange cross ) ++ "_" ++ T )%string in
           let str := (
"
Lemma injcommute_"++c++": 
               forall ( u : "++T++" ) ( t : "++s++" ) 
                      ( s:Ledger ), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_"++c++" : 
@InjectCommutableStates Ledger ( "++s++" ) "++T++(* " embeddedProduct_"++cross++" embedded"++T++ *)     
" := 
{
  injcommute := injcommute_"++c++" 
}.

Definition embeddedProduct_"++c++" := 
           @embeddedProduct Ledger ( "++ s ++ " ) " ++ T ++ "
  
           InjectCommutableStates_"++c++ ".

Existing Instance embeddedProduct_"++c++" .
" )%string
          in  let s := ( s ++ "* " ++ T ++ " " )%string in 

          str :: Ti_generator2 n' (n+1) c s 

end.
Fixpoint cross_gen (nn n : nat) (sl:string) :=
match nn with
| 1 => ( ( delete_last_symbol sl ) ++ ( "_T" ++ ( writeNat n ) ) )%string
| 0 => sl
| S nn => let q := ( sl ++ "T" ++ ( writeNat n ) ++ "x" )%string in
          cross_gen nn (n+1) q
end.
Compute (cross_gen 5 1 "").
Fixpoint star_gen (nn n : nat) (sl:string) :=
match nn with
| 1 =>  delete_last_symbol sl
| 0 =>  sl
| S nn => let q := ( sl ++ " T" ++ ( writeNat n ) ++ " *" )%string in
          star_gen nn (n+1) q
end.
Compute (star_gen 5 1 "").
Definition Ti_generator3 (n:nat) :=
let q := cross_gen (n-1) 1 "" in
let w := star_gen (n-1) 1 "" in
let e := ( "T" ++ ( writeNat (n-1) ) )%string in
( "
Axiom fullState_"++q++" : forall s s0, 
      injEmbed ( T:=( "++w++" ) ) 
(projEmbed s) (injEmbed (T:= "++e++" ) (projEmbed s) s0) = s.
(* Lemma fullState_"++q++" : forall s s0, 
      injEmbed ( T:=( "++w++" ) ) 
(projEmbed s) (injEmbed (T:= "++e++" ) (projEmbed s) s0) = s.
Proof.
  intros. compute. destruct s.
  auto.
Qed. *)

Instance FullState_"++q++" : 
         FullState Ledger ("++ w ++" ) " ++ e++" := 
{
  injComm := InjectCommutableStates_"++q++" ;
  fullState := fullState_"++q++" 
}." )%string .

Fixpoint Ti_generator4 (n:nat) :=
match n with
| 0 => nil
| S n' => let q := writeNat n in
( newline ++ "Notation ""'↑"++q++"' m"""++":= (liftEmbeddedState ( T := T"++q++" ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope." )%string ::
  Ti_generator4 n'
end.

Definition Ti_generator5 (n:nat) :=
let q := star_gen n 1 "" in
( newline ++ "Notation "" '↑0' m "" := ( liftEmbeddedState ( T := "++q++" ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope." )%string .

Fixpoint numbers_of_records(f:bool)(n:nat)(sl:list string) :=
match f , sl with
| _ , nil => nil
| false , "Definition" :: "T1" :: ":=" :: name :: "." :: t =>
           ( name , 1 ) :: numbers_of_records true 2 t
| true , "Definition" :: _ :: ":=" :: name :: "." :: t =>
           ( name , n ) :: numbers_of_records true (n+1) t
| true , "Definition" :: _ :: ":" :: t => nil
| _ , h :: t => numbers_of_records f n t
end.
Fixpoint find_tuple(s:string)(tl:list( string * nat )):=
match tl with
| nil => ""
| h :: t => let q := fst h in
            if ( q =? s ) then writeNat ( snd h )
            else find_tuple s t
end.
Fixpoint get_first_symbols_to_ ( s : string ) :=
match s with
| "" => ""
| String "_"%char t => ""
| String h t => String h ( get_first_symbols_to_ t )
end. (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
Fixpoint have_substring_m_(s : string) :=
match s with
| "" => false
| String "m"%char ( String "_"%char t ) => true
| String _ t => have_substring_m_ t
end.
Fixpoint double_arrows_generator'(n:nat)(sl:list string)
                                 (tl:list( string * nat )) :=
match sl with
| nil => nil
| "localStateP" :: t => nil
| name :: ":" :: "(@" :: t => if ( have_substring_m_ name )
                              then
                                  let q := writeNat n in
                                  let w := delete_first_symbol (get_first_symbols_to_ name) in
                                  let e := find_tuple w tl in
("Notation "" '↑↑"++q++"' n '^^' m "" := ( do a ← (↑"++e++" n " ++ (* ++name++ *)
" ) ; return! ( m a )  )%sol(at level 10, left associativity): solidity_scope."
++newline
)%string :: double_arrows_generator' (n+1) t tl
                               else double_arrows_generator' n t tl
| name :: ":" :: _ :: _ :: "(@" :: t => if ( have_substring_m_ name )
                              then
                                  let q := writeNat n in
                                  let w := delete_first_symbol (get_first_symbols_to_ name) in
                                  let e := find_tuple w tl in
("Notation "" '↑↑"++q++"' n '^^' m "" := ( do a ← (↑"++e++" n " ++ (* ++name++ *)
" ) ; return! ( m a )  )%sol(at level 10, left associativity): solidity_scope."
++newline
)%string :: double_arrows_generator' (n+1) t tl
                               else double_arrows_generator' n t tl
| h :: t => double_arrows_generator' n t tl
end.
Definition double_arrows_generator(sl:list(list string)) :=
let q := List.concat sl in
let w := numbers_of_records false 1 q in (* [writeNat (List.length w)] *)
(* ( out_tuple_2 w ) ++  *)
double_arrows_generator' 1 q w  .

Fixpoint how_many_records_in_Records'(f:bool)(n:nat)(sl:list string) :=
match f, sl with
| _, nil => n
| false , "Record" :: "LocalStateP" :: t => how_many_records_in_Records' true 1 t
| _, "." :: t => n
| true , ";" :: t => how_many_records_in_Records' true (n+1) t
| _, h :: t => how_many_records_in_Records' f n t
end.

Definition how_many_records_in_Records (sl:list(list string)) :=
let q := List.concat sl in
how_many_records_in_Records' false 0 q.
Fixpoint dotted_notation_generator'(n nn:nat) :=
match n with
| 0 => nil
| S n' =>  let q := writeNat nn in
           let w := writeNat (nn-1) in
 ("Notation ""·"++q++""":= (Next (·"++w++"))  (at level 60, right associativity).")%string ::
                newline :: dotted_notation_generator' n' (nn+1) 
end.

Definition dotted_notation_generator(n:nat) :=
"Notation ""·0""  := (Here)       (at level 60, right associativity)." :: newline ::
dotted_notation_generator' n 1 .

Compute (dotted_notation_generator 5).


Definition T1_T2 :=
"
Lemma injcommute_T1_T2: forall  (u:T2) (t:T1)  (s:Ledger), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T1_T2: 
         @InjectCommutableStates Ledger T1 T2 
               := 
{
  injcommute := injcommute_T1_T2
}.
Definition embeddedProduct_T1_T2 := 
           @embeddedProduct Ledger T1 T2 
                 InjectCommutableStates_T1_T2.
Existing Instance embeddedProduct_T1_T2.
".

Definition modu := "
Module LedgerClass (xt: XTypesSig) (sm: StateMonadSig) .
Module SolidityNotations := SolidityNotations.SolidityNotations xt sm.
Import SolidityNotations.
Existing Instance monadStateT.
Existing Instance monadStateStateT.
".

Definition m1 := "

(* 1 *)
(*embeddedType for all Accessors *)
Definition projEmbed_Accessor {U T}{f: T -> U}`{s: Struct T}`{a: @Accessor T U s f}: T -> U := f.
Definition injEmbed_Accessor {U T}{f: T -> U}`{s: Struct T}`{a: @Accessor T U s f} (x: U) (t: T): T :=
{$ t with f := x $}.

". 

Definition notarrarr := "
Notation "" '↑↑' n '^^' m "" := ( do a ← (↑2 n ) ; return! ( m a )  )(at level 10, left associativity): solidity_scope.

".

Fixpoint prepare_LedgerEvent (sl:list string) :=
match sl with
| nil => nil
| (String "009"%char "VMState_ι_events") :: ":" :: "L" :: t => 
               "VMState_ι_events" :: ":" :: "L" :: "(@" :: "LedgerEventP" :: ")" :: prepare_LedgerEvent t 
| h :: t => h :: prepare_LedgerEvent t
end.

Fixpoint prepare_types'(sl:list string) :=
match sl with
| nil => nil
| "Arguments" :: name :: t => let q := last_delete ( tail ( find_sq_braket_interior (-1) t ) ) in
                              let w := ( ( delete_last_symbol name ) ++ "P" )%string in
                              ( w , q ) :: prepare_types' t
| h :: t => prepare_types' t
end.
Fixpoint prepare_types''(tl:list(string * list(string)))(sl:list string) :=
let fix tail' (tl:list(string * list(string)))(sl:list string) :=
match sl with
| nil => nil
| ")" :: t => prepare_types'' tl t
| h :: t => tail' tl t
end in
match sl with
| nil => nil
| "(@" :: name :: t => let q := find_typelist tl name in
                       if ( Nat.eqb ( List.length q ) 0 )
                       then "(@" :: name :: prepare_types'' tl t
                       else "(@" :: name :: q ++ ")" :: tail' tl t
| h :: t => h :: prepare_types'' tl t
end.
Definition prepare_types(sl:list(list string)):=
let q  := List.concat sl in
let tl := prepare_types' q in
map ( prepare_types'' tl ) sl.

Definition addititional_structs := 
"
contract VMState {
   uint256 pubkey ;
   uint256 msg_pubkey ;
   uint64  now ;
   string  logstr ;
   uint128 balance ;
   uint256 address ;
   uint256 ltime ;
   TvmCell code ;
   list LedgerEvent events ;
   DePoolContract savedDePoolContract ;
}

".
(*Record VMStateP {I I256 I128 I64 I16 I8 C B} {L: Type-> Type} {A S } := VMStateC {
  msg_pubkey_VMState      : I256;	
  pubkey_VMState      : I256;
  now_VMState         : I64;
  logstr_VMState      : S;
  balance_VMState     : I128; 
  address_VMState     : I256;
  ltime_VMState       : I256; (* TODO: check the type *) 
  code_VMState        : C;  (* TODO: check the type *)
  events_VMState      : L (@LedgerEventP);
  savedDePoolContract_VMState  : @DePoolContractP I I64 I8 I16 B A I256    
}.
Arguments VMStateC [I I256 I128 I64 I32 I16 I8 C B HM L A S Bs]. *)

Fixpoint clearing(sl:list string) :=
match sl with
| nil => nil
| "{" :: "}" :: t => clearing t
| h :: t => h :: clearing t
end.
 
Definition shaper(s: string) := 
let s := ( s ++ addititional_structs )%string in 

let s:= clearComment1 false ( clearComment false (setSpace s) ) in    
let sl := split_string s newline in 
 let sl := map (split_string' " ") sl in 
 let sl := map clear_string_easy sl  in
let sl := clear_list_easy sl in
let sl := deleteComment sl in 
let sl := List.concat sl in 

let sl := array_2_mapping sl in

let enum := make_enum "" sl in
let enum_def := make_enum_default ( List.concat enum ) in

                                                               (* let sl := delete_angle_bracket sl in *)

let type_list := get_struct_list "" sl in                      (* out type_list. *)

let sl := sl ++ get_local_vars type_list sl in (*----------------------------------------*)

let union := union_all_contructs sl in                             (* let sl := union in *)

let sl := sl ++ union in

let all := make_contracts type_list sl in
let sl := concat_with_3_level all in
let sl := map (concat_with (newline(* ++" " *))%string) sl in
let sl := concat_with newline sl in                   (*                sl. *)
                  let sl := setSpace sl in 
                  let sl := concat_with newline (map clear_forward (split_string' newline sl)) in
                  let sl := set_forward_space sl in  
 
(* Building the right order *)
                  let sl := split_string' "Сontract" sl in 

                  let sl := map get_set_all sl in

let sl := map ( set_different_types type_list ) sl in

(************************************************************************************************)
let tl := types_collect sl in                   (*  let sl := out_tuple tl in   *)
let sl := map ( put_type_list tl ) sl in
let sl := map ( adding_parameters tl ) sl in

let sl := prepare_types sl in 

let tl := types_collect sl in                   (*  let sl := out_tuple tl in   *)
let sl := map ( put_type_list tl ) sl in
let sl := map ( adding_parameters tl ) sl in

let sl := prepare_types sl in

let tl := types_collect sl in                   (*  let sl := out_tuple tl in   *)
let sl := map ( put_type_list tl ) sl in
let sl := map ( adding_parameters tl ) sl in

(************************************************************************************************)
let sl := make_Ledger_struct sl in
                                                 (* let sl := map HM_to_forward sl in *) 

let sl := map ( set_arrow_types false ) sl in 

let sl := set_real_types sl in

let sl := ( get_before_modules sl ) ++ [modu] :: ( get_after_modules sl ) in

let sl := map End_delete sl in let sl := map owner_off sl in

let sl := map prepare_LedgerEvent sl in

let count := 250 (* how_many_records_in_Records sl *) in
let nots := (* [writeNat count] *)dotted_notation_generator count in

(* Doing the Ti *) 
let sl := nots :: sl ++ [m1] :: [ get_member_of_Ledger_record sl ] in
let num := number_of_def sl in
let Ti1 := Ti_generator1 num 1 in  
let Ti2 := Ti_generator2 num 3 "T1_T2" " T1 * T2 " in 
let Ti3 := Ti_generator3 (num+1) in
let Ti4 := Ti_generator4 num in
let Ti5 := Ti_generator5 num in 

let double_arrows := double_arrows_generator sl in

let sl := map clearing sl in

let sl := enum ++ [enum_def] ++ sl ++ [Ti1] ++ [[T1_T2]] ++ [Ti2] ++ 
                   [[Ti3]] ++ [Ti4] ++ [[Ti5]] ++ [[newline;newline]] ++ [double_arrows]  
(* [[notarrarr]] *) in


                recoveryComments ( ("
Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.
Require Import FinProof.ProgrammingWith.

Local Open Scope record.
Local Open Scope program_scope. 

Require Import FinProof.Common.
Require Import FinProof.StateMonad2.
Require Import depoolContract.SolidityNotations.

Inductive LedgerEventP  := NoEvent.
Definition LedgerEvent := LedgerEventP.

" ++ newline ++
                  concat_with " " (map (concat_with " ")  sl ) 
                  ++ newline ++ "End LedgerClass .")%string).

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

Extraction "./ClassGeneratorTogetherSol" main.

Check get_struct_list.
