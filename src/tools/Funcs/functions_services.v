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
 ["byte";"uint";"uint8";"uint16";"uint32";"uint64";"uint128";"uint256";
  "int";"int8";"int16";"int32";"int64";"int128";"int256";
   "bool";"mapping"] ++ tl .

(* first two sybbols from string *)
Definition first2 (s:string):=
match s with
| "" => s
| String a "" => s
| String a (String b t) => String a (String b "")
end.
(* first four sybbols from string *)
Definition first4 (s:string):=
match s with
| "" => s
| String a "" => s
| String a (String b "") => String a (String b "")
| String a (String b (String c "")) => String a (String b (String c ""))
| String a (String b (String c (String d t))) => String a (String b (String c (String d "")))
end.

Fixpoint is_num_this_string' (s:string) :=
match s with
| "" => true
| String "0"%char t => is_num_this_string' t
| String "1"%char t => is_num_this_string' t
| String "2"%char t => is_num_this_string' t
| String "3"%char t => is_num_this_string' t
| String "4"%char t => is_num_this_string' t
| String "5"%char t => is_num_this_string' t
| String "6"%char t => is_num_this_string' t
| String "7"%char t => is_num_this_string' t
| String "8"%char t => is_num_this_string' t
| String "9"%char t => is_num_this_string' t
| String "_"%char t => is_num_this_string' t
| _ => false
end.
Definition is_num_this_string (s:string) :=
match s with
| String "0"%char t => is_num_this_string' t
| String "1"%char t => is_num_this_string' t
| String "2"%char t => is_num_this_string' t
| String "3"%char t => is_num_this_string' t
| String "4"%char t => is_num_this_string' t
| String "5"%char t => is_num_this_string' t
| String "6"%char t => is_num_this_string' t
| String "7"%char t => is_num_this_string' t
| String "8"%char t => is_num_this_string' t
| String "9"%char t => is_num_this_string' t
| _ => false
end.
Definition isNum(s:string) := 
if (s =? "") then false
else
if ( (first4 s) =? "xInt" ) then true
else
is_num_this_string s .

Fixpoint have_it_symbol(c:ascii)(s:string) :=
match s with
| "" => false
| String h t => if (Nat.eqb (nat_of_ascii h) (nat_of_ascii c)) then true
                            else have_it_symbol c t
end.
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
Fixpoint semicolon_plus_newstring(sl:list string) :=
match sl with
| nil => nil
| ";" :: t => ";" :: newline :: tab :: (semicolon_plus_newstring t)
| "{" :: t => "{" :: newline :: tab :: (semicolon_plus_newstring t)
| "in" :: t => "in" :: newline :: tab :: (semicolon_plus_newstring t)
| ">>" :: t => ">>" :: newline :: tab :: (semicolon_plus_newstring t)
| "}" :: t => "}" :: newline :: tab :: (semicolon_plus_newstring t)

| h :: t => h :: (semicolon_plus_newstring t)
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
Fixpoint test_not_already_exists_for_list(st sl:list string) :=
match st with
| nil => true
| h :: t => if (test_already_exists h sl) then test_not_already_exists_for_list t sl
                                          else true
end.
Fixpoint for_lets(sl:list string) :=
match sl with
| nil => nil
| "(" :: "," :: t => "(" :: "_" :: "," :: (for_lets t)
| "," :: "," :: t => "," :: "_" :: "," :: (for_lets t)
| "," :: ")" :: t => "," :: "_" :: ")" :: (for_lets t)
| h :: t => h :: (for_lets t)
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

Fixpoint constructor_function(n:nat)(sl:list string) :=
match sl with
| nil => nil
| "constructor" :: "(" :: t => 
  "function" :: ( "Constructor"++(writeNat n) )%string :: "(" :: (constructor_function (S n) t)
| h :: t => h :: (constructor_function n t)
end.


Fixpoint require_correct(sl:list string) :=
match sl with
| nil => nil
| "require" :: "(" :: name :: n :: ")" :: ";" :: t => 
             "require" :: "(" :: name :: ")" :: n :: "??;;" :: (require_correct t)
| "require" :: "(" :: name :: ")" :: "," :: n :: ")" :: ";" :: t => 
             "require" :: "(" :: name :: ")" :: n :: "??;;" :: (require_correct t)

| "return!" :: "(" :: n :: ";" :: t => "return!" :: "(" :: n :: ")" :: ["."]

(* | h :: ":=" :: "{" :: t => if(h =? ")") 
                           then h :: ":=" :: "{" :: (require_correct t)
                           else if (have_it_symbol "164"%char h) 
                                then h :: ":=" :: "{" :: (require_correct t)
                                else h :: ")" :: ":=" :: "{" :: (require_correct t) *)
| h :: t => h :: (require_correct t)
end.
(* Braket omni tuple om lattice *)
Fixpoint make_lattice(sl:list string) :=
match sl with
| nil => nil
| ":" :: h :: ty :: "#" :: h1 :: ":=" :: t => 
  ":" :: h :: "(" :: ty :: "#" :: h1 :: ")" :: ":=" :: t
| ":" :: h :: ty :: "#" :: t => ":" :: h :: "(" :: ty :: "#" :: make_lattice t
| "#" :: ty :: ":=" :: t => "#" :: ty :: ")" :: ":=" :: t
| h :: t => h :: make_lattice t
end.

Fixpoint get_list_of_ids'(n:nat)(l:list string) :=
match l with
| nil => nil
| h1 :: "[" :: n1 :: "." :: n2 :: "]" :: "." :: h2 :: t =>
      ( ("t" ++ writeNat(n))%string, h1 :: "[" :: n1 :: "." :: n2 :: "]" :: "." :: [h2] ) 
      :: get_list_of_ids' (n+1) t

| h1 :: "[" :: nn :: "]" :: "." :: h2 :: t =>
      ( ("t" ++ writeNat(n))%string, h1 :: "[" :: nn :: "]" :: "." :: [h2] ) 
      :: get_list_of_ids' (n+1) t

| h1 :: "[" :: nn :: "]" :: t =>
      ( ("t" ++ writeNat(n))%string, h1 :: "[" :: nn :: ["]"]  ) 
      :: get_list_of_ids' (n+1) t

| h1 :: "." :: h2 :: "(" :: nn :: ")" :: t => 
      ( ("t" ++ writeNat(n))%string,  h1 :: "." :: h2 :: "(" :: nn :: [")"] ) 
      :: get_list_of_ids' (n+1) t

| h1 :: "(" :: nn :: ")" :: t => if(test_already_exists h1 separators)
                                 then get_list_of_ids' n t
                                 else
      ( ("t" ++ writeNat(n))%string,  h1 :: "(" :: nn :: [")"] ) 
      :: get_list_of_ids' (n+1) t

| h1 :: "." :: h2 :: t => if(h1 =? ")") 
      then                       get_list_of_ids' n t
      else
      ( ("t" ++ writeNat(n))%string, h1 :: "." :: [h2] ) 
      :: get_list_of_ids' (n+1) t

| h :: t =>  get_list_of_ids' n t
end.

Definition get_list_of_ids(sl:list(list string)) :=
let l := List.concat sl in
get_list_of_ids' 0 l.

Fixpoint get_exchs_of_ids'(n:nat)(l:list string) :=
match l with
| nil => nil
| h1 :: "[" :: n1 :: "." :: n2 :: "]" :: "." :: h2 :: t =>
      ("t" ++ writeNat(n))%string :: get_exchs_of_ids' (n+1) t

| h1 :: "[" :: nn :: "]" :: "." :: h2 :: t =>
      ("t" ++ writeNat(n))%string :: get_exchs_of_ids' (n+1) t

| h1 :: "[" :: nn :: "]" :: t =>
      ("t" ++ writeNat(n))%string :: get_exchs_of_ids' (n+1) t

| h1 :: "." :: h2 :: "(" :: nn :: ")" :: t => 
      ("t" ++ writeNat(n))%string :: get_exchs_of_ids' (n+1) t

| h1 :: "(" :: nn :: ")" :: t => if(test_already_exists h1 separators)
                                 then h1 :: "(" :: nn :: ")" :: get_exchs_of_ids' n t
                                 else
      ("t" ++ writeNat(n))%string :: get_exchs_of_ids' (n+1) t

| h1 :: "." :: h2 :: t => if(h1 =? ")") 
      then h1 :: "." :: h2 :: get_exchs_of_ids' n t
      else
      ("t" ++ writeNat(n))%string :: get_exchs_of_ids' (n+1) t 

| h :: t =>  h :: get_exchs_of_ids' n t
end.

Definition list_plus {X} (a b : list X) := b ++ a.

Fixpoint split_list(s:string)(acc l:list string) :=
match l with
| nil => nil
| h :: t => if(h =? s) then (acc++[newline]) :: split_list s [] t
                      else split_list s (acc++[h]) t
end.

Definition get_exchs_of_ids(sl:list(list string)) :=
let sl := map (list_plus ["КОНЕЦ"]) sl in
let l := List.concat sl in
let q := get_exchs_of_ids' 0 l in 
split_list "КОНЕЦ" [] q.

Fixpoint get_first_symbols_to_one (s:string):= true.

Definition delete_first_symbol(s:string) :=
match s with
| "" => ""
| String h t => t
end.
Fixpoint delete_first_symbols_include_determined_and_else_one(c s:string):=
match s with
| "" => ""
| String h t => let q := String h "" in
                if ( q =? c ) then delete_first_symbol t
                else delete_first_symbols_include_determined_and_else_one c t
end.

Compute (

let q := String "164"%char "" in


delete_first_symbols_include_determined_and_else_one q "DePoolContract_Ф_removeStake").

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

Fixpoint find_typelist(tl:list(string * list string))(s:string):=
match tl with
| nil => nil
| h :: t => if ( ( fst h ) =? s ) then snd h
                                  else find_typelist t s 
end.

Fixpoint newstringing_for_length (n:nat) (sl:list string) :=
match sl with
| nil => nil
| h :: t => let q := String.length h in
            let w := n + q in
            if ( w <? 52 ) then h :: newstringing_for_length w t
                           else h :: newline :: tab :: tab :: newstringing_for_length 0 t
end.


