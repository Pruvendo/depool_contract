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
Definition newline := "
" : string.
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
Definition headS {X} (x : list X) (d: X) :=
match (head x) with
| None => d
| Some x' => x'
end.
Definition next(l:list(list string)):=
match l with
| nil => ""
| h :: t => match h with
            | nil => headS (headS t nil) ""
            | h' :: t' => headS t' "" 
            end 
end.  

Fixpoint find_braket (n:Z) (sl:list string) :=
match sl with
| nil => nil 
| "{" :: t => "{" :: find_braket (n+1) t
| "}" :: t => if (Z.eqb n  0%Z) then "}" :: nil
                        else "}" :: find_braket (n-1) t
| h :: t => h :: find_braket n t 
end.

Fixpoint find_name (sl:list string) :=
match sl with
| nil => nil
| "{" :: t => find_braket (-1) sl
| h :: t => h :: find_name t
end.
Fixpoint get_interfaces (sl:list string) :=
match sl with
| nil => nil
| h :: t => match h with
            | "interface" => [h] ++ (find_name t) ++ (get_interfaces t)
            | _ => get_interfaces t
            end 
end.
Fixpoint get_contracts (sl:list string) :=
match sl with
| nil => nil
| h :: t => match h with
            | "contract" => [h] ++ (find_name t) ++ (get_contracts t)
            | _ => get_contracts t
            end 
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

Definition get_list_contracts (sl:list string) :=
let sl := concat_with " " sl in 
let sl := split_string sl "contract" in sl.

Definition headS'{X}(s:X)(l:list X) := headS l s.

Compute (
let s := "
integer a d c f g
///// sdkofjnsdfvdjeijvkedvjkemv ddfv

interface XP10 {
xp10 
xp10  xp10  xp10 
xp10 

/// xp10 xp10 xp10 xp10 xp10 xp10 
xp10 xp10 xp10 xp10 

}

asasasdasdasdasdsd xcvsvsv
sdcsdv
contract C000 { kjhjhkjhkjk kjjkjkjkkj }
////   asdasd

cfdfgdfgg
sdfsdfsdf dfvdf 
// sdfojsdfiojsdifjsidf
skdfmsdfmspdfspf ksdjfnsdjfn ksdjfnsdklnoasdfjspc nsdpfacjkpgicj
interface XP20 222 333 444 555 {
XP20
XP20
//o XP20
XP20
}
sdfjhsdufhsudhfujsdhfjsdhfjshndfjwsf

////
ljkhklj

contract C111 1 2 3 4 5 6 7 { sdfgg sdfgh }

klpaosudsyhiv


" in
let sl := split_string s newline in 
 let sl := map (split_string' " ") sl in 
 let sl := map clear_string_easy sl  in
let sl := clear_list_easy sl in
let sl := deleteComment sl in (* let sl := deleteComment2 sl in *)
 let sl := map (concat_with " " ) sl in 
 let sl := concat_with " "(* newline *) sl in 
let sl := split_string sl " " in  
(*вытаскиваем интерфейсы*)
let contracts := get_contracts sl in 
let sl := get_list_contracts contracts in 
let sl := clear_string_easy sl in
let sl := map clear_string_easy (map (split_string' " ") sl) in 
let names := map (headS' "") sl
in names).

Fixpoint set_records (names:list string) :=
match names with
| nil => nil
| h :: t => match h with
            | "" => set_records t
            | _ => newline :: "Record" :: (h++"P")%string :: (h++"C")%string :: set_records t
            end 
end.

Definition get_contract_interior (sl:list string) :=
let sl := tail (find_braket (-1) (tail sl)) in sl.

Definition shaper(s: string) := 
let sl := split_string s newline in 
 let sl := map (split_string' " ") sl in 
 let sl := map clear_string_easy sl  in
let sl := clear_list_easy sl in
let sl := deleteComment sl in (* let sl := deleteComment2 sl in *)
 let sl := map (concat_with " " ) sl in 
 let sl := concat_with " "(* newline *) sl in 
let sl := split_string sl " " in  
(*вытаскиваем интерфейсы*)
(* let interfaces := get_interfaces sl in let interfaces := concat_with " " interfaces in *)
(*вытаскиваем контракты*)
let contracts := get_contracts sl in 
let list_contracts := get_list_contracts contracts in 
let list_contracts := clear_string_easy list_contracts in
let list_contracts := map clear_string_easy (map (split_string' " ") list_contracts) in 
let names := map (headS' "") list_contracts in 
(* 1. делаем рекорды*)
let interiors := map get_contract_interior list_contracts in
let records := set_records names in

let sl := map (concat_with " " ) interiors in
concat_with " " sl(* records *).




(* let contracts := concat_with " " contracts in
( interfaces ++ "
" ++ contracts )%string.
 *)

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
