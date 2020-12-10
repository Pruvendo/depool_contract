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

Compute (map rename_numbers [ [ "1" ; "y" ; "234" ; "sdljkdfjn21"] ;
                              ["4" ; "5" ; "asdfsdf" ; "456g" ] ] ).

Inductive type_of_name :=
| NUMBER : type_of_name
| LOCAL  : type_of_name
| VAR    : type_of_name
| FUNf   : type_of_name
| NOTHING  : type_of_name.

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
| flase => NOTHING
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
 
Fixpoint array_2_mapping(sl:list string) :=
match sl with
| nil => nil
| typ :: "[" :: "]" :: name :: t => 
          "mapping" :: "(" :: "int" :: "=>" :: typ :: ")" :: name :: array_2_mapping t 
| h :: t => h :: array_2_mapping t
end.

Fixpoint get_to_sol(l:list(string*string))(fl:list string)(tl:list string) (sl:list string) :=
let fix delete_next_braket (l:list(string*string))(fl:list string)(tl:list string)(sl:list string) :=
match sl with
| nil => nil 
| ")" :: t => get_to_sol l fl tl t
| h :: t => h :: delete_next_braket l fl tl t
end in

let fix yes_function (f:bool)(l:list(string*string))(fl:list string)(tl:list string)(sl:list string) :=
match f , sl with
| _ , nil => nil
| true , ")" :: t => "()" :: get_to_sol l fl tl t
| true , h :: t => "(!" :: h :: yes_function false l fl tl t
| false , ")" :: t => "!)" :: get_to_sol l fl tl t
| _ , h :: t => h :: yes_function false l fl tl t
end in

let fix make_brace_ifs (l:list(string*string))(fl:list string)(tl:list string)(sl:list string) :=
match sl with
| nil => nil
| "{" :: t => "{" :: get_to_sol l fl tl t
(* when there arent braces *)
| ";" :: t => "}" :: get_to_sol l fl tl t
| h :: t => "{" :: h :: make_brace_ifs l fl tl t 
end in
 
let fix make_braket_ifs (n:nat)(l:list(string*string))(fl:list string)(tl:list string)(sl:list string) :=
match n , sl with
| _ , nil => nil
| 1  , ")" :: t => ")"         ::          make_brace_ifs l fl tl t
| n' , "(" :: t => "(" :: make_braket_ifs (n'+1) l fl tl t
| n' , ")" :: t => ")" :: make_braket_ifs (n'-1) l fl tl t
| _ , h :: t => h :: make_braket_ifs n l fl tl t
end in

match sl with
| nil => nil
| "if" :: "(" :: t => if (isElse t) then newline :: "Ife" :: "(" ::  make_braket_ifs 0 l fl tl t
                                    else newline :: "Ift" :: "(" ::  make_braket_ifs 0 l fl tl t
| "else" :: t => "else" :: make_brace_ifs l fl tl t

| "}" :: t => newline ::"}" :: newline :: get_to_sol l fl tl t

| ";" :: t => ">>" :: newline :: tab :: get_to_sol l fl tl t

| a :: "." :: b :: t => let q := (first2 a) in
                        if ( q =? "m_") then 
                                             let w := find_coq_name q l in
                                              w :: a :: "^^" :: b :: get_to_sol l fl tl t
                                        else  a :: "^^" :: b :: get_to_sol l fl tl t
| "address(0)" :: t => "xInt0" :: get_to_sol l fl tl t

| "Definition" :: h :: t => "Definition" :: h :: get_to_sol l fl tl t

| h :: "(" ::  t => if ( test_already_exists h tl )
                    then delete_next_braket l fl tl t
                    else if ( test_already_exists h fl )
                         then h :: yes_function true l fl tl t 
                         else h :: "(" :: get_to_sol l fl tl t

| h :: t => (* let q := first2 h in 
            if ( q =? "0x" )
            then ( writeNat ( get_hex2dec h ) ) :: get_to_sol l fl tl t
            else *) h :: get_to_sol l fl tl t
end. 
Check get_to_sol.
Definition if_who (a b : type_of_name) :=
match a, b with
| NUMBER, NUMBER => true
| LOCAL, LOCAL   => true
| VAR, VAR       => true
| FUNf, FUNf     => true
| NOTHING, NOTHING   => true
| _, _ => false
end.

Load "functions_operations2.v".

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

Definition header := "
Require Import Coq.Program.Basics.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.
Require Import FinProof.ProgrammingWith.

Local Open Scope record.
Local Open Scope program_scope. 

Require Import FinProof.Common.
Require Import FinProof.StateMonad2.


Require Import depoolContract.DePoolClass. 
Require Import depoolContract.SolidityNotations.
Require Import depoolContract.ProofEnvironment. 
Require Import depoolContract.DePoolSpec.

Module DePoolFuncs (xt: XTypesSig) (sm: StateMonadSig).

Module DePoolSpec := DePoolSpec xt sm.
Import DePoolSpec.
Import LedgerClass.
Import SolidityNotations.

Import xt. Import sm.

Set Typeclasses Iterative Deepening.
(*Set Typeclasses Depth 1.
Set Typeclasses Strict Resolution. *)
(* Set Typeclasses Debug.  *)
(* Set Typeclasses Unique Instances. 
Unset Typeclasses Unique Solutions. *)

(* Existing Instance monadStateT.
Existing Instance monadStateStateT. *)

Local Open Scope solidity_scope.
Local Open Scope string_scope.


(* 

UNCOMMENT THIS BLOCK AFTER VMState WOULD BE ADDED TO Ledger: *)

Definition setEventList l r := {$ r with VMState_ι_events := l $}.
(* Check setEventList. *)

Definition sendLedgerEvent (e: LedgerEventP) : LedgerT True :=
liftEmbeddedState ( T := T12 ) (modify (fun r => setEventList (xListCons e (VMState_ι_events r)) r) >> 
	  return! I ).
	  
Definition eventEqb (e1 e2: LedgerEvent): XBool := xBoolFalse.	  

Definition eventIn (e: LedgerEvent) : LedgerT XBool :=
↑  (embed_fun (fun r => xListIn eventEqb e (VMState_ι_events r))).

Definition getLastEvent : LedgerT (XMaybe LedgerEvent) :=
↑  (embed_fun (fun r => xListHead (VMState_ι_events r))).

Definition tvm_pubkey : LedgerT XInteger256 :=
  ↑returnε VMState_ι_pubkey.

Definition tvm_now : LedgerT XInteger64 :=
  ↑returnε VMState_ι_now.

Definition tvm_transfer (dest: XAddress) (value: XInteger256) 
  (bounce: XBool) (flags: XInteger8) 
  (payload: TvmCell) : LedgerT True := return! I.

Definition msg_pubkey : LedgerT XInteger256 :=
	↑returnε VMState_ι_msg_pubkey.

  (* sendLedgerEvent (TransactionSent 
(Transaction_ι_Transaction xInt0 xInt0 xInt0 xInt0 xInt0 xInt0 dest value flags payload bounce)) *)

(* Notation "" tx '->transfer' "" := (sendLedgerEvent (TransactionSent tx) >> 
		   tvm_transfer (tx ->> dest_ι_Transaction) (tx ->> value_ι_Transaction)
						(tx ->> bounce_ι_Transaction) (tx ->> sendFlags_ι_Transaction)
						(tx ->> payload_ι_Transaction)) (at level 60, tx constr, right associativity): solidity_scope.
 *)
Definition tvm_accept : LedgerT True := return! I.
Definition tvm_transLT : LedgerT XInteger64 := ↑returnε VMState_ι_ltime.

Definition tvm_setcode (newcode : TvmCell) : LedgerT True := (↑ <! VMState_ι_code <- newcode  !>) >> return! I.
Definition tvm_setCurrentCode (newcode : TvmCell) : LedgerT True :=  return! I.

(* Definition tvm_ignore_integer_overflow: LedgerT True := return! I. *)
Definition tvm_tree_cell_size (slice: TvmSlice) : LedgerT (XInteger # XInteger) := return! [(xInt0, xInt0)].
Definition tvm_ctos (cell : TvmCell): LedgerT TvmSlice := return! xStrNull. 
Definition tvm_reset_storage: LedgerT True :=  <! Ledger_ι_DePoolContract <- default  !> >> return! I.
Definition tvm_hash (cellTree: TvmCell) : LedgerT XInteger256 := return! xInt0. 
Definition tvm_rawConfigParam (x:XInteger) : LedgerT (XInteger # XInteger) := return! [(xInt0, xInt0)]. 

(*our stub: doesn't exists in TVM*)
(*actual call is uint128(address(this).balance);*)
Definition tvm_get_balance : LedgerT XInteger128 := ↑returnε VMState_ι_balance. 

Definition tvm_commit: LedgerT True :=
do l ← get;
put {$l with Ledger_ι_VMState := {$Ledger_ι_VMState l with VMState_ι_savedDePoolContract := Ledger_ι_DePoolContract l $}$};
void!.

Definition tvm_restore: LedgerT True :=
do l ← get;
put {$l with Ledger_ι_DePoolContract := VMState_ι_savedDePoolContract (Ledger_ι_VMState l) $};
void!.

Definition callDePool {X E} (m: LedgerT (XErrorValue X E)) : LedgerT (XErrorValue X E) :=
tvm_commit >> 
m >>= fun ea => xErrorMapDefaultF (fun a => return! (xValue a)) ea (fun er => tvm_restore >> return! (xError er)).


(* These functions doesn't need proof *)
(*DELETE THIS AFTER  PREVIOUS BLOCK WOULD BE UNCOMMENTED*)
(* Definition msg_pubkey : XInteger := xInt0.
Definition tvm_pubkey : XInteger := xInt0.
Definition tvm_pubkey1 ( x : XInteger ) : XInteger := xInt0.
Definition tvm_accept : LedgerT True := return! I.
Definition tvm_commit : LedgerT True := return! I.
Definition tvm_setcode ( x : TvmCell ) : LedgerT True := return! I.
Definition tvm_setCurrentCode ( x : TvmCell ) : LedgerT True := return! I. *)
(*********************************************************)


Set Typeclasses Iterative Deepening.
Set Typeclasses Depth 10.


".

Definition footer := 
"
End DePoolFuncs.
".




Fixpoint prepare_tuple(tl:list(string*string)):=
match tl with
| nil => nil
| h :: t => let q := get_first_symbols_to_ ( fst h ) in
            let w := snd h in
            ( q , w ) :: prepare_tuple t
end.

Fixpoint get_list_of_tuple( fl : list ( string * nat * ( list string ) ) ):=
match fl with
| nil => nil
| h :: t => let q := fst ( fst h ) in q :: get_list_of_tuple t
end.
(* Return nat *)
Compute ( snd ( 1 , 2 , 3 ) ).
Fixpoint get_trd(s:string)( fl : list ( string * nat * ( list string ) ) ):=
match fl with
| nil => nil
| h :: t => let q := fst ( fst h ) in
            if ( q =? s ) 
            then snd h
            else get_trd s t 
end.
Fixpoint get_snd(s:string)( fl : list ( string * nat * ( list string ) ) ):=
match fl with
| nil => 0
| h :: t => let q := fst ( fst h ) in
            if ( q =? s ) 
            then snd ( fst h )
            else get_snd s t 
end.
Check ( 1 <? 2).
Fixpoint delete_double_functions ( fl : list ( string * nat * ( list string ) ) ) 
                                    (sl:list(list string)) :=
match sl with
| nil => nil
| h :: t => match h with
  | nil => delete_double_functions fl t
  | "Definition" :: name :: t' => 
           let q := get_list_of_tuple fl in
           let w := List.length t' in
           if ( test_already_exists name q )
                 then delete_double_functions fl t
                 else let u := ( name , w , t' ) in
                      ("Definition" :: name :: t') :: delete_double_functions (u::fl) t

  | h' :: t' => h :: delete_double_functions fl t
  end
end.

Fixpoint Interface_list (sl:list string) :=
match sl with
| nil => nil
| "interface" :: name :: t => name :: Interface_list t
| h :: t => Interface_list t
end.

Fixpoint library_list (sl:list string) :=
match sl with
| nil => nil
| "library" :: name :: t => name :: library_list t
| h :: t => library_list t
end.

Fixpoint Interface_prepare(f:bool)(il:list string)(sl:list string):=
match f, sl with
| _, nil => nil
| true, ">>" :: t => "*)" :: Interface_prepare false il t
| true, ";" :: t => "*)" :: Interface_prepare false il t
| true , "." :: t => "*)" :: "." :: Interface_prepare false il t
| false, h :: t => if ( test_already_exists h il ) 
                   then "(*" :: h :: Interface_prepare true il t
                   else h :: Interface_prepare f il t
| _, h :: t => h :: Interface_prepare f il t
end.

Definition shaper(s: string) := let s:= clearComment1 false (clearComment false (setSpace s)) in 
let sl := split_string' newline s in 
let sl := map (split_string' " ") sl in 
let sl := map clear_string_easy sl  in
let sl := clear_list_easy sl in
let sl := deleteComment sl in 
let sl := List.concat sl in let sl := array_2_mapping sl in

let il := Interface_list sl in let ll := library_list sl in

(* concat name [ ] *)
let sl := concat_sq_brakets sl in 
                                                            (* *** *)
(* 'constructors' to 'function ConstructorsN'  *)
let sl := constructor_function 1 sl in
(* Adding modifier to functions's bodies *)
let sl := add_modifiers_to_functions sl in

let orig_text_funcs_list := get_orig_text_funcs_list "" sl in (*[[[[[[[[[[[[[[[[[[[[[[[[[*)

(* Here are global vars from contracts including structs *)
let vars_list := List.concat (make_contracts_v sl) in                  
let vars_list := clean_vars_list vars_list in
(* Building list of functions *) 
let funcs_list := functions_list "" sl in  
let struct_list := structs_list "" sl in
let consts_list := const_list "" sl in           (*  tuple_outing funcs_list. *)

let number_contracts := numering_not_empty_contracts 1 sl in (* tuple_outing number_contracts. *)
let number_contracts := prepare_tuple number_contracts in 
let numbers_contract_vars := numering_contract_vars sl in       (*  tuple_outing numbers_contract_vars. *)
 
(* definition right order functions for eval *)
(* let right_order := function_order sl in *)  (*\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\*)

let all := make_contracts sl in   

let sl :=  List.concat all in 
 
let sl := add_list_func_type sl in                          (* *** *)

let qq := clear_list_easy sl in 
 
let ff := map (renaming_local_vars) qq in
let ff := map (back_local_vars) ff in

(* functions renaming *)                                               (* *** *)
let ww := map (rename_sol2coq1 "" funcs_list)        ff in  


(* vars renaming *)
let aa := map (m_renaming vars_list) ww in
let aa' := map (else_renaming vars_list)         aa in    
(* Struct name as type renaming *) 
let bb := map (rename_sol2coq struct_list)       aa' in                 (* ** *)
 
let bb := map ( concat_op_equ ll ) bb in

let bb' := map (rename_sol2coq consts_list) bb in 
(* clearing for local variable declarations *)
let cc1 := map prepare_function_type_var bb' in  
let cc2 := map (delete_mapping false) cc1 in   
let cc3 := map rename_tvm_some cc2 in

(* all numbers to Coq format *)   
let dd := map rename_numbers cc3 in                                     (* ** *)

let dd := map split_iterior_members_list dd in   

  (* ** *)
let types := add_exist_types [] in

let funcs := map snd funcs_list in

let dd := map ( get_to_sol numbers_contract_vars funcs types ) dd in                         (* -- ^^ -- *)

 let dd := map delete_some dd in

let dd := map work_operations dd in                 (* ** *)

let dd := map prepare_easy_funcs dd in
 
let dd := delete_double_functions [] dd in                                 (* ** *)
 
                     let dd := map ( Interface_prepare false il ) dd in
 
let dd := map (repair_msg_point "msg_sender") dd in
let dd := map (repair_msg_point "msg_value") dd in 

let dd := map ( add_lift_to_vars number_contracts ) dd in

let dd := map all_end_prepare dd in

let dd := rigth_order_funcs [] dd dd in

let dd := map make_tuple_braket dd in


let dd := map analisys_for_returns dd in
let dd := map repair_require dd in
let dd := map repair_return dd in

                                      let dd := map dotted_prepare dd in

let digits_list := get_digits_list dd in

let dd := add_orig_funcs_texts orig_text_funcs_list dd in 

( digits_list ++  header ++ concat_with newline ( map ( concat_with " " ) dd ) ++ footer )%string. 

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








(*Fixpoint delete_double_functions ( fl : list ( string * nat * ( list string ) ) ) 
                                    (sl:list(list string)) :=
match sl with
| nil => nil
| h :: t => match h with
  | nil => delete_double_functions fl t
  | "Definition" :: name :: t' => 
           let q := get_list_of_tuple fl in
           let w := List.length t' in
           if ( test_already_exists name q )
           then let e := get_snd name fl in
                if ( e <? w ) 
                then let r := ( name , w , t' ) in
                     ("Definition1" :: name :: t') :: delete_double_functions (r::fl) t
                else let y := get_trd name fl in
                     ("Definition2" :: name :: y) :: delete_double_functions fl t
           else let u := ( name , w , t' ) in
                ("Definition3" :: name :: t') :: delete_double_functions (u::fl) t

  | h' :: t' => ("4"::h) :: delete_double_functions fl t
  end
end.*)



(* Fixpoint get_to_sol( l:list(string * string ) ) (sl:list string) :=
match sl with
| nil => nil
| "(" :: ")" :: t => "()" :: get_to_sol l t
| "if" :: "(" :: t => if (isElse t) then newline :: "Ife" :: "(" ::  get_to_sol l t
                                    else newline :: "Ift" :: "(" ::  get_to_sol l t
| "else" :: t => "else" :: get_to_sol l t

| h :: "(" :: t => let q := add_exist_types [] in
                   if ( test_already_exists h q )
                   then get_to_sol l t




"(!" :: get_to_sol l t
| ")" :: "{" :: t => ")" :: "{" :: get_to_sol l t
| ")" :: t => "!)" :: get_to_sol l t
| "{" :: t => newline ::"{" :: newline :: get_to_sol l t
| "}" :: t => newline ::"}" :: newline :: get_to_sol l t
| ";" :: t => ">>" :: newline :: tab :: get_to_sol l t
| a :: "." :: b :: t => let q := (first2 a) in
                        if ( q =? "m_") then 
                                             let w := find_coq_name q l in
                                              w :: a :: "^^" :: b :: get_to_sol l t
                                        else  a :: "^^" :: b :: get_to_sol l t
| "address(0)" :: t => "xInt0" :: get_to_sol l t
| h :: t => h :: get_to_sol l t
end. 
Check get_to_sol. *)