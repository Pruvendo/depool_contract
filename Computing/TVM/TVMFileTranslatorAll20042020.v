(* Require Export TVMCommands. *)
Require Import Coq.Lists.List. 
Require Import Io.All.
Require Import Io.System.All.
Require Import ListString.All.
Require Import Ascii.
Require Import String.
Require Import Strings.String. 
Import ListNotations.
Import C.Notations.

Require Export DataBase.
 
Require Import CommonHelpers.

Require Import StringHelpers.
 
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition header := 
"Require Export TVMModel.MonadState.TVMCommands.
Require Export TVMModel.MonadState.Common.
Require Import TVMModel.MonadState.MultisigGlobalVars.
Require Import TVMModel.MonadState.MultisigInitialState.
Require Import TVMModel.MonadState.TVMMonadState.
Require Import TVMModel.Base.Definitions.TVMHashmap.

Require Import TVMModel.Base.Definitions.TVMBit.
Require Import TVMModel.Base.Proofs.Basic.
Require Import TVMModel.Base.Definitions.StateTransforms.
Require Import TVMModel.Base.Proofs.TVMBitString_assoc.
Require Import TVMModel.Base.Proofs.TVMIntN.
Require Import TVMModel.Base.Proofs.TVMHashmap_axioms.
Require Import FinProof.Common.

Require Import FinProof.StateMonad6.
Require Import FinProof.StateMonad6Instances.
Require Import TVMModel.Computing.InitialState.
Import BitStringBinaryNotations.
Local Open Scope record.
(* From elpi Require Import elpi. *)
Require Import TVMModel.Computing.StandardBlock.

Section TVMComputing.
(* Load ""variables.v"". *)


".

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

Fixpoint findNewLine (l:list ascii):list ascii :=
match l with
| nil => nil
| h :: t => match h with
            | "
"%char => h :: t
            | _ => findNewLine t
            end
end.

Fixpoint erase_blank_str (l: list string) : list string :=
match l with
| nil => nil
| h :: t => if (isBlank h) then erase_blank_str t else cons h (erase_blank_str t)
end.

Fixpoint erase_start_blank (s : string ) : string :=
match s with
| EmptyString  => ""
| String " "%char t => erase_start_blank t
| String "009"%char t => erase_start_blank t
| String h t => String h t
end.

Definition quote := "034"%char.

Definition to_quotes (s:string):string :=
  ( String quote s ) ++ ( String quote " " ).

Compute (to_quotes "dfgdg xcbdvd ").

Definition headS {X} (x : list X) (d: X) :=
match (head x) with
| None => d
| Some x' => x'
end.

Fixpoint eraseComm (l:list(list string)):=
match l with
| [ ] => [ ]
| h :: t => match h with
            | [ ] => eraseComm t
            | h' :: t' => match h' with
                          | String ";"%char t'' => eraseComm t
                          | _ => cons h (eraseComm t)
                          end
            end 
end.

Fixpoint eraseComm' (l:list string):=
match l with
| [ ] => [ ] 
| h :: t => match h with
            | String ";"%char t' => [ ]
            | _ => cons h (eraseComm' t)
            end
end.

Fixpoint eraseBlank (l:list(list string)):=
match l with
| [ ] => [ ]
| [ ] :: t => eraseBlank t
| h :: t  => cons h ( eraseBlank t )
end.

Fixpoint pureCmd (s:string):=
match s with
| EmptyString => ""
| String " "%char t => pureCmd t
| String "009"%char t => pureCmd t
| _ => s
end.

Fixpoint addExec_ (l:list string):=
match l with 
| [ ] => [ ] 
| h :: t => let purecmd := (pureCmd h) in
            match (length purecmd) with
            | 1 => cons h t
            | _ => cons (append "Exec_" purecmd) t
            end
end.  

Fixpoint eraseComma (s : string):=
match s with
| "" => ""
| String "," t => ""
| String h t => String h (eraseComma t)
end.

Compute (eraseComma "s4,").
 
Definition xchgInstr (l:list string):=
match l with 
| [ ] => [ ] 
| h :: t => let purecmd := (pureCmd h) in
            match purecmd with
            | "Exec_PUSHCONT" => ["let" ; "a1" ; ":=" ; "("] 
            
            | "Exec_IF" => ["tvm_ifelse" ; "a1" ; "(return! I)" ;    "." ]
            | "Exec_IFELSE" => ["tvm_ifelse" ; "a1" ; "a2" ;         "." ]
            | "Exec_CALLX" => ["tvm_call_inline"; "a1"]
            | "Exec_UNTIL" => ["tvm_until" ; "a1" ]
            | "Exec_WHILE" => ["tvm_while" ; "a1" ; "a2" ]
            | "}" => [")" ; "in"]

            | "Exec_CALL" => cons "tvm_call_inline" t
            | "Exec_THROWIF" => cons "Exec_THROWIFz" t
            | "Exec_THROWIFNOT" => cons "Exec_THROWIFNOTz" t
            | "Exec_PUSHINT" => cons "Exec_PUSHINTz" t
            | "Exec_LDSLICE" => cons "Exec_LDSLICEz" t
            | "Exec_BLKDROP" => cons "Exec_BLKDROPz" t
            | "Exec_PLDU" => cons "Exec_PLDU'z" t
            | "Exec_LDU" => cons "Exec_LDU'z" t
            | "Exec_PLDI" => cons "Exec_PLDI'z" t
            | "Exec_NEQINT" => cons "Exec_NEQINTz" t
            | "Exec_BLKSWAP" => cons "Exec_BLKSWAPz" (map eraseComma t)
            | "Exec_STUR" => cons "Exec_STUR'z" t
            | "Exec_STU" => cons "Exec_STU'z" t
            | "Exec_LDI" => cons "Exec_LDI'z" t
            | "Exec_INDEX" => cons "Exec_INDEXz" t
            | "Exec_PLDREFIDX" => cons "Exec_PLDREFIDXz" t
            | "Exec_REVERSE" => cons "Exec_REVERSEz" t
            | "Exec_UFITS" => cons "Exec_UFITS'z" t
            | "Exec_PUSHPOW2DEC" => cons "Exec_PUSHPOW2DECz" t
            | "Exec_EQINT" => cons "Exec_EQINTz" t
            | "Exec_STI" => cons "Exec_STI'z" t
            | "Exec_STIR" => cons "Exec_STIR'z" t
            | "Exec_LESSINT" => cons "Exec_LESSINTz" t
            | "Exec_GETPARAM" => cons "Exec_GETPARAMz" t
            | "Exec_PUSH" => cons "Exec_PUSHs" t
            | "Exec_PUSHCTR" => cons "Exec_PUSHCTRs" t
            | "Exec_POP" => cons "Exec_POPs" t
            | "Exec_POPCTR" => cons "Exec_POPCTRs" t
            (* | "Exec_XCHG" => cons "Exec_XCHGs" t *)
            | "Exec_PUSHSLICE" => cons "Exec_PUSHSLICEs" (map to_quotes (map eraseComma t))
            | "Exec_THROWNOT" => cons "Exec_THROWNOTz" t

            | "Exec_CTOS" => cons "Exec_CTOS'" t
            | "Exec_DICTUGETREF" => cons "Exec_DICTUGETREF'" t
            | "Exec_DICTUSETREF" => cons "Exec_DICTUSETREF'" t
            | "Exec_DICTUGET" => cons "Exec_DICTUGET'" t
            | "Exec_SDSKIPFIRST" => cons "Exec_SDSKIPFIRST'" t
            | "Exec_SSKIPFIRST" => cons "Exec_SSKIPFIRST'" t
            | "Exec_STSLICER" => cons "Exec_STSLICER'" t
            
            | "Exec_Definition" => cons "Definition" t

            | "Exec_BLKPUSH" => cons "Exec_BLKPUSHzz" (map eraseComma t)
            | "Exec_GETGLOB" => cons "Exec_GETGLOBz"  (map eraseComma t)
            | "Exec_SETGLOB" => cons "Exec_SETGLOBz"  (map eraseComma t)
            | "Exec_SETINDEX" => cons "Exec_SETINDEXz" (map eraseComma t)
            | "Exec_STSLICECONST" => cons "Exec_STSLICECONSTz" (map eraseComma t)
            | "Exec_UNTUPLE" => cons "Exec_UNTUPLEz" (map eraseComma t)
            | "Exec_TUPLE" => cons "Exec_TUPLEz" (map eraseComma t)
            | "Exec_LDUQ" => cons "Exec_LDUQz" (map eraseComma t)

            | "Exec_PUSH2" => cons "Exec_PUSH2ss" (map to_quotes (map eraseComma t))
            | "Exec_PUSH3" => cons "Exec_PUSH3sss" (map to_quotes (map eraseComma t))
            | "Exec_XCHG"  => cons "Exec_XCHGs" (map to_quotes (map eraseComma t))
            | _ => l
            end
end.

Definition numberAdding (l:list string) :=
match l with
| [ ] => [ ] 
| h :: t => match (headS t "") with
            | EmptyString => l
            | "x8000000000000000000000000000000000000000000000000000000000000000001_" => [ h ; (String "034"%char ("x8000000000000000000000000000000000000000000000000000000000000000001_"++ (String "034"%char "") ) ) ]
            | "$submitTransaction$" => [ h ;  "993789643" ; ">>"]
            | "$getLimitIds$" => [ h ;  "926064552" ]
            | "$confirmTransaction$" => [ h ;  "777931709" ]
            |"$getTransactionIds$" => [ h ;  "567256068" ]
            |"$deleteLimit$" => [ h ;  "744515807" ]
            |"$executeUpdate$" => [ h ;  "257535241" ]
            |"$changeLimit$" => [ h ;  "916704511" ]
            |"$createPeriodicLimit$" => [ h ;  "1292964046" ]
            |"$constructor$" => [ h ;  "1971552448" ]
            |"$getCustodians$" => [ h ;  "637820572" ]
            |"$getLimit$" => [ h ;  "1798522630" ]
            |"$fallback$" => [ h ;  "1551819271" ]
            |"$confirmLimit$" => [ h ;  "1323660935" ]
            |"$acceptTransfer$" => [ h ;  "13175674" ]
            |"$getTransaction$" => [ h ;  "89706758" ]
            |"$getLimitConfirmationCount$" => [ h ;  "943494421" ]
            |"$TransferAccepted$" => [ h ;  "3930078345" ]
            |"$getLimitCount$" => [ h ;  "292260382" ]
            |"$onBounce$" => [ h ;  "40" ]
            |"$confirmUpdate$" => [ h ;  "916166115" ]
            |"$submitUpdate$" => [ h ;  "1301588124" ]
            |"$sendTransaction$" => [ h ;  "287282869" ]
            |"$createOperationLimit$" => [ h ;  "26870019" ]
            |"$getCustodianCount$" => [ h ; "52735650" ] 

            | "$LimitOverrun$" => [ h ; "23042020"]
            | _ => l
            end
end.

Fixpoint cutLast{X}(sl:list X) :=
match sl with
| nil => nil
| h :: nil => nil
| h :: t => h :: (cutLast t)
end.

Compute (cutLast ["1";"last";"first"]).

Fixpoint pasteGtGT (l:list (list string)) :=
let llast  := last (headS l [ ]) "" in
let lfirst := headS (headS (tail l) [ ] ) "" in 
match l with
| [ ] => [ ]
| h :: t => match llast , lfirst with
            | "" , _  => [ ]
            |  _ , "" => h :: [ ]
            | ":=", _ => cons h (pasteGtGT t)
| ".", "Definition" => ((cutLast h)++[">>"]++["return!"]++["I"]++["."])::(pasteGtGT t)
            | ".", "let" => ((cutLast h) ++ [">>"]) ::  (pasteGtGT t)
            | _, "Definition" => (h ++ ["."]) ::  (pasteGtGT t)
            | ".", _ => cons h (pasteGtGT t)
            | "in", _ => cons h (pasteGtGT t)
            | _ ,")" => cons h (pasteGtGT t)
            | "(" , _=> cons h (pasteGtGT t)
            | _ , _   => (h ++ [">>"]) :: (pasteGtGT t) 
           end
end.

Fixpoint paste_a1a2 (l:list (list string)) :=
let llast  := last (headS l [ ]) "" in
let lfirst := headS (headS (tail l) [ ] ) "" in 
match l with
| [ ] => [ ]
| h :: t => match llast , lfirst with
            | "in", "let" => h :: ["let" ; "a2" ; ":=" ; "("] :: (tail (paste_a1a2 t))
            | _ , _   => h ::  (paste_a1a2 t) 
           end
end.

Definition digit2nat (n : ascii) : nat :=
  match n with
    | "0"%char => 0
    | "1"%char => 1
    | "2"%char => 2
    | "3"%char => 3
    | "4"%char => 4
    | "5"%char => 5
    | "6"%char => 6
    | "7"%char => 7
    | "8"%char => 8
    | "9"%char => 9
    | _        => 10
  end.
 
Definition str2nat (s:string) : nat :=
  match s with
    | "0" => 0
    | "1" => 1
    | "2" => 2
    | "3" => 3
    | "4" => 4
    | "5" => 5
    | "6" => 6
    | "7" => 7
    | "8" => 8
    | "9" => 9
    | _   => 10
  end.
 
Definition nat2str (n : nat) : string := writeNat n.
 
Fixpoint isNumber(s:string):=
match s with
| EmptyString => false
| String h "" => if ( Nat.ltb (digit2nat h) 10) then true else false
| String h t =>  if (Nat.ltb (digit2nat h)  10) then isNumber t else false
end.

Definition quoteReg (s:string):=
match s with
| EmptyString => ""
| String "S"%char t => if (isNumber t) then (String "034"%char ( s ++ (String "034"%char "") ) ) else s
| String "s"%char t => if (isNumber t) then (String "034"%char ( s ++ (String "034"%char "") ) ) else s
| String "C"%char t => if (isNumber t) then (String "034"%char ( s ++ (String "034"%char "") ) ) else s
| String "c"%char t => if (isNumber t) then (String "034"%char ( s ++ (String "034"%char "") ) ) else s
| _ => s
end.

Definition quotation (l:list string) := map quoteReg l.

Definition quoteXCHG(l:list string):=
match l with
| [ ] => [ ] 
| "Exec_XCHGs" :: t => let a := headS t "" in ["Exec_XCHGs" ; (String "034"%char ( a ++ (String "034"%char "") ) ) ]
| _ => l
end.

Definition minusBraketation (s:string):=
match s with
| "" => ""
| String "-" t => (String "("%char ( s ++ (String ")"%char "") ) )
| _ => s
end.

(* Делим на части в зависимости от условных операторов *)
Fixpoint cut_by_if (n:nat)(fn:string)(sl:list(list string)) := 
match sl with 
| nil => [ [""] ]
| h :: t => match h with
            | nil => h :: (cut_by_if n fn t)
            | h' :: t' => match h' with
                          | "let" => match t' with
                                     | nil => h :: (cut_by_if n fn t)
                                     | "a01" :: t'' => 
          ( (fn++(nat2str n)++".

"++"Definition "++fn++(nat2str n)++" :=
 ")%string :: h) :: (cut_by_if (S n) fn t)
                                     | _ => h :: (cut_by_if n fn t)
                                     end
                          | _ => h :: (cut_by_if n fn t)
                          end
            end
end.

(* Ставим функции в обратной последовательности для вызовов *)
Definition twist (s:string) :=
let codeSplitted := split_string s "Definition" in
let sl := rev codeSplitted in
concat_with "Definition " sl.

Definition firstUp (l:list string) :=
match l with
| nil => nil
| "PUSHCONT" :: t => "-PUSHCONT" :: t
| _ => l
end.

Fixpoint counter2in' (n:nat)(s:string) :=
match s with
| "" => nil
| String "009"%char t => counter2in' (S n) t
| String h t          => (nat2str n) :: (String h t) :: nil
end.

Definition counter2in (sl:list string) :=
 (counter2in' 1 (headS sl "")) ++ (tail sl).

Definition pushcontUpNumber (sl:list string) :=
match sl with
| nil => nil
| h :: t => match t with
            | nil => nil 
            | h' :: t' => match h' with
                          | "" => nil
                          | ";" => nil
                          | ";;" => nil
                          | "PUSHCONT" => (nat2str (S (str2nat h))) :: t
                          | "}" => (nat2str (S (str2nat h))) :: t
                          | "IF" => (nat2str (S (str2nat h))) :: t
                          | "IFNOT" => (nat2str (S (str2nat h))) :: t
                          | "IFELSE" => (nat2str (S (str2nat h))) :: t
                          | "UNTIL" => (nat2str (S (str2nat h))) :: t
                          | "IFJMP" => (nat2str (S (str2nat h))) :: t
                          | "WHILE" => (nat2str (S (str2nat h))) :: t
                          | "CALLX" => (nat2str (S (str2nat h))) :: t
                          | "CONDSEL" => (nat2str (S (str2nat h))) :: t
                          | "JMPX" => (nat2str (S (str2nat h))) :: t
                         (*  | "WHILE" => (nat2str (S (str2nat h))) :: t
                          | "WHILE" => (nat2str (S (str2nat h))) :: t
                          | "WHILE" => (nat2str (S (str2nat h))) :: t
                          | "WHILE" => (nat2str (S (str2nat h))) :: t
                          | "WHILE" => (nat2str (S (str2nat h))) :: t
                          | "WHILE" => (nat2str (S (str2nat h))) :: t *)
                          | _ => sl
                          end
            end
end.

Check Nat.eqb.
(* Находим максимальную глубину *)
Fixpoint analizer (m:nat) (sl:list(list string)) := 
match sl with
| nil => m
| h :: t => match h with
            | nil => m
            | h' :: t' => let nn:=(str2nat h') in 
                          if (Nat.ltb nn 10) then (
                            if (Nat.eqb m nn) then analizer m t
                       else if (Nat.ltb nn m) then analizer m t
                                          else analizer nn t  
                                              )
                                         else analizer m t
            end
end.

(* Именуем как функции, так и их вызовы *)
Fixpoint namenator'(n:nat)(fn:string)(sl:list(list string)) :=
let c := str2nat ( headS (headS (sl) nil ) "" ) in 
let nn := str2nat ( headS (headS (tail sl) nil ) "" ) in
if ( Nat.ltb c nn ) then match sl with (* текущее меньше следующего *)
                        | nil => nil
                        | h :: t => 
          let fnn := (fn ++ (nat2str n))%string in
(h++[(newline++(nat2str c)++" ъ"++fnn++newline++
    newline)%string ; (nat2str nn) ;"Definition";fnn;":="])

(* (h++[(newline++(nat2str c)++" ъ"++fnn++newline++
    newline++(nat2str nn) ++" Definition "++fnn++" := ")%string]) *)
                                                       :: namenator' (S n) fn t
                        end 
                   else
if ( Nat.ltb nn c ) then match sl with (* текущее больше следующего *)
                        | nil => nil
                        | h :: t => (h++["."]++[newline]) :: namenator' n fn t
                        end 
                   else match sl with (* текущее = следующеmy *)
                        | nil => nil
                        | h :: t => h :: namenator' n fn t
                        end.
Check namenator'.
Definition namenator(fn:string)(sl:list(list string)) :=
["1";"Definition";fn;":="]::(namenator' 1 fn sl).

Compute ((*concat_with newline ( map (concat_with " " ) *)(namenator "qwerty"
[ 
["1" ; "g" ; "c6"] ;
["2" ; "2" ; "c6"] ;
["2" ; "3" ; "c6"] ;
["2" ; "4" ; "c6"] ;
["2" ; "5" ; "c6"] ;
["2" ; "6" ; "c6"] ;
["3" ; "7" ; "c6"] ;
["3" ; "8" ; "c6"] ;
["3" ; "9" ; "c6"] ;
["3" ; "0" ; "c6"] ;
["2" ; "a" ; "c6"] ;
["2" ; "b" ; "c6"] ;
["2" ; "c" ; "c6"] ;
["1" ; "d" ; "c6"] ;
["1" ; "e" ; "c6"] ;
["1" ; "f" ; "c6"] ;
["2" ; "g" ; "c6"] ;
["2" ; "h" ; "c6"] ;
["3" ; "i" ; "c6"] ;
["3" ; "g" ; "c6"] ;
["3" ; "k" ; "c6"] ;
["2" ; "l" ; "c6"] ;
["1" ; "m" ; "c6"] ;
["1" ; "n" ; "c6"] 
]
)).

Compute (analizer 0 [ [ "1" ; "fvdfv"] ; ["3";"jkjhk"] ; ["1" ; "dfg" ] ; ["sc";""]  ; ["3"]] ).
(* Cоставляем строки с заданной глубиной m *)
Fixpoint strDeeper'(m:nat)(sl:list(list string)) :=
let c := str2nat ( headS (headS (sl) nil ) "" ) in 
let nn := str2nat ( headS (headS (tail sl) nil ) "" ) in 
if (Nat.eqb c m) then match sl with (* если равны - всё присваиваем *)
                      | nil => nil
                      | h :: t => h :: (strDeeper' m t)
                      end 
                 else
(* if (Nat.ltb c m) then nil *) (* если текущее меньше заданого - щем следующее *) 
                 (* else *) match sl with (* если текущее больше заданого - идём далее *)
                      | nil => nil
                      | h :: t => strDeeper' m t
                      end.
 
Compute (analizer 0 [ 
["1" ; "g" ; "c6"] ;
["2" ; "2" ; "c6"] ;
["2" ; "3" ; "c6"] ;
["2" ; "4" ; "c6"] ;
["2" ; "5" ; "c6"] ;
["2" ; "6" ; "c6"] ;
["3" ; "7" ; "c6"] ;
["3" ; "8" ; "c6"] ;
["4" ; "88"] ;
["3" ; "9" ; "c6"] ;
["3" ; "0" ; "c6"] ;
["2" ; "a" ; "c6"] ;
["2" ; "b" ; "c6"] ;
["2" ; "c" ; "c6"] ;
["1" ; "d" ; "c6"] ;
["1" ; "e" ; "c6"] ;
["1" ; "f" ; "c6"] ;
["2" ; "g" ; "c6"] ;
["2" ; "h" ; "c6"] ;
["3" ; "i" ; "c6"] ;
["3" ; "g" ; "c6"] ;
["3" ; "k" ; "c6"] ;
["2" ; "l" ; "c6"] ;
["1" ; "m" ; "c6"] ;
["1" ; "n" ; "c6"] 
]).

(* Ищем ПЕРВОЕ втречаемое с заданным номером *)
Fixpoint strDeeper''(m:nat)(sl:list(list string)) :=
let c := str2nat ( headS (headS (sl) nil ) "" ) in 
if (Nat.eqb c m) then match sl with (* если равны - возвращаем *)
                      | nil => nil
                      | h :: t => sl
                      end 
                 else match sl with (* если не равны - ищем далее *)
                      | nil => nil
                      | h :: t => strDeeper'' m t
                      end.
(*  
Compute (let s:= concat_with newline ( map (concat_with " " ) (namenator "qwerty"
[ 
["1" ; "g" ; "c6"] ;
["2" ; "2" ; "c6"] ;
["2" ; "3" ; "c6"] ;
["2" ; "4" ; "c6"] ;
["2" ; "5" ; "c6"] ;
["2" ; "6" ; "c6"] ;
["3" ; "7" ; "c6"] ;
["3" ; "8" ; "c6"] ;
["4" ; "88"] ;
["3" ; "9" ; "c6"] ;
["3" ; "0" ; "c6"] ;
["2" ; "a" ; "c6"] ;
["2" ; "b" ; "c6"] ;
["2" ; "c" ; "c6"] ;
["1" ; "d" ; "c6"] ;
["1" ; "e" ; "c6"] ;
["1" ; "f" ; "c6"] ;
["2" ; "g" ; "c6"] ;
["2" ; "h" ; "c6"] ;
["3" ; "i" ; "c6"] ;
["3" ; "g" ; "c6"] ;
["3" ; "k" ; "c6"] ;
["2" ; "l" ; "c6"] ;
["1" ; "m" ; "c6"] ;
["1" ; "n" ; "c6"] 
]
)) in
let codeSplitted := split_string s newline in 
let codeTrimmed := filter (fun s => negb (String.eqb s "")) codeSplitted in 
let cmds := map readTVMCmd codeTrimmed in  
let m := 1 in
strDeeper' m (strDeeper'' m cmds) 

). *)

(* Функция вытаскивания всего и всех *)
Fixpoint pulling' (n:nat)(sl:list(list string)):=
match n with
| 0 => nil
| S n' => match sl with
          | nil => nil
          | h :: t => (strDeeper' n sl) ++ (pulling' n' sl)
          end 
end.

Check pulling'.

Definition pulling(sl:list(list string)):=
let l := analizer 0 sl in
pulling' l sl.

(* Compute (let s:= concat_with newline ( map (concat_with " " ) (namenator "qwerty"
[ 
["1" ; "g" ; "c6"] ;
["2" ; "2" ; "c6"] ;
["2" ; "3" ; "c6"] ;
["2" ; "4" ; "c6"] ;
["2" ; "5" ; "c6"] ;
["2" ; "6" ; "c6"] ;
["3" ; "7" ; "c6"] ;
["3" ; "8" ; "c6"] ;
["4" ; "88"] ;
["3" ; "9" ; "c6"] ;
["3" ; "0" ; "c6"] ;
["2" ; "a" ; "c6"] ;
["2" ; "b" ; "c6"] ;
["2" ; "c" ; "c6"] ;
["1" ; "d" ; "c6"] ;
["1" ; "e" ; "c6"] ;
["1" ; "f" ; "c6"] ;
["2" ; "g" ; "c6"] ;
["2" ; "h" ; "c6"] ;
["3" ; "i" ; "c6"] ;
["3" ; "g" ; "c6"] ;
["3" ; "k" ; "c6"] ;
["2" ; "l" ; "c6"] ;
["1" ; "m" ; "c6"] ;
["1" ; "n" ; "c6"] 
]
)) in 
let codeSplitted := split_string s newline in 
let codeTrimmed := filter (fun s => negb (String.eqb s "")) codeSplitted in
let cmds := map readTVMCmd codeTrimmed in  
(* let m := 3 in
(* strDeeper' m (strDeeper'' m cmds) *) *)
let ls := pulling cmds in
let sl := map (concat_with " " ) ls in 
let sl := concat_with newline sl in  
 sl
).
 *)
Fixpoint number_clear (ls:list(list string)):=
match ls with
| nil => nil
| h :: t => match h with
            | nil => nil 
            | h' :: t' => t' :: number_clear t
            end 
end.

(* clearing ". >>" and ":= >>" *)
Fixpoint clear_bags(sl:(list string)):=
match sl with
| nil => nil
| ":=" :: ">>" :: t => ":= " :: t
| "." :: ">>" :: t => ":= " :: t
| h :: t => h :: (clear_bags t)
end.

Fixpoint dc (s:string) :=
match s with
| "" => ""
| String "$"%char t => dc t
| String h "$" => String h ""
| String h t => String h (dc t) 
end.

Fixpoint dollarClear(sl:list string) :=
match sl with
| nil => nil
| h :: t => ( dc h ) :: (dollarClear t)
end.

Fixpoint getCharByNumber (n:nat)(s:string):=
match n, s with
| _, "" => "000"%char
| 0, String h t => h
| S n', String h t => getCharByNumber n' t 
end.
Fixpoint exec_clear'(n:nat)(s:string) :=
if Nat.ltb (length s) n then s
else 
match n, s with
| 0, _ => s
| _, "" => s
| S n', String h t => exec_clear' n' t 
end.
Compute (exec_clear' 7 "Exec_ъsubmitTransaction20").
Compute (getCharByNumber 6 "Exec_ъsubmitTransaction20").

Definition exec_clear (sl:list string) :=
match sl with
| nil => sl
| h :: t => match getCharByNumber 6 h with
            | "138"%char => (exec_clear' 7 h) :: t
            | _ => sl
            end 
end.
Compute (exec_clear ["Exec_ъsubmitTransaction20";"ssss";"rrrr"]).
Compute (exec_clear ["Exec_CTOS";"ssss";"rrrr"]).

Definition typeXCHG(ls:list string) :=
match ls with
| nil => ls
| h :: nil => ls
| "Exec_STSLICECONSTz" :: "x6_" :: t => "Exec_STSLICECONSTs" :: (to_quotes"x6_") :: t
| _ => ls
end.

Definition headS'{X}(s:X)(sl:list X) := headS sl s.

Fixpoint database'(sl:list (list string)):=
match sl with
| nil => nil
| h :: t => (database (headS h "") ) :: database' t 
end.
(* List of subfunctions names  *)
Fixpoint name2list(sl:list(list string)):=
match sl with
| nil => nil
| h :: t => match h with
            | h' :: t' => match h' with
                        | "Definition" => (headS t' "") :: name2list t
                        | _ => name2list t
                        end
            | _ => name2list t
            end 
end. 
(* Называем функции доказательств и цепляем верные строчки *)
Fixpoint db_namenator(db:list string)(names:list string) :=
match db with
| nil => ["Abort."]
| "Definition":: t => let name := (headS names "") in
                      ["Abort."] ++ 
("
Definition " ++ name ++ "StatePrepared: TVMState.
Proof.
intros.
remember (exec_state"++ name ++ " state0 ).
unfold " ++ name ++ " in Heqo.
toMNFRight in Heqo.")%string::(db_namenator t (tail names))

| h :: t => h :: ( db_namenator t names )
end. 

Definition db_namenator'(db:list string)(names:list string) := tail (db_namenator db names).
 
Fixpoint clear_newline (l:list (list string)):=
match l with
| nil => nil
| h :: t => match h with
            | nil => clear_newline t
            | _ => h :: (clear_newline t)
            end 
end.

Fixpoint test_comments_intro(l:string) :=
match l with
| "" => false
| String ";"%char t => true
| String h t => test_comments_intro t
end.

Fixpoint clear_comments_intro(l:string) :=
match l with
| "" => ""
| String ";"%char t => ""
| String h t => String h (clear_comments_intro t)
end.

Fixpoint clear_comments(l:list string) :=
match l with
| nil => nil
| h :: t =>   if test_comments_intro h then [clear_comments_intro h]
                                       else h :: (clear_comments t)
end.

Compute (clear_comments ["czxzxc";"zfsf;;;sdfsdf"]).



Definition shaper1(s fn : string) := 
let codeSplitted := split_string s newline in 
let codeTrimmed := filter (fun s => negb (String.eqb s "")) codeSplitted in 
let cmds := map readTVMCmd codeTrimmed in 
let sl := clear_newline cmds in 
let sl := map clear_comments sl in
let sl := map counter2in sl in 
let sl := map pushcontUpNumber sl in
let sl := clear_newline sl in
let sl := namenator fn sl in

let sl := map (concat_with " " ) sl in 
let sl := concat_with newline sl in 

let codeSplitted := split_string sl newline in 
let codeTrimmed := filter (fun s => negb (String.eqb s "")) codeSplitted in 
let cmds := map readTVMCmd codeTrimmed in 
let ls := number_clear (pulling cmds) in
let ls := map clear_bags ls in
let sl := map (concat_with " " ) ls in 
let sl := concat_with newline sl in 

let codeSplitted := split_string sl newline in 
let codeTrimmed := filter (fun s => negb (String.eqb s "")) codeSplitted in 
let sl := map readTVMCmd codeTrimmed in 

let sl := eraseBlank (map eraseComm' sl) in 
let sl := map addExec_ sl in let sl:= map xchgInstr sl in 
let sl := pasteGtGT sl in let sl := map ( map minusBraketation ) sl in
let sl := paste_a1a2 sl in let sl := map quotation sl in let sl := map numberAdding sl in
let sl := map dollarClear sl in let sl := map exec_clear sl in

let sl := map typeXCHG sl in let sl := cutLast sl in
(* Строим шаблоны доказательств. Для стандартных доказов - сами доказы.
   Для сложных - названия инструкций закомментированные *)
let db := database' sl  in
let db := db_namenator' db (name2list sl) in
let db := concat_with newline db in

let db := split_string db "Definition" in
let db := rev db in
let db := concat_with "
Definition" db in

let sl := map (concat_with " " ) sl in 
let ss := concat_with newline sl in  
(header ++ ss ++ "return! I ." ++ "
" ++ "
Definition " ++ db)%string.

Definition spl_str (s s1:string) := split_string s1 s.

Fixpoint funcNameFromFileName (fn:string) :=
match fn with
| EmptyString => EmptyString
| String "."%char t => EmptyString
| String c t => (String c (funcNameFromFileName t))
end. 

(* Compute ( funcNameFromFileName "." ). *)

Definition translator (argv : list LString.t) : C.t System.effect Datatypes.unit :=
  match argv with
  | [ _; file1 ] =>
    let! c1 := System.read_file file1 in
    match c1 with
    | Some c1' => System.log (LString.s (shaper1 (t2str c1') ((funcNameFromFileName (t2str file1))++"_tvm_") ) )
    | _ => System.log (LString.s "Cannot read the files.")
    end
  | _ => System.log (LString.s "Expected a parameter.")
  end. 

Definition main := Extraction.launch translator.

Extraction "./tvmFileTranslatorAll1" main.


(* Compute (let a1 := (let a1 := 125 in a1+5) in a1). *)

(*
Definition shaper (s fn: string) := 
let codeSplitted := split_string s newline in 
let codeTrimmed := filter (fun s => negb (String.eqb s "")) codeSplitted in 
let cmds := map readTVMCmd codeTrimmed in 
let cmds := map firstUp cmds in
let sl := eraseBlank (map eraseComm' cmds) in 
let sl := map addExec_ sl in let sl:= map xchgInstr sl in 
let sl := pasteGtGT sl in let sl := map quoteXCHG sl in let sl := map ( map minusBraketation ) sl in
let sl := paste_a1a2 sl in let sl := map quotation sl in let sl := map numberAdding sl in
let sl := map dollarClear sl in
(* Cut by if *)
let sl := cut_by_if 0 fn sl in
let sl := map (concat_with " " ) sl in 
let sl := concat_with newline sl in  
let sl := 
( append ((*  *) "Definition " ++ fn ++ " :=
") sl) in let ss := append sl ".

" in 
let ss := twist ss in
(header ++ "Definition " ++ ss ++ fn ++ "_tvm := " )%string. 
*)