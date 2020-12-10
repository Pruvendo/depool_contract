Require Import Coq.Lists.List.
Require Import Io.All.
Require Import Io.System.All.
Require Import ListString.All.
Require Import Ascii.
Require Import Strings.String. 
Import ListNotations.
Import C.Notations.

Require Import TVMModel.MonadState.CommonHelpers.
Require Import TVMModel.MonadState.StringHelpers.
 
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition xpu:string := "034".

Definition shaper (s1 s2:string):string := 
"Require Import TVMModel.MonadState.TVMParser." ++
"
Section TVMComputing.
Variables t1 t2 t3 t4: TVMContinuation.
Variable  t5 t6: TVMCell.
Variable t7 : TVMValue.

Variable cc0: TVMSlice.
Variable cc1: list TVMValue.
Variable cc2: list TVMRegistry.
Variable cc3: TVMCodePage.
Variable cc4: nat.

Variables gg0 gg1 gg2 gg3: TVMGas.

Definition nullState := {| 
           tvmRegistry := _TVMRegistryInit (ec_quit 0) t2 t3 t4 t5 t6 t7; 
           tvmCC := _TVMContinuationInit cc0 cc1 cc2 cc3 cc4;
           tvmGas := Build_TVMGasLimit gg0 gg1 gg2 gg3  |}.

Definition oldState :" ++ (string_left_trim s1) ++ "." ++
"

Definition text := " ++ (String "034"%char ( s2 ++ (String "034"%char "." ) ) ) ++
"

Opaque tvmIntN_sub.
Eval compute in ( parseTMVCode nullState text oldState ).
End TVMComputing.".

Fixpoint t2str(inp : LString.t):string :=
match inp with
| nil => EmptyString
| cons a b => String a ( t2str b) 
end. 

Fixpoint clear_patterns (s: string) :=
let sl := split_string s (String "010"%char "") in
let sl' := map (fun s => string_rev (snd (
fold_left (fun (acc: bool*string) c => if (fst acc) then match c with
                        | ";"%char => (false, snd acc)
                        | "."%char => (false, snd acc)
                        | a => (true, String a (snd acc))
                        end else acc) (str2chars s) (true, "")))) sl in
let sl'':=filter (fun s => negb (isBlank s)) sl' in sl''.

Definition isNil {X} (l: list X) :=
match l with
| [ ] => true
| _ => false
end.

Definition splitter (argv : list LString.t) : C.t System.effect Datatypes.unit :=
  match argv with
  | [ _; file1 ] =>
    let! c1 := System.read_file file1 in
    match c1 with
    | Some c1' => let s := t2str c1' in
                  let sl := split_string s ".globl" in
                  C.Let (fold_left (fun a fs => C.Let a (fun _ =>
                  let name := nth_error fs 0 in
                  match name with
                  | None => System.log (LString.s "Cannot read function name.")
                  | Some name => let name := string_left_trim name in
                                 let ss := concat_with (String "010"%char "") (tl fs) in
                                 C.Let (System.log (LString.s ("Writing " ++ name))) ( fun _ => C.Let (System.write_file 
                                                        (LString.s (name ++ ".tvm")) 
                                                        (LString.s ss)) (fun _ => C.Ret tt)) 
                  end ))  (filter (fun l => negb (isNil l)) (map clear_patterns sl)) (C.Ret tt)) (fun _ => System.log (LString.s "Success"))
    | _ => System.log (LString.s "Cannot read the files.")
    end
  | _ => System.log (LString.s "Expected 1 parameters.")
  end. 

(* 
Definition writeFile (argv : list LString.t) : C.t System.effect Datatypes.unit :=
C.Let (fold_left (fun aa f => C.Let aa (fun _ => System.write_file (LString.s f) (LString.s "bar"))) ["foo"; "foo1"; "foo2"] (C.Ret true))
 (fun _ => C.Ret tt). *)


Definition main := Extraction.launch splitter.

Extraction "tvmcode_splitter" main.


