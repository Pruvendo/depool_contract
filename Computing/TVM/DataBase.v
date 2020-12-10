(* Data Base for TVM-instructions and its proofing correspondence *)
Require Import Coq.Lists.List.
Require Import Io.All.
Require Import Io.System.All.
Require Import ListString.All.
Require Import Ascii.
Require Import Strings.String. 
Import ListNotations.
Import C.Notations.

Local Open Scope string_scope.
Local Open Scope list_scope.

Definition standard := "opaque. computeOne Heqo. transparent. simpl_subst Heqm Heqo m.".
Definition if_false := "liftOne Heqo.
rewrite ifelse_false with (i:=(Z2IN 257  0  )) in Heqm; [|auto|auto].".
Definition if_true := "liftOne Heqo.
rewrite ifelse_true  with (i:=(Z2IN 257 (-1) )) in Heqm; [|auto|auto].".

Fixpoint first_letter (n:nat)(s:string) :=
match n, s with
| 0, _ => ""
| S _, "" => ""
| S n', String h t => String h (first_letter n' t)
end.

Compute (first_letter 5 "123").

Definition database (s:string):=
let l :=
match s with
| "" => ""
|  "Exec_LDU'z" => "(*Exec_LDU'z*)"
|  "Exec_DICTUGET'" => "(*Exec_DICTUGET'*)"
|  "Exec_DICTUGETREF'" => "(*Exec_DICTUGETREF'*)"
|  "Exec_PLDU'z" => "(*Exec_PLDU'z*)"
|  "Exec_LSHIFT" => "(*Exec_LSHIFT*)"
|  "Exec_AND" => "(*Exec_AND*)"
|  "Exec_EQINTz" => "(*Exec_EQINTz*)"
|  "Exec_ADD" => "(*Exec_ADD*)"
|  "Exec_GEQ" => "(*Exec_GEQ*)"
|  "Exec_OR" => "(*Exec_OR*)"
|  "Exec_DICTUSETREF'" => "(*Exec_DICTUSETREF'*)"
|  "Exec_LDMSGADDR" => "(*Exec_LDMSGADDR*)"
|  "Exec_LDI'z" => "(*Exec_LDI'z*)"
|  "Exec_MUL" => "(*Exec_MUL*)"
|  "Exec_RSHIFT" => "(*Exec_RSHIFT*)"
|  "Exec_LESS" => "(*Exec_LESS*)"
|  "Exec_NEQINTz" => "(*Exec_NEQINTz*)"
|  "Exec_DROP" => "(*Exec_DROP*)"
|  "Exec_CTOS'" => "(*Exec_CTOS'*)"
|  "Exec_DICTUMINREF" => "(*Exec_DICTUMINREF*)"

|  "Exec_PUSH2ss" => "(*Exec_PUSH2ss*)"
|  "Exec_BLKPUSHz" => "(*Exec_BLKPUSHz*)"
|  "Exec_TUPLEz" => "(*Exec_TUPLEz*)"
|  "Exec_GETGLOBz" => "(*Exec_GETGLOBz*)"
|  "Exec_SETGLOBz" => "(*Exec_SETGLOBz*)"
|  "Exec_SETINDEXz" => "(*Exec_SETINDEXz*)"
|  "Exec_STSLICECONSTz" => "(*Exec_STSLICECONSTz*)"
|  "Exec_STSLICECONSTs" => "(*Exec_STSLICECONSTs*)"
|  "Exec_STB" =>   "(*Exec_STB*)"
|  "Exec_PUSH3sss" => "(*Exec_PUSH3sss*)"
|  "Exec_UNTUPLEz" => "(*Exec_UNTUPLEz*)"
|  "Exec_DICTEMPTY" => "(*Exec_DICTEMPTY*)"
|  "Exec_LDMSGADDRQ" => "(*Exec_LDMSGADDRQ*)"
|  "Exec_LDUQz" => "(*Exec_LDUQz*)"

| "tvm_ifelse" => if_true
| "tvm_call_inline" => "tvm_call_inline"
| "tvm_until" => "tvm_until"
| "tvm_while" => "tvm_while"


| "Definition" => "Definition"
| "let" => ""
| ")" => ""
|  _ => standard

end in
match first_letter 4 s with
| "Exec" => l
| "tvm_" => l
| "Defi" => l
| _ => ""
end.

Compute (database ")").



















