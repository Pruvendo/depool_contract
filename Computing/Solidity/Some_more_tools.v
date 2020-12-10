Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.
Require Import FinProof.ProgrammingWith.

Local Open Scope record.
Local Open Scope program_scope. 

Require Import FinProof.Common.
Require Import FinProof.StateMonad2.
Require Import MultiSigWallet.SolidityNotations.

Notation "·0"  := (Here)       (at level 60, right associativity). 
Notation "·1"  := (Next (·0))  (at level 60, right associativity).
Notation "·2"  := (Next (·1))  (at level 60, right associativity).
Notation "·3"  := (Next (·2))  (at level 60, right associativity).
Notation "·4"  := (Next (·3))  (at level 60, right associativity).
Notation "·5"  := (Next (·4))  (at level 60, right associativity).
Notation "·6"  := (Next (·5))  (at level 60, right associativity).
Notation "·7"  := (Next (·6))  (at level 60, right associativity).
Notation "·8"  := (Next (·7))  (at level 60, right associativity).
Notation "·9"  := (Next (·8))  (at level 60, right associativity).
Notation "·10" := (Next (·9))  (at level 60, right associativity).
Notation "·11" := (Next (·10)) (at level 60, right associativity).
Notation "·12" := (Next (·11)) (at level 60, right associativity).
Notation "·13" := (Next (·12)) (at level 60, right associativity).
Notation "·14" := (Next (·13)) (at level 60, right associativity).
Notation "·15" := (Next (·14)) (at level 60, right associativity).
Notation "·16" := (Next (·15)) (at level 60, right associativity).
Notation "·17" := (Next (·16)) (at level 60, right associativity).
Notation "·18" := (Next (·17)) (at level 60, right associativity).
Notation "·19" := (Next (·18)) (at level 60, right associativity).
Notation "·20" := (Next (·19)) (at level 60, right associativity).
Notation "·21" := (Next (·20)) (at level 60, right associativity).
Notation "·22" := (Next (·21)) (at level 60, right associativity).
Notation "·23" := (Next (·22)) (at level 60, right associativity).
Notation "·24" := (Next (·23)) (at level 60, right associativity).
Notation "·25" := (Next (·24)) (at level 60, right associativity).
Notation "·26" := (Next (·25)) (at level 60, right associativity).
Notation "·27" := (Next (·26)) (at level 60, right associativity).
Notation "·28" := (Next (·27)) (at level 60, right associativity).
Notation "·29" := (Next (·28)) (at level 60, right associativity).
Notation "·30" := (Next (·29)) (at level 60, right associativity).
Notation "·31" := (Next (·30)) (at level 60, right associativity).
Notation "·32" := (Next (·31)) (at level 60, right associativity).
Notation "·33" := (Next (·32)) (at level 60, right associativity).
Notation "·34" := (Next (·33)) (at level 60, right associativity).
Notation "·35" := (Next (·34)) (at level 60, right associativity).
Notation "·36" := (Next (·35)) (at level 60, right associativity).
Notation "·37" := (Next (·36)) (at level 60, right associativity).
Notation "·38" := (Next (·37)) (at level 60, right associativity).
Notation "·39" := (Next (·38)) (at level 60, right associativity).
Notation "·40" := (Next (·39)) (at level 60, right associativity).
Notation "·41" := (Next (·40)) (at level 60, right associativity).
Notation "·42" := (Next (·41)) (at level 60, right associativity).
Notation "·43" := (Next (·42)) (at level 60, right associativity).
Notation "·44" := (Next (·43)) (at level 60, right associativity).
Notation "·45" := (Next (·44)) (at level 60, right associativity).
Notation "·46" := (Next (·45)) (at level 60, right associativity).
Notation "·47" := (Next (·46)) (at level 60, right associativity).
Notation "·48" := (Next (·47)) (at level 60, right associativity).
Notation "·49" := (Next (·48)) (at level 60, right associativity).
Notation "·50" := (Next (·49)) (at level 60, right associativity).
Notation "·51" := (Next (·50)) (at level 60, right associativity).
Notation "·52" := (Next (·51)) (at level 60, right associativity).
Notation "·53" := (Next (·52)) (at level 60, right associativity).
Notation "·54" := (Next (·53)) (at level 60, right associativity).
Notation "·55" := (Next (·54)) (at level 60, right associativity).
Notation "·56" := (Next (·55)) (at level 60, right associativity).
Notation "·57" := (Next (·56)) (at level 60, right associativity).
Notation "·58" := (Next (·57)) (at level 60, right associativity).
Notation "·59" := (Next (·58)) (at level 60, right associativity).
Notation "·60" := (Next (·59)) (at level 60, right associativity).
Notation "·61" := (Next (·60)) (at level 60, right associativity).
Notation "·62" := (Next (·61)) (at level 60, right associativity).
Notation "·63" := (Next (·62)) (at level 60, right associativity).
Notation "·64" := (Next (·63)) (at level 60, right associativity).
Notation "·65" := (Next (·64)) (at level 60, right associativity).
Notation "·66" := (Next (·65)) (at level 60, right associativity).