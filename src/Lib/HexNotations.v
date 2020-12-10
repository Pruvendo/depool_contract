Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.
Require Import ZArith.
Require Import Lists.List.
Require Export Ascii.
Require Export Strings.String. 
Require Export Coq.Strings.Byte.

(* Require Export TVMModel.MonadState.CommonHelpers.
Require Export TVMModel.MonadState.StringHelpers. *)

Import ListNotations.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Module HexNotations.


Fixpoint pos2bytes (p:positive) : list Byte.byte:=
match p with
| (p~0~0~0~0)%positive => (pos2bytes p) ++ [ x30 ] 
| (p~0~0~0~1)%positive => (pos2bytes p) ++ [ x31 ] 
| (p~0~0~1~0)%positive => (pos2bytes p) ++ [ x32 ] 
| (p~0~0~1~1)%positive => (pos2bytes p) ++ [ x33 ] 
| (p~0~1~0~0)%positive => (pos2bytes p) ++ [ x34 ] 
| (p~0~1~0~1)%positive => (pos2bytes p) ++ [ x35 ] 
| (p~0~1~1~0)%positive => (pos2bytes p) ++ [ x36 ] 
| (p~0~1~1~1)%positive => (pos2bytes p) ++ [ x37 ] 
| (p~1~0~0~0)%positive => (pos2bytes p) ++ [ x38 ] 
| (p~1~0~0~1)%positive => (pos2bytes p) ++ [ x39 ] 
| (p~1~0~1~0)%positive => (pos2bytes p) ++ [ x41 ] 
| (p~1~0~1~1)%positive => (pos2bytes p) ++ [ x42 ] 
| (p~1~1~0~0)%positive => (pos2bytes p) ++ [ x43 ] 
| (p~1~1~0~1)%positive => (pos2bytes p) ++ [ x44 ] 
| (p~1~1~1~0)%positive => (pos2bytes p) ++ [ x45 ] 
| (p~1~1~1~1)%positive => (pos2bytes p) ++ [ x46 ] 
| 1%positive => [ x31 ]
| 2%positive => [ x32 ]
| 3%positive => [ x33 ]
| 4%positive => [ x34 ]
| 5%positive => [ x35 ]
| 6%positive => [ x36 ]
| 7%positive => [ x37 ]
| 8%positive => [ x38 ]
| 9%positive => [ x39 ]
| 10%positive => [ x41 ]
| 11%positive => [ x42 ]
| 12%positive => [ x43 ]
| 13%positive => [ x44 ]
| 14%positive => [ x45 ]
| 15%positive => [ x46 ]
end. 

Definition Z2bytes (z : Z) : list Byte.byte := 
match z with 
| 0%Z  => [x30]
| Z.pos p => pos2bytes p
| Z.neg p =>  [ ]
end.

Fixpoint bytes2Z' ( l : list Byte.byte ) : option Z :=
match l with
| [ ] => Some 0
| h :: t => let q := bytes2Z' t in match q with
                                   | None => None
                                   | Some q => match h with
                                               | x30 => Some ( 16 * q ) 
                                               | x31 => Some ( 16 * q + 1 )
                                               | x32 => Some ( 16 * q + 2 )
                                               | x33 => Some ( 16 * q + 3 )
                                               | x34 => Some ( 16 * q + 4 )
                                               | x35 => Some ( 16 * q + 5 )
                                               | x36 => Some ( 16 * q + 6 )
                                               | x37 => Some ( 16 * q + 7 )
                                               | x38 => Some ( 16 * q + 8 )
                                               | x39 => Some ( 16 * q + 9 )
                                               | x41 => Some ( 16 * q + 10 )
                                               | x42 => Some ( 16 * q + 11 )
                                               | x43 => Some ( 16 * q + 12 )
                                               | x44 => Some ( 16 * q + 13 )
                                               | x45 => Some ( 16 * q + 14 )
                                               | x46 => Some ( 16 * q + 15 )

                                               | x61 => Some ( 16 * q + 10 )
                                               | x62 => Some ( 16 * q + 11 )
                                               | x63 => Some ( 16 * q + 12 )
                                               | x64 => Some ( 16 * q + 13 )
                                               | x65 => Some ( 16 * q + 14 )
                                               | x66 => Some ( 16 * q + 15 )
                                               | _ => None
                                               end
                                   end
end.

Definition bytes2Z ( l : list Byte.byte ) : option Z :=
 bytes2Z' ( List.rev l ).



Declare Scope solidity_scope_hex .
Delimit Scope solidity_scope_hex with hex.
String Notation Z bytes2Z Z2bytes : solidity_scope_hex.

Definition idZ(z:Z) := z.

Declare Scope solidity_scope_dec .
Delimit Scope solidity_scope_dec with dec.
Numeral Notation Z idZ idZ : solidity_scope_dec.

Local Open Scope solidity_scope_hex.
Local Open Scope solidity_scope_dec.
(* Compute "334603dc8cfd56ff3df70032abbe42b9c8a4c5fca7606d74a9d9d772097883af".

Compute "FFFFFFFFFFFFFFFF". *)

End HexNotations .
