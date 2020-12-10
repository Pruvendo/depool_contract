Definition header :=
"
Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.
Require Import omega.Omega.
Require Import Setoid.
Require Import ZArith.

Require Import FinProof.Common.
Require Import FinProof.CommonInstances.
Require Import FinProof.StateMonad2.
Require Import FinProof.StateMonadInstances.
Require Import FinProof.ProgrammingWith. 

Local Open Scope struct_scope.

Require Import FinProof.CommonProofs.
Require Import depoolContract.ProofEnvironment.
Require Import depoolContract.DePoolClass.
Require Import depoolContract.SolidityNotations.

Require Import depoolContract.DePoolFunc.
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.

(* Import SolidityNotations. *)
Set Typeclasses Iterative Deepening.
Set Typeclasses Depth 100.
(*Set Typeclasses Strict Resolution. *)
(* Set Typeclasses Debug.  *) 
(* Set Typeclasses Unique Instances. 
Unset Typeclasses Unique Solutions. *)

(* Existing Instance monadStateT.
Existing Instance monadStateStateT. *)
(* Module MultiSigWalletSpecSig := MultiSigWalletSpecSig XTypesSig StateMonadSig. *)

Require Import depoolContract.Lib.CommonModelProofs.
Module CommonModelProofs := CommonModelProofs StateMonadSig.
Import CommonModelProofs. 
Require Import depoolContract.Lib.Tactics.
Require Import depoolContract.Lib.ErrorValueProofs.
Require Import depoolContract.Lib.CommonCommon.

(* Require Import MultiSigWallet.Proofs.tvmFunctionsProofs. *)

Import DePoolSpec.LedgerClass.SolidityNotations. 

Local Open Scope solidity_scope.

(* Require Import MultiSigWallet.Specifications._validatelimit_inlineSpec.
Module _validatelimit_inlineSpec := _validatelimit_inlineSpec MultiSigWalletSpecSig.
Import _validatelimit_inlineSpec. *)

Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope solidity_scope.
Require Import Lists.List.
Import ListNotations.
Local Open Scope list_scope.

(* Existing Instance embeddedLocalState.
 
Existing Instance monadStateT.
Existing Instance monadStateStateT. *)

(* Existing Instance embeddedLocalState.
Existing Instance embeddedMultisig. *)

".

Fixpoint erase_specified_smb (s:string) (sl:list string) :=
match sl with
| nil => nil
| h :: t => if ( h =? s ) then t
            else  h :: erase_specified_smb s t
end.
Definition headS {X} (d: X)(x : list X)  :=
match (head x) with
| None => d
| Some x' => x'
end.
Fixpoint find_for_snd_member_of_list(s:string)(sl:list(list string)):=
match sl with
| nil => nil
| h :: t => let q := headS "" ( tail h ) in
            if ( s =? q ) then let w := headS "" h in 
                               w :: q :: nil
                          else find_for_snd_member_of_list s t
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
Fixpoint find_brace_interior_from_current (n:Z) (sl:list string) :=
match sl with
| nil => nil 
| "{" :: t => "{" :: find_brace_interior_from_current (n+1) t
| "}" :: t => if (Z.eqb n  0%Z) then "}" :: nil
                        else "}" :: find_brace_interior_from_current (n-1) t
| h :: t => h :: find_brace_interior_from_current n t 
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
(* get lines between arguments and brace *)
Fixpoint find_crotch_interior (f:bool) (sl:list string) :=
match f, sl with
| _, nil => nil
| false, ")" :: t => find_crotch_interior true t
| true,  "{" :: t => nil
| true,   h  :: t => h :: (find_crotch_interior true t) 
| false,  h  :: t => find_crotch_interior true t
end.


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

(* Pulling the chains of zero-level *)
Fixpoint find_list_level_0(f:bool)(n:nat)(sl:list string ) :=
match f, n, sl with
| _,     _,     nil  => nil 
| false, _, "{" :: t => find_list_level_0 false (n+1) t
| true,  _, "{" :: t => find_list_level_0 false  n    t
| _,  _, "}" :: t    => find_list_level_0 false (n-1) t
| _,  _,  "" :: t    => find_list_level_0 false  n    t
| _,  _,  "function" :: t => find_list_level_0 true (n+1) t
| _,  _,  "struct"   :: t => find_list_level_0 true (n+1) t
| _,  _,  "modifier" :: t => find_list_level_0 true (n+1) t

| false, 0, _ :: "(" :: ")" :: "external" :: _ :: t => find_list_level_0 f n t

| false, 0, h :: t => h :: find_list_level_0 false 0 t
| _, _, h :: t =>   find_list_level_0 f n t
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
Fixpoint find_modifier_body(s:string)(sl:list (list string)) :=
match sl with
| nil => nil
| (_::h::t) :: t' => if ( s =? h ) then t
                     else find_modifier_body s t'
| h :: t =>  find_modifier_body s t
end.
(* Fixpoint find_members_level_0(f:bool)(n:nat)(sl:list string) :=
match sl with
| nil => nil
| type :: "constant" :: name :: "=" :: h :: ";" :: t => type :: name :: find_members_level_0
| type :: name :: ";" :: t => type :: name :: find_members_level_0
| h :: t => find_members_level_0 t
end. *)

Fixpoint set_modifier (ml:list(list string)) (sl:list string) :=
match sl with
| nil => nil
| h :: t => let q := find_modifier_body h ml in
            if ( Nat.eqb ( List.length q ) 0 )
            then h :: set_modifier ml t
            else newline :: "{" :: newline :: q ++ erase_specified_smb "{" ( set_modifier ml t )
end.







