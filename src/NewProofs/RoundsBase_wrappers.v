Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.
Require Import Setoid.
Require Import ZArith.
Require Import Psatz.


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

Require Import depoolContract.NewProofs.ProofHelpers.
Require Import depoolContract.DePoolFunc.

(* Set Typeclasses Iterative Deepening.
Set Typeclasses Depth 100. *)

Require Import depoolContract.Lib.CommonModelProofs.
Module CommonModelProofs := CommonModelProofs StateMonadSig.
Import CommonModelProofs. 
Require Import depoolContract.Lib.Tactics.
Require Import depoolContract.Lib.ErrorValueProofs.
Require Import depoolContract.Lib.CommonCommon.

(* Require Import MultiSigWallet.Proofs.tvmFunctionsProofs. *)

Import DePoolSpec.LedgerClass.SolidityNotations. 

Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope solidity_scope.
Require Import Lists.List.
Import ListNotations.
Local Open Scope list_scope.

Require Import depoolContract.DePoolConsts.
Module RoundsBaseWrappers (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.


Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair.


(* function isRoundPre0(uint64 id) internal inline returns (bool) { return id == m_roundQty - 1; } *)
(* Definition RoundsBase_Ф_isRoundPre0 (Л_id: XInteger64) : LedgerT XBool :=
  return!! (  $ Л_id ?== (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt1 ). *)

Lemma RoundsBase_Ф_isRoundPre0_exec: forall (id: XInteger64) (l: Ledger),
 exec_state (↓ RoundsBase_Ф_isRoundPre0 id) l = l .
Proof.
    intros.
    destructLedger l. 
    compute.
    repeat destructIf_solve2. 
Qed.
  
Lemma RoundsBase_Ф_isRoundPre0_eval: forall (id: XInteger64) (l: Ledger),
let m_roundQty := eval_state (↑11 D2! RoundsBase_ι_m_roundQty) l in
 eval_state (↓ RoundsBase_Ф_isRoundPre0 id) l = (id =? m_roundQty - 1).
Proof.
    intros.
    destructLedger l. 
    compute.
    repeat destructIf_solve2. 
Qed.


(* function isRound0(uint64 id)    internal inline returns (bool) { return id == m_roundQty - 2; } *)
(* Definition RoundsBase_Ф_isRound0 (Л_id: XInteger64) : LedgerT XBool :=
  return!! (   $ Л_id ?== (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt2 ). *)

Lemma RoundsBase_Ф_isRound0_exec: forall (id: XInteger64) (l: Ledger),
  exec_state (↓ RoundsBase_Ф_isRound0 id) l = l .
 Proof.
     intros.
     destructLedger l. 
     compute.
     repeat destructIf_solve2. 
 Qed.
   
 Lemma RoundsBase_Ф_isRound0_eval: forall (id: XInteger64) (l: Ledger),
 let m_roundQty := eval_state (↑11 D2! RoundsBase_ι_m_roundQty) l in
  eval_state (↓ RoundsBase_Ф_isRound0 id) l = (id =? m_roundQty - 2).
 Proof.
     intros.
     destructLedger l. 
     compute.
     repeat destructIf_solve2. 
 Qed.

(* function isRound1(uint64 id)    internal inline returns (bool) { return id == m_roundQty - 3; } *)
(* Definition RoundsBase_Ф_isRound1 (Л_id: XInteger64) : LedgerT XBool :=
   return!! (  $ Л_id ?== (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt3 ). *)

Lemma RoundsBase_Ф_isRound1_exec: forall (id: XInteger64) (l: Ledger),
  exec_state (↓ RoundsBase_Ф_isRound1 id) l = l .
 Proof.
     intros.
     destructLedger l. 
     compute.
     repeat destructIf_solve2. 
 Qed.
   
 Lemma RoundsBase_Ф_isRound1_eval: forall (id: XInteger64) (l: Ledger),
 let m_roundQty := eval_state (↑11 D2! RoundsBase_ι_m_roundQty) l in
  eval_state (↓ RoundsBase_Ф_isRound1 id) l = (id =? m_roundQty - 3).
 Proof.
     intros.
     destructLedger l. 
     compute.
     repeat destructIf_solve2. 
 Qed.

(* function isRound2(uint64 id)    internal inline returns (bool) { return id == m_roundQty - 4; } *)
(* Definition RoundsBase_Ф_isRound2 (Л_id: XInteger64) : LedgerT XBool :=
   return!! (  $ Л_id ?== (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt4 ). *)

Lemma RoundsBase_Ф_isRound2_exec: forall (id: XInteger64) (l: Ledger),
  exec_state (↓ RoundsBase_Ф_isRound2 id) l = l .
 Proof.
     intros.
     destructLedger l. 
     compute.
     repeat destructIf_solve2. 
 Qed.
   
 Lemma RoundsBase_Ф_isRound2_eval: forall (id: XInteger64) (l: Ledger),
 let m_roundQty := eval_state (↑11 D2! RoundsBase_ι_m_roundQty) l in
  eval_state (↓ RoundsBase_Ф_isRound2 id) l = (id =? m_roundQty - 4).
 Proof.
     intros.
     destructLedger l. 
     compute.
     repeat destructIf_solve2. 
 Qed.


(* function roundAt(uint64 id) internal returns (Round) {
    return m_rounds.fetch(id).get();
} *)
(* Definition RoundsBase_Ф_roundAt (Л_id: XInteger64) : LedgerT RoundsBase_ι_Round :=
   return!! (   (D1! (↑11 D2! RoundsBase_ι_m_rounds) ->fetch $ Л_id) ->get ). *)

Lemma RoundsBase_Ф_roundAt_exec: forall (id: XInteger64) (l: Ledger),
  exec_state (↓ RoundsBase_Ф_roundAt id) l = l .
 Proof.
     intros.
     destructLedger l. 
     compute.
     repeat destructIf_solve2. 
 Qed.
   
 Lemma RoundsBase_Ф_roundAt_eval: forall (id: XInteger64) (l: Ledger),
 let m_rounds := eval_state (↑11 D2! RoundsBase_ι_m_rounds) l in
  eval_state (↓ RoundsBase_Ф_roundAt id) l = m_rounds [ id ].
 Proof.
     intros.
     destructLedger l. 
     compute.
     repeat destructIf_solve2. 
 Qed.

(* function getRoundPre0() internal inline returns (Round) { return roundAt(m_roundQty - 1); } *)
(* Definition RoundsBase_Ф_getRoundPre0  : LedgerT RoundsBase_ι_Round :=
  return!! (   RoundsBase_Ф_roundAt (!  (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt1 !) ). *)
Lemma RoundsBase_Ф_getRoundPre0_exec: forall (id: XInteger64) (l: Ledger),
  exec_state (↓ RoundsBase_Ф_getRoundPre0) l = l .
 Proof.
     intros.
     destructLedger l. 
     compute.
     repeat destructIf_solve2. 
 Qed.
   
 Lemma RoundsBase_Ф_getRoundPre0_eval: forall (id: XInteger64) (l: Ledger),
 let m_rounds := eval_state (↑11 D2! RoundsBase_ι_m_rounds) l in
 let m_roundQty := eval_state (↑11 D2! RoundsBase_ι_m_roundQty) l in
  eval_state (↓ RoundsBase_Ф_getRoundPre0) l = m_rounds [ m_roundQty - 1  ].
 Proof.
     intros.
     destructLedger l. 
     compute.
     repeat destructIf_solve2. 
 Qed.

(* function getRound0()    internal inline returns (Round) { return roundAt(m_roundQty - 2); } *)
(* Definition RoundsBase_Ф_getRound0 : LedgerT RoundsBase_ι_Round :=
  return!! (   RoundsBase_Ф_roundAt (!  (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt2 !) ). *)

Lemma RoundsBase_Ф_getRound0_exec: forall (id: XInteger64) (l: Ledger),
  exec_state (↓ RoundsBase_Ф_getRound0) l = l .
 Proof.
     intros.
     destructLedger l. 
     compute.
     repeat destructIf_solve2. 
 Qed.
   
Lemma RoundsBase_Ф_getRound0_eval: forall (id: XInteger64) (l: Ledger),
 let m_rounds := eval_state (↑11 D2! RoundsBase_ι_m_rounds) l in
 let m_roundQty := eval_state (↑11 D2! RoundsBase_ι_m_roundQty) l in
  eval_state (↓ RoundsBase_Ф_getRound0) l = m_rounds [ m_roundQty - 2 ].
 Proof.
     intros.
     destructLedger l. 
     compute.
     repeat destructIf_solve2. 
 Qed.

(* function getRound1()    internal inline returns (Round) { return roundAt(m_roundQty - 3); } *)
(* Definition RoundsBase_Ф_getRound1 : LedgerT RoundsBase_ι_Round :=
  return!! (   RoundsBase_Ф_roundAt (!  (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt3 !) ). *)

Lemma RoundsBase_Ф_getRound1_exec: forall (id: XInteger64) (l: Ledger),
  exec_state (↓ RoundsBase_Ф_getRound1) l = l .
 Proof.
     intros.
     destructLedger l. 
     compute.
     repeat destructIf_solve2. 
 Qed.
   
Lemma RoundsBase_Ф_getRound1_eval: forall (id: XInteger64) (l: Ledger),
 let m_rounds := eval_state (↑11 D2! RoundsBase_ι_m_rounds) l in
 let m_roundQty := eval_state (↑11 D2! RoundsBase_ι_m_roundQty) l in
  eval_state (↓ RoundsBase_Ф_getRound1) l = m_rounds [ m_roundQty - 3 ].
 Proof.
     intros.
     destructLedger l. 
     compute.
     repeat destructIf_solve2. 
 Qed.

(* function getRound2()    internal inline returns (Round) { return roundAt(m_roundQty - 4); } *)
(* Definition RoundsBase_Ф_getRound2 : LedgerT RoundsBase_ι_Round :=
  return!! (   RoundsBase_Ф_roundAt (!  (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt4 !) ). *)

Lemma RoundsBase_Ф_getRound2_exec: forall (id: XInteger64) (l: Ledger),
  exec_state (↓ RoundsBase_Ф_getRound2) l = l .
 Proof.
     intros.
     destructLedger l. 
     compute.
     repeat destructIf_solve2. 
 Qed.
   
Lemma RoundsBase_Ф_getRound2_eval: forall (id: XInteger64) (l: Ledger),
 let m_rounds := eval_state (↑11 D2! RoundsBase_ι_m_rounds) l in
 let m_roundQty := eval_state (↑11 D2! RoundsBase_ι_m_roundQty) l in
  eval_state (↓ RoundsBase_Ф_getRound2) l = m_rounds [ m_roundQty - 4 ].
 Proof.
     intros.
     destructLedger l. 
     compute.
     repeat destructIf_solve2. 
 Qed.


(* function setRound(uint64 id, Round round) internal {
    m_rounds[id] = round;
} *)
(* Definition RoundsBase_Ф_setRound (Л_id: XInteger) ( Л_round: RoundsBase_ι_Round) : LedgerT True :=
     ↑11 U1! RoundsBase_ι_m_rounds [[ $Л_id ]] := $Л_round. *)

Lemma RoundsBase_Ф_setRound_exec: forall (id: XInteger64) ( Л_round: RoundsBase_ι_Round) (l: Ledger),
let m_rounds := eval_state (↑11 D2! RoundsBase_ι_m_rounds) l in
  exec_state (↓ RoundsBase_Ф_setRound id Л_round) l = {$ l With (RoundsBase_ι_m_rounds, m_rounds [id] ← Л_round ) $} .
 Proof.
     intros.
     destructLedger l. 
     compute.
     repeat destructIf_solve2. 
 Qed.
   
 Lemma RoundsBase_Ф_setRound_eval: forall (id: XInteger64) ( Л_round: RoundsBase_ι_Round) (l: Ledger),
  eval_state (↓ RoundsBase_Ф_setRound id Л_round ) l = I.
 Proof.
     intros.
     destructLedger l. 
     compute.
     repeat destructIf_solve2. 
 Qed.


(* function setRoundPre0(Round r) internal inline { setRound(m_roundQty - 1, r); } *)
(* Definition RoundsBase_Ф_setRoundPre0 ( Л_r: RoundsBase_ι_Round): LedgerT True :=
    RoundsBase_Ф_setRound (!  (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt1 , $Л_r  !). *)

Lemma RoundsBase_Ф_setRoundPre0_exec: forall ( Л_round: RoundsBase_ι_Round) (l: Ledger),
let m_rounds := eval_state (↑11 D2! RoundsBase_ι_m_rounds) l in
let m_roundQty := eval_state (↑11 D2! RoundsBase_ι_m_roundQty) l in
  exec_state (↓ RoundsBase_Ф_setRoundPre0 Л_round) l = {$ l With (RoundsBase_ι_m_rounds, m_rounds [m_roundQty - 1] ← Л_round ) $} .
 Proof.
     intros.
     destructLedger l. 
     compute.
     repeat destructIf_solve2. 
 Qed.
   
 Lemma RoundsBase_Ф_setRoundPre0_eval: forall ( Л_round: RoundsBase_ι_Round) (l: Ledger),
  eval_state (↓ RoundsBase_Ф_setRoundPre0 Л_round ) l = I.
 Proof.
     intros.
     destructLedger l. 
     compute.
     repeat destructIf_solve2. 
 Qed.

(* function setRound0(Round r)    internal inline { setRound(m_roundQty - 2, r); } *)
(* Definition RoundsBase_Ф_setRound0 ( Л_r: RoundsBase_ι_Round): LedgerT True :=
    RoundsBase_Ф_setRound (!  (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt2 , $Л_r  !). *)

Lemma RoundsBase_Ф_setRound0_exec: forall ( Л_round: RoundsBase_ι_Round) (l: Ledger),
let m_rounds := eval_state (↑11 D2! RoundsBase_ι_m_rounds) l in
let m_roundQty := eval_state (↑11 D2! RoundsBase_ι_m_roundQty) l in
  exec_state (↓ RoundsBase_Ф_setRound0 Л_round) l = {$ l With (RoundsBase_ι_m_rounds, m_rounds [m_roundQty - 2] ← Л_round ) $} .
 Proof.
     intros.
     destructLedger l. 
     compute.
     repeat destructIf_solve2. 
 Qed.
   
 Lemma RoundsBase_Ф_setRound0_eval: forall ( Л_round: RoundsBase_ι_Round) (l: Ledger),
  eval_state (↓ RoundsBase_Ф_setRound0 Л_round ) l = I.
 Proof.
     intros.
     destructLedger l. 
     compute.
     repeat destructIf_solve2. 
 Qed.


(* function setRound1(Round r)    internal inline { setRound(m_roundQty - 3, r); } *)
(* Definition RoundsBase_Ф_setRound1 ( Л_r: RoundsBase_ι_Round): LedgerT True :=
    RoundsBase_Ф_setRound (!  (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt3 , $Л_r  !). *)

Lemma RoundsBase_Ф_setRound1_exec: forall ( Л_round: RoundsBase_ι_Round) (l: Ledger),
let m_rounds := eval_state (↑11 D2! RoundsBase_ι_m_rounds) l in
let m_roundQty := eval_state (↑11 D2! RoundsBase_ι_m_roundQty) l in
  exec_state (↓ RoundsBase_Ф_setRound1 Л_round) l = {$ l With (RoundsBase_ι_m_rounds, m_rounds [m_roundQty - 3] ← Л_round ) $} .
 Proof.
     intros.
     destructLedger l. 
     compute.
     repeat destructIf_solve2. 
 Qed.
   
 Lemma RoundsBase_Ф_setRound1_eval: forall ( Л_round: RoundsBase_ι_Round) (l: Ledger),
  eval_state (↓ RoundsBase_Ф_setRound1 Л_round ) l = I.
 Proof.
     intros.
     destructLedger l. 
     compute.
     repeat destructIf_solve2. 
 Qed.

(* function setRound2(Round r)    internal inline { setRound(m_roundQty - 4, r); } *)
(* Definition RoundsBase_Ф_setRound2 ( Л_r: RoundsBase_ι_Round): LedgerT True :=
    RoundsBase_Ф_setRound (!  (↑11 D2! RoundsBase_ι_m_roundQty) !- $ xInt4 , $Л_r  !). *)

Lemma RoundsBase_Ф_setRound2_exec: forall ( Л_round: RoundsBase_ι_Round) (l: Ledger),
let m_rounds := eval_state (↑11 D2! RoundsBase_ι_m_rounds) l in
let m_roundQty := eval_state (↑11 D2! RoundsBase_ι_m_roundQty) l in
  exec_state (↓ RoundsBase_Ф_setRound2 Л_round) l = {$ l With (RoundsBase_ι_m_rounds, m_rounds [m_roundQty - 4] ← Л_round ) $} .
 Proof.
     intros.
     destructLedger l. 
     compute.
     repeat destructIf_solve2. 
 Qed.
   
 Lemma RoundsBase_Ф_setRound2_eval: forall ( Л_round: RoundsBase_ι_Round) (l: Ledger),
  eval_state (↓ RoundsBase_Ф_setRound2 Л_round ) l = I.
 Proof.
     intros.
     destructLedger l. 
     compute.
     repeat destructIf_solve2. 
 Qed.    


(* 
function fetchRound(uint64 id) internal returns (optional(Round)) {
    return m_rounds.fetch(id);
} *)
(* Definition RoundsBase_Ф_fetchRound (Л_id: XInteger64) : LedgerT (XMaybe RoundsBase_ι_Round) :=
  return!!   (D1! (↑11 D2! RoundsBase_ι_m_rounds) ->fetch $ Л_id) . *)

Lemma RoundsBase_Ф_fetchRound_exec: forall ( Л_id: XInteger64) (l: Ledger),
  exec_state (↓ RoundsBase_Ф_fetchRound Л_id) l = l .
 Proof.
     intros.
     destructLedger l. 
     compute.
     repeat destructIf_solve2. 
 Qed.
   
Lemma RoundsBase_Ф_fetchRound_eval: forall ( Л_id: XInteger64) (l: Ledger),
let m_rounds := eval_state (↑11 D2! RoundsBase_ι_m_rounds) l in
 eval_state (↓ RoundsBase_Ф_fetchRound Л_id ) l =  m_rounds [ Л_id ]?.
Proof.
    intros.
    destructLedger l. 
    compute.
    repeat destructIf_solve2. 
Qed.   


  (* function minRound() internal view returns(optional(uint64, Round)) {
    return m_rounds.min();
} *)

(* Definition RoundsBase_Ф_minRound : LedgerT (XMaybe (XInteger64 # RoundsBase_ι_Round)) :=
    return!!  (D1! (↑11 D2! RoundsBase_ι_m_rounds) ->min) . *)

 Lemma RoundsBase_Ф_minRound_exec: forall (l: Ledger),
  exec_state (↓ RoundsBase_Ф_minRound) l = l .
 Proof.
     intros.
     destructLedger l. 
     compute.
     repeat destructIf_solve2. 
 Qed.
   
Lemma RoundsBase_Ф_minRound_eval: forall (l: Ledger),
let m_rounds := eval_state (↑11 D2! RoundsBase_ι_m_rounds) l in
 eval_state (↓ RoundsBase_Ф_minRound ) l =  hmapMinM m_rounds.
Proof.
    intros.
    destructLedger l. 
    compute.
    repeat destructIf_solve2. 
Qed.    

 
 
 (* function nextRound(uint64 id) internal view returns(optional(uint64, Round)) {
     return m_rounds.next(id);
 } *)
(*  Definition RoundsBase_Ф_nextRound (Л_id: XInteger64) : LedgerT (XMaybe (XInteger64 # RoundsBase_ι_Round)) :=
    return!!  (D1! (↑11 D2! RoundsBase_ι_m_rounds) ->next $ Л_id) .
  *)

Lemma RoundsBase_Ф_nextRound_exec: forall  (Л_id: XInteger64) (l: Ledger),
  exec_state (↓ RoundsBase_Ф_nextRound Л_id) l = l .
 Proof.
     intros.
     destructLedger l. 
     compute.
     repeat destructIf_solve2. 
 Qed.
   
Lemma RoundsBase_Ф_nextRound_eval: forall  (Л_id: XInteger64) (l: Ledger),
let m_rounds := eval_state (↑11 D2! RoundsBase_ι_m_rounds) l in
 eval_state (↓ RoundsBase_Ф_nextRound Л_id ) l =  hmapNextM m_rounds Л_id.
Proof.
    intros.
    destructLedger l. 
    compute.
    repeat destructIf_solve2. 
Qed.   

End RoundsBaseWrappers.