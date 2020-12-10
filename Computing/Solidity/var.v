Require Export TVMModel.MonadState.TVMCommands.

Require Export TVMModel.MonadState.Common.

(* Require Export TVMModel.Computing.push_persistent_data_from_c4_to_c7_macro.
Require Export TVMModel.Computing.send_external_message_macro.
Require Export TVMModel.Computing.value_macro.
Require Export TVMModel.Computing.push_persistent_data_from_c7_to_c4_macro. *)

Require Import TVMModel.MonadState.MultisigGlobalVars.
Require Import TVMModel.MonadState.MultisigInitialState.
Require Import TVMModel.MonadState.TVMMonadState.
Require Import TVMModel.Base.Definitions.TVMHashmap.
Require Import TVMModel.Base.Definitions.TVMBit.
Require Import TVMModel.Base.Proofs.Basic.
Require Import TVMModel.Base.Definitions.StateTransforms.
Require Import TVMModel.Base.Proofs.TVMBitString_assoc.
Require Import TVMModel.Base.Proofs.TVMBitString.
Require Import TVMModel.Base.Proofs.TVMIntN.
Require Import TVMModel.Base.Proofs.TVMHashmap_axioms.
Require Import TVMModel.Base.Proofs.TVMCellHashmap.

Require Import FinProof.Common.
Require Import FinProof.StateMonad6.
Require Import FinProof.StateMonad6Instances.

Require Import TVMModel.Computing.InitialState.

Local Open Scope record.

Require Import TVMModel.Computing.StandardBlock.

Section TVMComputing. 
 Tactic Notation "prove_bs_rev" constr(bs) constr(pos) constr(fits) := 
rewrite I2ZBS_pos'_eq;
rewrite <- bs;
rewrite <- Z2IBS_rev_pos_pos;
[auto | apply pos| apply fits].    

Tactic Notation "prove_bs_rev" constr(rev) constr(def):= 
let H:=fresh"H" in
rewrite <- rev;
rewrite I2ZBS_pos'_eq;
unfold Z2IN; unfold Z2SIN;
match goal with
| |- _TVMInteger _ (_TVMSimpleInteger _ ?x) =  
     _TVMInteger _ (_TVMSimpleInteger _ ?y) => cut (x = y)
end; 
[intros H; rewrite H; auto | rewrite Z2IBS_pos_leading; auto; unfold def; simpl; omega].

Tactic Notation "prove_int_z" constr(rev) constr(def):= 
unfold def;
rewrite I2ZBS'_eq;
simpl bsAddLeadingZeros;
unfold I2ZBS';
fold def;
repeat rewrite I2ZBS_pos'_D0;
apply rev. 


Definition ElectorBase_ι_RECOVER_STAKE_MSG_VALUE : Z := 1*10^9 .
 

Variables ElectionParams_ι_m_electAt : Z . 
Variables (*! { _m_lc !*) _m_lc00 _m_lc01 _m_lc02 _m_lc03 _m_lc04 _m_lc05 _m_lc06 _m_lc07 _m_lc08 _m_lc09 _m_lc0A _m_lc0B _m_lc0C _m_lc0D _m_lc0E _m_lc0F _m_lc10 _m_lc11 _m_lc12 _m_lc13 _m_lc14 _m_lc15 _m_lc16 _m_lc17 _m_lc18 _m_lc19 _m_lc1A _m_lc1B _m_lc1C _m_lc1D _m_lc1E _m_lc1F  : TVMBit . 
Definition ElectionParams_ι_m_electAt_bs_def := [> _m_lc00 , _m_lc01 , _m_lc02 , _m_lc03 , _m_lc04 , _m_lc05 , _m_lc06 , _m_lc07 , _m_lc08 , _m_lc09 , _m_lc0A , _m_lc0B , _m_lc0C , _m_lc0D , _m_lc0E , _m_lc0F , _m_lc10 , _m_lc11 , _m_lc12 , _m_lc13 , _m_lc14 , _m_lc15 , _m_lc16 , _m_lc17 , _m_lc18 , _m_lc19 , _m_lc1A , _m_lc1B , _m_lc1C , _m_lc1D , _m_lc1E , _m_lc1F <] .
Lemma ElectionParams_ι_m_electAt_bs_id: ElectionParams_ι_m_electAt_bs_def = [> _m_lc00 , _m_lc01 , _m_lc02 , _m_lc03 , _m_lc04 , _m_lc05 , _m_lc06 , _m_lc07 , _m_lc08 , _m_lc09 , _m_lc0A , _m_lc0B , _m_lc0C , _m_lc0D , _m_lc0E , _m_lc0F , _m_lc10 , _m_lc11 , _m_lc12 , _m_lc13 , _m_lc14 , _m_lc15 , _m_lc16 , _m_lc17 , _m_lc18 , _m_lc19 , _m_lc1A , _m_lc1B , _m_lc1C , _m_lc1D , _m_lc1E , _m_lc1F (* } !*)  <] .
Proof. auto. Qed.
Axiom ElectionParams_ι_m_electAt_bs' : Z2IBS_pos (tvmBitStringLen ElectionParams_ι_m_electAt_bs_def) ElectionParams_ι_m_electAt = ElectionParams_ι_m_electAt_bs_def.
Lemma ElectionParams_ι_m_electAt_bs : Z2IBS_pos 32 ElectionParams_ι_m_electAt = ElectionParams_ι_m_electAt_bs_def.
Proof.
 rewrite <- ElectionParams_ι_m_electAt_bs'. auto. Qed.
Axiom ElectionParams_ι_m_electAt_pos: (0 <= ElectionParams_ι_m_electAt )%Z.
Axiom ElectionParams_ι_m_electAt_fits: zFitN_pos (tvmBitStringLen ElectionParams_ι_m_electAt_bs_def) ElectionParams_ι_m_electAt = true.
Lemma ElectionParams_ι_m_electAt_bs_rev : I2ZBS_pos' ElectionParams_ι_m_electAt_bs_def = ElectionParams_ι_m_electAt .
Proof.
  prove_bs_rev ElectionParams_ι_m_electAt_bs ElectionParams_ι_m_electAt_pos ElectionParams_ι_m_electAt_fits. 
Qed.
Lemma ElectionParams_ι_m_electAt_bs257 : Z2IN 257 ElectionParams_ι_m_electAt = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    ElectionParams_ι_m_electAt_bs_def)) ElectionParams_ι_m_electAt_bs_def)).
Proof.
  prove_bs_rev ElectionParams_ι_m_electAt_bs_rev ElectionParams_ι_m_electAt_bs_def.
Qed. 
Variables ElectionParams_ι_m_beginBefore : Z . 
Variables (*! { _m_bg !*) _m_bg00 _m_bg01 _m_bg02 _m_bg03 _m_bg04 _m_bg05 _m_bg06 _m_bg07 _m_bg08 _m_bg09 _m_bg0A _m_bg0B _m_bg0C _m_bg0D _m_bg0E _m_bg0F _m_bg10 _m_bg11 _m_bg12 _m_bg13 _m_bg14 _m_bg15 _m_bg16 _m_bg17 _m_bg18 _m_bg19 _m_bg1A _m_bg1B _m_bg1C _m_bg1D _m_bg1E _m_bg1F  : TVMBit . 
Definition ElectionParams_ι_m_beginBefore_bs_def := [> _m_bg00 , _m_bg01 , _m_bg02 , _m_bg03 , _m_bg04 , _m_bg05 , _m_bg06 , _m_bg07 , _m_bg08 , _m_bg09 , _m_bg0A , _m_bg0B , _m_bg0C , _m_bg0D , _m_bg0E , _m_bg0F , _m_bg10 , _m_bg11 , _m_bg12 , _m_bg13 , _m_bg14 , _m_bg15 , _m_bg16 , _m_bg17 , _m_bg18 , _m_bg19 , _m_bg1A , _m_bg1B , _m_bg1C , _m_bg1D , _m_bg1E , _m_bg1F <] .
Lemma ElectionParams_ι_m_beginBefore_bs_id: ElectionParams_ι_m_beginBefore_bs_def = [> _m_bg00 , _m_bg01 , _m_bg02 , _m_bg03 , _m_bg04 , _m_bg05 , _m_bg06 , _m_bg07 , _m_bg08 , _m_bg09 , _m_bg0A , _m_bg0B , _m_bg0C , _m_bg0D , _m_bg0E , _m_bg0F , _m_bg10 , _m_bg11 , _m_bg12 , _m_bg13 , _m_bg14 , _m_bg15 , _m_bg16 , _m_bg17 , _m_bg18 , _m_bg19 , _m_bg1A , _m_bg1B , _m_bg1C , _m_bg1D , _m_bg1E , _m_bg1F (* } !*)  <] .
Proof. auto. Qed.
Axiom ElectionParams_ι_m_beginBefore_bs' : Z2IBS_pos (tvmBitStringLen ElectionParams_ι_m_beginBefore_bs_def) ElectionParams_ι_m_beginBefore = ElectionParams_ι_m_beginBefore_bs_def.
Lemma ElectionParams_ι_m_beginBefore_bs : Z2IBS_pos 32 ElectionParams_ι_m_beginBefore = ElectionParams_ι_m_beginBefore_bs_def.
Proof.
 rewrite <- ElectionParams_ι_m_beginBefore_bs'. auto. Qed.
Axiom ElectionParams_ι_m_beginBefore_pos: (0 <= ElectionParams_ι_m_beginBefore )%Z.
Axiom ElectionParams_ι_m_beginBefore_fits: zFitN_pos (tvmBitStringLen ElectionParams_ι_m_beginBefore_bs_def) ElectionParams_ι_m_beginBefore = true.
Lemma ElectionParams_ι_m_beginBefore_bs_rev : I2ZBS_pos' ElectionParams_ι_m_beginBefore_bs_def = ElectionParams_ι_m_beginBefore .
Proof.
  prove_bs_rev ElectionParams_ι_m_beginBefore_bs ElectionParams_ι_m_beginBefore_pos ElectionParams_ι_m_beginBefore_fits. 
Qed.
Lemma ElectionParams_ι_m_beginBefore_bs257 : Z2IN 257 ElectionParams_ι_m_beginBefore = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    ElectionParams_ι_m_beginBefore_bs_def)) ElectionParams_ι_m_beginBefore_bs_def)).
Proof.
  prove_bs_rev ElectionParams_ι_m_beginBefore_bs_rev ElectionParams_ι_m_beginBefore_bs_def.
Qed. 
Variables ElectionParams_ι_m_endBefore : Z . 
Variables (*! { _m_nd !*) _m_nd00 _m_nd01 _m_nd02 _m_nd03 _m_nd04 _m_nd05 _m_nd06 _m_nd07 _m_nd08 _m_nd09 _m_nd0A _m_nd0B _m_nd0C _m_nd0D _m_nd0E _m_nd0F _m_nd10 _m_nd11 _m_nd12 _m_nd13 _m_nd14 _m_nd15 _m_nd16 _m_nd17 _m_nd18 _m_nd19 _m_nd1A _m_nd1B _m_nd1C _m_nd1D _m_nd1E _m_nd1F  : TVMBit . 
Definition ElectionParams_ι_m_endBefore_bs_def := [> _m_nd00 , _m_nd01 , _m_nd02 , _m_nd03 , _m_nd04 , _m_nd05 , _m_nd06 , _m_nd07 , _m_nd08 , _m_nd09 , _m_nd0A , _m_nd0B , _m_nd0C , _m_nd0D , _m_nd0E , _m_nd0F , _m_nd10 , _m_nd11 , _m_nd12 , _m_nd13 , _m_nd14 , _m_nd15 , _m_nd16 , _m_nd17 , _m_nd18 , _m_nd19 , _m_nd1A , _m_nd1B , _m_nd1C , _m_nd1D , _m_nd1E , _m_nd1F <] .
Lemma ElectionParams_ι_m_endBefore_bs_id: ElectionParams_ι_m_endBefore_bs_def = [> _m_nd00 , _m_nd01 , _m_nd02 , _m_nd03 , _m_nd04 , _m_nd05 , _m_nd06 , _m_nd07 , _m_nd08 , _m_nd09 , _m_nd0A , _m_nd0B , _m_nd0C , _m_nd0D , _m_nd0E , _m_nd0F , _m_nd10 , _m_nd11 , _m_nd12 , _m_nd13 , _m_nd14 , _m_nd15 , _m_nd16 , _m_nd17 , _m_nd18 , _m_nd19 , _m_nd1A , _m_nd1B , _m_nd1C , _m_nd1D , _m_nd1E , _m_nd1F (* } !*)  <] .
Proof. auto. Qed.
Axiom ElectionParams_ι_m_endBefore_bs' : Z2IBS_pos (tvmBitStringLen ElectionParams_ι_m_endBefore_bs_def) ElectionParams_ι_m_endBefore = ElectionParams_ι_m_endBefore_bs_def.
Lemma ElectionParams_ι_m_endBefore_bs : Z2IBS_pos 32 ElectionParams_ι_m_endBefore = ElectionParams_ι_m_endBefore_bs_def.
Proof.
 rewrite <- ElectionParams_ι_m_endBefore_bs'. auto. Qed.
Axiom ElectionParams_ι_m_endBefore_pos: (0 <= ElectionParams_ι_m_endBefore )%Z.
Axiom ElectionParams_ι_m_endBefore_fits: zFitN_pos (tvmBitStringLen ElectionParams_ι_m_endBefore_bs_def) ElectionParams_ι_m_endBefore = true.
Lemma ElectionParams_ι_m_endBefore_bs_rev : I2ZBS_pos' ElectionParams_ι_m_endBefore_bs_def = ElectionParams_ι_m_endBefore .
Proof.
  prove_bs_rev ElectionParams_ι_m_endBefore_bs ElectionParams_ι_m_endBefore_pos ElectionParams_ι_m_endBefore_fits. 
Qed.
Lemma ElectionParams_ι_m_endBefore_bs257 : Z2IN 257 ElectionParams_ι_m_endBefore = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    ElectionParams_ι_m_endBefore_bs_def)) ElectionParams_ι_m_endBefore_bs_def)).
Proof.
  prove_bs_rev ElectionParams_ι_m_endBefore_bs_rev ElectionParams_ι_m_endBefore_bs_def.
Qed. 
Variables ElectionParams_ι_m_electedFor : Z . 
Variables (*! { _m_lc !*) _m_lc00 _m_lc01 _m_lc02 _m_lc03 _m_lc04 _m_lc05 _m_lc06 _m_lc07 _m_lc08 _m_lc09 _m_lc0A _m_lc0B _m_lc0C _m_lc0D _m_lc0E _m_lc0F _m_lc10 _m_lc11 _m_lc12 _m_lc13 _m_lc14 _m_lc15 _m_lc16 _m_lc17 _m_lc18 _m_lc19 _m_lc1A _m_lc1B _m_lc1C _m_lc1D _m_lc1E _m_lc1F  : TVMBit . 
Definition ElectionParams_ι_m_electedFor_bs_def := [> _m_lc00 , _m_lc01 , _m_lc02 , _m_lc03 , _m_lc04 , _m_lc05 , _m_lc06 , _m_lc07 , _m_lc08 , _m_lc09 , _m_lc0A , _m_lc0B , _m_lc0C , _m_lc0D , _m_lc0E , _m_lc0F , _m_lc10 , _m_lc11 , _m_lc12 , _m_lc13 , _m_lc14 , _m_lc15 , _m_lc16 , _m_lc17 , _m_lc18 , _m_lc19 , _m_lc1A , _m_lc1B , _m_lc1C , _m_lc1D , _m_lc1E , _m_lc1F <] .
Lemma ElectionParams_ι_m_electedFor_bs_id: ElectionParams_ι_m_electedFor_bs_def = [> _m_lc00 , _m_lc01 , _m_lc02 , _m_lc03 , _m_lc04 , _m_lc05 , _m_lc06 , _m_lc07 , _m_lc08 , _m_lc09 , _m_lc0A , _m_lc0B , _m_lc0C , _m_lc0D , _m_lc0E , _m_lc0F , _m_lc10 , _m_lc11 , _m_lc12 , _m_lc13 , _m_lc14 , _m_lc15 , _m_lc16 , _m_lc17 , _m_lc18 , _m_lc19 , _m_lc1A , _m_lc1B , _m_lc1C , _m_lc1D , _m_lc1E , _m_lc1F (* } !*)  <] .
Proof. auto. Qed.
Axiom ElectionParams_ι_m_electedFor_bs' : Z2IBS_pos (tvmBitStringLen ElectionParams_ι_m_electedFor_bs_def) ElectionParams_ι_m_electedFor = ElectionParams_ι_m_electedFor_bs_def.
Lemma ElectionParams_ι_m_electedFor_bs : Z2IBS_pos 32 ElectionParams_ι_m_electedFor = ElectionParams_ι_m_electedFor_bs_def.
Proof.
 rewrite <- ElectionParams_ι_m_electedFor_bs'. auto. Qed.
Axiom ElectionParams_ι_m_electedFor_pos: (0 <= ElectionParams_ι_m_electedFor )%Z.
Axiom ElectionParams_ι_m_electedFor_fits: zFitN_pos (tvmBitStringLen ElectionParams_ι_m_electedFor_bs_def) ElectionParams_ι_m_electedFor = true.
Lemma ElectionParams_ι_m_electedFor_bs_rev : I2ZBS_pos' ElectionParams_ι_m_electedFor_bs_def = ElectionParams_ι_m_electedFor .
Proof.
  prove_bs_rev ElectionParams_ι_m_electedFor_bs ElectionParams_ι_m_electedFor_pos ElectionParams_ι_m_electedFor_fits. 
Qed.
Lemma ElectionParams_ι_m_electedFor_bs257 : Z2IN 257 ElectionParams_ι_m_electedFor = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    ElectionParams_ι_m_electedFor_bs_def)) ElectionParams_ι_m_electedFor_bs_def)).
Proof.
  prove_bs_rev ElectionParams_ι_m_electedFor_bs_rev ElectionParams_ι_m_electedFor_bs_def.
Qed. 
Variables ElectionParams_ι_m_heldFor : Z . 
Variables (*! { _m_hl !*) _m_hl00 _m_hl01 _m_hl02 _m_hl03 _m_hl04 _m_hl05 _m_hl06 _m_hl07 _m_hl08 _m_hl09 _m_hl0A _m_hl0B _m_hl0C _m_hl0D _m_hl0E _m_hl0F _m_hl10 _m_hl11 _m_hl12 _m_hl13 _m_hl14 _m_hl15 _m_hl16 _m_hl17 _m_hl18 _m_hl19 _m_hl1A _m_hl1B _m_hl1C _m_hl1D _m_hl1E _m_hl1F  : TVMBit . 
Definition ElectionParams_ι_m_heldFor_bs_def := [> _m_hl00 , _m_hl01 , _m_hl02 , _m_hl03 , _m_hl04 , _m_hl05 , _m_hl06 , _m_hl07 , _m_hl08 , _m_hl09 , _m_hl0A , _m_hl0B , _m_hl0C , _m_hl0D , _m_hl0E , _m_hl0F , _m_hl10 , _m_hl11 , _m_hl12 , _m_hl13 , _m_hl14 , _m_hl15 , _m_hl16 , _m_hl17 , _m_hl18 , _m_hl19 , _m_hl1A , _m_hl1B , _m_hl1C , _m_hl1D , _m_hl1E , _m_hl1F <] .
Lemma ElectionParams_ι_m_heldFor_bs_id: ElectionParams_ι_m_heldFor_bs_def = [> _m_hl00 , _m_hl01 , _m_hl02 , _m_hl03 , _m_hl04 , _m_hl05 , _m_hl06 , _m_hl07 , _m_hl08 , _m_hl09 , _m_hl0A , _m_hl0B , _m_hl0C , _m_hl0D , _m_hl0E , _m_hl0F , _m_hl10 , _m_hl11 , _m_hl12 , _m_hl13 , _m_hl14 , _m_hl15 , _m_hl16 , _m_hl17 , _m_hl18 , _m_hl19 , _m_hl1A , _m_hl1B , _m_hl1C , _m_hl1D , _m_hl1E , _m_hl1F (* } !*)  <] .
Proof. auto. Qed.
Axiom ElectionParams_ι_m_heldFor_bs' : Z2IBS_pos (tvmBitStringLen ElectionParams_ι_m_heldFor_bs_def) ElectionParams_ι_m_heldFor = ElectionParams_ι_m_heldFor_bs_def.
Lemma ElectionParams_ι_m_heldFor_bs : Z2IBS_pos 32 ElectionParams_ι_m_heldFor = ElectionParams_ι_m_heldFor_bs_def.
Proof.
 rewrite <- ElectionParams_ι_m_heldFor_bs'. auto. Qed.
Axiom ElectionParams_ι_m_heldFor_pos: (0 <= ElectionParams_ι_m_heldFor )%Z.
Axiom ElectionParams_ι_m_heldFor_fits: zFitN_pos (tvmBitStringLen ElectionParams_ι_m_heldFor_bs_def) ElectionParams_ι_m_heldFor = true.
Lemma ElectionParams_ι_m_heldFor_bs_rev : I2ZBS_pos' ElectionParams_ι_m_heldFor_bs_def = ElectionParams_ι_m_heldFor .
Proof.
  prove_bs_rev ElectionParams_ι_m_heldFor_bs ElectionParams_ι_m_heldFor_pos ElectionParams_ι_m_heldFor_fits. 
Qed.
Lemma ElectionParams_ι_m_heldFor_bs257 : Z2IN 257 ElectionParams_ι_m_heldFor = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    ElectionParams_ι_m_heldFor_bs_def)) ElectionParams_ι_m_heldFor_bs_def)).
Proof.
  prove_bs_rev ElectionParams_ι_m_heldFor_bs_rev ElectionParams_ι_m_heldFor_bs_def.
Qed.
Definition RoundsBase_ι_STEP_POOLING : Z := 0 .
 Definition RoundsBase_ι_STEP_WAITING_REQUESTS : Z := 1 .
 Definition RoundsBase_ι_STEP_ELECTIONS : Z := 2 .
 Definition RoundsBase_ι_STEP_WAITING_ELECTION_RESULTS : Z := 3 .
 Definition RoundsBase_ι_STEP_WAITING_UNFREEZE : Z := 4 .
 Definition RoundsBase_ι_STEP_COMPLETED : Z := 5 .
 Definition RoundsBase_ι_STEP_COMPLETING : Z := 6 .
 Definition RoundsBase_ι_ROUND_UNDEFINED : Z := 0 .
 Definition RoundsBase_ι_ROUND_RECEIVED_REWARD : Z := 7 .
 Definition RoundsBase_ι_ROUND_POOL_CLOSED : Z := 1 .
 Definition RoundsBase_ι_ROUND_MISSED_ELECTIONS : Z := 2 .
 Definition RoundsBase_ι_ROUND_NOT_ENOUGH_TOTAL_STAKE : Z := 3 .
 Definition RoundsBase_ι_ROUND_NODE_STAKE_TOO_SMALL : Z := 4 .
 Definition RoundsBase_ι_ROUND_STAKE_REJECTED : Z := 5 .
 Definition RoundsBase_ι_ROUND_LOST_ELECTIONS : Z := 6 .
 
Variables RoundsBase_ι_m_startIdx : Z . 
Variables (*! { _m_st !*) _m_st00 _m_st01 _m_st02 _m_st03 _m_st04 _m_st05 _m_st06 _m_st07 _m_st08 _m_st09 _m_st0A _m_st0B _m_st0C _m_st0D _m_st0E _m_st0F _m_st10 _m_st11 _m_st12 _m_st13 _m_st14 _m_st15 _m_st16 _m_st17 _m_st18 _m_st19 _m_st1A _m_st1B _m_st1C _m_st1D _m_st1E _m_st1F _m_st20 _m_st21 _m_st22 _m_st23 _m_st24 _m_st25 _m_st26 _m_st27 _m_st28 _m_st29 _m_st2A _m_st2B _m_st2C _m_st2D _m_st2E _m_st2F _m_st30 _m_st31 _m_st32 _m_st33 _m_st34 _m_st35 _m_st36 _m_st37 _m_st38 _m_st39 _m_st3A _m_st3B _m_st3C _m_st3D _m_st3E _m_st3F  : TVMBit . 
Definition RoundsBase_ι_m_startIdx_bs_def := [> _m_st00 , _m_st01 , _m_st02 , _m_st03 , _m_st04 , _m_st05 , _m_st06 , _m_st07 , _m_st08 , _m_st09 , _m_st0A , _m_st0B , _m_st0C , _m_st0D , _m_st0E , _m_st0F , _m_st10 , _m_st11 , _m_st12 , _m_st13 , _m_st14 , _m_st15 , _m_st16 , _m_st17 , _m_st18 , _m_st19 , _m_st1A , _m_st1B , _m_st1C , _m_st1D , _m_st1E , _m_st1F , _m_st20 , _m_st21 , _m_st22 , _m_st23 , _m_st24 , _m_st25 , _m_st26 , _m_st27 , _m_st28 , _m_st29 , _m_st2A , _m_st2B , _m_st2C , _m_st2D , _m_st2E , _m_st2F , _m_st30 , _m_st31 , _m_st32 , _m_st33 , _m_st34 , _m_st35 , _m_st36 , _m_st37 , _m_st38 , _m_st39 , _m_st3A , _m_st3B , _m_st3C , _m_st3D , _m_st3E , _m_st3F <] .
Lemma RoundsBase_ι_m_startIdx_bs_id: RoundsBase_ι_m_startIdx_bs_def = [> _m_st00 , _m_st01 , _m_st02 , _m_st03 , _m_st04 , _m_st05 , _m_st06 , _m_st07 , _m_st08 , _m_st09 , _m_st0A , _m_st0B , _m_st0C , _m_st0D , _m_st0E , _m_st0F , _m_st10 , _m_st11 , _m_st12 , _m_st13 , _m_st14 , _m_st15 , _m_st16 , _m_st17 , _m_st18 , _m_st19 , _m_st1A , _m_st1B , _m_st1C , _m_st1D , _m_st1E , _m_st1F , _m_st20 , _m_st21 , _m_st22 , _m_st23 , _m_st24 , _m_st25 , _m_st26 , _m_st27 , _m_st28 , _m_st29 , _m_st2A , _m_st2B , _m_st2C , _m_st2D , _m_st2E , _m_st2F , _m_st30 , _m_st31 , _m_st32 , _m_st33 , _m_st34 , _m_st35 , _m_st36 , _m_st37 , _m_st38 , _m_st39 , _m_st3A , _m_st3B , _m_st3C , _m_st3D , _m_st3E , _m_st3F (* } !*)  <] .
Proof. auto. Qed.
Axiom RoundsBase_ι_m_startIdx_bs' : Z2IBS_pos (tvmBitStringLen RoundsBase_ι_m_startIdx_bs_def) RoundsBase_ι_m_startIdx = RoundsBase_ι_m_startIdx_bs_def.
Lemma RoundsBase_ι_m_startIdx_bs : Z2IBS_pos 64 RoundsBase_ι_m_startIdx = RoundsBase_ι_m_startIdx_bs_def.
Proof.
 rewrite <- RoundsBase_ι_m_startIdx_bs'. auto. Qed.
Axiom RoundsBase_ι_m_startIdx_pos: (0 <= RoundsBase_ι_m_startIdx )%Z.
Axiom RoundsBase_ι_m_startIdx_fits: zFitN_pos (tvmBitStringLen RoundsBase_ι_m_startIdx_bs_def) RoundsBase_ι_m_startIdx = true.
Lemma RoundsBase_ι_m_startIdx_bs_rev : I2ZBS_pos' RoundsBase_ι_m_startIdx_bs_def = RoundsBase_ι_m_startIdx .
Proof.
  prove_bs_rev RoundsBase_ι_m_startIdx_bs RoundsBase_ι_m_startIdx_pos RoundsBase_ι_m_startIdx_fits. 
Qed.
Lemma RoundsBase_ι_m_startIdx_bs257 : Z2IN 257 RoundsBase_ι_m_startIdx = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    RoundsBase_ι_m_startIdx_bs_def)) RoundsBase_ι_m_startIdx_bs_def)).
Proof.
  prove_bs_rev RoundsBase_ι_m_startIdx_bs_rev RoundsBase_ι_m_startIdx_bs_def.
Qed. 
Variables RoundsBase_ι_m_roundsCount : Z . 
Variables (*! { _m_rn !*) _m_rn00 _m_rn01 _m_rn02 _m_rn03 _m_rn04 _m_rn05 _m_rn06 _m_rn07  : TVMBit . 
Definition RoundsBase_ι_m_roundsCount_bs_def := [> _m_rn00 , _m_rn01 , _m_rn02 , _m_rn03 , _m_rn04 , _m_rn05 , _m_rn06 , _m_rn07 <] .
Lemma RoundsBase_ι_m_roundsCount_bs_id: RoundsBase_ι_m_roundsCount_bs_def = [> _m_rn00 , _m_rn01 , _m_rn02 , _m_rn03 , _m_rn04 , _m_rn05 , _m_rn06 , _m_rn07 (* } !*)  <] .
Proof. auto. Qed.
Axiom RoundsBase_ι_m_roundsCount_bs' : Z2IBS_pos (tvmBitStringLen RoundsBase_ι_m_roundsCount_bs_def) RoundsBase_ι_m_roundsCount = RoundsBase_ι_m_roundsCount_bs_def.
Lemma RoundsBase_ι_m_roundsCount_bs : Z2IBS_pos 8 RoundsBase_ι_m_roundsCount = RoundsBase_ι_m_roundsCount_bs_def.
Proof.
 rewrite <- RoundsBase_ι_m_roundsCount_bs'. auto. Qed.
Axiom RoundsBase_ι_m_roundsCount_pos: (0 <= RoundsBase_ι_m_roundsCount )%Z.
Axiom RoundsBase_ι_m_roundsCount_fits: zFitN_pos (tvmBitStringLen RoundsBase_ι_m_roundsCount_bs_def) RoundsBase_ι_m_roundsCount = true.
Lemma RoundsBase_ι_m_roundsCount_bs_rev : I2ZBS_pos' RoundsBase_ι_m_roundsCount_bs_def = RoundsBase_ι_m_roundsCount .
Proof.
  prove_bs_rev RoundsBase_ι_m_roundsCount_bs RoundsBase_ι_m_roundsCount_pos RoundsBase_ι_m_roundsCount_fits. 
Qed.
Lemma RoundsBase_ι_m_roundsCount_bs257 : Z2IN 257 RoundsBase_ι_m_roundsCount = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    RoundsBase_ι_m_roundsCount_bs_def)) RoundsBase_ι_m_roundsCount_bs_def)).
Proof.
  prove_bs_rev RoundsBase_ι_m_roundsCount_bs_rev RoundsBase_ι_m_roundsCount_bs_def.
Qed.
Definition StakingContract_ι_NOM_FRACTION : Z := 70 .
 Definition StakingContract_ι_NODE_FRACTION : Z := 25 .
 Definition StakingContract_ι_REMOVE_STAKE_FEE : Z := 3*10^7 .
 Definition StakingContract_ι_ADD_STAKE_FEE : Z := 3*10^8 .
 Definition StakingContract_ι_PAUSE_STAKE_FEE : Z := 3*10^7 .
 Definition StakingContract_ι_CONTINUE_STAKE_FEE : Z := 3*10^7 .
 Definition StakingContract_ι_SET_REINVEST_FEE : Z := 3*10^7 .
 Definition StakingContract_ι_NOTIFY_FEE : Z := 3*10^6 .
 Definition StakingContract_ι_MIN_VAL_STAKE : Z := 10001000000000 .
 Definition StakingContract_ι_MAX_MSGS_PER_TR : Z := 40 .
 Definition StakingContract_ι_NODE_WALLET_MIN_STAKE : Z := 20 .
 Definition StakingContract_ι_TICKTOCK_PERIOD : Z := 30 .
 Definition StakingContract_ι_ROUND_UP_VALUE : Z := 1*10^9 .
 Definition StakingContract_ι_ANSWER_MSG_FEE : Z := 3*10^6 .
 Definition StakingContract_ι_STATUS_SUCCESS : Z := 0 .
 Definition StakingContract_ι_STATUS_NO_ACTIVE_ROUNDS : Z := 2 .
 Definition StakingContract_ι_STATUS_POOL_CLOSED : Z := 3 .
 Definition StakingContract_ι_STATUS_ROUND_STAKE_LIMIT : Z := 4 .
 Definition StakingContract_ι_STATUS_MSG_VAL_TOO_SMALL : Z := 5 .
 Definition StakingContract_ι_STATUS_NO_STAKE : Z := 6 .
  
Variables StakingContract_ι_m_minStake : Z . 
Variables (*! { _m_mn !*) _m_mn00 _m_mn01 _m_mn02 _m_mn03 _m_mn04 _m_mn05 _m_mn06 _m_mn07 _m_mn08 _m_mn09 _m_mn0A _m_mn0B _m_mn0C _m_mn0D _m_mn0E _m_mn0F _m_mn10 _m_mn11 _m_mn12 _m_mn13 _m_mn14 _m_mn15 _m_mn16 _m_mn17 _m_mn18 _m_mn19 _m_mn1A _m_mn1B _m_mn1C _m_mn1D _m_mn1E _m_mn1F _m_mn20 _m_mn21 _m_mn22 _m_mn23 _m_mn24 _m_mn25 _m_mn26 _m_mn27 _m_mn28 _m_mn29 _m_mn2A _m_mn2B _m_mn2C _m_mn2D _m_mn2E _m_mn2F _m_mn30 _m_mn31 _m_mn32 _m_mn33 _m_mn34 _m_mn35 _m_mn36 _m_mn37 _m_mn38 _m_mn39 _m_mn3A _m_mn3B _m_mn3C _m_mn3D _m_mn3E _m_mn3F  : TVMBit . 
Definition StakingContract_ι_m_minStake_bs_def := [> _m_mn00 , _m_mn01 , _m_mn02 , _m_mn03 , _m_mn04 , _m_mn05 , _m_mn06 , _m_mn07 , _m_mn08 , _m_mn09 , _m_mn0A , _m_mn0B , _m_mn0C , _m_mn0D , _m_mn0E , _m_mn0F , _m_mn10 , _m_mn11 , _m_mn12 , _m_mn13 , _m_mn14 , _m_mn15 , _m_mn16 , _m_mn17 , _m_mn18 , _m_mn19 , _m_mn1A , _m_mn1B , _m_mn1C , _m_mn1D , _m_mn1E , _m_mn1F , _m_mn20 , _m_mn21 , _m_mn22 , _m_mn23 , _m_mn24 , _m_mn25 , _m_mn26 , _m_mn27 , _m_mn28 , _m_mn29 , _m_mn2A , _m_mn2B , _m_mn2C , _m_mn2D , _m_mn2E , _m_mn2F , _m_mn30 , _m_mn31 , _m_mn32 , _m_mn33 , _m_mn34 , _m_mn35 , _m_mn36 , _m_mn37 , _m_mn38 , _m_mn39 , _m_mn3A , _m_mn3B , _m_mn3C , _m_mn3D , _m_mn3E , _m_mn3F <] .
Lemma StakingContract_ι_m_minStake_bs_id: StakingContract_ι_m_minStake_bs_def = [> _m_mn00 , _m_mn01 , _m_mn02 , _m_mn03 , _m_mn04 , _m_mn05 , _m_mn06 , _m_mn07 , _m_mn08 , _m_mn09 , _m_mn0A , _m_mn0B , _m_mn0C , _m_mn0D , _m_mn0E , _m_mn0F , _m_mn10 , _m_mn11 , _m_mn12 , _m_mn13 , _m_mn14 , _m_mn15 , _m_mn16 , _m_mn17 , _m_mn18 , _m_mn19 , _m_mn1A , _m_mn1B , _m_mn1C , _m_mn1D , _m_mn1E , _m_mn1F , _m_mn20 , _m_mn21 , _m_mn22 , _m_mn23 , _m_mn24 , _m_mn25 , _m_mn26 , _m_mn27 , _m_mn28 , _m_mn29 , _m_mn2A , _m_mn2B , _m_mn2C , _m_mn2D , _m_mn2E , _m_mn2F , _m_mn30 , _m_mn31 , _m_mn32 , _m_mn33 , _m_mn34 , _m_mn35 , _m_mn36 , _m_mn37 , _m_mn38 , _m_mn39 , _m_mn3A , _m_mn3B , _m_mn3C , _m_mn3D , _m_mn3E , _m_mn3F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι_m_minStake_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι_m_minStake_bs_def) StakingContract_ι_m_minStake = StakingContract_ι_m_minStake_bs_def.
Lemma StakingContract_ι_m_minStake_bs : Z2IBS_pos 64 StakingContract_ι_m_minStake = StakingContract_ι_m_minStake_bs_def.
Proof.
 rewrite <- StakingContract_ι_m_minStake_bs'. auto. Qed.
Axiom StakingContract_ι_m_minStake_pos: (0 <= StakingContract_ι_m_minStake )%Z.
Axiom StakingContract_ι_m_minStake_fits: zFitN_pos (tvmBitStringLen StakingContract_ι_m_minStake_bs_def) StakingContract_ι_m_minStake = true.
Lemma StakingContract_ι_m_minStake_bs_rev : I2ZBS_pos' StakingContract_ι_m_minStake_bs_def = StakingContract_ι_m_minStake .
Proof.
  prove_bs_rev StakingContract_ι_m_minStake_bs StakingContract_ι_m_minStake_pos StakingContract_ι_m_minStake_fits. 
Qed.
Lemma StakingContract_ι_m_minStake_bs257 : Z2IN 257 StakingContract_ι_m_minStake = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι_m_minStake_bs_def)) StakingContract_ι_m_minStake_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι_m_minStake_bs_rev StakingContract_ι_m_minStake_bs_def.
Qed. 
Variables StakingContract_ι_m_minRoundStake : Z . 
Variables (*! { _m_mn !*) _m_mn00 _m_mn01 _m_mn02 _m_mn03 _m_mn04 _m_mn05 _m_mn06 _m_mn07 _m_mn08 _m_mn09 _m_mn0A _m_mn0B _m_mn0C _m_mn0D _m_mn0E _m_mn0F _m_mn10 _m_mn11 _m_mn12 _m_mn13 _m_mn14 _m_mn15 _m_mn16 _m_mn17 _m_mn18 _m_mn19 _m_mn1A _m_mn1B _m_mn1C _m_mn1D _m_mn1E _m_mn1F _m_mn20 _m_mn21 _m_mn22 _m_mn23 _m_mn24 _m_mn25 _m_mn26 _m_mn27 _m_mn28 _m_mn29 _m_mn2A _m_mn2B _m_mn2C _m_mn2D _m_mn2E _m_mn2F _m_mn30 _m_mn31 _m_mn32 _m_mn33 _m_mn34 _m_mn35 _m_mn36 _m_mn37 _m_mn38 _m_mn39 _m_mn3A _m_mn3B _m_mn3C _m_mn3D _m_mn3E _m_mn3F  : TVMBit . 
Definition StakingContract_ι_m_minRoundStake_bs_def := [> _m_mn00 , _m_mn01 , _m_mn02 , _m_mn03 , _m_mn04 , _m_mn05 , _m_mn06 , _m_mn07 , _m_mn08 , _m_mn09 , _m_mn0A , _m_mn0B , _m_mn0C , _m_mn0D , _m_mn0E , _m_mn0F , _m_mn10 , _m_mn11 , _m_mn12 , _m_mn13 , _m_mn14 , _m_mn15 , _m_mn16 , _m_mn17 , _m_mn18 , _m_mn19 , _m_mn1A , _m_mn1B , _m_mn1C , _m_mn1D , _m_mn1E , _m_mn1F , _m_mn20 , _m_mn21 , _m_mn22 , _m_mn23 , _m_mn24 , _m_mn25 , _m_mn26 , _m_mn27 , _m_mn28 , _m_mn29 , _m_mn2A , _m_mn2B , _m_mn2C , _m_mn2D , _m_mn2E , _m_mn2F , _m_mn30 , _m_mn31 , _m_mn32 , _m_mn33 , _m_mn34 , _m_mn35 , _m_mn36 , _m_mn37 , _m_mn38 , _m_mn39 , _m_mn3A , _m_mn3B , _m_mn3C , _m_mn3D , _m_mn3E , _m_mn3F <] .
Lemma StakingContract_ι_m_minRoundStake_bs_id: StakingContract_ι_m_minRoundStake_bs_def = [> _m_mn00 , _m_mn01 , _m_mn02 , _m_mn03 , _m_mn04 , _m_mn05 , _m_mn06 , _m_mn07 , _m_mn08 , _m_mn09 , _m_mn0A , _m_mn0B , _m_mn0C , _m_mn0D , _m_mn0E , _m_mn0F , _m_mn10 , _m_mn11 , _m_mn12 , _m_mn13 , _m_mn14 , _m_mn15 , _m_mn16 , _m_mn17 , _m_mn18 , _m_mn19 , _m_mn1A , _m_mn1B , _m_mn1C , _m_mn1D , _m_mn1E , _m_mn1F , _m_mn20 , _m_mn21 , _m_mn22 , _m_mn23 , _m_mn24 , _m_mn25 , _m_mn26 , _m_mn27 , _m_mn28 , _m_mn29 , _m_mn2A , _m_mn2B , _m_mn2C , _m_mn2D , _m_mn2E , _m_mn2F , _m_mn30 , _m_mn31 , _m_mn32 , _m_mn33 , _m_mn34 , _m_mn35 , _m_mn36 , _m_mn37 , _m_mn38 , _m_mn39 , _m_mn3A , _m_mn3B , _m_mn3C , _m_mn3D , _m_mn3E , _m_mn3F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι_m_minRoundStake_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι_m_minRoundStake_bs_def) StakingContract_ι_m_minRoundStake = StakingContract_ι_m_minRoundStake_bs_def.
Lemma StakingContract_ι_m_minRoundStake_bs : Z2IBS_pos 64 StakingContract_ι_m_minRoundStake = StakingContract_ι_m_minRoundStake_bs_def.
Proof.
 rewrite <- StakingContract_ι_m_minRoundStake_bs'. auto. Qed.
Axiom StakingContract_ι_m_minRoundStake_pos: (0 <= StakingContract_ι_m_minRoundStake )%Z.
Axiom StakingContract_ι_m_minRoundStake_fits: zFitN_pos (tvmBitStringLen StakingContract_ι_m_minRoundStake_bs_def) StakingContract_ι_m_minRoundStake = true.
Lemma StakingContract_ι_m_minRoundStake_bs_rev : I2ZBS_pos' StakingContract_ι_m_minRoundStake_bs_def = StakingContract_ι_m_minRoundStake .
Proof.
  prove_bs_rev StakingContract_ι_m_minRoundStake_bs StakingContract_ι_m_minRoundStake_pos StakingContract_ι_m_minRoundStake_fits. 
Qed.
Lemma StakingContract_ι_m_minRoundStake_bs257 : Z2IN 257 StakingContract_ι_m_minRoundStake = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι_m_minRoundStake_bs_def)) StakingContract_ι_m_minRoundStake_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι_m_minRoundStake_bs_rev StakingContract_ι_m_minRoundStake_bs_def.
Qed. 
Variables StakingContract_ι_m_maxRoundStake : Z . 
Variables (*! { _m_mx !*) _m_mx00 _m_mx01 _m_mx02 _m_mx03 _m_mx04 _m_mx05 _m_mx06 _m_mx07 _m_mx08 _m_mx09 _m_mx0A _m_mx0B _m_mx0C _m_mx0D _m_mx0E _m_mx0F _m_mx10 _m_mx11 _m_mx12 _m_mx13 _m_mx14 _m_mx15 _m_mx16 _m_mx17 _m_mx18 _m_mx19 _m_mx1A _m_mx1B _m_mx1C _m_mx1D _m_mx1E _m_mx1F _m_mx20 _m_mx21 _m_mx22 _m_mx23 _m_mx24 _m_mx25 _m_mx26 _m_mx27 _m_mx28 _m_mx29 _m_mx2A _m_mx2B _m_mx2C _m_mx2D _m_mx2E _m_mx2F _m_mx30 _m_mx31 _m_mx32 _m_mx33 _m_mx34 _m_mx35 _m_mx36 _m_mx37 _m_mx38 _m_mx39 _m_mx3A _m_mx3B _m_mx3C _m_mx3D _m_mx3E _m_mx3F  : TVMBit . 
Definition StakingContract_ι_m_maxRoundStake_bs_def := [> _m_mx00 , _m_mx01 , _m_mx02 , _m_mx03 , _m_mx04 , _m_mx05 , _m_mx06 , _m_mx07 , _m_mx08 , _m_mx09 , _m_mx0A , _m_mx0B , _m_mx0C , _m_mx0D , _m_mx0E , _m_mx0F , _m_mx10 , _m_mx11 , _m_mx12 , _m_mx13 , _m_mx14 , _m_mx15 , _m_mx16 , _m_mx17 , _m_mx18 , _m_mx19 , _m_mx1A , _m_mx1B , _m_mx1C , _m_mx1D , _m_mx1E , _m_mx1F , _m_mx20 , _m_mx21 , _m_mx22 , _m_mx23 , _m_mx24 , _m_mx25 , _m_mx26 , _m_mx27 , _m_mx28 , _m_mx29 , _m_mx2A , _m_mx2B , _m_mx2C , _m_mx2D , _m_mx2E , _m_mx2F , _m_mx30 , _m_mx31 , _m_mx32 , _m_mx33 , _m_mx34 , _m_mx35 , _m_mx36 , _m_mx37 , _m_mx38 , _m_mx39 , _m_mx3A , _m_mx3B , _m_mx3C , _m_mx3D , _m_mx3E , _m_mx3F <] .
Lemma StakingContract_ι_m_maxRoundStake_bs_id: StakingContract_ι_m_maxRoundStake_bs_def = [> _m_mx00 , _m_mx01 , _m_mx02 , _m_mx03 , _m_mx04 , _m_mx05 , _m_mx06 , _m_mx07 , _m_mx08 , _m_mx09 , _m_mx0A , _m_mx0B , _m_mx0C , _m_mx0D , _m_mx0E , _m_mx0F , _m_mx10 , _m_mx11 , _m_mx12 , _m_mx13 , _m_mx14 , _m_mx15 , _m_mx16 , _m_mx17 , _m_mx18 , _m_mx19 , _m_mx1A , _m_mx1B , _m_mx1C , _m_mx1D , _m_mx1E , _m_mx1F , _m_mx20 , _m_mx21 , _m_mx22 , _m_mx23 , _m_mx24 , _m_mx25 , _m_mx26 , _m_mx27 , _m_mx28 , _m_mx29 , _m_mx2A , _m_mx2B , _m_mx2C , _m_mx2D , _m_mx2E , _m_mx2F , _m_mx30 , _m_mx31 , _m_mx32 , _m_mx33 , _m_mx34 , _m_mx35 , _m_mx36 , _m_mx37 , _m_mx38 , _m_mx39 , _m_mx3A , _m_mx3B , _m_mx3C , _m_mx3D , _m_mx3E , _m_mx3F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι_m_maxRoundStake_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι_m_maxRoundStake_bs_def) StakingContract_ι_m_maxRoundStake = StakingContract_ι_m_maxRoundStake_bs_def.
Lemma StakingContract_ι_m_maxRoundStake_bs : Z2IBS_pos 64 StakingContract_ι_m_maxRoundStake = StakingContract_ι_m_maxRoundStake_bs_def.
Proof.
 rewrite <- StakingContract_ι_m_maxRoundStake_bs'. auto. Qed.
Axiom StakingContract_ι_m_maxRoundStake_pos: (0 <= StakingContract_ι_m_maxRoundStake )%Z.
Axiom StakingContract_ι_m_maxRoundStake_fits: zFitN_pos (tvmBitStringLen StakingContract_ι_m_maxRoundStake_bs_def) StakingContract_ι_m_maxRoundStake = true.
Lemma StakingContract_ι_m_maxRoundStake_bs_rev : I2ZBS_pos' StakingContract_ι_m_maxRoundStake_bs_def = StakingContract_ι_m_maxRoundStake .
Proof.
  prove_bs_rev StakingContract_ι_m_maxRoundStake_bs StakingContract_ι_m_maxRoundStake_pos StakingContract_ι_m_maxRoundStake_fits. 
Qed.
Lemma StakingContract_ι_m_maxRoundStake_bs257 : Z2IN 257 StakingContract_ι_m_maxRoundStake = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι_m_maxRoundStake_bs_def)) StakingContract_ι_m_maxRoundStake_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι_m_maxRoundStake_bs_rev StakingContract_ι_m_maxRoundStake_bs_def.
Qed. 
Variables StakingContract_ι_m_lastRoundInterest : Z . 
Variables (*! { _m_ls !*) _m_ls00 _m_ls01 _m_ls02 _m_ls03 _m_ls04 _m_ls05 _m_ls06 _m_ls07 _m_ls08 _m_ls09 _m_ls0A _m_ls0B _m_ls0C _m_ls0D _m_ls0E _m_ls0F _m_ls10 _m_ls11 _m_ls12 _m_ls13 _m_ls14 _m_ls15 _m_ls16 _m_ls17 _m_ls18 _m_ls19 _m_ls1A _m_ls1B _m_ls1C _m_ls1D _m_ls1E _m_ls1F _m_ls20 _m_ls21 _m_ls22 _m_ls23 _m_ls24 _m_ls25 _m_ls26 _m_ls27 _m_ls28 _m_ls29 _m_ls2A _m_ls2B _m_ls2C _m_ls2D _m_ls2E _m_ls2F _m_ls30 _m_ls31 _m_ls32 _m_ls33 _m_ls34 _m_ls35 _m_ls36 _m_ls37 _m_ls38 _m_ls39 _m_ls3A _m_ls3B _m_ls3C _m_ls3D _m_ls3E _m_ls3F  : TVMBit . 
Definition StakingContract_ι_m_lastRoundInterest_bs_def := [> _m_ls00 , _m_ls01 , _m_ls02 , _m_ls03 , _m_ls04 , _m_ls05 , _m_ls06 , _m_ls07 , _m_ls08 , _m_ls09 , _m_ls0A , _m_ls0B , _m_ls0C , _m_ls0D , _m_ls0E , _m_ls0F , _m_ls10 , _m_ls11 , _m_ls12 , _m_ls13 , _m_ls14 , _m_ls15 , _m_ls16 , _m_ls17 , _m_ls18 , _m_ls19 , _m_ls1A , _m_ls1B , _m_ls1C , _m_ls1D , _m_ls1E , _m_ls1F , _m_ls20 , _m_ls21 , _m_ls22 , _m_ls23 , _m_ls24 , _m_ls25 , _m_ls26 , _m_ls27 , _m_ls28 , _m_ls29 , _m_ls2A , _m_ls2B , _m_ls2C , _m_ls2D , _m_ls2E , _m_ls2F , _m_ls30 , _m_ls31 , _m_ls32 , _m_ls33 , _m_ls34 , _m_ls35 , _m_ls36 , _m_ls37 , _m_ls38 , _m_ls39 , _m_ls3A , _m_ls3B , _m_ls3C , _m_ls3D , _m_ls3E , _m_ls3F <] .
Lemma StakingContract_ι_m_lastRoundInterest_bs_id: StakingContract_ι_m_lastRoundInterest_bs_def = [> _m_ls00 , _m_ls01 , _m_ls02 , _m_ls03 , _m_ls04 , _m_ls05 , _m_ls06 , _m_ls07 , _m_ls08 , _m_ls09 , _m_ls0A , _m_ls0B , _m_ls0C , _m_ls0D , _m_ls0E , _m_ls0F , _m_ls10 , _m_ls11 , _m_ls12 , _m_ls13 , _m_ls14 , _m_ls15 , _m_ls16 , _m_ls17 , _m_ls18 , _m_ls19 , _m_ls1A , _m_ls1B , _m_ls1C , _m_ls1D , _m_ls1E , _m_ls1F , _m_ls20 , _m_ls21 , _m_ls22 , _m_ls23 , _m_ls24 , _m_ls25 , _m_ls26 , _m_ls27 , _m_ls28 , _m_ls29 , _m_ls2A , _m_ls2B , _m_ls2C , _m_ls2D , _m_ls2E , _m_ls2F , _m_ls30 , _m_ls31 , _m_ls32 , _m_ls33 , _m_ls34 , _m_ls35 , _m_ls36 , _m_ls37 , _m_ls38 , _m_ls39 , _m_ls3A , _m_ls3B , _m_ls3C , _m_ls3D , _m_ls3E , _m_ls3F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι_m_lastRoundInterest_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι_m_lastRoundInterest_bs_def) StakingContract_ι_m_lastRoundInterest = StakingContract_ι_m_lastRoundInterest_bs_def.
Lemma StakingContract_ι_m_lastRoundInterest_bs : Z2IBS_pos 64 StakingContract_ι_m_lastRoundInterest = StakingContract_ι_m_lastRoundInterest_bs_def.
Proof.
 rewrite <- StakingContract_ι_m_lastRoundInterest_bs'. auto. Qed.
Axiom StakingContract_ι_m_lastRoundInterest_pos: (0 <= StakingContract_ι_m_lastRoundInterest )%Z.
Axiom StakingContract_ι_m_lastRoundInterest_fits: zFitN_pos (tvmBitStringLen StakingContract_ι_m_lastRoundInterest_bs_def) StakingContract_ι_m_lastRoundInterest = true.
Lemma StakingContract_ι_m_lastRoundInterest_bs_rev : I2ZBS_pos' StakingContract_ι_m_lastRoundInterest_bs_def = StakingContract_ι_m_lastRoundInterest .
Proof.
  prove_bs_rev StakingContract_ι_m_lastRoundInterest_bs StakingContract_ι_m_lastRoundInterest_pos StakingContract_ι_m_lastRoundInterest_fits. 
Qed.
Lemma StakingContract_ι_m_lastRoundInterest_bs257 : Z2IN 257 StakingContract_ι_m_lastRoundInterest = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι_m_lastRoundInterest_bs_def)) StakingContract_ι_m_lastRoundInterest_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι_m_lastRoundInterest_bs_rev StakingContract_ι_m_lastRoundInterest_bs_def.
Qed.

Variables OwnerBase_ι_withdrawOwnerReward_А_amount : Z . 
Variables (*! { _mnt !*) _mnt00 _mnt01 _mnt02 _mnt03 _mnt04 _mnt05 _mnt06 _mnt07 _mnt08 _mnt09 _mnt0A _mnt0B _mnt0C _mnt0D _mnt0E _mnt0F _mnt10 _mnt11 _mnt12 _mnt13 _mnt14 _mnt15 _mnt16 _mnt17 _mnt18 _mnt19 _mnt1A _mnt1B _mnt1C _mnt1D _mnt1E _mnt1F _mnt20 _mnt21 _mnt22 _mnt23 _mnt24 _mnt25 _mnt26 _mnt27 _mnt28 _mnt29 _mnt2A _mnt2B _mnt2C _mnt2D _mnt2E _mnt2F _mnt30 _mnt31 _mnt32 _mnt33 _mnt34 _mnt35 _mnt36 _mnt37 _mnt38 _mnt39 _mnt3A _mnt3B _mnt3C _mnt3D _mnt3E _mnt3F  : TVMBit . 
Definition OwnerBase_ι_withdrawOwnerReward_А_amount_bs_def := [> _mnt00 , _mnt01 , _mnt02 , _mnt03 , _mnt04 , _mnt05 , _mnt06 , _mnt07 , _mnt08 , _mnt09 , _mnt0A , _mnt0B , _mnt0C , _mnt0D , _mnt0E , _mnt0F , _mnt10 , _mnt11 , _mnt12 , _mnt13 , _mnt14 , _mnt15 , _mnt16 , _mnt17 , _mnt18 , _mnt19 , _mnt1A , _mnt1B , _mnt1C , _mnt1D , _mnt1E , _mnt1F , _mnt20 , _mnt21 , _mnt22 , _mnt23 , _mnt24 , _mnt25 , _mnt26 , _mnt27 , _mnt28 , _mnt29 , _mnt2A , _mnt2B , _mnt2C , _mnt2D , _mnt2E , _mnt2F , _mnt30 , _mnt31 , _mnt32 , _mnt33 , _mnt34 , _mnt35 , _mnt36 , _mnt37 , _mnt38 , _mnt39 , _mnt3A , _mnt3B , _mnt3C , _mnt3D , _mnt3E , _mnt3F <] .
Lemma OwnerBase_ι_withdrawOwnerReward_А_amount_bs_id: OwnerBase_ι_withdrawOwnerReward_А_amount_bs_def = [> _mnt00 , _mnt01 , _mnt02 , _mnt03 , _mnt04 , _mnt05 , _mnt06 , _mnt07 , _mnt08 , _mnt09 , _mnt0A , _mnt0B , _mnt0C , _mnt0D , _mnt0E , _mnt0F , _mnt10 , _mnt11 , _mnt12 , _mnt13 , _mnt14 , _mnt15 , _mnt16 , _mnt17 , _mnt18 , _mnt19 , _mnt1A , _mnt1B , _mnt1C , _mnt1D , _mnt1E , _mnt1F , _mnt20 , _mnt21 , _mnt22 , _mnt23 , _mnt24 , _mnt25 , _mnt26 , _mnt27 , _mnt28 , _mnt29 , _mnt2A , _mnt2B , _mnt2C , _mnt2D , _mnt2E , _mnt2F , _mnt30 , _mnt31 , _mnt32 , _mnt33 , _mnt34 , _mnt35 , _mnt36 , _mnt37 , _mnt38 , _mnt39 , _mnt3A , _mnt3B , _mnt3C , _mnt3D , _mnt3E , _mnt3F (* } !*)  <] .
Proof. auto. Qed.
Axiom OwnerBase_ι_withdrawOwnerReward_А_amount_bs' : Z2IBS_pos (tvmBitStringLen OwnerBase_ι_withdrawOwnerReward_А_amount_bs_def) OwnerBase_ι_withdrawOwnerReward_А_amount = OwnerBase_ι_withdrawOwnerReward_А_amount_bs_def.
Lemma OwnerBase_ι_withdrawOwnerReward_А_amount_bs : Z2IBS_pos 64 OwnerBase_ι_withdrawOwnerReward_А_amount = OwnerBase_ι_withdrawOwnerReward_А_amount_bs_def.
Proof.
 rewrite <- OwnerBase_ι_withdrawOwnerReward_А_amount_bs'. auto. Qed.
Axiom OwnerBase_ι_withdrawOwnerReward_А_amount_pos: (0 <= OwnerBase_ι_withdrawOwnerReward_А_amount )%Z.
Axiom OwnerBase_ι_withdrawOwnerReward_А_amount_fits: zFitN_pos (tvmBitStringLen OwnerBase_ι_withdrawOwnerReward_А_amount_bs_def) OwnerBase_ι_withdrawOwnerReward_А_amount = true.
Lemma OwnerBase_ι_withdrawOwnerReward_А_amount_bs_rev : I2ZBS_pos' OwnerBase_ι_withdrawOwnerReward_А_amount_bs_def = OwnerBase_ι_withdrawOwnerReward_А_amount .
Proof.
  prove_bs_rev OwnerBase_ι_withdrawOwnerReward_А_amount_bs OwnerBase_ι_withdrawOwnerReward_А_amount_pos OwnerBase_ι_withdrawOwnerReward_А_amount_fits. 
Qed.
Lemma OwnerBase_ι_withdrawOwnerReward_А_amount_bs257 : Z2IN 257 OwnerBase_ι_withdrawOwnerReward_А_amount = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    OwnerBase_ι_withdrawOwnerReward_А_amount_bs_def)) OwnerBase_ι_withdrawOwnerReward_А_amount_bs_def)).
Proof.
  prove_bs_rev OwnerBase_ι_withdrawOwnerReward_А_amount_bs_rev OwnerBase_ι_withdrawOwnerReward_А_amount_bs_def.
Qed.

Variables OwnerBase_ι__increaseOwnerReward_А_ownerReward : Z . 
Variables (*! { _wnrR !*) _wnrR00 _wnrR01 _wnrR02 _wnrR03 _wnrR04 _wnrR05 _wnrR06 _wnrR07 _wnrR08 _wnrR09 _wnrR0A _wnrR0B _wnrR0C _wnrR0D _wnrR0E _wnrR0F _wnrR10 _wnrR11 _wnrR12 _wnrR13 _wnrR14 _wnrR15 _wnrR16 _wnrR17 _wnrR18 _wnrR19 _wnrR1A _wnrR1B _wnrR1C _wnrR1D _wnrR1E _wnrR1F _wnrR20 _wnrR21 _wnrR22 _wnrR23 _wnrR24 _wnrR25 _wnrR26 _wnrR27 _wnrR28 _wnrR29 _wnrR2A _wnrR2B _wnrR2C _wnrR2D _wnrR2E _wnrR2F _wnrR30 _wnrR31 _wnrR32 _wnrR33 _wnrR34 _wnrR35 _wnrR36 _wnrR37 _wnrR38 _wnrR39 _wnrR3A _wnrR3B _wnrR3C _wnrR3D _wnrR3E _wnrR3F  : TVMBit . 
Definition OwnerBase_ι__increaseOwnerReward_А_ownerReward_bs_def := [> _wnrR00 , _wnrR01 , _wnrR02 , _wnrR03 , _wnrR04 , _wnrR05 , _wnrR06 , _wnrR07 , _wnrR08 , _wnrR09 , _wnrR0A , _wnrR0B , _wnrR0C , _wnrR0D , _wnrR0E , _wnrR0F , _wnrR10 , _wnrR11 , _wnrR12 , _wnrR13 , _wnrR14 , _wnrR15 , _wnrR16 , _wnrR17 , _wnrR18 , _wnrR19 , _wnrR1A , _wnrR1B , _wnrR1C , _wnrR1D , _wnrR1E , _wnrR1F , _wnrR20 , _wnrR21 , _wnrR22 , _wnrR23 , _wnrR24 , _wnrR25 , _wnrR26 , _wnrR27 , _wnrR28 , _wnrR29 , _wnrR2A , _wnrR2B , _wnrR2C , _wnrR2D , _wnrR2E , _wnrR2F , _wnrR30 , _wnrR31 , _wnrR32 , _wnrR33 , _wnrR34 , _wnrR35 , _wnrR36 , _wnrR37 , _wnrR38 , _wnrR39 , _wnrR3A , _wnrR3B , _wnrR3C , _wnrR3D , _wnrR3E , _wnrR3F <] .
Lemma OwnerBase_ι__increaseOwnerReward_А_ownerReward_bs_id: OwnerBase_ι__increaseOwnerReward_А_ownerReward_bs_def = [> _wnrR00 , _wnrR01 , _wnrR02 , _wnrR03 , _wnrR04 , _wnrR05 , _wnrR06 , _wnrR07 , _wnrR08 , _wnrR09 , _wnrR0A , _wnrR0B , _wnrR0C , _wnrR0D , _wnrR0E , _wnrR0F , _wnrR10 , _wnrR11 , _wnrR12 , _wnrR13 , _wnrR14 , _wnrR15 , _wnrR16 , _wnrR17 , _wnrR18 , _wnrR19 , _wnrR1A , _wnrR1B , _wnrR1C , _wnrR1D , _wnrR1E , _wnrR1F , _wnrR20 , _wnrR21 , _wnrR22 , _wnrR23 , _wnrR24 , _wnrR25 , _wnrR26 , _wnrR27 , _wnrR28 , _wnrR29 , _wnrR2A , _wnrR2B , _wnrR2C , _wnrR2D , _wnrR2E , _wnrR2F , _wnrR30 , _wnrR31 , _wnrR32 , _wnrR33 , _wnrR34 , _wnrR35 , _wnrR36 , _wnrR37 , _wnrR38 , _wnrR39 , _wnrR3A , _wnrR3B , _wnrR3C , _wnrR3D , _wnrR3E , _wnrR3F (* } !*)  <] .
Proof. auto. Qed.
Axiom OwnerBase_ι__increaseOwnerReward_А_ownerReward_bs' : Z2IBS_pos (tvmBitStringLen OwnerBase_ι__increaseOwnerReward_А_ownerReward_bs_def) OwnerBase_ι__increaseOwnerReward_А_ownerReward = OwnerBase_ι__increaseOwnerReward_А_ownerReward_bs_def.
Lemma OwnerBase_ι__increaseOwnerReward_А_ownerReward_bs : Z2IBS_pos 64 OwnerBase_ι__increaseOwnerReward_А_ownerReward = OwnerBase_ι__increaseOwnerReward_А_ownerReward_bs_def.
Proof.
 rewrite <- OwnerBase_ι__increaseOwnerReward_А_ownerReward_bs'. auto. Qed.
Axiom OwnerBase_ι__increaseOwnerReward_А_ownerReward_pos: (0 <= OwnerBase_ι__increaseOwnerReward_А_ownerReward )%Z.
Axiom OwnerBase_ι__increaseOwnerReward_А_ownerReward_fits: zFitN_pos (tvmBitStringLen OwnerBase_ι__increaseOwnerReward_А_ownerReward_bs_def) OwnerBase_ι__increaseOwnerReward_А_ownerReward = true.
Lemma OwnerBase_ι__increaseOwnerReward_А_ownerReward_bs_rev : I2ZBS_pos' OwnerBase_ι__increaseOwnerReward_А_ownerReward_bs_def = OwnerBase_ι__increaseOwnerReward_А_ownerReward .
Proof.
  prove_bs_rev OwnerBase_ι__increaseOwnerReward_А_ownerReward_bs OwnerBase_ι__increaseOwnerReward_А_ownerReward_pos OwnerBase_ι__increaseOwnerReward_А_ownerReward_fits. 
Qed.
Lemma OwnerBase_ι__increaseOwnerReward_А_ownerReward_bs257 : Z2IN 257 OwnerBase_ι__increaseOwnerReward_А_ownerReward = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    OwnerBase_ι__increaseOwnerReward_А_ownerReward_bs_def)) OwnerBase_ι__increaseOwnerReward_А_ownerReward_bs_def)).
Proof.
  prove_bs_rev OwnerBase_ι__increaseOwnerReward_А_ownerReward_bs_rev OwnerBase_ι__increaseOwnerReward_А_ownerReward_bs_def.
Qed.

Variables ElectorBase_ι__recoverPendingRoundStakes_А_pendingId : Z . 
Variables (*! { _pndn !*) _pndn00 _pndn01 _pndn02 _pndn03 _pndn04 _pndn05 _pndn06 _pndn07 _pndn08 _pndn09 _pndn0A _pndn0B _pndn0C _pndn0D _pndn0E _pndn0F _pndn10 _pndn11 _pndn12 _pndn13 _pndn14 _pndn15 _pndn16 _pndn17 _pndn18 _pndn19 _pndn1A _pndn1B _pndn1C _pndn1D _pndn1E _pndn1F  : TVMBit . 
Definition ElectorBase_ι__recoverPendingRoundStakes_А_pendingId_bs_def := [> _pndn00 , _pndn01 , _pndn02 , _pndn03 , _pndn04 , _pndn05 , _pndn06 , _pndn07 , _pndn08 , _pndn09 , _pndn0A , _pndn0B , _pndn0C , _pndn0D , _pndn0E , _pndn0F , _pndn10 , _pndn11 , _pndn12 , _pndn13 , _pndn14 , _pndn15 , _pndn16 , _pndn17 , _pndn18 , _pndn19 , _pndn1A , _pndn1B , _pndn1C , _pndn1D , _pndn1E , _pndn1F <] .
Lemma ElectorBase_ι__recoverPendingRoundStakes_А_pendingId_bs_id: ElectorBase_ι__recoverPendingRoundStakes_А_pendingId_bs_def = [> _pndn00 , _pndn01 , _pndn02 , _pndn03 , _pndn04 , _pndn05 , _pndn06 , _pndn07 , _pndn08 , _pndn09 , _pndn0A , _pndn0B , _pndn0C , _pndn0D , _pndn0E , _pndn0F , _pndn10 , _pndn11 , _pndn12 , _pndn13 , _pndn14 , _pndn15 , _pndn16 , _pndn17 , _pndn18 , _pndn19 , _pndn1A , _pndn1B , _pndn1C , _pndn1D , _pndn1E , _pndn1F (* } !*)  <] .
Proof. auto. Qed.
Axiom ElectorBase_ι__recoverPendingRoundStakes_А_pendingId_bs' : Z2IBS_pos (tvmBitStringLen ElectorBase_ι__recoverPendingRoundStakes_А_pendingId_bs_def) ElectorBase_ι__recoverPendingRoundStakes_А_pendingId = ElectorBase_ι__recoverPendingRoundStakes_А_pendingId_bs_def.
Lemma ElectorBase_ι__recoverPendingRoundStakes_А_pendingId_bs : Z2IBS_pos 32 ElectorBase_ι__recoverPendingRoundStakes_А_pendingId = ElectorBase_ι__recoverPendingRoundStakes_А_pendingId_bs_def.
Proof.
 rewrite <- ElectorBase_ι__recoverPendingRoundStakes_А_pendingId_bs'. auto. Qed.
Axiom ElectorBase_ι__recoverPendingRoundStakes_А_pendingId_pos: (0 <= ElectorBase_ι__recoverPendingRoundStakes_А_pendingId )%Z.
Axiom ElectorBase_ι__recoverPendingRoundStakes_А_pendingId_fits: zFitN_pos (tvmBitStringLen ElectorBase_ι__recoverPendingRoundStakes_А_pendingId_bs_def) ElectorBase_ι__recoverPendingRoundStakes_А_pendingId = true.
Lemma ElectorBase_ι__recoverPendingRoundStakes_А_pendingId_bs_rev : I2ZBS_pos' ElectorBase_ι__recoverPendingRoundStakes_А_pendingId_bs_def = ElectorBase_ι__recoverPendingRoundStakes_А_pendingId .
Proof.
  prove_bs_rev ElectorBase_ι__recoverPendingRoundStakes_А_pendingId_bs ElectorBase_ι__recoverPendingRoundStakes_А_pendingId_pos ElectorBase_ι__recoverPendingRoundStakes_А_pendingId_fits. 
Qed.
Lemma ElectorBase_ι__recoverPendingRoundStakes_А_pendingId_bs257 : Z2IN 257 ElectorBase_ι__recoverPendingRoundStakes_А_pendingId = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    ElectorBase_ι__recoverPendingRoundStakes_А_pendingId_bs_def)) ElectorBase_ι__recoverPendingRoundStakes_А_pendingId_bs_def)).
Proof.
  prove_bs_rev ElectorBase_ι__recoverPendingRoundStakes_А_pendingId_bs_rev ElectorBase_ι__recoverPendingRoundStakes_А_pendingId_bs_def.
Qed.
 
Variables ElectorBase_ι__runForElection_А_nodeStake : Z . 
Variables (*! { _ndSt !*) _ndSt00 _ndSt01 _ndSt02 _ndSt03 _ndSt04 _ndSt05 _ndSt06 _ndSt07 _ndSt08 _ndSt09 _ndSt0A _ndSt0B _ndSt0C _ndSt0D _ndSt0E _ndSt0F _ndSt10 _ndSt11 _ndSt12 _ndSt13 _ndSt14 _ndSt15 _ndSt16 _ndSt17 _ndSt18 _ndSt19 _ndSt1A _ndSt1B _ndSt1C _ndSt1D _ndSt1E _ndSt1F _ndSt20 _ndSt21 _ndSt22 _ndSt23 _ndSt24 _ndSt25 _ndSt26 _ndSt27 _ndSt28 _ndSt29 _ndSt2A _ndSt2B _ndSt2C _ndSt2D _ndSt2E _ndSt2F _ndSt30 _ndSt31 _ndSt32 _ndSt33 _ndSt34 _ndSt35 _ndSt36 _ndSt37 _ndSt38 _ndSt39 _ndSt3A _ndSt3B _ndSt3C _ndSt3D _ndSt3E _ndSt3F  : TVMBit . 
Definition ElectorBase_ι__runForElection_А_nodeStake_bs_def := [> _ndSt00 , _ndSt01 , _ndSt02 , _ndSt03 , _ndSt04 , _ndSt05 , _ndSt06 , _ndSt07 , _ndSt08 , _ndSt09 , _ndSt0A , _ndSt0B , _ndSt0C , _ndSt0D , _ndSt0E , _ndSt0F , _ndSt10 , _ndSt11 , _ndSt12 , _ndSt13 , _ndSt14 , _ndSt15 , _ndSt16 , _ndSt17 , _ndSt18 , _ndSt19 , _ndSt1A , _ndSt1B , _ndSt1C , _ndSt1D , _ndSt1E , _ndSt1F , _ndSt20 , _ndSt21 , _ndSt22 , _ndSt23 , _ndSt24 , _ndSt25 , _ndSt26 , _ndSt27 , _ndSt28 , _ndSt29 , _ndSt2A , _ndSt2B , _ndSt2C , _ndSt2D , _ndSt2E , _ndSt2F , _ndSt30 , _ndSt31 , _ndSt32 , _ndSt33 , _ndSt34 , _ndSt35 , _ndSt36 , _ndSt37 , _ndSt38 , _ndSt39 , _ndSt3A , _ndSt3B , _ndSt3C , _ndSt3D , _ndSt3E , _ndSt3F <] .
Lemma ElectorBase_ι__runForElection_А_nodeStake_bs_id: ElectorBase_ι__runForElection_А_nodeStake_bs_def = [> _ndSt00 , _ndSt01 , _ndSt02 , _ndSt03 , _ndSt04 , _ndSt05 , _ndSt06 , _ndSt07 , _ndSt08 , _ndSt09 , _ndSt0A , _ndSt0B , _ndSt0C , _ndSt0D , _ndSt0E , _ndSt0F , _ndSt10 , _ndSt11 , _ndSt12 , _ndSt13 , _ndSt14 , _ndSt15 , _ndSt16 , _ndSt17 , _ndSt18 , _ndSt19 , _ndSt1A , _ndSt1B , _ndSt1C , _ndSt1D , _ndSt1E , _ndSt1F , _ndSt20 , _ndSt21 , _ndSt22 , _ndSt23 , _ndSt24 , _ndSt25 , _ndSt26 , _ndSt27 , _ndSt28 , _ndSt29 , _ndSt2A , _ndSt2B , _ndSt2C , _ndSt2D , _ndSt2E , _ndSt2F , _ndSt30 , _ndSt31 , _ndSt32 , _ndSt33 , _ndSt34 , _ndSt35 , _ndSt36 , _ndSt37 , _ndSt38 , _ndSt39 , _ndSt3A , _ndSt3B , _ndSt3C , _ndSt3D , _ndSt3E , _ndSt3F (* } !*)  <] .
Proof. auto. Qed.
Axiom ElectorBase_ι__runForElection_А_nodeStake_bs' : Z2IBS_pos (tvmBitStringLen ElectorBase_ι__runForElection_А_nodeStake_bs_def) ElectorBase_ι__runForElection_А_nodeStake = ElectorBase_ι__runForElection_А_nodeStake_bs_def.
Lemma ElectorBase_ι__runForElection_А_nodeStake_bs : Z2IBS_pos 64 ElectorBase_ι__runForElection_А_nodeStake = ElectorBase_ι__runForElection_А_nodeStake_bs_def.
Proof.
 rewrite <- ElectorBase_ι__runForElection_А_nodeStake_bs'. auto. Qed.
Axiom ElectorBase_ι__runForElection_А_nodeStake_pos: (0 <= ElectorBase_ι__runForElection_А_nodeStake )%Z.
Axiom ElectorBase_ι__runForElection_А_nodeStake_fits: zFitN_pos (tvmBitStringLen ElectorBase_ι__runForElection_А_nodeStake_bs_def) ElectorBase_ι__runForElection_А_nodeStake = true.
Lemma ElectorBase_ι__runForElection_А_nodeStake_bs_rev : I2ZBS_pos' ElectorBase_ι__runForElection_А_nodeStake_bs_def = ElectorBase_ι__runForElection_А_nodeStake .
Proof.
  prove_bs_rev ElectorBase_ι__runForElection_А_nodeStake_bs ElectorBase_ι__runForElection_А_nodeStake_pos ElectorBase_ι__runForElection_А_nodeStake_fits. 
Qed.
Lemma ElectorBase_ι__runForElection_А_nodeStake_bs257 : Z2IN 257 ElectorBase_ι__runForElection_А_nodeStake = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    ElectorBase_ι__runForElection_А_nodeStake_bs_def)) ElectorBase_ι__runForElection_А_nodeStake_bs_def)).
Proof.
  prove_bs_rev ElectorBase_ι__runForElection_А_nodeStake_bs_rev ElectorBase_ι__runForElection_А_nodeStake_bs_def.
Qed.

Variables ElectionParams_ι__isRoundUnfrozen_А_oldestRoundId : Z . 
Variables (*! { _ldst !*) _ldst00 _ldst01 _ldst02 _ldst03 _ldst04 _ldst05 _ldst06 _ldst07 _ldst08 _ldst09 _ldst0A _ldst0B _ldst0C _ldst0D _ldst0E _ldst0F _ldst10 _ldst11 _ldst12 _ldst13 _ldst14 _ldst15 _ldst16 _ldst17 _ldst18 _ldst19 _ldst1A _ldst1B _ldst1C _ldst1D _ldst1E _ldst1F  : TVMBit . 
Definition ElectionParams_ι__isRoundUnfrozen_А_oldestRoundId_bs_def := [> _ldst00 , _ldst01 , _ldst02 , _ldst03 , _ldst04 , _ldst05 , _ldst06 , _ldst07 , _ldst08 , _ldst09 , _ldst0A , _ldst0B , _ldst0C , _ldst0D , _ldst0E , _ldst0F , _ldst10 , _ldst11 , _ldst12 , _ldst13 , _ldst14 , _ldst15 , _ldst16 , _ldst17 , _ldst18 , _ldst19 , _ldst1A , _ldst1B , _ldst1C , _ldst1D , _ldst1E , _ldst1F <] .
Lemma ElectionParams_ι__isRoundUnfrozen_А_oldestRoundId_bs_id: ElectionParams_ι__isRoundUnfrozen_А_oldestRoundId_bs_def = [> _ldst00 , _ldst01 , _ldst02 , _ldst03 , _ldst04 , _ldst05 , _ldst06 , _ldst07 , _ldst08 , _ldst09 , _ldst0A , _ldst0B , _ldst0C , _ldst0D , _ldst0E , _ldst0F , _ldst10 , _ldst11 , _ldst12 , _ldst13 , _ldst14 , _ldst15 , _ldst16 , _ldst17 , _ldst18 , _ldst19 , _ldst1A , _ldst1B , _ldst1C , _ldst1D , _ldst1E , _ldst1F (* } !*)  <] .
Proof. auto. Qed.
Axiom ElectionParams_ι__isRoundUnfrozen_А_oldestRoundId_bs' : Z2IBS_pos (tvmBitStringLen ElectionParams_ι__isRoundUnfrozen_А_oldestRoundId_bs_def) ElectionParams_ι__isRoundUnfrozen_А_oldestRoundId = ElectionParams_ι__isRoundUnfrozen_А_oldestRoundId_bs_def.
Lemma ElectionParams_ι__isRoundUnfrozen_А_oldestRoundId_bs : Z2IBS_pos 32 ElectionParams_ι__isRoundUnfrozen_А_oldestRoundId = ElectionParams_ι__isRoundUnfrozen_А_oldestRoundId_bs_def.
Proof.
 rewrite <- ElectionParams_ι__isRoundUnfrozen_А_oldestRoundId_bs'. auto. Qed.
Axiom ElectionParams_ι__isRoundUnfrozen_А_oldestRoundId_pos: (0 <= ElectionParams_ι__isRoundUnfrozen_А_oldestRoundId )%Z.
Axiom ElectionParams_ι__isRoundUnfrozen_А_oldestRoundId_fits: zFitN_pos (tvmBitStringLen ElectionParams_ι__isRoundUnfrozen_А_oldestRoundId_bs_def) ElectionParams_ι__isRoundUnfrozen_А_oldestRoundId = true.
Lemma ElectionParams_ι__isRoundUnfrozen_А_oldestRoundId_bs_rev : I2ZBS_pos' ElectionParams_ι__isRoundUnfrozen_А_oldestRoundId_bs_def = ElectionParams_ι__isRoundUnfrozen_А_oldestRoundId .
Proof.
  prove_bs_rev ElectionParams_ι__isRoundUnfrozen_А_oldestRoundId_bs ElectionParams_ι__isRoundUnfrozen_А_oldestRoundId_pos ElectionParams_ι__isRoundUnfrozen_А_oldestRoundId_fits. 
Qed.
Lemma ElectionParams_ι__isRoundUnfrozen_А_oldestRoundId_bs257 : Z2IN 257 ElectionParams_ι__isRoundUnfrozen_А_oldestRoundId = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    ElectionParams_ι__isRoundUnfrozen_А_oldestRoundId_bs_def)) ElectionParams_ι__isRoundUnfrozen_А_oldestRoundId_bs_def)).
Proof.
  prove_bs_rev ElectionParams_ι__isRoundUnfrozen_А_oldestRoundId_bs_rev ElectionParams_ι__isRoundUnfrozen_А_oldestRoundId_bs_def.
Qed.

Variables ElectionParams_ι__isElectionOver_А_currentElectAt : Z . 
Variables (*! { _crrn !*) _crrn00 _crrn01 _crrn02 _crrn03 _crrn04 _crrn05 _crrn06 _crrn07 _crrn08 _crrn09 _crrn0A _crrn0B _crrn0C _crrn0D _crrn0E _crrn0F _crrn10 _crrn11 _crrn12 _crrn13 _crrn14 _crrn15 _crrn16 _crrn17 _crrn18 _crrn19 _crrn1A _crrn1B _crrn1C _crrn1D _crrn1E _crrn1F  : TVMBit . 
Definition ElectionParams_ι__isElectionOver_А_currentElectAt_bs_def := [> _crrn00 , _crrn01 , _crrn02 , _crrn03 , _crrn04 , _crrn05 , _crrn06 , _crrn07 , _crrn08 , _crrn09 , _crrn0A , _crrn0B , _crrn0C , _crrn0D , _crrn0E , _crrn0F , _crrn10 , _crrn11 , _crrn12 , _crrn13 , _crrn14 , _crrn15 , _crrn16 , _crrn17 , _crrn18 , _crrn19 , _crrn1A , _crrn1B , _crrn1C , _crrn1D , _crrn1E , _crrn1F <] .
Lemma ElectionParams_ι__isElectionOver_А_currentElectAt_bs_id: ElectionParams_ι__isElectionOver_А_currentElectAt_bs_def = [> _crrn00 , _crrn01 , _crrn02 , _crrn03 , _crrn04 , _crrn05 , _crrn06 , _crrn07 , _crrn08 , _crrn09 , _crrn0A , _crrn0B , _crrn0C , _crrn0D , _crrn0E , _crrn0F , _crrn10 , _crrn11 , _crrn12 , _crrn13 , _crrn14 , _crrn15 , _crrn16 , _crrn17 , _crrn18 , _crrn19 , _crrn1A , _crrn1B , _crrn1C , _crrn1D , _crrn1E , _crrn1F (* } !*)  <] .
Proof. auto. Qed.
Axiom ElectionParams_ι__isElectionOver_А_currentElectAt_bs' : Z2IBS_pos (tvmBitStringLen ElectionParams_ι__isElectionOver_А_currentElectAt_bs_def) ElectionParams_ι__isElectionOver_А_currentElectAt = ElectionParams_ι__isElectionOver_А_currentElectAt_bs_def.
Lemma ElectionParams_ι__isElectionOver_А_currentElectAt_bs : Z2IBS_pos 32 ElectionParams_ι__isElectionOver_А_currentElectAt = ElectionParams_ι__isElectionOver_А_currentElectAt_bs_def.
Proof.
 rewrite <- ElectionParams_ι__isElectionOver_А_currentElectAt_bs'. auto. Qed.
Axiom ElectionParams_ι__isElectionOver_А_currentElectAt_pos: (0 <= ElectionParams_ι__isElectionOver_А_currentElectAt )%Z.
Axiom ElectionParams_ι__isElectionOver_А_currentElectAt_fits: zFitN_pos (tvmBitStringLen ElectionParams_ι__isElectionOver_А_currentElectAt_bs_def) ElectionParams_ι__isElectionOver_А_currentElectAt = true.
Lemma ElectionParams_ι__isElectionOver_А_currentElectAt_bs_rev : I2ZBS_pos' ElectionParams_ι__isElectionOver_А_currentElectAt_bs_def = ElectionParams_ι__isElectionOver_А_currentElectAt .
Proof.
  prove_bs_rev ElectionParams_ι__isElectionOver_А_currentElectAt_bs ElectionParams_ι__isElectionOver_А_currentElectAt_pos ElectionParams_ι__isElectionOver_А_currentElectAt_fits. 
Qed.
Lemma ElectionParams_ι__isElectionOver_А_currentElectAt_bs257 : Z2IN 257 ElectionParams_ι__isElectionOver_А_currentElectAt = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    ElectionParams_ι__isElectionOver_А_currentElectAt_bs_def)) ElectionParams_ι__isElectionOver_А_currentElectAt_bs_def)).
Proof.
  prove_bs_rev ElectionParams_ι__isElectionOver_А_currentElectAt_bs_rev ElectionParams_ι__isElectionOver_А_currentElectAt_bs_def.
Qed.


 
Variables StakeholderBase_ι__stakeholderUpdateStake_А_totalStake : Z . 
Variables (*! { _ttlS !*) _ttlS00 _ttlS01 _ttlS02 _ttlS03 _ttlS04 _ttlS05 _ttlS06 _ttlS07 _ttlS08 _ttlS09 _ttlS0A _ttlS0B _ttlS0C _ttlS0D _ttlS0E _ttlS0F _ttlS10 _ttlS11 _ttlS12 _ttlS13 _ttlS14 _ttlS15 _ttlS16 _ttlS17 _ttlS18 _ttlS19 _ttlS1A _ttlS1B _ttlS1C _ttlS1D _ttlS1E _ttlS1F _ttlS20 _ttlS21 _ttlS22 _ttlS23 _ttlS24 _ttlS25 _ttlS26 _ttlS27 _ttlS28 _ttlS29 _ttlS2A _ttlS2B _ttlS2C _ttlS2D _ttlS2E _ttlS2F _ttlS30 _ttlS31 _ttlS32 _ttlS33 _ttlS34 _ttlS35 _ttlS36 _ttlS37 _ttlS38 _ttlS39 _ttlS3A _ttlS3B _ttlS3C _ttlS3D _ttlS3E _ttlS3F  : TVMBit . 
Definition StakeholderBase_ι__stakeholderUpdateStake_А_totalStake_bs_def := [> _ttlS00 , _ttlS01 , _ttlS02 , _ttlS03 , _ttlS04 , _ttlS05 , _ttlS06 , _ttlS07 , _ttlS08 , _ttlS09 , _ttlS0A , _ttlS0B , _ttlS0C , _ttlS0D , _ttlS0E , _ttlS0F , _ttlS10 , _ttlS11 , _ttlS12 , _ttlS13 , _ttlS14 , _ttlS15 , _ttlS16 , _ttlS17 , _ttlS18 , _ttlS19 , _ttlS1A , _ttlS1B , _ttlS1C , _ttlS1D , _ttlS1E , _ttlS1F , _ttlS20 , _ttlS21 , _ttlS22 , _ttlS23 , _ttlS24 , _ttlS25 , _ttlS26 , _ttlS27 , _ttlS28 , _ttlS29 , _ttlS2A , _ttlS2B , _ttlS2C , _ttlS2D , _ttlS2E , _ttlS2F , _ttlS30 , _ttlS31 , _ttlS32 , _ttlS33 , _ttlS34 , _ttlS35 , _ttlS36 , _ttlS37 , _ttlS38 , _ttlS39 , _ttlS3A , _ttlS3B , _ttlS3C , _ttlS3D , _ttlS3E , _ttlS3F <] .
Lemma StakeholderBase_ι__stakeholderUpdateStake_А_totalStake_bs_id: StakeholderBase_ι__stakeholderUpdateStake_А_totalStake_bs_def = [> _ttlS00 , _ttlS01 , _ttlS02 , _ttlS03 , _ttlS04 , _ttlS05 , _ttlS06 , _ttlS07 , _ttlS08 , _ttlS09 , _ttlS0A , _ttlS0B , _ttlS0C , _ttlS0D , _ttlS0E , _ttlS0F , _ttlS10 , _ttlS11 , _ttlS12 , _ttlS13 , _ttlS14 , _ttlS15 , _ttlS16 , _ttlS17 , _ttlS18 , _ttlS19 , _ttlS1A , _ttlS1B , _ttlS1C , _ttlS1D , _ttlS1E , _ttlS1F , _ttlS20 , _ttlS21 , _ttlS22 , _ttlS23 , _ttlS24 , _ttlS25 , _ttlS26 , _ttlS27 , _ttlS28 , _ttlS29 , _ttlS2A , _ttlS2B , _ttlS2C , _ttlS2D , _ttlS2E , _ttlS2F , _ttlS30 , _ttlS31 , _ttlS32 , _ttlS33 , _ttlS34 , _ttlS35 , _ttlS36 , _ttlS37 , _ttlS38 , _ttlS39 , _ttlS3A , _ttlS3B , _ttlS3C , _ttlS3D , _ttlS3E , _ttlS3F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakeholderBase_ι__stakeholderUpdateStake_А_totalStake_bs' : Z2IBS_pos (tvmBitStringLen StakeholderBase_ι__stakeholderUpdateStake_А_totalStake_bs_def) StakeholderBase_ι__stakeholderUpdateStake_А_totalStake = StakeholderBase_ι__stakeholderUpdateStake_А_totalStake_bs_def.
Lemma StakeholderBase_ι__stakeholderUpdateStake_А_totalStake_bs : Z2IBS_pos 64 StakeholderBase_ι__stakeholderUpdateStake_А_totalStake = StakeholderBase_ι__stakeholderUpdateStake_А_totalStake_bs_def.
Proof.
 rewrite <- StakeholderBase_ι__stakeholderUpdateStake_А_totalStake_bs'. auto. Qed.
Axiom StakeholderBase_ι__stakeholderUpdateStake_А_totalStake_pos: (0 <= StakeholderBase_ι__stakeholderUpdateStake_А_totalStake )%Z.
Axiom StakeholderBase_ι__stakeholderUpdateStake_А_totalStake_fits: zFitN_pos (tvmBitStringLen StakeholderBase_ι__stakeholderUpdateStake_А_totalStake_bs_def) StakeholderBase_ι__stakeholderUpdateStake_А_totalStake = true.
Lemma StakeholderBase_ι__stakeholderUpdateStake_А_totalStake_bs_rev : I2ZBS_pos' StakeholderBase_ι__stakeholderUpdateStake_А_totalStake_bs_def = StakeholderBase_ι__stakeholderUpdateStake_А_totalStake .
Proof.
  prove_bs_rev StakeholderBase_ι__stakeholderUpdateStake_А_totalStake_bs StakeholderBase_ι__stakeholderUpdateStake_А_totalStake_pos StakeholderBase_ι__stakeholderUpdateStake_А_totalStake_fits. 
Qed.
Lemma StakeholderBase_ι__stakeholderUpdateStake_А_totalStake_bs257 : Z2IN 257 StakeholderBase_ι__stakeholderUpdateStake_А_totalStake = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakeholderBase_ι__stakeholderUpdateStake_А_totalStake_bs_def)) StakeholderBase_ι__stakeholderUpdateStake_А_totalStake_bs_def)).
Proof.
  prove_bs_rev StakeholderBase_ι__stakeholderUpdateStake_А_totalStake_bs_rev StakeholderBase_ι__stakeholderUpdateStake_А_totalStake_bs_def.
Qed. 
 
Variables StakeholderBase_ι__stakeholderRemoveStake_А_removedStake : Z . 
Variables (*! { _rmvd !*) _rmvd00 _rmvd01 _rmvd02 _rmvd03 _rmvd04 _rmvd05 _rmvd06 _rmvd07 _rmvd08 _rmvd09 _rmvd0A _rmvd0B _rmvd0C _rmvd0D _rmvd0E _rmvd0F _rmvd10 _rmvd11 _rmvd12 _rmvd13 _rmvd14 _rmvd15 _rmvd16 _rmvd17 _rmvd18 _rmvd19 _rmvd1A _rmvd1B _rmvd1C _rmvd1D _rmvd1E _rmvd1F _rmvd20 _rmvd21 _rmvd22 _rmvd23 _rmvd24 _rmvd25 _rmvd26 _rmvd27 _rmvd28 _rmvd29 _rmvd2A _rmvd2B _rmvd2C _rmvd2D _rmvd2E _rmvd2F _rmvd30 _rmvd31 _rmvd32 _rmvd33 _rmvd34 _rmvd35 _rmvd36 _rmvd37 _rmvd38 _rmvd39 _rmvd3A _rmvd3B _rmvd3C _rmvd3D _rmvd3E _rmvd3F  : TVMBit . 
Definition StakeholderBase_ι__stakeholderRemoveStake_А_removedStake_bs_def := [> _rmvd00 , _rmvd01 , _rmvd02 , _rmvd03 , _rmvd04 , _rmvd05 , _rmvd06 , _rmvd07 , _rmvd08 , _rmvd09 , _rmvd0A , _rmvd0B , _rmvd0C , _rmvd0D , _rmvd0E , _rmvd0F , _rmvd10 , _rmvd11 , _rmvd12 , _rmvd13 , _rmvd14 , _rmvd15 , _rmvd16 , _rmvd17 , _rmvd18 , _rmvd19 , _rmvd1A , _rmvd1B , _rmvd1C , _rmvd1D , _rmvd1E , _rmvd1F , _rmvd20 , _rmvd21 , _rmvd22 , _rmvd23 , _rmvd24 , _rmvd25 , _rmvd26 , _rmvd27 , _rmvd28 , _rmvd29 , _rmvd2A , _rmvd2B , _rmvd2C , _rmvd2D , _rmvd2E , _rmvd2F , _rmvd30 , _rmvd31 , _rmvd32 , _rmvd33 , _rmvd34 , _rmvd35 , _rmvd36 , _rmvd37 , _rmvd38 , _rmvd39 , _rmvd3A , _rmvd3B , _rmvd3C , _rmvd3D , _rmvd3E , _rmvd3F <] .
Lemma StakeholderBase_ι__stakeholderRemoveStake_А_removedStake_bs_id: StakeholderBase_ι__stakeholderRemoveStake_А_removedStake_bs_def = [> _rmvd00 , _rmvd01 , _rmvd02 , _rmvd03 , _rmvd04 , _rmvd05 , _rmvd06 , _rmvd07 , _rmvd08 , _rmvd09 , _rmvd0A , _rmvd0B , _rmvd0C , _rmvd0D , _rmvd0E , _rmvd0F , _rmvd10 , _rmvd11 , _rmvd12 , _rmvd13 , _rmvd14 , _rmvd15 , _rmvd16 , _rmvd17 , _rmvd18 , _rmvd19 , _rmvd1A , _rmvd1B , _rmvd1C , _rmvd1D , _rmvd1E , _rmvd1F , _rmvd20 , _rmvd21 , _rmvd22 , _rmvd23 , _rmvd24 , _rmvd25 , _rmvd26 , _rmvd27 , _rmvd28 , _rmvd29 , _rmvd2A , _rmvd2B , _rmvd2C , _rmvd2D , _rmvd2E , _rmvd2F , _rmvd30 , _rmvd31 , _rmvd32 , _rmvd33 , _rmvd34 , _rmvd35 , _rmvd36 , _rmvd37 , _rmvd38 , _rmvd39 , _rmvd3A , _rmvd3B , _rmvd3C , _rmvd3D , _rmvd3E , _rmvd3F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakeholderBase_ι__stakeholderRemoveStake_А_removedStake_bs' : Z2IBS_pos (tvmBitStringLen StakeholderBase_ι__stakeholderRemoveStake_А_removedStake_bs_def) StakeholderBase_ι__stakeholderRemoveStake_А_removedStake = StakeholderBase_ι__stakeholderRemoveStake_А_removedStake_bs_def.
Lemma StakeholderBase_ι__stakeholderRemoveStake_А_removedStake_bs : Z2IBS_pos 64 StakeholderBase_ι__stakeholderRemoveStake_А_removedStake = StakeholderBase_ι__stakeholderRemoveStake_А_removedStake_bs_def.
Proof.
 rewrite <- StakeholderBase_ι__stakeholderRemoveStake_А_removedStake_bs'. auto. Qed.
Axiom StakeholderBase_ι__stakeholderRemoveStake_А_removedStake_pos: (0 <= StakeholderBase_ι__stakeholderRemoveStake_А_removedStake )%Z.
Axiom StakeholderBase_ι__stakeholderRemoveStake_А_removedStake_fits: zFitN_pos (tvmBitStringLen StakeholderBase_ι__stakeholderRemoveStake_А_removedStake_bs_def) StakeholderBase_ι__stakeholderRemoveStake_А_removedStake = true.
Lemma StakeholderBase_ι__stakeholderRemoveStake_А_removedStake_bs_rev : I2ZBS_pos' StakeholderBase_ι__stakeholderRemoveStake_А_removedStake_bs_def = StakeholderBase_ι__stakeholderRemoveStake_А_removedStake .
Proof.
  prove_bs_rev StakeholderBase_ι__stakeholderRemoveStake_А_removedStake_bs StakeholderBase_ι__stakeholderRemoveStake_А_removedStake_pos StakeholderBase_ι__stakeholderRemoveStake_А_removedStake_fits. 
Qed.
Lemma StakeholderBase_ι__stakeholderRemoveStake_А_removedStake_bs257 : Z2IN 257 StakeholderBase_ι__stakeholderRemoveStake_А_removedStake = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakeholderBase_ι__stakeholderRemoveStake_А_removedStake_bs_def)) StakeholderBase_ι__stakeholderRemoveStake_А_removedStake_bs_def)).
Proof.
  prove_bs_rev StakeholderBase_ι__stakeholderRemoveStake_А_removedStake_bs_rev StakeholderBase_ι__stakeholderRemoveStake_А_removedStake_bs_def.
Qed. 
Variables StakeholderBase_ι__stakeholderRemoveStake_А_unusedStake : Z . 
Variables (*! { _nsdS !*) _nsdS00 _nsdS01 _nsdS02 _nsdS03 _nsdS04 _nsdS05 _nsdS06 _nsdS07 _nsdS08 _nsdS09 _nsdS0A _nsdS0B _nsdS0C _nsdS0D _nsdS0E _nsdS0F _nsdS10 _nsdS11 _nsdS12 _nsdS13 _nsdS14 _nsdS15 _nsdS16 _nsdS17 _nsdS18 _nsdS19 _nsdS1A _nsdS1B _nsdS1C _nsdS1D _nsdS1E _nsdS1F _nsdS20 _nsdS21 _nsdS22 _nsdS23 _nsdS24 _nsdS25 _nsdS26 _nsdS27 _nsdS28 _nsdS29 _nsdS2A _nsdS2B _nsdS2C _nsdS2D _nsdS2E _nsdS2F _nsdS30 _nsdS31 _nsdS32 _nsdS33 _nsdS34 _nsdS35 _nsdS36 _nsdS37 _nsdS38 _nsdS39 _nsdS3A _nsdS3B _nsdS3C _nsdS3D _nsdS3E _nsdS3F  : TVMBit . 
Definition StakeholderBase_ι__stakeholderRemoveStake_А_unusedStake_bs_def := [> _nsdS00 , _nsdS01 , _nsdS02 , _nsdS03 , _nsdS04 , _nsdS05 , _nsdS06 , _nsdS07 , _nsdS08 , _nsdS09 , _nsdS0A , _nsdS0B , _nsdS0C , _nsdS0D , _nsdS0E , _nsdS0F , _nsdS10 , _nsdS11 , _nsdS12 , _nsdS13 , _nsdS14 , _nsdS15 , _nsdS16 , _nsdS17 , _nsdS18 , _nsdS19 , _nsdS1A , _nsdS1B , _nsdS1C , _nsdS1D , _nsdS1E , _nsdS1F , _nsdS20 , _nsdS21 , _nsdS22 , _nsdS23 , _nsdS24 , _nsdS25 , _nsdS26 , _nsdS27 , _nsdS28 , _nsdS29 , _nsdS2A , _nsdS2B , _nsdS2C , _nsdS2D , _nsdS2E , _nsdS2F , _nsdS30 , _nsdS31 , _nsdS32 , _nsdS33 , _nsdS34 , _nsdS35 , _nsdS36 , _nsdS37 , _nsdS38 , _nsdS39 , _nsdS3A , _nsdS3B , _nsdS3C , _nsdS3D , _nsdS3E , _nsdS3F <] .
Lemma StakeholderBase_ι__stakeholderRemoveStake_А_unusedStake_bs_id: StakeholderBase_ι__stakeholderRemoveStake_А_unusedStake_bs_def = [> _nsdS00 , _nsdS01 , _nsdS02 , _nsdS03 , _nsdS04 , _nsdS05 , _nsdS06 , _nsdS07 , _nsdS08 , _nsdS09 , _nsdS0A , _nsdS0B , _nsdS0C , _nsdS0D , _nsdS0E , _nsdS0F , _nsdS10 , _nsdS11 , _nsdS12 , _nsdS13 , _nsdS14 , _nsdS15 , _nsdS16 , _nsdS17 , _nsdS18 , _nsdS19 , _nsdS1A , _nsdS1B , _nsdS1C , _nsdS1D , _nsdS1E , _nsdS1F , _nsdS20 , _nsdS21 , _nsdS22 , _nsdS23 , _nsdS24 , _nsdS25 , _nsdS26 , _nsdS27 , _nsdS28 , _nsdS29 , _nsdS2A , _nsdS2B , _nsdS2C , _nsdS2D , _nsdS2E , _nsdS2F , _nsdS30 , _nsdS31 , _nsdS32 , _nsdS33 , _nsdS34 , _nsdS35 , _nsdS36 , _nsdS37 , _nsdS38 , _nsdS39 , _nsdS3A , _nsdS3B , _nsdS3C , _nsdS3D , _nsdS3E , _nsdS3F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakeholderBase_ι__stakeholderRemoveStake_А_unusedStake_bs' : Z2IBS_pos (tvmBitStringLen StakeholderBase_ι__stakeholderRemoveStake_А_unusedStake_bs_def) StakeholderBase_ι__stakeholderRemoveStake_А_unusedStake = StakeholderBase_ι__stakeholderRemoveStake_А_unusedStake_bs_def.
Lemma StakeholderBase_ι__stakeholderRemoveStake_А_unusedStake_bs : Z2IBS_pos 64 StakeholderBase_ι__stakeholderRemoveStake_А_unusedStake = StakeholderBase_ι__stakeholderRemoveStake_А_unusedStake_bs_def.
Proof.
 rewrite <- StakeholderBase_ι__stakeholderRemoveStake_А_unusedStake_bs'. auto. Qed.
Axiom StakeholderBase_ι__stakeholderRemoveStake_А_unusedStake_pos: (0 <= StakeholderBase_ι__stakeholderRemoveStake_А_unusedStake )%Z.
Axiom StakeholderBase_ι__stakeholderRemoveStake_А_unusedStake_fits: zFitN_pos (tvmBitStringLen StakeholderBase_ι__stakeholderRemoveStake_А_unusedStake_bs_def) StakeholderBase_ι__stakeholderRemoveStake_А_unusedStake = true.
Lemma StakeholderBase_ι__stakeholderRemoveStake_А_unusedStake_bs_rev : I2ZBS_pos' StakeholderBase_ι__stakeholderRemoveStake_А_unusedStake_bs_def = StakeholderBase_ι__stakeholderRemoveStake_А_unusedStake .
Proof.
  prove_bs_rev StakeholderBase_ι__stakeholderRemoveStake_А_unusedStake_bs StakeholderBase_ι__stakeholderRemoveStake_А_unusedStake_pos StakeholderBase_ι__stakeholderRemoveStake_А_unusedStake_fits. 
Qed.
Lemma StakeholderBase_ι__stakeholderRemoveStake_А_unusedStake_bs257 : Z2IN 257 StakeholderBase_ι__stakeholderRemoveStake_А_unusedStake = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakeholderBase_ι__stakeholderRemoveStake_А_unusedStake_bs_def)) StakeholderBase_ι__stakeholderRemoveStake_А_unusedStake_bs_def)).
Proof.
  prove_bs_rev StakeholderBase_ι__stakeholderRemoveStake_А_unusedStake_bs_rev StakeholderBase_ι__stakeholderRemoveStake_А_unusedStake_bs_def.
Qed.
 
 
Variables StakeholderBase_ι__stakeholderUpdateReward_А_reward : Z . 
Variables (*! { _rwrd !*) _rwrd00 _rwrd01 _rwrd02 _rwrd03 _rwrd04 _rwrd05 _rwrd06 _rwrd07 _rwrd08 _rwrd09 _rwrd0A _rwrd0B _rwrd0C _rwrd0D _rwrd0E _rwrd0F _rwrd10 _rwrd11 _rwrd12 _rwrd13 _rwrd14 _rwrd15 _rwrd16 _rwrd17 _rwrd18 _rwrd19 _rwrd1A _rwrd1B _rwrd1C _rwrd1D _rwrd1E _rwrd1F _rwrd20 _rwrd21 _rwrd22 _rwrd23 _rwrd24 _rwrd25 _rwrd26 _rwrd27 _rwrd28 _rwrd29 _rwrd2A _rwrd2B _rwrd2C _rwrd2D _rwrd2E _rwrd2F _rwrd30 _rwrd31 _rwrd32 _rwrd33 _rwrd34 _rwrd35 _rwrd36 _rwrd37 _rwrd38 _rwrd39 _rwrd3A _rwrd3B _rwrd3C _rwrd3D _rwrd3E _rwrd3F  : TVMBit . 
Definition StakeholderBase_ι__stakeholderUpdateReward_А_reward_bs_def := [> _rwrd00 , _rwrd01 , _rwrd02 , _rwrd03 , _rwrd04 , _rwrd05 , _rwrd06 , _rwrd07 , _rwrd08 , _rwrd09 , _rwrd0A , _rwrd0B , _rwrd0C , _rwrd0D , _rwrd0E , _rwrd0F , _rwrd10 , _rwrd11 , _rwrd12 , _rwrd13 , _rwrd14 , _rwrd15 , _rwrd16 , _rwrd17 , _rwrd18 , _rwrd19 , _rwrd1A , _rwrd1B , _rwrd1C , _rwrd1D , _rwrd1E , _rwrd1F , _rwrd20 , _rwrd21 , _rwrd22 , _rwrd23 , _rwrd24 , _rwrd25 , _rwrd26 , _rwrd27 , _rwrd28 , _rwrd29 , _rwrd2A , _rwrd2B , _rwrd2C , _rwrd2D , _rwrd2E , _rwrd2F , _rwrd30 , _rwrd31 , _rwrd32 , _rwrd33 , _rwrd34 , _rwrd35 , _rwrd36 , _rwrd37 , _rwrd38 , _rwrd39 , _rwrd3A , _rwrd3B , _rwrd3C , _rwrd3D , _rwrd3E , _rwrd3F <] .
Lemma StakeholderBase_ι__stakeholderUpdateReward_А_reward_bs_id: StakeholderBase_ι__stakeholderUpdateReward_А_reward_bs_def = [> _rwrd00 , _rwrd01 , _rwrd02 , _rwrd03 , _rwrd04 , _rwrd05 , _rwrd06 , _rwrd07 , _rwrd08 , _rwrd09 , _rwrd0A , _rwrd0B , _rwrd0C , _rwrd0D , _rwrd0E , _rwrd0F , _rwrd10 , _rwrd11 , _rwrd12 , _rwrd13 , _rwrd14 , _rwrd15 , _rwrd16 , _rwrd17 , _rwrd18 , _rwrd19 , _rwrd1A , _rwrd1B , _rwrd1C , _rwrd1D , _rwrd1E , _rwrd1F , _rwrd20 , _rwrd21 , _rwrd22 , _rwrd23 , _rwrd24 , _rwrd25 , _rwrd26 , _rwrd27 , _rwrd28 , _rwrd29 , _rwrd2A , _rwrd2B , _rwrd2C , _rwrd2D , _rwrd2E , _rwrd2F , _rwrd30 , _rwrd31 , _rwrd32 , _rwrd33 , _rwrd34 , _rwrd35 , _rwrd36 , _rwrd37 , _rwrd38 , _rwrd39 , _rwrd3A , _rwrd3B , _rwrd3C , _rwrd3D , _rwrd3E , _rwrd3F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakeholderBase_ι__stakeholderUpdateReward_А_reward_bs' : Z2IBS_pos (tvmBitStringLen StakeholderBase_ι__stakeholderUpdateReward_А_reward_bs_def) StakeholderBase_ι__stakeholderUpdateReward_А_reward = StakeholderBase_ι__stakeholderUpdateReward_А_reward_bs_def.
Lemma StakeholderBase_ι__stakeholderUpdateReward_А_reward_bs : Z2IBS_pos 64 StakeholderBase_ι__stakeholderUpdateReward_А_reward = StakeholderBase_ι__stakeholderUpdateReward_А_reward_bs_def.
Proof.
 rewrite <- StakeholderBase_ι__stakeholderUpdateReward_А_reward_bs'. auto. Qed.
Axiom StakeholderBase_ι__stakeholderUpdateReward_А_reward_pos: (0 <= StakeholderBase_ι__stakeholderUpdateReward_А_reward )%Z.
Axiom StakeholderBase_ι__stakeholderUpdateReward_А_reward_fits: zFitN_pos (tvmBitStringLen StakeholderBase_ι__stakeholderUpdateReward_А_reward_bs_def) StakeholderBase_ι__stakeholderUpdateReward_А_reward = true.
Lemma StakeholderBase_ι__stakeholderUpdateReward_А_reward_bs_rev : I2ZBS_pos' StakeholderBase_ι__stakeholderUpdateReward_А_reward_bs_def = StakeholderBase_ι__stakeholderUpdateReward_А_reward .
Proof.
  prove_bs_rev StakeholderBase_ι__stakeholderUpdateReward_А_reward_bs StakeholderBase_ι__stakeholderUpdateReward_А_reward_pos StakeholderBase_ι__stakeholderUpdateReward_А_reward_fits. 
Qed.
Lemma StakeholderBase_ι__stakeholderUpdateReward_А_reward_bs257 : Z2IN 257 StakeholderBase_ι__stakeholderUpdateReward_А_reward = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakeholderBase_ι__stakeholderUpdateReward_А_reward_bs_def)) StakeholderBase_ι__stakeholderUpdateReward_А_reward_bs_def)).
Proof.
  prove_bs_rev StakeholderBase_ι__stakeholderUpdateReward_А_reward_bs_rev StakeholderBase_ι__stakeholderUpdateReward_А_reward_bs_def.
Qed. 
Variables StakeholderBase_ι__stakeholderUpdateReward_А_fee : Z . 
Variables (*! { _f !*) _f00 _f01 _f02 _f03 _f04 _f05 _f06 _f07 _f08 _f09 _f0A _f0B _f0C _f0D _f0E _f0F _f10 _f11 _f12 _f13 _f14 _f15 _f16 _f17 _f18 _f19 _f1A _f1B _f1C _f1D _f1E _f1F _f20 _f21 _f22 _f23 _f24 _f25 _f26 _f27 _f28 _f29 _f2A _f2B _f2C _f2D _f2E _f2F _f30 _f31 _f32 _f33 _f34 _f35 _f36 _f37 _f38 _f39 _f3A _f3B _f3C _f3D _f3E _f3F  : TVMBit . 
Definition StakeholderBase_ι__stakeholderUpdateReward_А_fee_bs_def := [> _f00 , _f01 , _f02 , _f03 , _f04 , _f05 , _f06 , _f07 , _f08 , _f09 , _f0A , _f0B , _f0C , _f0D , _f0E , _f0F , _f10 , _f11 , _f12 , _f13 , _f14 , _f15 , _f16 , _f17 , _f18 , _f19 , _f1A , _f1B , _f1C , _f1D , _f1E , _f1F , _f20 , _f21 , _f22 , _f23 , _f24 , _f25 , _f26 , _f27 , _f28 , _f29 , _f2A , _f2B , _f2C , _f2D , _f2E , _f2F , _f30 , _f31 , _f32 , _f33 , _f34 , _f35 , _f36 , _f37 , _f38 , _f39 , _f3A , _f3B , _f3C , _f3D , _f3E , _f3F <] .
Lemma StakeholderBase_ι__stakeholderUpdateReward_А_fee_bs_id: StakeholderBase_ι__stakeholderUpdateReward_А_fee_bs_def = [> _f00 , _f01 , _f02 , _f03 , _f04 , _f05 , _f06 , _f07 , _f08 , _f09 , _f0A , _f0B , _f0C , _f0D , _f0E , _f0F , _f10 , _f11 , _f12 , _f13 , _f14 , _f15 , _f16 , _f17 , _f18 , _f19 , _f1A , _f1B , _f1C , _f1D , _f1E , _f1F , _f20 , _f21 , _f22 , _f23 , _f24 , _f25 , _f26 , _f27 , _f28 , _f29 , _f2A , _f2B , _f2C , _f2D , _f2E , _f2F , _f30 , _f31 , _f32 , _f33 , _f34 , _f35 , _f36 , _f37 , _f38 , _f39 , _f3A , _f3B , _f3C , _f3D , _f3E , _f3F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakeholderBase_ι__stakeholderUpdateReward_А_fee_bs' : Z2IBS_pos (tvmBitStringLen StakeholderBase_ι__stakeholderUpdateReward_А_fee_bs_def) StakeholderBase_ι__stakeholderUpdateReward_А_fee = StakeholderBase_ι__stakeholderUpdateReward_А_fee_bs_def.
Lemma StakeholderBase_ι__stakeholderUpdateReward_А_fee_bs : Z2IBS_pos 64 StakeholderBase_ι__stakeholderUpdateReward_А_fee = StakeholderBase_ι__stakeholderUpdateReward_А_fee_bs_def.
Proof.
 rewrite <- StakeholderBase_ι__stakeholderUpdateReward_А_fee_bs'. auto. Qed.
Axiom StakeholderBase_ι__stakeholderUpdateReward_А_fee_pos: (0 <= StakeholderBase_ι__stakeholderUpdateReward_А_fee )%Z.
Axiom StakeholderBase_ι__stakeholderUpdateReward_А_fee_fits: zFitN_pos (tvmBitStringLen StakeholderBase_ι__stakeholderUpdateReward_А_fee_bs_def) StakeholderBase_ι__stakeholderUpdateReward_А_fee = true.
Lemma StakeholderBase_ι__stakeholderUpdateReward_А_fee_bs_rev : I2ZBS_pos' StakeholderBase_ι__stakeholderUpdateReward_А_fee_bs_def = StakeholderBase_ι__stakeholderUpdateReward_А_fee .
Proof.
  prove_bs_rev StakeholderBase_ι__stakeholderUpdateReward_А_fee_bs StakeholderBase_ι__stakeholderUpdateReward_А_fee_pos StakeholderBase_ι__stakeholderUpdateReward_А_fee_fits. 
Qed.
Lemma StakeholderBase_ι__stakeholderUpdateReward_А_fee_bs257 : Z2IN 257 StakeholderBase_ι__stakeholderUpdateReward_А_fee = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakeholderBase_ι__stakeholderUpdateReward_А_fee_bs_def)) StakeholderBase_ι__stakeholderUpdateReward_А_fee_bs_def)).
Proof.
  prove_bs_rev StakeholderBase_ι__stakeholderUpdateReward_А_fee_bs_rev StakeholderBase_ι__stakeholderUpdateReward_А_fee_bs_def.
Qed.
 
Variables StakeholderBase_ι__stakeholderUpdateUnusedStake_А_add : Z . 
Variables (*! { _dd !*) _dd00 _dd01 _dd02 _dd03 _dd04 _dd05 _dd06 _dd07 _dd08 _dd09 _dd0A _dd0B _dd0C _dd0D _dd0E _dd0F _dd10 _dd11 _dd12 _dd13 _dd14 _dd15 _dd16 _dd17 _dd18 _dd19 _dd1A _dd1B _dd1C _dd1D _dd1E _dd1F _dd20 _dd21 _dd22 _dd23 _dd24 _dd25 _dd26 _dd27 _dd28 _dd29 _dd2A _dd2B _dd2C _dd2D _dd2E _dd2F _dd30 _dd31 _dd32 _dd33 _dd34 _dd35 _dd36 _dd37 _dd38 _dd39 _dd3A _dd3B _dd3C _dd3D _dd3E _dd3F  : TVMBit . 
Definition StakeholderBase_ι__stakeholderUpdateUnusedStake_А_add_bs_def := [> _dd00 , _dd01 , _dd02 , _dd03 , _dd04 , _dd05 , _dd06 , _dd07 , _dd08 , _dd09 , _dd0A , _dd0B , _dd0C , _dd0D , _dd0E , _dd0F , _dd10 , _dd11 , _dd12 , _dd13 , _dd14 , _dd15 , _dd16 , _dd17 , _dd18 , _dd19 , _dd1A , _dd1B , _dd1C , _dd1D , _dd1E , _dd1F , _dd20 , _dd21 , _dd22 , _dd23 , _dd24 , _dd25 , _dd26 , _dd27 , _dd28 , _dd29 , _dd2A , _dd2B , _dd2C , _dd2D , _dd2E , _dd2F , _dd30 , _dd31 , _dd32 , _dd33 , _dd34 , _dd35 , _dd36 , _dd37 , _dd38 , _dd39 , _dd3A , _dd3B , _dd3C , _dd3D , _dd3E , _dd3F <] .
Lemma StakeholderBase_ι__stakeholderUpdateUnusedStake_А_add_bs_id: StakeholderBase_ι__stakeholderUpdateUnusedStake_А_add_bs_def = [> _dd00 , _dd01 , _dd02 , _dd03 , _dd04 , _dd05 , _dd06 , _dd07 , _dd08 , _dd09 , _dd0A , _dd0B , _dd0C , _dd0D , _dd0E , _dd0F , _dd10 , _dd11 , _dd12 , _dd13 , _dd14 , _dd15 , _dd16 , _dd17 , _dd18 , _dd19 , _dd1A , _dd1B , _dd1C , _dd1D , _dd1E , _dd1F , _dd20 , _dd21 , _dd22 , _dd23 , _dd24 , _dd25 , _dd26 , _dd27 , _dd28 , _dd29 , _dd2A , _dd2B , _dd2C , _dd2D , _dd2E , _dd2F , _dd30 , _dd31 , _dd32 , _dd33 , _dd34 , _dd35 , _dd36 , _dd37 , _dd38 , _dd39 , _dd3A , _dd3B , _dd3C , _dd3D , _dd3E , _dd3F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakeholderBase_ι__stakeholderUpdateUnusedStake_А_add_bs' : Z2IBS_pos (tvmBitStringLen StakeholderBase_ι__stakeholderUpdateUnusedStake_А_add_bs_def) StakeholderBase_ι__stakeholderUpdateUnusedStake_А_add = StakeholderBase_ι__stakeholderUpdateUnusedStake_А_add_bs_def.
Lemma StakeholderBase_ι__stakeholderUpdateUnusedStake_А_add_bs : Z2IBS_pos 64 StakeholderBase_ι__stakeholderUpdateUnusedStake_А_add = StakeholderBase_ι__stakeholderUpdateUnusedStake_А_add_bs_def.
Proof.
 rewrite <- StakeholderBase_ι__stakeholderUpdateUnusedStake_А_add_bs'. auto. Qed.
Axiom StakeholderBase_ι__stakeholderUpdateUnusedStake_А_add_pos: (0 <= StakeholderBase_ι__stakeholderUpdateUnusedStake_А_add )%Z.
Axiom StakeholderBase_ι__stakeholderUpdateUnusedStake_А_add_fits: zFitN_pos (tvmBitStringLen StakeholderBase_ι__stakeholderUpdateUnusedStake_А_add_bs_def) StakeholderBase_ι__stakeholderUpdateUnusedStake_А_add = true.
Lemma StakeholderBase_ι__stakeholderUpdateUnusedStake_А_add_bs_rev : I2ZBS_pos' StakeholderBase_ι__stakeholderUpdateUnusedStake_А_add_bs_def = StakeholderBase_ι__stakeholderUpdateUnusedStake_А_add .
Proof.
  prove_bs_rev StakeholderBase_ι__stakeholderUpdateUnusedStake_А_add_bs StakeholderBase_ι__stakeholderUpdateUnusedStake_А_add_pos StakeholderBase_ι__stakeholderUpdateUnusedStake_А_add_fits. 
Qed.
Lemma StakeholderBase_ι__stakeholderUpdateUnusedStake_А_add_bs257 : Z2IN 257 StakeholderBase_ι__stakeholderUpdateUnusedStake_А_add = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakeholderBase_ι__stakeholderUpdateUnusedStake_А_add_bs_def)) StakeholderBase_ι__stakeholderUpdateUnusedStake_А_add_bs_def)).
Proof.
  prove_bs_rev StakeholderBase_ι__stakeholderUpdateUnusedStake_А_add_bs_rev StakeholderBase_ι__stakeholderUpdateUnusedStake_А_add_bs_def.
Qed. 
Variables StakeholderBase_ι__stakeholderUpdateUnusedStake_А_remove : Z . 
Variables (*! { _rmv !*) _rmv00 _rmv01 _rmv02 _rmv03 _rmv04 _rmv05 _rmv06 _rmv07 _rmv08 _rmv09 _rmv0A _rmv0B _rmv0C _rmv0D _rmv0E _rmv0F _rmv10 _rmv11 _rmv12 _rmv13 _rmv14 _rmv15 _rmv16 _rmv17 _rmv18 _rmv19 _rmv1A _rmv1B _rmv1C _rmv1D _rmv1E _rmv1F _rmv20 _rmv21 _rmv22 _rmv23 _rmv24 _rmv25 _rmv26 _rmv27 _rmv28 _rmv29 _rmv2A _rmv2B _rmv2C _rmv2D _rmv2E _rmv2F _rmv30 _rmv31 _rmv32 _rmv33 _rmv34 _rmv35 _rmv36 _rmv37 _rmv38 _rmv39 _rmv3A _rmv3B _rmv3C _rmv3D _rmv3E _rmv3F  : TVMBit . 
Definition StakeholderBase_ι__stakeholderUpdateUnusedStake_А_remove_bs_def := [> _rmv00 , _rmv01 , _rmv02 , _rmv03 , _rmv04 , _rmv05 , _rmv06 , _rmv07 , _rmv08 , _rmv09 , _rmv0A , _rmv0B , _rmv0C , _rmv0D , _rmv0E , _rmv0F , _rmv10 , _rmv11 , _rmv12 , _rmv13 , _rmv14 , _rmv15 , _rmv16 , _rmv17 , _rmv18 , _rmv19 , _rmv1A , _rmv1B , _rmv1C , _rmv1D , _rmv1E , _rmv1F , _rmv20 , _rmv21 , _rmv22 , _rmv23 , _rmv24 , _rmv25 , _rmv26 , _rmv27 , _rmv28 , _rmv29 , _rmv2A , _rmv2B , _rmv2C , _rmv2D , _rmv2E , _rmv2F , _rmv30 , _rmv31 , _rmv32 , _rmv33 , _rmv34 , _rmv35 , _rmv36 , _rmv37 , _rmv38 , _rmv39 , _rmv3A , _rmv3B , _rmv3C , _rmv3D , _rmv3E , _rmv3F <] .
Lemma StakeholderBase_ι__stakeholderUpdateUnusedStake_А_remove_bs_id: StakeholderBase_ι__stakeholderUpdateUnusedStake_А_remove_bs_def = [> _rmv00 , _rmv01 , _rmv02 , _rmv03 , _rmv04 , _rmv05 , _rmv06 , _rmv07 , _rmv08 , _rmv09 , _rmv0A , _rmv0B , _rmv0C , _rmv0D , _rmv0E , _rmv0F , _rmv10 , _rmv11 , _rmv12 , _rmv13 , _rmv14 , _rmv15 , _rmv16 , _rmv17 , _rmv18 , _rmv19 , _rmv1A , _rmv1B , _rmv1C , _rmv1D , _rmv1E , _rmv1F , _rmv20 , _rmv21 , _rmv22 , _rmv23 , _rmv24 , _rmv25 , _rmv26 , _rmv27 , _rmv28 , _rmv29 , _rmv2A , _rmv2B , _rmv2C , _rmv2D , _rmv2E , _rmv2F , _rmv30 , _rmv31 , _rmv32 , _rmv33 , _rmv34 , _rmv35 , _rmv36 , _rmv37 , _rmv38 , _rmv39 , _rmv3A , _rmv3B , _rmv3C , _rmv3D , _rmv3E , _rmv3F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakeholderBase_ι__stakeholderUpdateUnusedStake_А_remove_bs' : Z2IBS_pos (tvmBitStringLen StakeholderBase_ι__stakeholderUpdateUnusedStake_А_remove_bs_def) StakeholderBase_ι__stakeholderUpdateUnusedStake_А_remove = StakeholderBase_ι__stakeholderUpdateUnusedStake_А_remove_bs_def.
Lemma StakeholderBase_ι__stakeholderUpdateUnusedStake_А_remove_bs : Z2IBS_pos 64 StakeholderBase_ι__stakeholderUpdateUnusedStake_А_remove = StakeholderBase_ι__stakeholderUpdateUnusedStake_А_remove_bs_def.
Proof.
 rewrite <- StakeholderBase_ι__stakeholderUpdateUnusedStake_А_remove_bs'. auto. Qed.
Axiom StakeholderBase_ι__stakeholderUpdateUnusedStake_А_remove_pos: (0 <= StakeholderBase_ι__stakeholderUpdateUnusedStake_А_remove )%Z.
Axiom StakeholderBase_ι__stakeholderUpdateUnusedStake_А_remove_fits: zFitN_pos (tvmBitStringLen StakeholderBase_ι__stakeholderUpdateUnusedStake_А_remove_bs_def) StakeholderBase_ι__stakeholderUpdateUnusedStake_А_remove = true.
Lemma StakeholderBase_ι__stakeholderUpdateUnusedStake_А_remove_bs_rev : I2ZBS_pos' StakeholderBase_ι__stakeholderUpdateUnusedStake_А_remove_bs_def = StakeholderBase_ι__stakeholderUpdateUnusedStake_А_remove .
Proof.
  prove_bs_rev StakeholderBase_ι__stakeholderUpdateUnusedStake_А_remove_bs StakeholderBase_ι__stakeholderUpdateUnusedStake_А_remove_pos StakeholderBase_ι__stakeholderUpdateUnusedStake_А_remove_fits. 
Qed.
Lemma StakeholderBase_ι__stakeholderUpdateUnusedStake_А_remove_bs257 : Z2IN 257 StakeholderBase_ι__stakeholderUpdateUnusedStake_А_remove = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakeholderBase_ι__stakeholderUpdateUnusedStake_А_remove_bs_def)) StakeholderBase_ι__stakeholderUpdateUnusedStake_А_remove_bs_def)).
Proof.
  prove_bs_rev StakeholderBase_ι__stakeholderUpdateUnusedStake_А_remove_bs_rev StakeholderBase_ι__stakeholderUpdateUnusedStake_А_remove_bs_def.
Qed.

Variables RoundsBase_ι__addNewPoolingRound_А_validationStart : Z . 
Variables (*! { _vldt !*) _vldt00 _vldt01 _vldt02 _vldt03 _vldt04 _vldt05 _vldt06 _vldt07 _vldt08 _vldt09 _vldt0A _vldt0B _vldt0C _vldt0D _vldt0E _vldt0F _vldt10 _vldt11 _vldt12 _vldt13 _vldt14 _vldt15 _vldt16 _vldt17 _vldt18 _vldt19 _vldt1A _vldt1B _vldt1C _vldt1D _vldt1E _vldt1F  : TVMBit . 
Definition RoundsBase_ι__addNewPoolingRound_А_validationStart_bs_def := [> _vldt00 , _vldt01 , _vldt02 , _vldt03 , _vldt04 , _vldt05 , _vldt06 , _vldt07 , _vldt08 , _vldt09 , _vldt0A , _vldt0B , _vldt0C , _vldt0D , _vldt0E , _vldt0F , _vldt10 , _vldt11 , _vldt12 , _vldt13 , _vldt14 , _vldt15 , _vldt16 , _vldt17 , _vldt18 , _vldt19 , _vldt1A , _vldt1B , _vldt1C , _vldt1D , _vldt1E , _vldt1F <] .
Lemma RoundsBase_ι__addNewPoolingRound_А_validationStart_bs_id: RoundsBase_ι__addNewPoolingRound_А_validationStart_bs_def = [> _vldt00 , _vldt01 , _vldt02 , _vldt03 , _vldt04 , _vldt05 , _vldt06 , _vldt07 , _vldt08 , _vldt09 , _vldt0A , _vldt0B , _vldt0C , _vldt0D , _vldt0E , _vldt0F , _vldt10 , _vldt11 , _vldt12 , _vldt13 , _vldt14 , _vldt15 , _vldt16 , _vldt17 , _vldt18 , _vldt19 , _vldt1A , _vldt1B , _vldt1C , _vldt1D , _vldt1E , _vldt1F (* } !*)  <] .
Proof. auto. Qed.
Axiom RoundsBase_ι__addNewPoolingRound_А_validationStart_bs' : Z2IBS_pos (tvmBitStringLen RoundsBase_ι__addNewPoolingRound_А_validationStart_bs_def) RoundsBase_ι__addNewPoolingRound_А_validationStart = RoundsBase_ι__addNewPoolingRound_А_validationStart_bs_def.
Lemma RoundsBase_ι__addNewPoolingRound_А_validationStart_bs : Z2IBS_pos 32 RoundsBase_ι__addNewPoolingRound_А_validationStart = RoundsBase_ι__addNewPoolingRound_А_validationStart_bs_def.
Proof.
 rewrite <- RoundsBase_ι__addNewPoolingRound_А_validationStart_bs'. auto. Qed.
Axiom RoundsBase_ι__addNewPoolingRound_А_validationStart_pos: (0 <= RoundsBase_ι__addNewPoolingRound_А_validationStart )%Z.
Axiom RoundsBase_ι__addNewPoolingRound_А_validationStart_fits: zFitN_pos (tvmBitStringLen RoundsBase_ι__addNewPoolingRound_А_validationStart_bs_def) RoundsBase_ι__addNewPoolingRound_А_validationStart = true.
Lemma RoundsBase_ι__addNewPoolingRound_А_validationStart_bs_rev : I2ZBS_pos' RoundsBase_ι__addNewPoolingRound_А_validationStart_bs_def = RoundsBase_ι__addNewPoolingRound_А_validationStart .
Proof.
  prove_bs_rev RoundsBase_ι__addNewPoolingRound_А_validationStart_bs RoundsBase_ι__addNewPoolingRound_А_validationStart_pos RoundsBase_ι__addNewPoolingRound_А_validationStart_fits. 
Qed.
Lemma RoundsBase_ι__addNewPoolingRound_А_validationStart_bs257 : Z2IN 257 RoundsBase_ι__addNewPoolingRound_А_validationStart = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    RoundsBase_ι__addNewPoolingRound_А_validationStart_bs_def)) RoundsBase_ι__addNewPoolingRound_А_validationStart_bs_def)).
Proof.
  prove_bs_rev RoundsBase_ι__addNewPoolingRound_А_validationStart_bs_rev RoundsBase_ι__addNewPoolingRound_А_validationStart_bs_def.
Qed. 
Variables RoundsBase_ι__addNewPoolingRound_А_validationPeriod : Z . 
Variables (*! { _vldt !*) _vldt00 _vldt01 _vldt02 _vldt03 _vldt04 _vldt05 _vldt06 _vldt07 _vldt08 _vldt09 _vldt0A _vldt0B _vldt0C _vldt0D _vldt0E _vldt0F _vldt10 _vldt11 _vldt12 _vldt13 _vldt14 _vldt15 _vldt16 _vldt17 _vldt18 _vldt19 _vldt1A _vldt1B _vldt1C _vldt1D _vldt1E _vldt1F  : TVMBit . 
Definition RoundsBase_ι__addNewPoolingRound_А_validationPeriod_bs_def := [> _vldt00 , _vldt01 , _vldt02 , _vldt03 , _vldt04 , _vldt05 , _vldt06 , _vldt07 , _vldt08 , _vldt09 , _vldt0A , _vldt0B , _vldt0C , _vldt0D , _vldt0E , _vldt0F , _vldt10 , _vldt11 , _vldt12 , _vldt13 , _vldt14 , _vldt15 , _vldt16 , _vldt17 , _vldt18 , _vldt19 , _vldt1A , _vldt1B , _vldt1C , _vldt1D , _vldt1E , _vldt1F <] .
Lemma RoundsBase_ι__addNewPoolingRound_А_validationPeriod_bs_id: RoundsBase_ι__addNewPoolingRound_А_validationPeriod_bs_def = [> _vldt00 , _vldt01 , _vldt02 , _vldt03 , _vldt04 , _vldt05 , _vldt06 , _vldt07 , _vldt08 , _vldt09 , _vldt0A , _vldt0B , _vldt0C , _vldt0D , _vldt0E , _vldt0F , _vldt10 , _vldt11 , _vldt12 , _vldt13 , _vldt14 , _vldt15 , _vldt16 , _vldt17 , _vldt18 , _vldt19 , _vldt1A , _vldt1B , _vldt1C , _vldt1D , _vldt1E , _vldt1F (* } !*)  <] .
Proof. auto. Qed.
Axiom RoundsBase_ι__addNewPoolingRound_А_validationPeriod_bs' : Z2IBS_pos (tvmBitStringLen RoundsBase_ι__addNewPoolingRound_А_validationPeriod_bs_def) RoundsBase_ι__addNewPoolingRound_А_validationPeriod = RoundsBase_ι__addNewPoolingRound_А_validationPeriod_bs_def.
Lemma RoundsBase_ι__addNewPoolingRound_А_validationPeriod_bs : Z2IBS_pos 32 RoundsBase_ι__addNewPoolingRound_А_validationPeriod = RoundsBase_ι__addNewPoolingRound_А_validationPeriod_bs_def.
Proof.
 rewrite <- RoundsBase_ι__addNewPoolingRound_А_validationPeriod_bs'. auto. Qed.
Axiom RoundsBase_ι__addNewPoolingRound_А_validationPeriod_pos: (0 <= RoundsBase_ι__addNewPoolingRound_А_validationPeriod )%Z.
Axiom RoundsBase_ι__addNewPoolingRound_А_validationPeriod_fits: zFitN_pos (tvmBitStringLen RoundsBase_ι__addNewPoolingRound_А_validationPeriod_bs_def) RoundsBase_ι__addNewPoolingRound_А_validationPeriod = true.
Lemma RoundsBase_ι__addNewPoolingRound_А_validationPeriod_bs_rev : I2ZBS_pos' RoundsBase_ι__addNewPoolingRound_А_validationPeriod_bs_def = RoundsBase_ι__addNewPoolingRound_А_validationPeriod .
Proof.
  prove_bs_rev RoundsBase_ι__addNewPoolingRound_А_validationPeriod_bs RoundsBase_ι__addNewPoolingRound_А_validationPeriod_pos RoundsBase_ι__addNewPoolingRound_А_validationPeriod_fits. 
Qed.
Lemma RoundsBase_ι__addNewPoolingRound_А_validationPeriod_bs257 : Z2IN 257 RoundsBase_ι__addNewPoolingRound_А_validationPeriod = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    RoundsBase_ι__addNewPoolingRound_А_validationPeriod_bs_def)) RoundsBase_ι__addNewPoolingRound_А_validationPeriod_bs_def)).
Proof.
  prove_bs_rev RoundsBase_ι__addNewPoolingRound_А_validationPeriod_bs_rev RoundsBase_ι__addNewPoolingRound_А_validationPeriod_bs_def.
Qed.



  
Variables RoundsBase_ι__roundAddStake_А_stake : Z . 
Variables (*! { _stk !*) _stk00 _stk01 _stk02 _stk03 _stk04 _stk05 _stk06 _stk07 _stk08 _stk09 _stk0A _stk0B _stk0C _stk0D _stk0E _stk0F _stk10 _stk11 _stk12 _stk13 _stk14 _stk15 _stk16 _stk17 _stk18 _stk19 _stk1A _stk1B _stk1C _stk1D _stk1E _stk1F _stk20 _stk21 _stk22 _stk23 _stk24 _stk25 _stk26 _stk27 _stk28 _stk29 _stk2A _stk2B _stk2C _stk2D _stk2E _stk2F _stk30 _stk31 _stk32 _stk33 _stk34 _stk35 _stk36 _stk37 _stk38 _stk39 _stk3A _stk3B _stk3C _stk3D _stk3E _stk3F  : TVMBit . 
Definition RoundsBase_ι__roundAddStake_А_stake_bs_def := [> _stk00 , _stk01 , _stk02 , _stk03 , _stk04 , _stk05 , _stk06 , _stk07 , _stk08 , _stk09 , _stk0A , _stk0B , _stk0C , _stk0D , _stk0E , _stk0F , _stk10 , _stk11 , _stk12 , _stk13 , _stk14 , _stk15 , _stk16 , _stk17 , _stk18 , _stk19 , _stk1A , _stk1B , _stk1C , _stk1D , _stk1E , _stk1F , _stk20 , _stk21 , _stk22 , _stk23 , _stk24 , _stk25 , _stk26 , _stk27 , _stk28 , _stk29 , _stk2A , _stk2B , _stk2C , _stk2D , _stk2E , _stk2F , _stk30 , _stk31 , _stk32 , _stk33 , _stk34 , _stk35 , _stk36 , _stk37 , _stk38 , _stk39 , _stk3A , _stk3B , _stk3C , _stk3D , _stk3E , _stk3F <] .
Lemma RoundsBase_ι__roundAddStake_А_stake_bs_id: RoundsBase_ι__roundAddStake_А_stake_bs_def = [> _stk00 , _stk01 , _stk02 , _stk03 , _stk04 , _stk05 , _stk06 , _stk07 , _stk08 , _stk09 , _stk0A , _stk0B , _stk0C , _stk0D , _stk0E , _stk0F , _stk10 , _stk11 , _stk12 , _stk13 , _stk14 , _stk15 , _stk16 , _stk17 , _stk18 , _stk19 , _stk1A , _stk1B , _stk1C , _stk1D , _stk1E , _stk1F , _stk20 , _stk21 , _stk22 , _stk23 , _stk24 , _stk25 , _stk26 , _stk27 , _stk28 , _stk29 , _stk2A , _stk2B , _stk2C , _stk2D , _stk2E , _stk2F , _stk30 , _stk31 , _stk32 , _stk33 , _stk34 , _stk35 , _stk36 , _stk37 , _stk38 , _stk39 , _stk3A , _stk3B , _stk3C , _stk3D , _stk3E , _stk3F (* } !*)  <] .
Proof. auto. Qed.
Axiom RoundsBase_ι__roundAddStake_А_stake_bs' : Z2IBS_pos (tvmBitStringLen RoundsBase_ι__roundAddStake_А_stake_bs_def) RoundsBase_ι__roundAddStake_А_stake = RoundsBase_ι__roundAddStake_А_stake_bs_def.
Lemma RoundsBase_ι__roundAddStake_А_stake_bs : Z2IBS_pos 64 RoundsBase_ι__roundAddStake_А_stake = RoundsBase_ι__roundAddStake_А_stake_bs_def.
Proof.
 rewrite <- RoundsBase_ι__roundAddStake_А_stake_bs'. auto. Qed.
Axiom RoundsBase_ι__roundAddStake_А_stake_pos: (0 <= RoundsBase_ι__roundAddStake_А_stake )%Z.
Axiom RoundsBase_ι__roundAddStake_А_stake_fits: zFitN_pos (tvmBitStringLen RoundsBase_ι__roundAddStake_А_stake_bs_def) RoundsBase_ι__roundAddStake_А_stake = true.
Lemma RoundsBase_ι__roundAddStake_А_stake_bs_rev : I2ZBS_pos' RoundsBase_ι__roundAddStake_А_stake_bs_def = RoundsBase_ι__roundAddStake_А_stake .
Proof.
  prove_bs_rev RoundsBase_ι__roundAddStake_А_stake_bs RoundsBase_ι__roundAddStake_А_stake_pos RoundsBase_ι__roundAddStake_А_stake_fits. 
Qed.
Lemma RoundsBase_ι__roundAddStake_А_stake_bs257 : Z2IN 257 RoundsBase_ι__roundAddStake_А_stake = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    RoundsBase_ι__roundAddStake_А_stake_bs_def)) RoundsBase_ι__roundAddStake_А_stake_bs_def)).
Proof.
  prove_bs_rev RoundsBase_ι__roundAddStake_А_stake_bs_rev RoundsBase_ι__roundAddStake_А_stake_bs_def.
Qed.
  
Variables RoundsBase_ι__roundSetStake_А_endStake : Z . 
Variables (*! { _ndSt !*) _ndSt00 _ndSt01 _ndSt02 _ndSt03 _ndSt04 _ndSt05 _ndSt06 _ndSt07 _ndSt08 _ndSt09 _ndSt0A _ndSt0B _ndSt0C _ndSt0D _ndSt0E _ndSt0F _ndSt10 _ndSt11 _ndSt12 _ndSt13 _ndSt14 _ndSt15 _ndSt16 _ndSt17 _ndSt18 _ndSt19 _ndSt1A _ndSt1B _ndSt1C _ndSt1D _ndSt1E _ndSt1F _ndSt20 _ndSt21 _ndSt22 _ndSt23 _ndSt24 _ndSt25 _ndSt26 _ndSt27 _ndSt28 _ndSt29 _ndSt2A _ndSt2B _ndSt2C _ndSt2D _ndSt2E _ndSt2F _ndSt30 _ndSt31 _ndSt32 _ndSt33 _ndSt34 _ndSt35 _ndSt36 _ndSt37 _ndSt38 _ndSt39 _ndSt3A _ndSt3B _ndSt3C _ndSt3D _ndSt3E _ndSt3F  : TVMBit . 
Definition RoundsBase_ι__roundSetStake_А_endStake_bs_def := [> _ndSt00 , _ndSt01 , _ndSt02 , _ndSt03 , _ndSt04 , _ndSt05 , _ndSt06 , _ndSt07 , _ndSt08 , _ndSt09 , _ndSt0A , _ndSt0B , _ndSt0C , _ndSt0D , _ndSt0E , _ndSt0F , _ndSt10 , _ndSt11 , _ndSt12 , _ndSt13 , _ndSt14 , _ndSt15 , _ndSt16 , _ndSt17 , _ndSt18 , _ndSt19 , _ndSt1A , _ndSt1B , _ndSt1C , _ndSt1D , _ndSt1E , _ndSt1F , _ndSt20 , _ndSt21 , _ndSt22 , _ndSt23 , _ndSt24 , _ndSt25 , _ndSt26 , _ndSt27 , _ndSt28 , _ndSt29 , _ndSt2A , _ndSt2B , _ndSt2C , _ndSt2D , _ndSt2E , _ndSt2F , _ndSt30 , _ndSt31 , _ndSt32 , _ndSt33 , _ndSt34 , _ndSt35 , _ndSt36 , _ndSt37 , _ndSt38 , _ndSt39 , _ndSt3A , _ndSt3B , _ndSt3C , _ndSt3D , _ndSt3E , _ndSt3F <] .
Lemma RoundsBase_ι__roundSetStake_А_endStake_bs_id: RoundsBase_ι__roundSetStake_А_endStake_bs_def = [> _ndSt00 , _ndSt01 , _ndSt02 , _ndSt03 , _ndSt04 , _ndSt05 , _ndSt06 , _ndSt07 , _ndSt08 , _ndSt09 , _ndSt0A , _ndSt0B , _ndSt0C , _ndSt0D , _ndSt0E , _ndSt0F , _ndSt10 , _ndSt11 , _ndSt12 , _ndSt13 , _ndSt14 , _ndSt15 , _ndSt16 , _ndSt17 , _ndSt18 , _ndSt19 , _ndSt1A , _ndSt1B , _ndSt1C , _ndSt1D , _ndSt1E , _ndSt1F , _ndSt20 , _ndSt21 , _ndSt22 , _ndSt23 , _ndSt24 , _ndSt25 , _ndSt26 , _ndSt27 , _ndSt28 , _ndSt29 , _ndSt2A , _ndSt2B , _ndSt2C , _ndSt2D , _ndSt2E , _ndSt2F , _ndSt30 , _ndSt31 , _ndSt32 , _ndSt33 , _ndSt34 , _ndSt35 , _ndSt36 , _ndSt37 , _ndSt38 , _ndSt39 , _ndSt3A , _ndSt3B , _ndSt3C , _ndSt3D , _ndSt3E , _ndSt3F (* } !*)  <] .
Proof. auto. Qed.
Axiom RoundsBase_ι__roundSetStake_А_endStake_bs' : Z2IBS_pos (tvmBitStringLen RoundsBase_ι__roundSetStake_А_endStake_bs_def) RoundsBase_ι__roundSetStake_А_endStake = RoundsBase_ι__roundSetStake_А_endStake_bs_def.
Lemma RoundsBase_ι__roundSetStake_А_endStake_bs : Z2IBS_pos 64 RoundsBase_ι__roundSetStake_А_endStake = RoundsBase_ι__roundSetStake_А_endStake_bs_def.
Proof.
 rewrite <- RoundsBase_ι__roundSetStake_А_endStake_bs'. auto. Qed.
Axiom RoundsBase_ι__roundSetStake_А_endStake_pos: (0 <= RoundsBase_ι__roundSetStake_А_endStake )%Z.
Axiom RoundsBase_ι__roundSetStake_А_endStake_fits: zFitN_pos (tvmBitStringLen RoundsBase_ι__roundSetStake_А_endStake_bs_def) RoundsBase_ι__roundSetStake_А_endStake = true.
Lemma RoundsBase_ι__roundSetStake_А_endStake_bs_rev : I2ZBS_pos' RoundsBase_ι__roundSetStake_А_endStake_bs_def = RoundsBase_ι__roundSetStake_А_endStake .
Proof.
  prove_bs_rev RoundsBase_ι__roundSetStake_А_endStake_bs RoundsBase_ι__roundSetStake_А_endStake_pos RoundsBase_ι__roundSetStake_А_endStake_fits. 
Qed.
Lemma RoundsBase_ι__roundSetStake_А_endStake_bs257 : Z2IN 257 RoundsBase_ι__roundSetStake_А_endStake = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    RoundsBase_ι__roundSetStake_А_endStake_bs_def)) RoundsBase_ι__roundSetStake_А_endStake_bs_def)).
Proof.
  prove_bs_rev RoundsBase_ι__roundSetStake_А_endStake_bs_rev RoundsBase_ι__roundSetStake_А_endStake_bs_def.
Qed.
 
Variables RoundsBase_ι__roundInvestStake_А_stake : Z . 
Variables (*! { _stk !*) _stk00 _stk01 _stk02 _stk03 _stk04 _stk05 _stk06 _stk07 _stk08 _stk09 _stk0A _stk0B _stk0C _stk0D _stk0E _stk0F _stk10 _stk11 _stk12 _stk13 _stk14 _stk15 _stk16 _stk17 _stk18 _stk19 _stk1A _stk1B _stk1C _stk1D _stk1E _stk1F _stk20 _stk21 _stk22 _stk23 _stk24 _stk25 _stk26 _stk27 _stk28 _stk29 _stk2A _stk2B _stk2C _stk2D _stk2E _stk2F _stk30 _stk31 _stk32 _stk33 _stk34 _stk35 _stk36 _stk37 _stk38 _stk39 _stk3A _stk3B _stk3C _stk3D _stk3E _stk3F  : TVMBit . 
Definition RoundsBase_ι__roundInvestStake_А_stake_bs_def := [> _stk00 , _stk01 , _stk02 , _stk03 , _stk04 , _stk05 , _stk06 , _stk07 , _stk08 , _stk09 , _stk0A , _stk0B , _stk0C , _stk0D , _stk0E , _stk0F , _stk10 , _stk11 , _stk12 , _stk13 , _stk14 , _stk15 , _stk16 , _stk17 , _stk18 , _stk19 , _stk1A , _stk1B , _stk1C , _stk1D , _stk1E , _stk1F , _stk20 , _stk21 , _stk22 , _stk23 , _stk24 , _stk25 , _stk26 , _stk27 , _stk28 , _stk29 , _stk2A , _stk2B , _stk2C , _stk2D , _stk2E , _stk2F , _stk30 , _stk31 , _stk32 , _stk33 , _stk34 , _stk35 , _stk36 , _stk37 , _stk38 , _stk39 , _stk3A , _stk3B , _stk3C , _stk3D , _stk3E , _stk3F <] .
Lemma RoundsBase_ι__roundInvestStake_А_stake_bs_id: RoundsBase_ι__roundInvestStake_А_stake_bs_def = [> _stk00 , _stk01 , _stk02 , _stk03 , _stk04 , _stk05 , _stk06 , _stk07 , _stk08 , _stk09 , _stk0A , _stk0B , _stk0C , _stk0D , _stk0E , _stk0F , _stk10 , _stk11 , _stk12 , _stk13 , _stk14 , _stk15 , _stk16 , _stk17 , _stk18 , _stk19 , _stk1A , _stk1B , _stk1C , _stk1D , _stk1E , _stk1F , _stk20 , _stk21 , _stk22 , _stk23 , _stk24 , _stk25 , _stk26 , _stk27 , _stk28 , _stk29 , _stk2A , _stk2B , _stk2C , _stk2D , _stk2E , _stk2F , _stk30 , _stk31 , _stk32 , _stk33 , _stk34 , _stk35 , _stk36 , _stk37 , _stk38 , _stk39 , _stk3A , _stk3B , _stk3C , _stk3D , _stk3E , _stk3F (* } !*)  <] .
Proof. auto. Qed.
Axiom RoundsBase_ι__roundInvestStake_А_stake_bs' : Z2IBS_pos (tvmBitStringLen RoundsBase_ι__roundInvestStake_А_stake_bs_def) RoundsBase_ι__roundInvestStake_А_stake = RoundsBase_ι__roundInvestStake_А_stake_bs_def.
Lemma RoundsBase_ι__roundInvestStake_А_stake_bs : Z2IBS_pos 64 RoundsBase_ι__roundInvestStake_А_stake = RoundsBase_ι__roundInvestStake_А_stake_bs_def.
Proof.
 rewrite <- RoundsBase_ι__roundInvestStake_А_stake_bs'. auto. Qed.
Axiom RoundsBase_ι__roundInvestStake_А_stake_pos: (0 <= RoundsBase_ι__roundInvestStake_А_stake )%Z.
Axiom RoundsBase_ι__roundInvestStake_А_stake_fits: zFitN_pos (tvmBitStringLen RoundsBase_ι__roundInvestStake_А_stake_bs_def) RoundsBase_ι__roundInvestStake_А_stake = true.
Lemma RoundsBase_ι__roundInvestStake_А_stake_bs_rev : I2ZBS_pos' RoundsBase_ι__roundInvestStake_А_stake_bs_def = RoundsBase_ι__roundInvestStake_А_stake .
Proof.
  prove_bs_rev RoundsBase_ι__roundInvestStake_А_stake_bs RoundsBase_ι__roundInvestStake_А_stake_pos RoundsBase_ι__roundInvestStake_А_stake_fits. 
Qed.
Lemma RoundsBase_ι__roundInvestStake_А_stake_bs257 : Z2IN 257 RoundsBase_ι__roundInvestStake_А_stake = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    RoundsBase_ι__roundInvestStake_А_stake_bs_def)) RoundsBase_ι__roundInvestStake_А_stake_bs_def)).
Proof.
  prove_bs_rev RoundsBase_ι__roundInvestStake_А_stake_bs_rev RoundsBase_ι__roundInvestStake_А_stake_bs_def.
Qed.


Variables RoundsBase_ι__removePendingRound_А_pendingId : Z . 
Variables (*! { _pndn !*) _pndn00 _pndn01 _pndn02 _pndn03 _pndn04 _pndn05 _pndn06 _pndn07 _pndn08 _pndn09 _pndn0A _pndn0B _pndn0C _pndn0D _pndn0E _pndn0F _pndn10 _pndn11 _pndn12 _pndn13 _pndn14 _pndn15 _pndn16 _pndn17 _pndn18 _pndn19 _pndn1A _pndn1B _pndn1C _pndn1D _pndn1E _pndn1F  : TVMBit . 
Definition RoundsBase_ι__removePendingRound_А_pendingId_bs_def := [> _pndn00 , _pndn01 , _pndn02 , _pndn03 , _pndn04 , _pndn05 , _pndn06 , _pndn07 , _pndn08 , _pndn09 , _pndn0A , _pndn0B , _pndn0C , _pndn0D , _pndn0E , _pndn0F , _pndn10 , _pndn11 , _pndn12 , _pndn13 , _pndn14 , _pndn15 , _pndn16 , _pndn17 , _pndn18 , _pndn19 , _pndn1A , _pndn1B , _pndn1C , _pndn1D , _pndn1E , _pndn1F <] .
Lemma RoundsBase_ι__removePendingRound_А_pendingId_bs_id: RoundsBase_ι__removePendingRound_А_pendingId_bs_def = [> _pndn00 , _pndn01 , _pndn02 , _pndn03 , _pndn04 , _pndn05 , _pndn06 , _pndn07 , _pndn08 , _pndn09 , _pndn0A , _pndn0B , _pndn0C , _pndn0D , _pndn0E , _pndn0F , _pndn10 , _pndn11 , _pndn12 , _pndn13 , _pndn14 , _pndn15 , _pndn16 , _pndn17 , _pndn18 , _pndn19 , _pndn1A , _pndn1B , _pndn1C , _pndn1D , _pndn1E , _pndn1F (* } !*)  <] .
Proof. auto. Qed.
Axiom RoundsBase_ι__removePendingRound_А_pendingId_bs' : Z2IBS_pos (tvmBitStringLen RoundsBase_ι__removePendingRound_А_pendingId_bs_def) RoundsBase_ι__removePendingRound_А_pendingId = RoundsBase_ι__removePendingRound_А_pendingId_bs_def.
Lemma RoundsBase_ι__removePendingRound_А_pendingId_bs : Z2IBS_pos 32 RoundsBase_ι__removePendingRound_А_pendingId = RoundsBase_ι__removePendingRound_А_pendingId_bs_def.
Proof.
 rewrite <- RoundsBase_ι__removePendingRound_А_pendingId_bs'. auto. Qed.
Axiom RoundsBase_ι__removePendingRound_А_pendingId_pos: (0 <= RoundsBase_ι__removePendingRound_А_pendingId )%Z.
Axiom RoundsBase_ι__removePendingRound_А_pendingId_fits: zFitN_pos (tvmBitStringLen RoundsBase_ι__removePendingRound_А_pendingId_bs_def) RoundsBase_ι__removePendingRound_А_pendingId = true.
Lemma RoundsBase_ι__removePendingRound_А_pendingId_bs_rev : I2ZBS_pos' RoundsBase_ι__removePendingRound_А_pendingId_bs_def = RoundsBase_ι__removePendingRound_А_pendingId .
Proof.
  prove_bs_rev RoundsBase_ι__removePendingRound_А_pendingId_bs RoundsBase_ι__removePendingRound_А_pendingId_pos RoundsBase_ι__removePendingRound_А_pendingId_fits. 
Qed.
Lemma RoundsBase_ι__removePendingRound_А_pendingId_bs257 : Z2IN 257 RoundsBase_ι__removePendingRound_А_pendingId = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    RoundsBase_ι__removePendingRound_А_pendingId_bs_def)) RoundsBase_ι__removePendingRound_А_pendingId_bs_def)).
Proof.
  prove_bs_rev RoundsBase_ι__removePendingRound_А_pendingId_bs_rev RoundsBase_ι__removePendingRound_А_pendingId_bs_def.
Qed.



Variables StakingContract_ι__calcLastRoundInterest_А_totalStake : Z . 
Variables (*! { _ttlS !*) _ttlS00 _ttlS01 _ttlS02 _ttlS03 _ttlS04 _ttlS05 _ttlS06 _ttlS07 _ttlS08 _ttlS09 _ttlS0A _ttlS0B _ttlS0C _ttlS0D _ttlS0E _ttlS0F _ttlS10 _ttlS11 _ttlS12 _ttlS13 _ttlS14 _ttlS15 _ttlS16 _ttlS17 _ttlS18 _ttlS19 _ttlS1A _ttlS1B _ttlS1C _ttlS1D _ttlS1E _ttlS1F _ttlS20 _ttlS21 _ttlS22 _ttlS23 _ttlS24 _ttlS25 _ttlS26 _ttlS27 _ttlS28 _ttlS29 _ttlS2A _ttlS2B _ttlS2C _ttlS2D _ttlS2E _ttlS2F _ttlS30 _ttlS31 _ttlS32 _ttlS33 _ttlS34 _ttlS35 _ttlS36 _ttlS37 _ttlS38 _ttlS39 _ttlS3A _ttlS3B _ttlS3C _ttlS3D _ttlS3E _ttlS3F  : TVMBit . 
Definition StakingContract_ι__calcLastRoundInterest_А_totalStake_bs_def := [> _ttlS00 , _ttlS01 , _ttlS02 , _ttlS03 , _ttlS04 , _ttlS05 , _ttlS06 , _ttlS07 , _ttlS08 , _ttlS09 , _ttlS0A , _ttlS0B , _ttlS0C , _ttlS0D , _ttlS0E , _ttlS0F , _ttlS10 , _ttlS11 , _ttlS12 , _ttlS13 , _ttlS14 , _ttlS15 , _ttlS16 , _ttlS17 , _ttlS18 , _ttlS19 , _ttlS1A , _ttlS1B , _ttlS1C , _ttlS1D , _ttlS1E , _ttlS1F , _ttlS20 , _ttlS21 , _ttlS22 , _ttlS23 , _ttlS24 , _ttlS25 , _ttlS26 , _ttlS27 , _ttlS28 , _ttlS29 , _ttlS2A , _ttlS2B , _ttlS2C , _ttlS2D , _ttlS2E , _ttlS2F , _ttlS30 , _ttlS31 , _ttlS32 , _ttlS33 , _ttlS34 , _ttlS35 , _ttlS36 , _ttlS37 , _ttlS38 , _ttlS39 , _ttlS3A , _ttlS3B , _ttlS3C , _ttlS3D , _ttlS3E , _ttlS3F <] .
Lemma StakingContract_ι__calcLastRoundInterest_А_totalStake_bs_id: StakingContract_ι__calcLastRoundInterest_А_totalStake_bs_def = [> _ttlS00 , _ttlS01 , _ttlS02 , _ttlS03 , _ttlS04 , _ttlS05 , _ttlS06 , _ttlS07 , _ttlS08 , _ttlS09 , _ttlS0A , _ttlS0B , _ttlS0C , _ttlS0D , _ttlS0E , _ttlS0F , _ttlS10 , _ttlS11 , _ttlS12 , _ttlS13 , _ttlS14 , _ttlS15 , _ttlS16 , _ttlS17 , _ttlS18 , _ttlS19 , _ttlS1A , _ttlS1B , _ttlS1C , _ttlS1D , _ttlS1E , _ttlS1F , _ttlS20 , _ttlS21 , _ttlS22 , _ttlS23 , _ttlS24 , _ttlS25 , _ttlS26 , _ttlS27 , _ttlS28 , _ttlS29 , _ttlS2A , _ttlS2B , _ttlS2C , _ttlS2D , _ttlS2E , _ttlS2F , _ttlS30 , _ttlS31 , _ttlS32 , _ttlS33 , _ttlS34 , _ttlS35 , _ttlS36 , _ttlS37 , _ttlS38 , _ttlS39 , _ttlS3A , _ttlS3B , _ttlS3C , _ttlS3D , _ttlS3E , _ttlS3F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι__calcLastRoundInterest_А_totalStake_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι__calcLastRoundInterest_А_totalStake_bs_def) StakingContract_ι__calcLastRoundInterest_А_totalStake = StakingContract_ι__calcLastRoundInterest_А_totalStake_bs_def.
Lemma StakingContract_ι__calcLastRoundInterest_А_totalStake_bs : Z2IBS_pos 64 StakingContract_ι__calcLastRoundInterest_А_totalStake = StakingContract_ι__calcLastRoundInterest_А_totalStake_bs_def.
Proof.
 rewrite <- StakingContract_ι__calcLastRoundInterest_А_totalStake_bs'. auto. Qed.
Axiom StakingContract_ι__calcLastRoundInterest_А_totalStake_pos: (0 <= StakingContract_ι__calcLastRoundInterest_А_totalStake )%Z.
Axiom StakingContract_ι__calcLastRoundInterest_А_totalStake_fits: zFitN_pos (tvmBitStringLen StakingContract_ι__calcLastRoundInterest_А_totalStake_bs_def) StakingContract_ι__calcLastRoundInterest_А_totalStake = true.
Lemma StakingContract_ι__calcLastRoundInterest_А_totalStake_bs_rev : I2ZBS_pos' StakingContract_ι__calcLastRoundInterest_А_totalStake_bs_def = StakingContract_ι__calcLastRoundInterest_А_totalStake .
Proof.
  prove_bs_rev StakingContract_ι__calcLastRoundInterest_А_totalStake_bs StakingContract_ι__calcLastRoundInterest_А_totalStake_pos StakingContract_ι__calcLastRoundInterest_А_totalStake_fits. 
Qed.
Lemma StakingContract_ι__calcLastRoundInterest_А_totalStake_bs257 : Z2IN 257 StakingContract_ι__calcLastRoundInterest_А_totalStake = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι__calcLastRoundInterest_А_totalStake_bs_def)) StakingContract_ι__calcLastRoundInterest_А_totalStake_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι__calcLastRoundInterest_А_totalStake_bs_rev StakingContract_ι__calcLastRoundInterest_А_totalStake_bs_def.
Qed. 
Variables StakingContract_ι__calcLastRoundInterest_А_rewards : Z . 
Variables (*! { _rwrd !*) _rwrd00 _rwrd01 _rwrd02 _rwrd03 _rwrd04 _rwrd05 _rwrd06 _rwrd07 _rwrd08 _rwrd09 _rwrd0A _rwrd0B _rwrd0C _rwrd0D _rwrd0E _rwrd0F _rwrd10 _rwrd11 _rwrd12 _rwrd13 _rwrd14 _rwrd15 _rwrd16 _rwrd17 _rwrd18 _rwrd19 _rwrd1A _rwrd1B _rwrd1C _rwrd1D _rwrd1E _rwrd1F _rwrd20 _rwrd21 _rwrd22 _rwrd23 _rwrd24 _rwrd25 _rwrd26 _rwrd27 _rwrd28 _rwrd29 _rwrd2A _rwrd2B _rwrd2C _rwrd2D _rwrd2E _rwrd2F _rwrd30 _rwrd31 _rwrd32 _rwrd33 _rwrd34 _rwrd35 _rwrd36 _rwrd37 _rwrd38 _rwrd39 _rwrd3A _rwrd3B _rwrd3C _rwrd3D _rwrd3E _rwrd3F  : TVMBit . 
Definition StakingContract_ι__calcLastRoundInterest_А_rewards_bs_def := [> _rwrd00 , _rwrd01 , _rwrd02 , _rwrd03 , _rwrd04 , _rwrd05 , _rwrd06 , _rwrd07 , _rwrd08 , _rwrd09 , _rwrd0A , _rwrd0B , _rwrd0C , _rwrd0D , _rwrd0E , _rwrd0F , _rwrd10 , _rwrd11 , _rwrd12 , _rwrd13 , _rwrd14 , _rwrd15 , _rwrd16 , _rwrd17 , _rwrd18 , _rwrd19 , _rwrd1A , _rwrd1B , _rwrd1C , _rwrd1D , _rwrd1E , _rwrd1F , _rwrd20 , _rwrd21 , _rwrd22 , _rwrd23 , _rwrd24 , _rwrd25 , _rwrd26 , _rwrd27 , _rwrd28 , _rwrd29 , _rwrd2A , _rwrd2B , _rwrd2C , _rwrd2D , _rwrd2E , _rwrd2F , _rwrd30 , _rwrd31 , _rwrd32 , _rwrd33 , _rwrd34 , _rwrd35 , _rwrd36 , _rwrd37 , _rwrd38 , _rwrd39 , _rwrd3A , _rwrd3B , _rwrd3C , _rwrd3D , _rwrd3E , _rwrd3F <] .
Lemma StakingContract_ι__calcLastRoundInterest_А_rewards_bs_id: StakingContract_ι__calcLastRoundInterest_А_rewards_bs_def = [> _rwrd00 , _rwrd01 , _rwrd02 , _rwrd03 , _rwrd04 , _rwrd05 , _rwrd06 , _rwrd07 , _rwrd08 , _rwrd09 , _rwrd0A , _rwrd0B , _rwrd0C , _rwrd0D , _rwrd0E , _rwrd0F , _rwrd10 , _rwrd11 , _rwrd12 , _rwrd13 , _rwrd14 , _rwrd15 , _rwrd16 , _rwrd17 , _rwrd18 , _rwrd19 , _rwrd1A , _rwrd1B , _rwrd1C , _rwrd1D , _rwrd1E , _rwrd1F , _rwrd20 , _rwrd21 , _rwrd22 , _rwrd23 , _rwrd24 , _rwrd25 , _rwrd26 , _rwrd27 , _rwrd28 , _rwrd29 , _rwrd2A , _rwrd2B , _rwrd2C , _rwrd2D , _rwrd2E , _rwrd2F , _rwrd30 , _rwrd31 , _rwrd32 , _rwrd33 , _rwrd34 , _rwrd35 , _rwrd36 , _rwrd37 , _rwrd38 , _rwrd39 , _rwrd3A , _rwrd3B , _rwrd3C , _rwrd3D , _rwrd3E , _rwrd3F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι__calcLastRoundInterest_А_rewards_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι__calcLastRoundInterest_А_rewards_bs_def) StakingContract_ι__calcLastRoundInterest_А_rewards = StakingContract_ι__calcLastRoundInterest_А_rewards_bs_def.
Lemma StakingContract_ι__calcLastRoundInterest_А_rewards_bs : Z2IBS_pos 64 StakingContract_ι__calcLastRoundInterest_А_rewards = StakingContract_ι__calcLastRoundInterest_А_rewards_bs_def.
Proof.
 rewrite <- StakingContract_ι__calcLastRoundInterest_А_rewards_bs'. auto. Qed.
Axiom StakingContract_ι__calcLastRoundInterest_А_rewards_pos: (0 <= StakingContract_ι__calcLastRoundInterest_А_rewards )%Z.
Axiom StakingContract_ι__calcLastRoundInterest_А_rewards_fits: zFitN_pos (tvmBitStringLen StakingContract_ι__calcLastRoundInterest_А_rewards_bs_def) StakingContract_ι__calcLastRoundInterest_А_rewards = true.
Lemma StakingContract_ι__calcLastRoundInterest_А_rewards_bs_rev : I2ZBS_pos' StakingContract_ι__calcLastRoundInterest_А_rewards_bs_def = StakingContract_ι__calcLastRoundInterest_А_rewards .
Proof.
  prove_bs_rev StakingContract_ι__calcLastRoundInterest_А_rewards_bs StakingContract_ι__calcLastRoundInterest_А_rewards_pos StakingContract_ι__calcLastRoundInterest_А_rewards_fits. 
Qed.
Lemma StakingContract_ι__calcLastRoundInterest_А_rewards_bs257 : Z2IN 257 StakingContract_ι__calcLastRoundInterest_А_rewards = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι__calcLastRoundInterest_А_rewards_bs_def)) StakingContract_ι__calcLastRoundInterest_А_rewards_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι__calcLastRoundInterest_А_rewards_bs_rev StakingContract_ι__calcLastRoundInterest_А_rewards_bs_def.
Qed.

Variables StakingContract_ι__returnError_А_errcode : Z . 
Variables (*! { _rrcd !*) _rrcd00 _rrcd01 _rrcd02 _rrcd03 _rrcd04 _rrcd05 _rrcd06 _rrcd07 _rrcd08 _rrcd09 _rrcd0A _rrcd0B _rrcd0C _rrcd0D _rrcd0E _rrcd0F _rrcd10 _rrcd11 _rrcd12 _rrcd13 _rrcd14 _rrcd15 _rrcd16 _rrcd17 _rrcd18 _rrcd19 _rrcd1A _rrcd1B _rrcd1C _rrcd1D _rrcd1E _rrcd1F  : TVMBit . 
Definition StakingContract_ι__returnError_А_errcode_bs_def := [> _rrcd00 , _rrcd01 , _rrcd02 , _rrcd03 , _rrcd04 , _rrcd05 , _rrcd06 , _rrcd07 , _rrcd08 , _rrcd09 , _rrcd0A , _rrcd0B , _rrcd0C , _rrcd0D , _rrcd0E , _rrcd0F , _rrcd10 , _rrcd11 , _rrcd12 , _rrcd13 , _rrcd14 , _rrcd15 , _rrcd16 , _rrcd17 , _rrcd18 , _rrcd19 , _rrcd1A , _rrcd1B , _rrcd1C , _rrcd1D , _rrcd1E , _rrcd1F <] .
Lemma StakingContract_ι__returnError_А_errcode_bs_id: StakingContract_ι__returnError_А_errcode_bs_def = [> _rrcd00 , _rrcd01 , _rrcd02 , _rrcd03 , _rrcd04 , _rrcd05 , _rrcd06 , _rrcd07 , _rrcd08 , _rrcd09 , _rrcd0A , _rrcd0B , _rrcd0C , _rrcd0D , _rrcd0E , _rrcd0F , _rrcd10 , _rrcd11 , _rrcd12 , _rrcd13 , _rrcd14 , _rrcd15 , _rrcd16 , _rrcd17 , _rrcd18 , _rrcd19 , _rrcd1A , _rrcd1B , _rrcd1C , _rrcd1D , _rrcd1E , _rrcd1F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι__returnError_А_errcode_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι__returnError_А_errcode_bs_def) StakingContract_ι__returnError_А_errcode = StakingContract_ι__returnError_А_errcode_bs_def.
Lemma StakingContract_ι__returnError_А_errcode_bs : Z2IBS_pos 32 StakingContract_ι__returnError_А_errcode = StakingContract_ι__returnError_А_errcode_bs_def.
Proof.
 rewrite <- StakingContract_ι__returnError_А_errcode_bs'. auto. Qed.
Axiom StakingContract_ι__returnError_А_errcode_pos: (0 <= StakingContract_ι__returnError_А_errcode )%Z.
Axiom StakingContract_ι__returnError_А_errcode_fits: zFitN_pos (tvmBitStringLen StakingContract_ι__returnError_А_errcode_bs_def) StakingContract_ι__returnError_А_errcode = true.
Lemma StakingContract_ι__returnError_А_errcode_bs_rev : I2ZBS_pos' StakingContract_ι__returnError_А_errcode_bs_def = StakingContract_ι__returnError_А_errcode .
Proof.
  prove_bs_rev StakingContract_ι__returnError_А_errcode_bs StakingContract_ι__returnError_А_errcode_pos StakingContract_ι__returnError_А_errcode_fits. 
Qed.
Lemma StakingContract_ι__returnError_А_errcode_bs257 : Z2IN 257 StakingContract_ι__returnError_А_errcode = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι__returnError_А_errcode_bs_def)) StakingContract_ι__returnError_А_errcode_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι__returnError_А_errcode_bs_rev StakingContract_ι__returnError_А_errcode_bs_def.
Qed. 
Variables StakingContract_ι__returnError_А_amount : Z . 
Variables (*! { _mnt !*) _mnt00 _mnt01 _mnt02 _mnt03 _mnt04 _mnt05 _mnt06 _mnt07 _mnt08 _mnt09 _mnt0A _mnt0B _mnt0C _mnt0D _mnt0E _mnt0F _mnt10 _mnt11 _mnt12 _mnt13 _mnt14 _mnt15 _mnt16 _mnt17 _mnt18 _mnt19 _mnt1A _mnt1B _mnt1C _mnt1D _mnt1E _mnt1F _mnt20 _mnt21 _mnt22 _mnt23 _mnt24 _mnt25 _mnt26 _mnt27 _mnt28 _mnt29 _mnt2A _mnt2B _mnt2C _mnt2D _mnt2E _mnt2F _mnt30 _mnt31 _mnt32 _mnt33 _mnt34 _mnt35 _mnt36 _mnt37 _mnt38 _mnt39 _mnt3A _mnt3B _mnt3C _mnt3D _mnt3E _mnt3F  : TVMBit . 
Definition StakingContract_ι__returnError_А_amount_bs_def := [> _mnt00 , _mnt01 , _mnt02 , _mnt03 , _mnt04 , _mnt05 , _mnt06 , _mnt07 , _mnt08 , _mnt09 , _mnt0A , _mnt0B , _mnt0C , _mnt0D , _mnt0E , _mnt0F , _mnt10 , _mnt11 , _mnt12 , _mnt13 , _mnt14 , _mnt15 , _mnt16 , _mnt17 , _mnt18 , _mnt19 , _mnt1A , _mnt1B , _mnt1C , _mnt1D , _mnt1E , _mnt1F , _mnt20 , _mnt21 , _mnt22 , _mnt23 , _mnt24 , _mnt25 , _mnt26 , _mnt27 , _mnt28 , _mnt29 , _mnt2A , _mnt2B , _mnt2C , _mnt2D , _mnt2E , _mnt2F , _mnt30 , _mnt31 , _mnt32 , _mnt33 , _mnt34 , _mnt35 , _mnt36 , _mnt37 , _mnt38 , _mnt39 , _mnt3A , _mnt3B , _mnt3C , _mnt3D , _mnt3E , _mnt3F <] .
Lemma StakingContract_ι__returnError_А_amount_bs_id: StakingContract_ι__returnError_А_amount_bs_def = [> _mnt00 , _mnt01 , _mnt02 , _mnt03 , _mnt04 , _mnt05 , _mnt06 , _mnt07 , _mnt08 , _mnt09 , _mnt0A , _mnt0B , _mnt0C , _mnt0D , _mnt0E , _mnt0F , _mnt10 , _mnt11 , _mnt12 , _mnt13 , _mnt14 , _mnt15 , _mnt16 , _mnt17 , _mnt18 , _mnt19 , _mnt1A , _mnt1B , _mnt1C , _mnt1D , _mnt1E , _mnt1F , _mnt20 , _mnt21 , _mnt22 , _mnt23 , _mnt24 , _mnt25 , _mnt26 , _mnt27 , _mnt28 , _mnt29 , _mnt2A , _mnt2B , _mnt2C , _mnt2D , _mnt2E , _mnt2F , _mnt30 , _mnt31 , _mnt32 , _mnt33 , _mnt34 , _mnt35 , _mnt36 , _mnt37 , _mnt38 , _mnt39 , _mnt3A , _mnt3B , _mnt3C , _mnt3D , _mnt3E , _mnt3F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι__returnError_А_amount_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι__returnError_А_amount_bs_def) StakingContract_ι__returnError_А_amount = StakingContract_ι__returnError_А_amount_bs_def.
Lemma StakingContract_ι__returnError_А_amount_bs : Z2IBS_pos 64 StakingContract_ι__returnError_А_amount = StakingContract_ι__returnError_А_amount_bs_def.
Proof.
 rewrite <- StakingContract_ι__returnError_А_amount_bs'. auto. Qed.
Axiom StakingContract_ι__returnError_А_amount_pos: (0 <= StakingContract_ι__returnError_А_amount )%Z.
Axiom StakingContract_ι__returnError_А_amount_fits: zFitN_pos (tvmBitStringLen StakingContract_ι__returnError_А_amount_bs_def) StakingContract_ι__returnError_А_amount = true.
Lemma StakingContract_ι__returnError_А_amount_bs_rev : I2ZBS_pos' StakingContract_ι__returnError_А_amount_bs_def = StakingContract_ι__returnError_А_amount .
Proof.
  prove_bs_rev StakingContract_ι__returnError_А_amount_bs StakingContract_ι__returnError_А_amount_pos StakingContract_ι__returnError_А_amount_fits. 
Qed.
Lemma StakingContract_ι__returnError_А_amount_bs257 : Z2IN 257 StakingContract_ι__returnError_А_amount = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι__returnError_А_amount_bs_def)) StakingContract_ι__returnError_А_amount_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι__returnError_А_amount_bs_rev StakingContract_ι__returnError_А_amount_bs_def.
Qed. 
Variables StakingContract_ι__returnError_А_comment : Z . 
Variables (*! { _cmmn !*) _cmmn00 _cmmn01 _cmmn02 _cmmn03 _cmmn04 _cmmn05 _cmmn06 _cmmn07 _cmmn08 _cmmn09 _cmmn0A _cmmn0B _cmmn0C _cmmn0D _cmmn0E _cmmn0F _cmmn10 _cmmn11 _cmmn12 _cmmn13 _cmmn14 _cmmn15 _cmmn16 _cmmn17 _cmmn18 _cmmn19 _cmmn1A _cmmn1B _cmmn1C _cmmn1D _cmmn1E _cmmn1F _cmmn20 _cmmn21 _cmmn22 _cmmn23 _cmmn24 _cmmn25 _cmmn26 _cmmn27 _cmmn28 _cmmn29 _cmmn2A _cmmn2B _cmmn2C _cmmn2D _cmmn2E _cmmn2F _cmmn30 _cmmn31 _cmmn32 _cmmn33 _cmmn34 _cmmn35 _cmmn36 _cmmn37 _cmmn38 _cmmn39 _cmmn3A _cmmn3B _cmmn3C _cmmn3D _cmmn3E _cmmn3F  : TVMBit . 
Definition StakingContract_ι__returnError_А_comment_bs_def := [> _cmmn00 , _cmmn01 , _cmmn02 , _cmmn03 , _cmmn04 , _cmmn05 , _cmmn06 , _cmmn07 , _cmmn08 , _cmmn09 , _cmmn0A , _cmmn0B , _cmmn0C , _cmmn0D , _cmmn0E , _cmmn0F , _cmmn10 , _cmmn11 , _cmmn12 , _cmmn13 , _cmmn14 , _cmmn15 , _cmmn16 , _cmmn17 , _cmmn18 , _cmmn19 , _cmmn1A , _cmmn1B , _cmmn1C , _cmmn1D , _cmmn1E , _cmmn1F , _cmmn20 , _cmmn21 , _cmmn22 , _cmmn23 , _cmmn24 , _cmmn25 , _cmmn26 , _cmmn27 , _cmmn28 , _cmmn29 , _cmmn2A , _cmmn2B , _cmmn2C , _cmmn2D , _cmmn2E , _cmmn2F , _cmmn30 , _cmmn31 , _cmmn32 , _cmmn33 , _cmmn34 , _cmmn35 , _cmmn36 , _cmmn37 , _cmmn38 , _cmmn39 , _cmmn3A , _cmmn3B , _cmmn3C , _cmmn3D , _cmmn3E , _cmmn3F <] .
Lemma StakingContract_ι__returnError_А_comment_bs_id: StakingContract_ι__returnError_А_comment_bs_def = [> _cmmn00 , _cmmn01 , _cmmn02 , _cmmn03 , _cmmn04 , _cmmn05 , _cmmn06 , _cmmn07 , _cmmn08 , _cmmn09 , _cmmn0A , _cmmn0B , _cmmn0C , _cmmn0D , _cmmn0E , _cmmn0F , _cmmn10 , _cmmn11 , _cmmn12 , _cmmn13 , _cmmn14 , _cmmn15 , _cmmn16 , _cmmn17 , _cmmn18 , _cmmn19 , _cmmn1A , _cmmn1B , _cmmn1C , _cmmn1D , _cmmn1E , _cmmn1F , _cmmn20 , _cmmn21 , _cmmn22 , _cmmn23 , _cmmn24 , _cmmn25 , _cmmn26 , _cmmn27 , _cmmn28 , _cmmn29 , _cmmn2A , _cmmn2B , _cmmn2C , _cmmn2D , _cmmn2E , _cmmn2F , _cmmn30 , _cmmn31 , _cmmn32 , _cmmn33 , _cmmn34 , _cmmn35 , _cmmn36 , _cmmn37 , _cmmn38 , _cmmn39 , _cmmn3A , _cmmn3B , _cmmn3C , _cmmn3D , _cmmn3E , _cmmn3F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι__returnError_А_comment_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι__returnError_А_comment_bs_def) StakingContract_ι__returnError_А_comment = StakingContract_ι__returnError_А_comment_bs_def.
Lemma StakingContract_ι__returnError_А_comment_bs : Z2IBS_pos 64 StakingContract_ι__returnError_А_comment = StakingContract_ι__returnError_А_comment_bs_def.
Proof.
 rewrite <- StakingContract_ι__returnError_А_comment_bs'. auto. Qed.
Axiom StakingContract_ι__returnError_А_comment_pos: (0 <= StakingContract_ι__returnError_А_comment )%Z.
Axiom StakingContract_ι__returnError_А_comment_fits: zFitN_pos (tvmBitStringLen StakingContract_ι__returnError_А_comment_bs_def) StakingContract_ι__returnError_А_comment = true.
Lemma StakingContract_ι__returnError_А_comment_bs_rev : I2ZBS_pos' StakingContract_ι__returnError_А_comment_bs_def = StakingContract_ι__returnError_А_comment .
Proof.
  prove_bs_rev StakingContract_ι__returnError_А_comment_bs StakingContract_ι__returnError_А_comment_pos StakingContract_ι__returnError_А_comment_fits. 
Qed.
Lemma StakingContract_ι__returnError_А_comment_bs257 : Z2IN 257 StakingContract_ι__returnError_А_comment = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι__returnError_А_comment_bs_def)) StakingContract_ι__returnError_А_comment_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι__returnError_А_comment_bs_rev StakingContract_ι__returnError_А_comment_bs_def.
Qed.

Variables StakingContract_ι__returnConfirmation_А_fee : Z . 
Variables (*! { _f !*) _f00 _f01 _f02 _f03 _f04 _f05 _f06 _f07 _f08 _f09 _f0A _f0B _f0C _f0D _f0E _f0F _f10 _f11 _f12 _f13 _f14 _f15 _f16 _f17 _f18 _f19 _f1A _f1B _f1C _f1D _f1E _f1F _f20 _f21 _f22 _f23 _f24 _f25 _f26 _f27 _f28 _f29 _f2A _f2B _f2C _f2D _f2E _f2F _f30 _f31 _f32 _f33 _f34 _f35 _f36 _f37 _f38 _f39 _f3A _f3B _f3C _f3D _f3E _f3F  : TVMBit . 
Definition StakingContract_ι__returnConfirmation_А_fee_bs_def := [> _f00 , _f01 , _f02 , _f03 , _f04 , _f05 , _f06 , _f07 , _f08 , _f09 , _f0A , _f0B , _f0C , _f0D , _f0E , _f0F , _f10 , _f11 , _f12 , _f13 , _f14 , _f15 , _f16 , _f17 , _f18 , _f19 , _f1A , _f1B , _f1C , _f1D , _f1E , _f1F , _f20 , _f21 , _f22 , _f23 , _f24 , _f25 , _f26 , _f27 , _f28 , _f29 , _f2A , _f2B , _f2C , _f2D , _f2E , _f2F , _f30 , _f31 , _f32 , _f33 , _f34 , _f35 , _f36 , _f37 , _f38 , _f39 , _f3A , _f3B , _f3C , _f3D , _f3E , _f3F <] .
Lemma StakingContract_ι__returnConfirmation_А_fee_bs_id: StakingContract_ι__returnConfirmation_А_fee_bs_def = [> _f00 , _f01 , _f02 , _f03 , _f04 , _f05 , _f06 , _f07 , _f08 , _f09 , _f0A , _f0B , _f0C , _f0D , _f0E , _f0F , _f10 , _f11 , _f12 , _f13 , _f14 , _f15 , _f16 , _f17 , _f18 , _f19 , _f1A , _f1B , _f1C , _f1D , _f1E , _f1F , _f20 , _f21 , _f22 , _f23 , _f24 , _f25 , _f26 , _f27 , _f28 , _f29 , _f2A , _f2B , _f2C , _f2D , _f2E , _f2F , _f30 , _f31 , _f32 , _f33 , _f34 , _f35 , _f36 , _f37 , _f38 , _f39 , _f3A , _f3B , _f3C , _f3D , _f3E , _f3F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι__returnConfirmation_А_fee_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι__returnConfirmation_А_fee_bs_def) StakingContract_ι__returnConfirmation_А_fee = StakingContract_ι__returnConfirmation_А_fee_bs_def.
Lemma StakingContract_ι__returnConfirmation_А_fee_bs : Z2IBS_pos 64 StakingContract_ι__returnConfirmation_А_fee = StakingContract_ι__returnConfirmation_А_fee_bs_def.
Proof.
 rewrite <- StakingContract_ι__returnConfirmation_А_fee_bs'. auto. Qed.
Axiom StakingContract_ι__returnConfirmation_А_fee_pos: (0 <= StakingContract_ι__returnConfirmation_А_fee )%Z.
Axiom StakingContract_ι__returnConfirmation_А_fee_fits: zFitN_pos (tvmBitStringLen StakingContract_ι__returnConfirmation_А_fee_bs_def) StakingContract_ι__returnConfirmation_А_fee = true.
Lemma StakingContract_ι__returnConfirmation_А_fee_bs_rev : I2ZBS_pos' StakingContract_ι__returnConfirmation_А_fee_bs_def = StakingContract_ι__returnConfirmation_А_fee .
Proof.
  prove_bs_rev StakingContract_ι__returnConfirmation_А_fee_bs StakingContract_ι__returnConfirmation_А_fee_pos StakingContract_ι__returnConfirmation_А_fee_fits. 
Qed.
Lemma StakingContract_ι__returnConfirmation_А_fee_bs257 : Z2IN 257 StakingContract_ι__returnConfirmation_А_fee = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι__returnConfirmation_А_fee_bs_def)) StakingContract_ι__returnConfirmation_А_fee_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι__returnConfirmation_А_fee_bs_rev StakingContract_ι__returnConfirmation_А_fee_bs_def.
Qed.
  
Variables StakingContract_ι__investStake_А_unusedStake : Z . 
Variables (*! { _nsdS !*) _nsdS00 _nsdS01 _nsdS02 _nsdS03 _nsdS04 _nsdS05 _nsdS06 _nsdS07 _nsdS08 _nsdS09 _nsdS0A _nsdS0B _nsdS0C _nsdS0D _nsdS0E _nsdS0F _nsdS10 _nsdS11 _nsdS12 _nsdS13 _nsdS14 _nsdS15 _nsdS16 _nsdS17 _nsdS18 _nsdS19 _nsdS1A _nsdS1B _nsdS1C _nsdS1D _nsdS1E _nsdS1F _nsdS20 _nsdS21 _nsdS22 _nsdS23 _nsdS24 _nsdS25 _nsdS26 _nsdS27 _nsdS28 _nsdS29 _nsdS2A _nsdS2B _nsdS2C _nsdS2D _nsdS2E _nsdS2F _nsdS30 _nsdS31 _nsdS32 _nsdS33 _nsdS34 _nsdS35 _nsdS36 _nsdS37 _nsdS38 _nsdS39 _nsdS3A _nsdS3B _nsdS3C _nsdS3D _nsdS3E _nsdS3F  : TVMBit . 
Definition StakingContract_ι__investStake_А_unusedStake_bs_def := [> _nsdS00 , _nsdS01 , _nsdS02 , _nsdS03 , _nsdS04 , _nsdS05 , _nsdS06 , _nsdS07 , _nsdS08 , _nsdS09 , _nsdS0A , _nsdS0B , _nsdS0C , _nsdS0D , _nsdS0E , _nsdS0F , _nsdS10 , _nsdS11 , _nsdS12 , _nsdS13 , _nsdS14 , _nsdS15 , _nsdS16 , _nsdS17 , _nsdS18 , _nsdS19 , _nsdS1A , _nsdS1B , _nsdS1C , _nsdS1D , _nsdS1E , _nsdS1F , _nsdS20 , _nsdS21 , _nsdS22 , _nsdS23 , _nsdS24 , _nsdS25 , _nsdS26 , _nsdS27 , _nsdS28 , _nsdS29 , _nsdS2A , _nsdS2B , _nsdS2C , _nsdS2D , _nsdS2E , _nsdS2F , _nsdS30 , _nsdS31 , _nsdS32 , _nsdS33 , _nsdS34 , _nsdS35 , _nsdS36 , _nsdS37 , _nsdS38 , _nsdS39 , _nsdS3A , _nsdS3B , _nsdS3C , _nsdS3D , _nsdS3E , _nsdS3F <] .
Lemma StakingContract_ι__investStake_А_unusedStake_bs_id: StakingContract_ι__investStake_А_unusedStake_bs_def = [> _nsdS00 , _nsdS01 , _nsdS02 , _nsdS03 , _nsdS04 , _nsdS05 , _nsdS06 , _nsdS07 , _nsdS08 , _nsdS09 , _nsdS0A , _nsdS0B , _nsdS0C , _nsdS0D , _nsdS0E , _nsdS0F , _nsdS10 , _nsdS11 , _nsdS12 , _nsdS13 , _nsdS14 , _nsdS15 , _nsdS16 , _nsdS17 , _nsdS18 , _nsdS19 , _nsdS1A , _nsdS1B , _nsdS1C , _nsdS1D , _nsdS1E , _nsdS1F , _nsdS20 , _nsdS21 , _nsdS22 , _nsdS23 , _nsdS24 , _nsdS25 , _nsdS26 , _nsdS27 , _nsdS28 , _nsdS29 , _nsdS2A , _nsdS2B , _nsdS2C , _nsdS2D , _nsdS2E , _nsdS2F , _nsdS30 , _nsdS31 , _nsdS32 , _nsdS33 , _nsdS34 , _nsdS35 , _nsdS36 , _nsdS37 , _nsdS38 , _nsdS39 , _nsdS3A , _nsdS3B , _nsdS3C , _nsdS3D , _nsdS3E , _nsdS3F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι__investStake_А_unusedStake_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι__investStake_А_unusedStake_bs_def) StakingContract_ι__investStake_А_unusedStake = StakingContract_ι__investStake_А_unusedStake_bs_def.
Lemma StakingContract_ι__investStake_А_unusedStake_bs : Z2IBS_pos 64 StakingContract_ι__investStake_А_unusedStake = StakingContract_ι__investStake_А_unusedStake_bs_def.
Proof.
 rewrite <- StakingContract_ι__investStake_А_unusedStake_bs'. auto. Qed.
Axiom StakingContract_ι__investStake_А_unusedStake_pos: (0 <= StakingContract_ι__investStake_А_unusedStake )%Z.
Axiom StakingContract_ι__investStake_А_unusedStake_fits: zFitN_pos (tvmBitStringLen StakingContract_ι__investStake_А_unusedStake_bs_def) StakingContract_ι__investStake_А_unusedStake = true.
Lemma StakingContract_ι__investStake_А_unusedStake_bs_rev : I2ZBS_pos' StakingContract_ι__investStake_А_unusedStake_bs_def = StakingContract_ι__investStake_А_unusedStake .
Proof.
  prove_bs_rev StakingContract_ι__investStake_А_unusedStake_bs StakingContract_ι__investStake_А_unusedStake_pos StakingContract_ι__investStake_А_unusedStake_fits. 
Qed.
Lemma StakingContract_ι__investStake_А_unusedStake_bs257 : Z2IN 257 StakingContract_ι__investStake_А_unusedStake = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι__investStake_А_unusedStake_bs_def)) StakingContract_ι__investStake_А_unusedStake_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι__investStake_А_unusedStake_bs_rev StakingContract_ι__investStake_А_unusedStake_bs_def.
Qed. 
Variables StakingContract_ι__investStake_А_newStake : Z . 
Variables (*! { _nwSt !*) _nwSt00 _nwSt01 _nwSt02 _nwSt03 _nwSt04 _nwSt05 _nwSt06 _nwSt07 _nwSt08 _nwSt09 _nwSt0A _nwSt0B _nwSt0C _nwSt0D _nwSt0E _nwSt0F _nwSt10 _nwSt11 _nwSt12 _nwSt13 _nwSt14 _nwSt15 _nwSt16 _nwSt17 _nwSt18 _nwSt19 _nwSt1A _nwSt1B _nwSt1C _nwSt1D _nwSt1E _nwSt1F _nwSt20 _nwSt21 _nwSt22 _nwSt23 _nwSt24 _nwSt25 _nwSt26 _nwSt27 _nwSt28 _nwSt29 _nwSt2A _nwSt2B _nwSt2C _nwSt2D _nwSt2E _nwSt2F _nwSt30 _nwSt31 _nwSt32 _nwSt33 _nwSt34 _nwSt35 _nwSt36 _nwSt37 _nwSt38 _nwSt39 _nwSt3A _nwSt3B _nwSt3C _nwSt3D _nwSt3E _nwSt3F  : TVMBit . 
Definition StakingContract_ι__investStake_А_newStake_bs_def := [> _nwSt00 , _nwSt01 , _nwSt02 , _nwSt03 , _nwSt04 , _nwSt05 , _nwSt06 , _nwSt07 , _nwSt08 , _nwSt09 , _nwSt0A , _nwSt0B , _nwSt0C , _nwSt0D , _nwSt0E , _nwSt0F , _nwSt10 , _nwSt11 , _nwSt12 , _nwSt13 , _nwSt14 , _nwSt15 , _nwSt16 , _nwSt17 , _nwSt18 , _nwSt19 , _nwSt1A , _nwSt1B , _nwSt1C , _nwSt1D , _nwSt1E , _nwSt1F , _nwSt20 , _nwSt21 , _nwSt22 , _nwSt23 , _nwSt24 , _nwSt25 , _nwSt26 , _nwSt27 , _nwSt28 , _nwSt29 , _nwSt2A , _nwSt2B , _nwSt2C , _nwSt2D , _nwSt2E , _nwSt2F , _nwSt30 , _nwSt31 , _nwSt32 , _nwSt33 , _nwSt34 , _nwSt35 , _nwSt36 , _nwSt37 , _nwSt38 , _nwSt39 , _nwSt3A , _nwSt3B , _nwSt3C , _nwSt3D , _nwSt3E , _nwSt3F <] .
Lemma StakingContract_ι__investStake_А_newStake_bs_id: StakingContract_ι__investStake_А_newStake_bs_def = [> _nwSt00 , _nwSt01 , _nwSt02 , _nwSt03 , _nwSt04 , _nwSt05 , _nwSt06 , _nwSt07 , _nwSt08 , _nwSt09 , _nwSt0A , _nwSt0B , _nwSt0C , _nwSt0D , _nwSt0E , _nwSt0F , _nwSt10 , _nwSt11 , _nwSt12 , _nwSt13 , _nwSt14 , _nwSt15 , _nwSt16 , _nwSt17 , _nwSt18 , _nwSt19 , _nwSt1A , _nwSt1B , _nwSt1C , _nwSt1D , _nwSt1E , _nwSt1F , _nwSt20 , _nwSt21 , _nwSt22 , _nwSt23 , _nwSt24 , _nwSt25 , _nwSt26 , _nwSt27 , _nwSt28 , _nwSt29 , _nwSt2A , _nwSt2B , _nwSt2C , _nwSt2D , _nwSt2E , _nwSt2F , _nwSt30 , _nwSt31 , _nwSt32 , _nwSt33 , _nwSt34 , _nwSt35 , _nwSt36 , _nwSt37 , _nwSt38 , _nwSt39 , _nwSt3A , _nwSt3B , _nwSt3C , _nwSt3D , _nwSt3E , _nwSt3F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι__investStake_А_newStake_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι__investStake_А_newStake_bs_def) StakingContract_ι__investStake_А_newStake = StakingContract_ι__investStake_А_newStake_bs_def.
Lemma StakingContract_ι__investStake_А_newStake_bs : Z2IBS_pos 64 StakingContract_ι__investStake_А_newStake = StakingContract_ι__investStake_А_newStake_bs_def.
Proof.
 rewrite <- StakingContract_ι__investStake_А_newStake_bs'. auto. Qed.
Axiom StakingContract_ι__investStake_А_newStake_pos: (0 <= StakingContract_ι__investStake_А_newStake )%Z.
Axiom StakingContract_ι__investStake_А_newStake_fits: zFitN_pos (tvmBitStringLen StakingContract_ι__investStake_А_newStake_bs_def) StakingContract_ι__investStake_А_newStake = true.
Lemma StakingContract_ι__investStake_А_newStake_bs_rev : I2ZBS_pos' StakingContract_ι__investStake_А_newStake_bs_def = StakingContract_ι__investStake_А_newStake .
Proof.
  prove_bs_rev StakingContract_ι__investStake_А_newStake_bs StakingContract_ι__investStake_А_newStake_pos StakingContract_ι__investStake_А_newStake_fits. 
Qed.
Lemma StakingContract_ι__investStake_А_newStake_bs257 : Z2IN 257 StakingContract_ι__investStake_А_newStake = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι__investStake_А_newStake_bs_def)) StakingContract_ι__investStake_А_newStake_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι__investStake_А_newStake_bs_rev StakingContract_ι__investStake_А_newStake_bs_def.
Qed. 


Variables StakingContract_ι__addRequest_А_stakeAt : Z . 
Variables (*! { _stkt !*) _stkt00 _stkt01 _stkt02 _stkt03 _stkt04 _stkt05 _stkt06 _stkt07 _stkt08 _stkt09 _stkt0A _stkt0B _stkt0C _stkt0D _stkt0E _stkt0F _stkt10 _stkt11 _stkt12 _stkt13 _stkt14 _stkt15 _stkt16 _stkt17 _stkt18 _stkt19 _stkt1A _stkt1B _stkt1C _stkt1D _stkt1E _stkt1F  : TVMBit . 
Definition StakingContract_ι__addRequest_А_stakeAt_bs_def := [> _stkt00 , _stkt01 , _stkt02 , _stkt03 , _stkt04 , _stkt05 , _stkt06 , _stkt07 , _stkt08 , _stkt09 , _stkt0A , _stkt0B , _stkt0C , _stkt0D , _stkt0E , _stkt0F , _stkt10 , _stkt11 , _stkt12 , _stkt13 , _stkt14 , _stkt15 , _stkt16 , _stkt17 , _stkt18 , _stkt19 , _stkt1A , _stkt1B , _stkt1C , _stkt1D , _stkt1E , _stkt1F <] .
Lemma StakingContract_ι__addRequest_А_stakeAt_bs_id: StakingContract_ι__addRequest_А_stakeAt_bs_def = [> _stkt00 , _stkt01 , _stkt02 , _stkt03 , _stkt04 , _stkt05 , _stkt06 , _stkt07 , _stkt08 , _stkt09 , _stkt0A , _stkt0B , _stkt0C , _stkt0D , _stkt0E , _stkt0F , _stkt10 , _stkt11 , _stkt12 , _stkt13 , _stkt14 , _stkt15 , _stkt16 , _stkt17 , _stkt18 , _stkt19 , _stkt1A , _stkt1B , _stkt1C , _stkt1D , _stkt1E , _stkt1F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι__addRequest_А_stakeAt_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι__addRequest_А_stakeAt_bs_def) StakingContract_ι__addRequest_А_stakeAt = StakingContract_ι__addRequest_А_stakeAt_bs_def.
Lemma StakingContract_ι__addRequest_А_stakeAt_bs : Z2IBS_pos 32 StakingContract_ι__addRequest_А_stakeAt = StakingContract_ι__addRequest_А_stakeAt_bs_def.
Proof.
 rewrite <- StakingContract_ι__addRequest_А_stakeAt_bs'. auto. Qed.
Axiom StakingContract_ι__addRequest_А_stakeAt_pos: (0 <= StakingContract_ι__addRequest_А_stakeAt )%Z.
Axiom StakingContract_ι__addRequest_А_stakeAt_fits: zFitN_pos (tvmBitStringLen StakingContract_ι__addRequest_А_stakeAt_bs_def) StakingContract_ι__addRequest_А_stakeAt = true.
Lemma StakingContract_ι__addRequest_А_stakeAt_bs_rev : I2ZBS_pos' StakingContract_ι__addRequest_А_stakeAt_bs_def = StakingContract_ι__addRequest_А_stakeAt .
Proof.
  prove_bs_rev StakingContract_ι__addRequest_А_stakeAt_bs StakingContract_ι__addRequest_А_stakeAt_pos StakingContract_ι__addRequest_А_stakeAt_fits. 
Qed.
Lemma StakingContract_ι__addRequest_А_stakeAt_bs257 : Z2IN 257 StakingContract_ι__addRequest_А_stakeAt = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι__addRequest_А_stakeAt_bs_def)) StakingContract_ι__addRequest_А_stakeAt_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι__addRequest_А_stakeAt_bs_rev StakingContract_ι__addRequest_А_stakeAt_bs_def.
Qed. 

Variables StakingContract_ι__acceptPendingRoundStake_А_pendingId : Z . 
Variables (*! { _pndn !*) _pndn00 _pndn01 _pndn02 _pndn03 _pndn04 _pndn05 _pndn06 _pndn07 _pndn08 _pndn09 _pndn0A _pndn0B _pndn0C _pndn0D _pndn0E _pndn0F _pndn10 _pndn11 _pndn12 _pndn13 _pndn14 _pndn15 _pndn16 _pndn17 _pndn18 _pndn19 _pndn1A _pndn1B _pndn1C _pndn1D _pndn1E _pndn1F  : TVMBit . 
Definition StakingContract_ι__acceptPendingRoundStake_А_pendingId_bs_def := [> _pndn00 , _pndn01 , _pndn02 , _pndn03 , _pndn04 , _pndn05 , _pndn06 , _pndn07 , _pndn08 , _pndn09 , _pndn0A , _pndn0B , _pndn0C , _pndn0D , _pndn0E , _pndn0F , _pndn10 , _pndn11 , _pndn12 , _pndn13 , _pndn14 , _pndn15 , _pndn16 , _pndn17 , _pndn18 , _pndn19 , _pndn1A , _pndn1B , _pndn1C , _pndn1D , _pndn1E , _pndn1F <] .
Lemma StakingContract_ι__acceptPendingRoundStake_А_pendingId_bs_id: StakingContract_ι__acceptPendingRoundStake_А_pendingId_bs_def = [> _pndn00 , _pndn01 , _pndn02 , _pndn03 , _pndn04 , _pndn05 , _pndn06 , _pndn07 , _pndn08 , _pndn09 , _pndn0A , _pndn0B , _pndn0C , _pndn0D , _pndn0E , _pndn0F , _pndn10 , _pndn11 , _pndn12 , _pndn13 , _pndn14 , _pndn15 , _pndn16 , _pndn17 , _pndn18 , _pndn19 , _pndn1A , _pndn1B , _pndn1C , _pndn1D , _pndn1E , _pndn1F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι__acceptPendingRoundStake_А_pendingId_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι__acceptPendingRoundStake_А_pendingId_bs_def) StakingContract_ι__acceptPendingRoundStake_А_pendingId = StakingContract_ι__acceptPendingRoundStake_А_pendingId_bs_def.
Lemma StakingContract_ι__acceptPendingRoundStake_А_pendingId_bs : Z2IBS_pos 32 StakingContract_ι__acceptPendingRoundStake_А_pendingId = StakingContract_ι__acceptPendingRoundStake_А_pendingId_bs_def.
Proof.
 rewrite <- StakingContract_ι__acceptPendingRoundStake_А_pendingId_bs'. auto. Qed.
Axiom StakingContract_ι__acceptPendingRoundStake_А_pendingId_pos: (0 <= StakingContract_ι__acceptPendingRoundStake_А_pendingId )%Z.
Axiom StakingContract_ι__acceptPendingRoundStake_А_pendingId_fits: zFitN_pos (tvmBitStringLen StakingContract_ι__acceptPendingRoundStake_А_pendingId_bs_def) StakingContract_ι__acceptPendingRoundStake_А_pendingId = true.
Lemma StakingContract_ι__acceptPendingRoundStake_А_pendingId_bs_rev : I2ZBS_pos' StakingContract_ι__acceptPendingRoundStake_А_pendingId_bs_def = StakingContract_ι__acceptPendingRoundStake_А_pendingId .
Proof.
  prove_bs_rev StakingContract_ι__acceptPendingRoundStake_А_pendingId_bs StakingContract_ι__acceptPendingRoundStake_А_pendingId_pos StakingContract_ι__acceptPendingRoundStake_А_pendingId_fits. 
Qed.
Lemma StakingContract_ι__acceptPendingRoundStake_А_pendingId_bs257 : Z2IN 257 StakingContract_ι__acceptPendingRoundStake_А_pendingId = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι__acceptPendingRoundStake_А_pendingId_bs_def)) StakingContract_ι__acceptPendingRoundStake_А_pendingId_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι__acceptPendingRoundStake_А_pendingId_bs_rev StakingContract_ι__acceptPendingRoundStake_А_pendingId_bs_def.
Qed.
 
 
Variables StakingContract_ι__completeRound2_А_completionStatus : Z . 
Variables (*! { _cmpl !*) _cmpl00 _cmpl01 _cmpl02 _cmpl03 _cmpl04 _cmpl05 _cmpl06 _cmpl07  : TVMBit . 
Definition StakingContract_ι__completeRound2_А_completionStatus_bs_def := [> _cmpl00 , _cmpl01 , _cmpl02 , _cmpl03 , _cmpl04 , _cmpl05 , _cmpl06 , _cmpl07 <] .
Lemma StakingContract_ι__completeRound2_А_completionStatus_bs_id: StakingContract_ι__completeRound2_А_completionStatus_bs_def = [> _cmpl00 , _cmpl01 , _cmpl02 , _cmpl03 , _cmpl04 , _cmpl05 , _cmpl06 , _cmpl07 (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι__completeRound2_А_completionStatus_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι__completeRound2_А_completionStatus_bs_def) StakingContract_ι__completeRound2_А_completionStatus = StakingContract_ι__completeRound2_А_completionStatus_bs_def.
Lemma StakingContract_ι__completeRound2_А_completionStatus_bs : Z2IBS_pos 8 StakingContract_ι__completeRound2_А_completionStatus = StakingContract_ι__completeRound2_А_completionStatus_bs_def.
Proof.
 rewrite <- StakingContract_ι__completeRound2_А_completionStatus_bs'. auto. Qed.
Axiom StakingContract_ι__completeRound2_А_completionStatus_pos: (0 <= StakingContract_ι__completeRound2_А_completionStatus )%Z.
Axiom StakingContract_ι__completeRound2_А_completionStatus_fits: zFitN_pos (tvmBitStringLen StakingContract_ι__completeRound2_А_completionStatus_bs_def) StakingContract_ι__completeRound2_А_completionStatus = true.
Lemma StakingContract_ι__completeRound2_А_completionStatus_bs_rev : I2ZBS_pos' StakingContract_ι__completeRound2_А_completionStatus_bs_def = StakingContract_ι__completeRound2_А_completionStatus .
Proof.
  prove_bs_rev StakingContract_ι__completeRound2_А_completionStatus_bs StakingContract_ι__completeRound2_А_completionStatus_pos StakingContract_ι__completeRound2_А_completionStatus_fits. 
Qed.
Lemma StakingContract_ι__completeRound2_А_completionStatus_bs257 : Z2IN 257 StakingContract_ι__completeRound2_А_completionStatus = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι__completeRound2_А_completionStatus_bs_def)) StakingContract_ι__completeRound2_А_completionStatus_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι__completeRound2_А_completionStatus_bs_rev StakingContract_ι__completeRound2_А_completionStatus_bs_def.
Qed.

Variables StakingContract_ι__recalcStakeAndFees_А_stake : Z . 
Variables (*! { _stk !*) _stk00 _stk01 _stk02 _stk03 _stk04 _stk05 _stk06 _stk07 _stk08 _stk09 _stk0A _stk0B _stk0C _stk0D _stk0E _stk0F _stk10 _stk11 _stk12 _stk13 _stk14 _stk15 _stk16 _stk17 _stk18 _stk19 _stk1A _stk1B _stk1C _stk1D _stk1E _stk1F _stk20 _stk21 _stk22 _stk23 _stk24 _stk25 _stk26 _stk27 _stk28 _stk29 _stk2A _stk2B _stk2C _stk2D _stk2E _stk2F _stk30 _stk31 _stk32 _stk33 _stk34 _stk35 _stk36 _stk37 _stk38 _stk39 _stk3A _stk3B _stk3C _stk3D _stk3E _stk3F  : TVMBit . 
Definition StakingContract_ι__recalcStakeAndFees_А_stake_bs_def := [> _stk00 , _stk01 , _stk02 , _stk03 , _stk04 , _stk05 , _stk06 , _stk07 , _stk08 , _stk09 , _stk0A , _stk0B , _stk0C , _stk0D , _stk0E , _stk0F , _stk10 , _stk11 , _stk12 , _stk13 , _stk14 , _stk15 , _stk16 , _stk17 , _stk18 , _stk19 , _stk1A , _stk1B , _stk1C , _stk1D , _stk1E , _stk1F , _stk20 , _stk21 , _stk22 , _stk23 , _stk24 , _stk25 , _stk26 , _stk27 , _stk28 , _stk29 , _stk2A , _stk2B , _stk2C , _stk2D , _stk2E , _stk2F , _stk30 , _stk31 , _stk32 , _stk33 , _stk34 , _stk35 , _stk36 , _stk37 , _stk38 , _stk39 , _stk3A , _stk3B , _stk3C , _stk3D , _stk3E , _stk3F <] .
Lemma StakingContract_ι__recalcStakeAndFees_А_stake_bs_id: StakingContract_ι__recalcStakeAndFees_А_stake_bs_def = [> _stk00 , _stk01 , _stk02 , _stk03 , _stk04 , _stk05 , _stk06 , _stk07 , _stk08 , _stk09 , _stk0A , _stk0B , _stk0C , _stk0D , _stk0E , _stk0F , _stk10 , _stk11 , _stk12 , _stk13 , _stk14 , _stk15 , _stk16 , _stk17 , _stk18 , _stk19 , _stk1A , _stk1B , _stk1C , _stk1D , _stk1E , _stk1F , _stk20 , _stk21 , _stk22 , _stk23 , _stk24 , _stk25 , _stk26 , _stk27 , _stk28 , _stk29 , _stk2A , _stk2B , _stk2C , _stk2D , _stk2E , _stk2F , _stk30 , _stk31 , _stk32 , _stk33 , _stk34 , _stk35 , _stk36 , _stk37 , _stk38 , _stk39 , _stk3A , _stk3B , _stk3C , _stk3D , _stk3E , _stk3F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι__recalcStakeAndFees_А_stake_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι__recalcStakeAndFees_А_stake_bs_def) StakingContract_ι__recalcStakeAndFees_А_stake = StakingContract_ι__recalcStakeAndFees_А_stake_bs_def.
Lemma StakingContract_ι__recalcStakeAndFees_А_stake_bs : Z2IBS_pos 64 StakingContract_ι__recalcStakeAndFees_А_stake = StakingContract_ι__recalcStakeAndFees_А_stake_bs_def.
Proof.
 rewrite <- StakingContract_ι__recalcStakeAndFees_А_stake_bs'. auto. Qed.
Axiom StakingContract_ι__recalcStakeAndFees_А_stake_pos: (0 <= StakingContract_ι__recalcStakeAndFees_А_stake )%Z.
Axiom StakingContract_ι__recalcStakeAndFees_А_stake_fits: zFitN_pos (tvmBitStringLen StakingContract_ι__recalcStakeAndFees_А_stake_bs_def) StakingContract_ι__recalcStakeAndFees_А_stake = true.
Lemma StakingContract_ι__recalcStakeAndFees_А_stake_bs_rev : I2ZBS_pos' StakingContract_ι__recalcStakeAndFees_А_stake_bs_def = StakingContract_ι__recalcStakeAndFees_А_stake .
Proof.
  prove_bs_rev StakingContract_ι__recalcStakeAndFees_А_stake_bs StakingContract_ι__recalcStakeAndFees_А_stake_pos StakingContract_ι__recalcStakeAndFees_А_stake_fits. 
Qed.
Lemma StakingContract_ι__recalcStakeAndFees_А_stake_bs257 : Z2IN 257 StakingContract_ι__recalcStakeAndFees_А_stake = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι__recalcStakeAndFees_А_stake_bs_def)) StakingContract_ι__recalcStakeAndFees_А_stake_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι__recalcStakeAndFees_А_stake_bs_rev StakingContract_ι__recalcStakeAndFees_А_stake_bs_def.
Qed. 
Variables StakingContract_ι__recalcStakeAndFees_А_reward : Z . 
Variables (*! { _rwrd !*) _rwrd00 _rwrd01 _rwrd02 _rwrd03 _rwrd04 _rwrd05 _rwrd06 _rwrd07 _rwrd08 _rwrd09 _rwrd0A _rwrd0B _rwrd0C _rwrd0D _rwrd0E _rwrd0F _rwrd10 _rwrd11 _rwrd12 _rwrd13 _rwrd14 _rwrd15 _rwrd16 _rwrd17 _rwrd18 _rwrd19 _rwrd1A _rwrd1B _rwrd1C _rwrd1D _rwrd1E _rwrd1F _rwrd20 _rwrd21 _rwrd22 _rwrd23 _rwrd24 _rwrd25 _rwrd26 _rwrd27 _rwrd28 _rwrd29 _rwrd2A _rwrd2B _rwrd2C _rwrd2D _rwrd2E _rwrd2F _rwrd30 _rwrd31 _rwrd32 _rwrd33 _rwrd34 _rwrd35 _rwrd36 _rwrd37 _rwrd38 _rwrd39 _rwrd3A _rwrd3B _rwrd3C _rwrd3D _rwrd3E _rwrd3F  : TVMBit . 
Definition StakingContract_ι__recalcStakeAndFees_А_reward_bs_def := [> _rwrd00 , _rwrd01 , _rwrd02 , _rwrd03 , _rwrd04 , _rwrd05 , _rwrd06 , _rwrd07 , _rwrd08 , _rwrd09 , _rwrd0A , _rwrd0B , _rwrd0C , _rwrd0D , _rwrd0E , _rwrd0F , _rwrd10 , _rwrd11 , _rwrd12 , _rwrd13 , _rwrd14 , _rwrd15 , _rwrd16 , _rwrd17 , _rwrd18 , _rwrd19 , _rwrd1A , _rwrd1B , _rwrd1C , _rwrd1D , _rwrd1E , _rwrd1F , _rwrd20 , _rwrd21 , _rwrd22 , _rwrd23 , _rwrd24 , _rwrd25 , _rwrd26 , _rwrd27 , _rwrd28 , _rwrd29 , _rwrd2A , _rwrd2B , _rwrd2C , _rwrd2D , _rwrd2E , _rwrd2F , _rwrd30 , _rwrd31 , _rwrd32 , _rwrd33 , _rwrd34 , _rwrd35 , _rwrd36 , _rwrd37 , _rwrd38 , _rwrd39 , _rwrd3A , _rwrd3B , _rwrd3C , _rwrd3D , _rwrd3E , _rwrd3F <] .
Lemma StakingContract_ι__recalcStakeAndFees_А_reward_bs_id: StakingContract_ι__recalcStakeAndFees_А_reward_bs_def = [> _rwrd00 , _rwrd01 , _rwrd02 , _rwrd03 , _rwrd04 , _rwrd05 , _rwrd06 , _rwrd07 , _rwrd08 , _rwrd09 , _rwrd0A , _rwrd0B , _rwrd0C , _rwrd0D , _rwrd0E , _rwrd0F , _rwrd10 , _rwrd11 , _rwrd12 , _rwrd13 , _rwrd14 , _rwrd15 , _rwrd16 , _rwrd17 , _rwrd18 , _rwrd19 , _rwrd1A , _rwrd1B , _rwrd1C , _rwrd1D , _rwrd1E , _rwrd1F , _rwrd20 , _rwrd21 , _rwrd22 , _rwrd23 , _rwrd24 , _rwrd25 , _rwrd26 , _rwrd27 , _rwrd28 , _rwrd29 , _rwrd2A , _rwrd2B , _rwrd2C , _rwrd2D , _rwrd2E , _rwrd2F , _rwrd30 , _rwrd31 , _rwrd32 , _rwrd33 , _rwrd34 , _rwrd35 , _rwrd36 , _rwrd37 , _rwrd38 , _rwrd39 , _rwrd3A , _rwrd3B , _rwrd3C , _rwrd3D , _rwrd3E , _rwrd3F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι__recalcStakeAndFees_А_reward_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι__recalcStakeAndFees_А_reward_bs_def) StakingContract_ι__recalcStakeAndFees_А_reward = StakingContract_ι__recalcStakeAndFees_А_reward_bs_def.
Lemma StakingContract_ι__recalcStakeAndFees_А_reward_bs : Z2IBS_pos 64 StakingContract_ι__recalcStakeAndFees_А_reward = StakingContract_ι__recalcStakeAndFees_А_reward_bs_def.
Proof.
 rewrite <- StakingContract_ι__recalcStakeAndFees_А_reward_bs'. auto. Qed.
Axiom StakingContract_ι__recalcStakeAndFees_А_reward_pos: (0 <= StakingContract_ι__recalcStakeAndFees_А_reward )%Z.
Axiom StakingContract_ι__recalcStakeAndFees_А_reward_fits: zFitN_pos (tvmBitStringLen StakingContract_ι__recalcStakeAndFees_А_reward_bs_def) StakingContract_ι__recalcStakeAndFees_А_reward = true.
Lemma StakingContract_ι__recalcStakeAndFees_А_reward_bs_rev : I2ZBS_pos' StakingContract_ι__recalcStakeAndFees_А_reward_bs_def = StakingContract_ι__recalcStakeAndFees_А_reward .
Proof.
  prove_bs_rev StakingContract_ι__recalcStakeAndFees_А_reward_bs StakingContract_ι__recalcStakeAndFees_А_reward_pos StakingContract_ι__recalcStakeAndFees_А_reward_fits. 
Qed.
Lemma StakingContract_ι__recalcStakeAndFees_А_reward_bs257 : Z2IN 257 StakingContract_ι__recalcStakeAndFees_А_reward = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι__recalcStakeAndFees_А_reward_bs_def)) StakingContract_ι__recalcStakeAndFees_А_reward_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι__recalcStakeAndFees_А_reward_bs_rev StakingContract_ι__recalcStakeAndFees_А_reward_bs_def.
Qed. 
Variables StakingContract_ι__recalcStakeAndFees_А_roundStake : Z . 
Variables (*! { _rndS !*) _rndS00 _rndS01 _rndS02 _rndS03 _rndS04 _rndS05 _rndS06 _rndS07 _rndS08 _rndS09 _rndS0A _rndS0B _rndS0C _rndS0D _rndS0E _rndS0F _rndS10 _rndS11 _rndS12 _rndS13 _rndS14 _rndS15 _rndS16 _rndS17 _rndS18 _rndS19 _rndS1A _rndS1B _rndS1C _rndS1D _rndS1E _rndS1F _rndS20 _rndS21 _rndS22 _rndS23 _rndS24 _rndS25 _rndS26 _rndS27 _rndS28 _rndS29 _rndS2A _rndS2B _rndS2C _rndS2D _rndS2E _rndS2F _rndS30 _rndS31 _rndS32 _rndS33 _rndS34 _rndS35 _rndS36 _rndS37 _rndS38 _rndS39 _rndS3A _rndS3B _rndS3C _rndS3D _rndS3E _rndS3F  : TVMBit . 
Definition StakingContract_ι__recalcStakeAndFees_А_roundStake_bs_def := [> _rndS00 , _rndS01 , _rndS02 , _rndS03 , _rndS04 , _rndS05 , _rndS06 , _rndS07 , _rndS08 , _rndS09 , _rndS0A , _rndS0B , _rndS0C , _rndS0D , _rndS0E , _rndS0F , _rndS10 , _rndS11 , _rndS12 , _rndS13 , _rndS14 , _rndS15 , _rndS16 , _rndS17 , _rndS18 , _rndS19 , _rndS1A , _rndS1B , _rndS1C , _rndS1D , _rndS1E , _rndS1F , _rndS20 , _rndS21 , _rndS22 , _rndS23 , _rndS24 , _rndS25 , _rndS26 , _rndS27 , _rndS28 , _rndS29 , _rndS2A , _rndS2B , _rndS2C , _rndS2D , _rndS2E , _rndS2F , _rndS30 , _rndS31 , _rndS32 , _rndS33 , _rndS34 , _rndS35 , _rndS36 , _rndS37 , _rndS38 , _rndS39 , _rndS3A , _rndS3B , _rndS3C , _rndS3D , _rndS3E , _rndS3F <] .
Lemma StakingContract_ι__recalcStakeAndFees_А_roundStake_bs_id: StakingContract_ι__recalcStakeAndFees_А_roundStake_bs_def = [> _rndS00 , _rndS01 , _rndS02 , _rndS03 , _rndS04 , _rndS05 , _rndS06 , _rndS07 , _rndS08 , _rndS09 , _rndS0A , _rndS0B , _rndS0C , _rndS0D , _rndS0E , _rndS0F , _rndS10 , _rndS11 , _rndS12 , _rndS13 , _rndS14 , _rndS15 , _rndS16 , _rndS17 , _rndS18 , _rndS19 , _rndS1A , _rndS1B , _rndS1C , _rndS1D , _rndS1E , _rndS1F , _rndS20 , _rndS21 , _rndS22 , _rndS23 , _rndS24 , _rndS25 , _rndS26 , _rndS27 , _rndS28 , _rndS29 , _rndS2A , _rndS2B , _rndS2C , _rndS2D , _rndS2E , _rndS2F , _rndS30 , _rndS31 , _rndS32 , _rndS33 , _rndS34 , _rndS35 , _rndS36 , _rndS37 , _rndS38 , _rndS39 , _rndS3A , _rndS3B , _rndS3C , _rndS3D , _rndS3E , _rndS3F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι__recalcStakeAndFees_А_roundStake_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι__recalcStakeAndFees_А_roundStake_bs_def) StakingContract_ι__recalcStakeAndFees_А_roundStake = StakingContract_ι__recalcStakeAndFees_А_roundStake_bs_def.
Lemma StakingContract_ι__recalcStakeAndFees_А_roundStake_bs : Z2IBS_pos 64 StakingContract_ι__recalcStakeAndFees_А_roundStake = StakingContract_ι__recalcStakeAndFees_А_roundStake_bs_def.
Proof.
 rewrite <- StakingContract_ι__recalcStakeAndFees_А_roundStake_bs'. auto. Qed.
Axiom StakingContract_ι__recalcStakeAndFees_А_roundStake_pos: (0 <= StakingContract_ι__recalcStakeAndFees_А_roundStake )%Z.
Axiom StakingContract_ι__recalcStakeAndFees_А_roundStake_fits: zFitN_pos (tvmBitStringLen StakingContract_ι__recalcStakeAndFees_А_roundStake_bs_def) StakingContract_ι__recalcStakeAndFees_А_roundStake = true.
Lemma StakingContract_ι__recalcStakeAndFees_А_roundStake_bs_rev : I2ZBS_pos' StakingContract_ι__recalcStakeAndFees_А_roundStake_bs_def = StakingContract_ι__recalcStakeAndFees_А_roundStake .
Proof.
  prove_bs_rev StakingContract_ι__recalcStakeAndFees_А_roundStake_bs StakingContract_ι__recalcStakeAndFees_А_roundStake_pos StakingContract_ι__recalcStakeAndFees_А_roundStake_fits. 
Qed.
Lemma StakingContract_ι__recalcStakeAndFees_А_roundStake_bs257 : Z2IN 257 StakingContract_ι__recalcStakeAndFees_А_roundStake = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι__recalcStakeAndFees_А_roundStake_bs_def)) StakingContract_ι__recalcStakeAndFees_А_roundStake_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι__recalcStakeAndFees_А_roundStake_bs_rev StakingContract_ι__recalcStakeAndFees_А_roundStake_bs_def.
Qed. 
Variables StakingContract_ι__recalcStakeAndFees_А_roundRewards : Z . 
Variables (*! { _rndR !*) _rndR00 _rndR01 _rndR02 _rndR03 _rndR04 _rndR05 _rndR06 _rndR07 _rndR08 _rndR09 _rndR0A _rndR0B _rndR0C _rndR0D _rndR0E _rndR0F _rndR10 _rndR11 _rndR12 _rndR13 _rndR14 _rndR15 _rndR16 _rndR17 _rndR18 _rndR19 _rndR1A _rndR1B _rndR1C _rndR1D _rndR1E _rndR1F _rndR20 _rndR21 _rndR22 _rndR23 _rndR24 _rndR25 _rndR26 _rndR27 _rndR28 _rndR29 _rndR2A _rndR2B _rndR2C _rndR2D _rndR2E _rndR2F _rndR30 _rndR31 _rndR32 _rndR33 _rndR34 _rndR35 _rndR36 _rndR37 _rndR38 _rndR39 _rndR3A _rndR3B _rndR3C _rndR3D _rndR3E _rndR3F  : TVMBit . 
Definition StakingContract_ι__recalcStakeAndFees_А_roundRewards_bs_def := [> _rndR00 , _rndR01 , _rndR02 , _rndR03 , _rndR04 , _rndR05 , _rndR06 , _rndR07 , _rndR08 , _rndR09 , _rndR0A , _rndR0B , _rndR0C , _rndR0D , _rndR0E , _rndR0F , _rndR10 , _rndR11 , _rndR12 , _rndR13 , _rndR14 , _rndR15 , _rndR16 , _rndR17 , _rndR18 , _rndR19 , _rndR1A , _rndR1B , _rndR1C , _rndR1D , _rndR1E , _rndR1F , _rndR20 , _rndR21 , _rndR22 , _rndR23 , _rndR24 , _rndR25 , _rndR26 , _rndR27 , _rndR28 , _rndR29 , _rndR2A , _rndR2B , _rndR2C , _rndR2D , _rndR2E , _rndR2F , _rndR30 , _rndR31 , _rndR32 , _rndR33 , _rndR34 , _rndR35 , _rndR36 , _rndR37 , _rndR38 , _rndR39 , _rndR3A , _rndR3B , _rndR3C , _rndR3D , _rndR3E , _rndR3F <] .
Lemma StakingContract_ι__recalcStakeAndFees_А_roundRewards_bs_id: StakingContract_ι__recalcStakeAndFees_А_roundRewards_bs_def = [> _rndR00 , _rndR01 , _rndR02 , _rndR03 , _rndR04 , _rndR05 , _rndR06 , _rndR07 , _rndR08 , _rndR09 , _rndR0A , _rndR0B , _rndR0C , _rndR0D , _rndR0E , _rndR0F , _rndR10 , _rndR11 , _rndR12 , _rndR13 , _rndR14 , _rndR15 , _rndR16 , _rndR17 , _rndR18 , _rndR19 , _rndR1A , _rndR1B , _rndR1C , _rndR1D , _rndR1E , _rndR1F , _rndR20 , _rndR21 , _rndR22 , _rndR23 , _rndR24 , _rndR25 , _rndR26 , _rndR27 , _rndR28 , _rndR29 , _rndR2A , _rndR2B , _rndR2C , _rndR2D , _rndR2E , _rndR2F , _rndR30 , _rndR31 , _rndR32 , _rndR33 , _rndR34 , _rndR35 , _rndR36 , _rndR37 , _rndR38 , _rndR39 , _rndR3A , _rndR3B , _rndR3C , _rndR3D , _rndR3E , _rndR3F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι__recalcStakeAndFees_А_roundRewards_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι__recalcStakeAndFees_А_roundRewards_bs_def) StakingContract_ι__recalcStakeAndFees_А_roundRewards = StakingContract_ι__recalcStakeAndFees_А_roundRewards_bs_def.
Lemma StakingContract_ι__recalcStakeAndFees_А_roundRewards_bs : Z2IBS_pos 64 StakingContract_ι__recalcStakeAndFees_А_roundRewards = StakingContract_ι__recalcStakeAndFees_А_roundRewards_bs_def.
Proof.
 rewrite <- StakingContract_ι__recalcStakeAndFees_А_roundRewards_bs'. auto. Qed.
Axiom StakingContract_ι__recalcStakeAndFees_А_roundRewards_pos: (0 <= StakingContract_ι__recalcStakeAndFees_А_roundRewards )%Z.
Axiom StakingContract_ι__recalcStakeAndFees_А_roundRewards_fits: zFitN_pos (tvmBitStringLen StakingContract_ι__recalcStakeAndFees_А_roundRewards_bs_def) StakingContract_ι__recalcStakeAndFees_А_roundRewards = true.
Lemma StakingContract_ι__recalcStakeAndFees_А_roundRewards_bs_rev : I2ZBS_pos' StakingContract_ι__recalcStakeAndFees_А_roundRewards_bs_def = StakingContract_ι__recalcStakeAndFees_А_roundRewards .
Proof.
  prove_bs_rev StakingContract_ι__recalcStakeAndFees_А_roundRewards_bs StakingContract_ι__recalcStakeAndFees_А_roundRewards_pos StakingContract_ι__recalcStakeAndFees_А_roundRewards_fits. 
Qed.
Lemma StakingContract_ι__recalcStakeAndFees_А_roundRewards_bs257 : Z2IN 257 StakingContract_ι__recalcStakeAndFees_А_roundRewards = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι__recalcStakeAndFees_А_roundRewards_bs_def)) StakingContract_ι__recalcStakeAndFees_А_roundRewards_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι__recalcStakeAndFees_А_roundRewards_bs_rev StakingContract_ι__recalcStakeAndFees_А_roundRewards_bs_def.
Qed.
   
Variables StakingContract_ι__returnOrReinvest2_А_stake : Z . 
Variables (*! { _stk !*) _stk00 _stk01 _stk02 _stk03 _stk04 _stk05 _stk06 _stk07 _stk08 _stk09 _stk0A _stk0B _stk0C _stk0D _stk0E _stk0F _stk10 _stk11 _stk12 _stk13 _stk14 _stk15 _stk16 _stk17 _stk18 _stk19 _stk1A _stk1B _stk1C _stk1D _stk1E _stk1F _stk20 _stk21 _stk22 _stk23 _stk24 _stk25 _stk26 _stk27 _stk28 _stk29 _stk2A _stk2B _stk2C _stk2D _stk2E _stk2F _stk30 _stk31 _stk32 _stk33 _stk34 _stk35 _stk36 _stk37 _stk38 _stk39 _stk3A _stk3B _stk3C _stk3D _stk3E _stk3F  : TVMBit . 
Definition StakingContract_ι__returnOrReinvest2_А_stake_bs_def := [> _stk00 , _stk01 , _stk02 , _stk03 , _stk04 , _stk05 , _stk06 , _stk07 , _stk08 , _stk09 , _stk0A , _stk0B , _stk0C , _stk0D , _stk0E , _stk0F , _stk10 , _stk11 , _stk12 , _stk13 , _stk14 , _stk15 , _stk16 , _stk17 , _stk18 , _stk19 , _stk1A , _stk1B , _stk1C , _stk1D , _stk1E , _stk1F , _stk20 , _stk21 , _stk22 , _stk23 , _stk24 , _stk25 , _stk26 , _stk27 , _stk28 , _stk29 , _stk2A , _stk2B , _stk2C , _stk2D , _stk2E , _stk2F , _stk30 , _stk31 , _stk32 , _stk33 , _stk34 , _stk35 , _stk36 , _stk37 , _stk38 , _stk39 , _stk3A , _stk3B , _stk3C , _stk3D , _stk3E , _stk3F <] .
Lemma StakingContract_ι__returnOrReinvest2_А_stake_bs_id: StakingContract_ι__returnOrReinvest2_А_stake_bs_def = [> _stk00 , _stk01 , _stk02 , _stk03 , _stk04 , _stk05 , _stk06 , _stk07 , _stk08 , _stk09 , _stk0A , _stk0B , _stk0C , _stk0D , _stk0E , _stk0F , _stk10 , _stk11 , _stk12 , _stk13 , _stk14 , _stk15 , _stk16 , _stk17 , _stk18 , _stk19 , _stk1A , _stk1B , _stk1C , _stk1D , _stk1E , _stk1F , _stk20 , _stk21 , _stk22 , _stk23 , _stk24 , _stk25 , _stk26 , _stk27 , _stk28 , _stk29 , _stk2A , _stk2B , _stk2C , _stk2D , _stk2E , _stk2F , _stk30 , _stk31 , _stk32 , _stk33 , _stk34 , _stk35 , _stk36 , _stk37 , _stk38 , _stk39 , _stk3A , _stk3B , _stk3C , _stk3D , _stk3E , _stk3F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι__returnOrReinvest2_А_stake_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι__returnOrReinvest2_А_stake_bs_def) StakingContract_ι__returnOrReinvest2_А_stake = StakingContract_ι__returnOrReinvest2_А_stake_bs_def.
Lemma StakingContract_ι__returnOrReinvest2_А_stake_bs : Z2IBS_pos 64 StakingContract_ι__returnOrReinvest2_А_stake = StakingContract_ι__returnOrReinvest2_А_stake_bs_def.
Proof.
 rewrite <- StakingContract_ι__returnOrReinvest2_А_stake_bs'. auto. Qed.
Axiom StakingContract_ι__returnOrReinvest2_А_stake_pos: (0 <= StakingContract_ι__returnOrReinvest2_А_stake )%Z.
Axiom StakingContract_ι__returnOrReinvest2_А_stake_fits: zFitN_pos (tvmBitStringLen StakingContract_ι__returnOrReinvest2_А_stake_bs_def) StakingContract_ι__returnOrReinvest2_А_stake = true.
Lemma StakingContract_ι__returnOrReinvest2_А_stake_bs_rev : I2ZBS_pos' StakingContract_ι__returnOrReinvest2_А_stake_bs_def = StakingContract_ι__returnOrReinvest2_А_stake .
Proof.
  prove_bs_rev StakingContract_ι__returnOrReinvest2_А_stake_bs StakingContract_ι__returnOrReinvest2_А_stake_pos StakingContract_ι__returnOrReinvest2_А_stake_fits. 
Qed.
Lemma StakingContract_ι__returnOrReinvest2_А_stake_bs257 : Z2IN 257 StakingContract_ι__returnOrReinvest2_А_stake = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι__returnOrReinvest2_А_stake_bs_def)) StakingContract_ι__returnOrReinvest2_А_stake_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι__returnOrReinvest2_А_stake_bs_rev StakingContract_ι__returnOrReinvest2_А_stake_bs_def.
Qed.



Variables StakingContract_ι_removeStake_А_stake : Z . 
Variables (*! { _stk !*) _stk00 _stk01 _stk02 _stk03 _stk04 _stk05 _stk06 _stk07 _stk08 _stk09 _stk0A _stk0B _stk0C _stk0D _stk0E _stk0F _stk10 _stk11 _stk12 _stk13 _stk14 _stk15 _stk16 _stk17 _stk18 _stk19 _stk1A _stk1B _stk1C _stk1D _stk1E _stk1F _stk20 _stk21 _stk22 _stk23 _stk24 _stk25 _stk26 _stk27 _stk28 _stk29 _stk2A _stk2B _stk2C _stk2D _stk2E _stk2F _stk30 _stk31 _stk32 _stk33 _stk34 _stk35 _stk36 _stk37 _stk38 _stk39 _stk3A _stk3B _stk3C _stk3D _stk3E _stk3F  : TVMBit . 
Definition StakingContract_ι_removeStake_А_stake_bs_def := [> _stk00 , _stk01 , _stk02 , _stk03 , _stk04 , _stk05 , _stk06 , _stk07 , _stk08 , _stk09 , _stk0A , _stk0B , _stk0C , _stk0D , _stk0E , _stk0F , _stk10 , _stk11 , _stk12 , _stk13 , _stk14 , _stk15 , _stk16 , _stk17 , _stk18 , _stk19 , _stk1A , _stk1B , _stk1C , _stk1D , _stk1E , _stk1F , _stk20 , _stk21 , _stk22 , _stk23 , _stk24 , _stk25 , _stk26 , _stk27 , _stk28 , _stk29 , _stk2A , _stk2B , _stk2C , _stk2D , _stk2E , _stk2F , _stk30 , _stk31 , _stk32 , _stk33 , _stk34 , _stk35 , _stk36 , _stk37 , _stk38 , _stk39 , _stk3A , _stk3B , _stk3C , _stk3D , _stk3E , _stk3F <] .
Lemma StakingContract_ι_removeStake_А_stake_bs_id: StakingContract_ι_removeStake_А_stake_bs_def = [> _stk00 , _stk01 , _stk02 , _stk03 , _stk04 , _stk05 , _stk06 , _stk07 , _stk08 , _stk09 , _stk0A , _stk0B , _stk0C , _stk0D , _stk0E , _stk0F , _stk10 , _stk11 , _stk12 , _stk13 , _stk14 , _stk15 , _stk16 , _stk17 , _stk18 , _stk19 , _stk1A , _stk1B , _stk1C , _stk1D , _stk1E , _stk1F , _stk20 , _stk21 , _stk22 , _stk23 , _stk24 , _stk25 , _stk26 , _stk27 , _stk28 , _stk29 , _stk2A , _stk2B , _stk2C , _stk2D , _stk2E , _stk2F , _stk30 , _stk31 , _stk32 , _stk33 , _stk34 , _stk35 , _stk36 , _stk37 , _stk38 , _stk39 , _stk3A , _stk3B , _stk3C , _stk3D , _stk3E , _stk3F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι_removeStake_А_stake_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι_removeStake_А_stake_bs_def) StakingContract_ι_removeStake_А_stake = StakingContract_ι_removeStake_А_stake_bs_def.
Lemma StakingContract_ι_removeStake_А_stake_bs : Z2IBS_pos 64 StakingContract_ι_removeStake_А_stake = StakingContract_ι_removeStake_А_stake_bs_def.
Proof.
 rewrite <- StakingContract_ι_removeStake_А_stake_bs'. auto. Qed.
Axiom StakingContract_ι_removeStake_А_stake_pos: (0 <= StakingContract_ι_removeStake_А_stake )%Z.
Axiom StakingContract_ι_removeStake_А_stake_fits: zFitN_pos (tvmBitStringLen StakingContract_ι_removeStake_А_stake_bs_def) StakingContract_ι_removeStake_А_stake = true.
Lemma StakingContract_ι_removeStake_А_stake_bs_rev : I2ZBS_pos' StakingContract_ι_removeStake_А_stake_bs_def = StakingContract_ι_removeStake_А_stake .
Proof.
  prove_bs_rev StakingContract_ι_removeStake_А_stake_bs StakingContract_ι_removeStake_А_stake_pos StakingContract_ι_removeStake_А_stake_fits. 
Qed.
Lemma StakingContract_ι_removeStake_А_stake_bs257 : Z2IN 257 StakingContract_ι_removeStake_А_stake = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι_removeStake_А_stake_bs_def)) StakingContract_ι_removeStake_А_stake_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι_removeStake_А_stake_bs_rev StakingContract_ι_removeStake_А_stake_bs_def.
Qed.

Variables StakingContract_ι_continueStake_А_amount : Z . 
Variables (*! { _mnt !*) _mnt00 _mnt01 _mnt02 _mnt03 _mnt04 _mnt05 _mnt06 _mnt07 _mnt08 _mnt09 _mnt0A _mnt0B _mnt0C _mnt0D _mnt0E _mnt0F _mnt10 _mnt11 _mnt12 _mnt13 _mnt14 _mnt15 _mnt16 _mnt17 _mnt18 _mnt19 _mnt1A _mnt1B _mnt1C _mnt1D _mnt1E _mnt1F _mnt20 _mnt21 _mnt22 _mnt23 _mnt24 _mnt25 _mnt26 _mnt27 _mnt28 _mnt29 _mnt2A _mnt2B _mnt2C _mnt2D _mnt2E _mnt2F _mnt30 _mnt31 _mnt32 _mnt33 _mnt34 _mnt35 _mnt36 _mnt37 _mnt38 _mnt39 _mnt3A _mnt3B _mnt3C _mnt3D _mnt3E _mnt3F  : TVMBit . 
Definition StakingContract_ι_continueStake_А_amount_bs_def := [> _mnt00 , _mnt01 , _mnt02 , _mnt03 , _mnt04 , _mnt05 , _mnt06 , _mnt07 , _mnt08 , _mnt09 , _mnt0A , _mnt0B , _mnt0C , _mnt0D , _mnt0E , _mnt0F , _mnt10 , _mnt11 , _mnt12 , _mnt13 , _mnt14 , _mnt15 , _mnt16 , _mnt17 , _mnt18 , _mnt19 , _mnt1A , _mnt1B , _mnt1C , _mnt1D , _mnt1E , _mnt1F , _mnt20 , _mnt21 , _mnt22 , _mnt23 , _mnt24 , _mnt25 , _mnt26 , _mnt27 , _mnt28 , _mnt29 , _mnt2A , _mnt2B , _mnt2C , _mnt2D , _mnt2E , _mnt2F , _mnt30 , _mnt31 , _mnt32 , _mnt33 , _mnt34 , _mnt35 , _mnt36 , _mnt37 , _mnt38 , _mnt39 , _mnt3A , _mnt3B , _mnt3C , _mnt3D , _mnt3E , _mnt3F <] .
Lemma StakingContract_ι_continueStake_А_amount_bs_id: StakingContract_ι_continueStake_А_amount_bs_def = [> _mnt00 , _mnt01 , _mnt02 , _mnt03 , _mnt04 , _mnt05 , _mnt06 , _mnt07 , _mnt08 , _mnt09 , _mnt0A , _mnt0B , _mnt0C , _mnt0D , _mnt0E , _mnt0F , _mnt10 , _mnt11 , _mnt12 , _mnt13 , _mnt14 , _mnt15 , _mnt16 , _mnt17 , _mnt18 , _mnt19 , _mnt1A , _mnt1B , _mnt1C , _mnt1D , _mnt1E , _mnt1F , _mnt20 , _mnt21 , _mnt22 , _mnt23 , _mnt24 , _mnt25 , _mnt26 , _mnt27 , _mnt28 , _mnt29 , _mnt2A , _mnt2B , _mnt2C , _mnt2D , _mnt2E , _mnt2F , _mnt30 , _mnt31 , _mnt32 , _mnt33 , _mnt34 , _mnt35 , _mnt36 , _mnt37 , _mnt38 , _mnt39 , _mnt3A , _mnt3B , _mnt3C , _mnt3D , _mnt3E , _mnt3F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι_continueStake_А_amount_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι_continueStake_А_amount_bs_def) StakingContract_ι_continueStake_А_amount = StakingContract_ι_continueStake_А_amount_bs_def.
Lemma StakingContract_ι_continueStake_А_amount_bs : Z2IBS_pos 64 StakingContract_ι_continueStake_А_amount = StakingContract_ι_continueStake_А_amount_bs_def.
Proof.
 rewrite <- StakingContract_ι_continueStake_А_amount_bs'. auto. Qed.
Axiom StakingContract_ι_continueStake_А_amount_pos: (0 <= StakingContract_ι_continueStake_А_amount )%Z.
Axiom StakingContract_ι_continueStake_А_amount_fits: zFitN_pos (tvmBitStringLen StakingContract_ι_continueStake_А_amount_bs_def) StakingContract_ι_continueStake_А_amount = true.
Lemma StakingContract_ι_continueStake_А_amount_bs_rev : I2ZBS_pos' StakingContract_ι_continueStake_А_amount_bs_def = StakingContract_ι_continueStake_А_amount .
Proof.
  prove_bs_rev StakingContract_ι_continueStake_А_amount_bs StakingContract_ι_continueStake_А_amount_pos StakingContract_ι_continueStake_А_amount_fits. 
Qed.
Lemma StakingContract_ι_continueStake_А_amount_bs257 : Z2IN 257 StakingContract_ι_continueStake_А_amount = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι_continueStake_А_amount_bs_def)) StakingContract_ι_continueStake_А_amount_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι_continueStake_А_amount_bs_rev StakingContract_ι_continueStake_А_amount_bs_def.
Qed. 


Variables StakingContract_ι_processNewStake_А_queryId : Z . 
Variables (*! { _qrd !*) _qrd00 _qrd01 _qrd02 _qrd03 _qrd04 _qrd05 _qrd06 _qrd07 _qrd08 _qrd09 _qrd0A _qrd0B _qrd0C _qrd0D _qrd0E _qrd0F _qrd10 _qrd11 _qrd12 _qrd13 _qrd14 _qrd15 _qrd16 _qrd17 _qrd18 _qrd19 _qrd1A _qrd1B _qrd1C _qrd1D _qrd1E _qrd1F _qrd20 _qrd21 _qrd22 _qrd23 _qrd24 _qrd25 _qrd26 _qrd27 _qrd28 _qrd29 _qrd2A _qrd2B _qrd2C _qrd2D _qrd2E _qrd2F _qrd30 _qrd31 _qrd32 _qrd33 _qrd34 _qrd35 _qrd36 _qrd37 _qrd38 _qrd39 _qrd3A _qrd3B _qrd3C _qrd3D _qrd3E _qrd3F  : TVMBit . 
Definition StakingContract_ι_processNewStake_А_queryId_bs_def := [> _qrd00 , _qrd01 , _qrd02 , _qrd03 , _qrd04 , _qrd05 , _qrd06 , _qrd07 , _qrd08 , _qrd09 , _qrd0A , _qrd0B , _qrd0C , _qrd0D , _qrd0E , _qrd0F , _qrd10 , _qrd11 , _qrd12 , _qrd13 , _qrd14 , _qrd15 , _qrd16 , _qrd17 , _qrd18 , _qrd19 , _qrd1A , _qrd1B , _qrd1C , _qrd1D , _qrd1E , _qrd1F , _qrd20 , _qrd21 , _qrd22 , _qrd23 , _qrd24 , _qrd25 , _qrd26 , _qrd27 , _qrd28 , _qrd29 , _qrd2A , _qrd2B , _qrd2C , _qrd2D , _qrd2E , _qrd2F , _qrd30 , _qrd31 , _qrd32 , _qrd33 , _qrd34 , _qrd35 , _qrd36 , _qrd37 , _qrd38 , _qrd39 , _qrd3A , _qrd3B , _qrd3C , _qrd3D , _qrd3E , _qrd3F <] .
Lemma StakingContract_ι_processNewStake_А_queryId_bs_id: StakingContract_ι_processNewStake_А_queryId_bs_def = [> _qrd00 , _qrd01 , _qrd02 , _qrd03 , _qrd04 , _qrd05 , _qrd06 , _qrd07 , _qrd08 , _qrd09 , _qrd0A , _qrd0B , _qrd0C , _qrd0D , _qrd0E , _qrd0F , _qrd10 , _qrd11 , _qrd12 , _qrd13 , _qrd14 , _qrd15 , _qrd16 , _qrd17 , _qrd18 , _qrd19 , _qrd1A , _qrd1B , _qrd1C , _qrd1D , _qrd1E , _qrd1F , _qrd20 , _qrd21 , _qrd22 , _qrd23 , _qrd24 , _qrd25 , _qrd26 , _qrd27 , _qrd28 , _qrd29 , _qrd2A , _qrd2B , _qrd2C , _qrd2D , _qrd2E , _qrd2F , _qrd30 , _qrd31 , _qrd32 , _qrd33 , _qrd34 , _qrd35 , _qrd36 , _qrd37 , _qrd38 , _qrd39 , _qrd3A , _qrd3B , _qrd3C , _qrd3D , _qrd3E , _qrd3F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι_processNewStake_А_queryId_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι_processNewStake_А_queryId_bs_def) StakingContract_ι_processNewStake_А_queryId = StakingContract_ι_processNewStake_А_queryId_bs_def.
Lemma StakingContract_ι_processNewStake_А_queryId_bs : Z2IBS_pos 64 StakingContract_ι_processNewStake_А_queryId = StakingContract_ι_processNewStake_А_queryId_bs_def.
Proof.
 rewrite <- StakingContract_ι_processNewStake_А_queryId_bs'. auto. Qed.
Axiom StakingContract_ι_processNewStake_А_queryId_pos: (0 <= StakingContract_ι_processNewStake_А_queryId )%Z.
Axiom StakingContract_ι_processNewStake_А_queryId_fits: zFitN_pos (tvmBitStringLen StakingContract_ι_processNewStake_А_queryId_bs_def) StakingContract_ι_processNewStake_А_queryId = true.
Lemma StakingContract_ι_processNewStake_А_queryId_bs_rev : I2ZBS_pos' StakingContract_ι_processNewStake_А_queryId_bs_def = StakingContract_ι_processNewStake_А_queryId .
Proof.
  prove_bs_rev StakingContract_ι_processNewStake_А_queryId_bs StakingContract_ι_processNewStake_А_queryId_pos StakingContract_ι_processNewStake_А_queryId_fits. 
Qed.
Lemma StakingContract_ι_processNewStake_А_queryId_bs257 : Z2IN 257 StakingContract_ι_processNewStake_А_queryId = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι_processNewStake_А_queryId_bs_def)) StakingContract_ι_processNewStake_А_queryId_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι_processNewStake_А_queryId_bs_rev StakingContract_ι_processNewStake_А_queryId_bs_def.
Qed. 
Variables StakingContract_ι_processNewStake_А_validatorKey : Z . 
Variables (*! { _vldt !*) _vldt00 _vldt01 _vldt02 _vldt03 _vldt04 _vldt05 _vldt06 _vldt07 _vldt08 _vldt09 _vldt0A _vldt0B _vldt0C _vldt0D _vldt0E _vldt0F _vldt10 _vldt11 _vldt12 _vldt13 _vldt14 _vldt15 _vldt16 _vldt17 _vldt18 _vldt19 _vldt1A _vldt1B _vldt1C _vldt1D _vldt1E _vldt1F _vldt20 _vldt21 _vldt22 _vldt23 _vldt24 _vldt25 _vldt26 _vldt27 _vldt28 _vldt29 _vldt2A _vldt2B _vldt2C _vldt2D _vldt2E _vldt2F _vldt30 _vldt31 _vldt32 _vldt33 _vldt34 _vldt35 _vldt36 _vldt37 _vldt38 _vldt39 _vldt3A _vldt3B _vldt3C _vldt3D _vldt3E _vldt3F _vldt40 _vldt41 _vldt42 _vldt43 _vldt44 _vldt45 _vldt46 _vldt47 _vldt48 _vldt49 _vldt4A _vldt4B _vldt4C _vldt4D _vldt4E _vldt4F _vldt50 _vldt51 _vldt52 _vldt53 _vldt54 _vldt55 _vldt56 _vldt57 _vldt58 _vldt59 _vldt5A _vldt5B _vldt5C _vldt5D _vldt5E _vldt5F _vldt60 _vldt61 _vldt62 _vldt63 _vldt64 _vldt65 _vldt66 _vldt67 _vldt68 _vldt69 _vldt6A _vldt6B _vldt6C _vldt6D _vldt6E _vldt6F _vldt70 _vldt71 _vldt72 _vldt73 _vldt74 _vldt75 _vldt76 _vldt77 _vldt78 _vldt79 _vldt7A _vldt7B _vldt7C _vldt7D _vldt7E _vldt7F _vldt80 _vldt81 _vldt82 _vldt83 _vldt84 _vldt85 _vldt86 _vldt87 _vldt88 _vldt89 _vldt8A _vldt8B _vldt8C _vldt8D _vldt8E _vldt8F _vldt90 _vldt91 _vldt92 _vldt93 _vldt94 _vldt95 _vldt96 _vldt97 _vldt98 _vldt99 _vldt9A _vldt9B _vldt9C _vldt9D _vldt9E _vldt9F _vldtA0 _vldtA1 _vldtA2 _vldtA3 _vldtA4 _vldtA5 _vldtA6 _vldtA7 _vldtA8 _vldtA9 _vldtAA _vldtAB _vldtAC _vldtAD _vldtAE _vldtAF _vldtB0 _vldtB1 _vldtB2 _vldtB3 _vldtB4 _vldtB5 _vldtB6 _vldtB7 _vldtB8 _vldtB9 _vldtBA _vldtBB _vldtBC _vldtBD _vldtBE _vldtBF _vldtC0 _vldtC1 _vldtC2 _vldtC3 _vldtC4 _vldtC5 _vldtC6 _vldtC7 _vldtC8 _vldtC9 _vldtCA _vldtCB _vldtCC _vldtCD _vldtCE _vldtCF _vldtD0 _vldtD1 _vldtD2 _vldtD3 _vldtD4 _vldtD5 _vldtD6 _vldtD7 _vldtD8 _vldtD9 _vldtDA _vldtDB _vldtDC _vldtDD _vldtDE _vldtDF _vldtE0 _vldtE1 _vldtE2 _vldtE3 _vldtE4 _vldtE5 _vldtE6 _vldtE7 _vldtE8 _vldtE9 _vldtEA _vldtEB _vldtEC _vldtED _vldtEE _vldtEF _vldtF0 _vldtF1 _vldtF2 _vldtF3 _vldtF4 _vldtF5 _vldtF6 _vldtF7 _vldtF8 _vldtF9 _vldtFA _vldtFB _vldtFC _vldtFD _vldtFE _vldtFF  : TVMBit . 
Definition StakingContract_ι_processNewStake_А_validatorKey_bs_def := [> _vldt00 , _vldt01 , _vldt02 , _vldt03 , _vldt04 , _vldt05 , _vldt06 , _vldt07 , _vldt08 , _vldt09 , _vldt0A , _vldt0B , _vldt0C , _vldt0D , _vldt0E , _vldt0F , _vldt10 , _vldt11 , _vldt12 , _vldt13 , _vldt14 , _vldt15 , _vldt16 , _vldt17 , _vldt18 , _vldt19 , _vldt1A , _vldt1B , _vldt1C , _vldt1D , _vldt1E , _vldt1F , _vldt20 , _vldt21 , _vldt22 , _vldt23 , _vldt24 , _vldt25 , _vldt26 , _vldt27 , _vldt28 , _vldt29 , _vldt2A , _vldt2B , _vldt2C , _vldt2D , _vldt2E , _vldt2F , _vldt30 , _vldt31 , _vldt32 , _vldt33 , _vldt34 , _vldt35 , _vldt36 , _vldt37 , _vldt38 , _vldt39 , _vldt3A , _vldt3B , _vldt3C , _vldt3D , _vldt3E , _vldt3F , _vldt40 , _vldt41 , _vldt42 , _vldt43 , _vldt44 , _vldt45 , _vldt46 , _vldt47 , _vldt48 , _vldt49 , _vldt4A , _vldt4B , _vldt4C , _vldt4D , _vldt4E , _vldt4F , _vldt50 , _vldt51 , _vldt52 , _vldt53 , _vldt54 , _vldt55 , _vldt56 , _vldt57 , _vldt58 , _vldt59 , _vldt5A , _vldt5B , _vldt5C , _vldt5D , _vldt5E , _vldt5F , _vldt60 , _vldt61 , _vldt62 , _vldt63 , _vldt64 , _vldt65 , _vldt66 , _vldt67 , _vldt68 , _vldt69 , _vldt6A , _vldt6B , _vldt6C , _vldt6D , _vldt6E , _vldt6F , _vldt70 , _vldt71 , _vldt72 , _vldt73 , _vldt74 , _vldt75 , _vldt76 , _vldt77 , _vldt78 , _vldt79 , _vldt7A , _vldt7B , _vldt7C , _vldt7D , _vldt7E , _vldt7F , _vldt80 , _vldt81 , _vldt82 , _vldt83 , _vldt84 , _vldt85 , _vldt86 , _vldt87 , _vldt88 , _vldt89 , _vldt8A , _vldt8B , _vldt8C , _vldt8D , _vldt8E , _vldt8F , _vldt90 , _vldt91 , _vldt92 , _vldt93 , _vldt94 , _vldt95 , _vldt96 , _vldt97 , _vldt98 , _vldt99 , _vldt9A , _vldt9B , _vldt9C , _vldt9D , _vldt9E , _vldt9F , _vldtA0 , _vldtA1 , _vldtA2 , _vldtA3 , _vldtA4 , _vldtA5 , _vldtA6 , _vldtA7 , _vldtA8 , _vldtA9 , _vldtAA , _vldtAB , _vldtAC , _vldtAD , _vldtAE , _vldtAF , _vldtB0 , _vldtB1 , _vldtB2 , _vldtB3 , _vldtB4 , _vldtB5 , _vldtB6 , _vldtB7 , _vldtB8 , _vldtB9 , _vldtBA , _vldtBB , _vldtBC , _vldtBD , _vldtBE , _vldtBF , _vldtC0 , _vldtC1 , _vldtC2 , _vldtC3 , _vldtC4 , _vldtC5 , _vldtC6 , _vldtC7 , _vldtC8 , _vldtC9 , _vldtCA , _vldtCB , _vldtCC , _vldtCD , _vldtCE , _vldtCF , _vldtD0 , _vldtD1 , _vldtD2 , _vldtD3 , _vldtD4 , _vldtD5 , _vldtD6 , _vldtD7 , _vldtD8 , _vldtD9 , _vldtDA , _vldtDB , _vldtDC , _vldtDD , _vldtDE , _vldtDF , _vldtE0 , _vldtE1 , _vldtE2 , _vldtE3 , _vldtE4 , _vldtE5 , _vldtE6 , _vldtE7 , _vldtE8 , _vldtE9 , _vldtEA , _vldtEB , _vldtEC , _vldtED , _vldtEE , _vldtEF , _vldtF0 , _vldtF1 , _vldtF2 , _vldtF3 , _vldtF4 , _vldtF5 , _vldtF6 , _vldtF7 , _vldtF8 , _vldtF9 , _vldtFA , _vldtFB , _vldtFC , _vldtFD , _vldtFE , _vldtFF <] .
Lemma StakingContract_ι_processNewStake_А_validatorKey_bs_id: StakingContract_ι_processNewStake_А_validatorKey_bs_def = [> _vldt00 , _vldt01 , _vldt02 , _vldt03 , _vldt04 , _vldt05 , _vldt06 , _vldt07 , _vldt08 , _vldt09 , _vldt0A , _vldt0B , _vldt0C , _vldt0D , _vldt0E , _vldt0F , _vldt10 , _vldt11 , _vldt12 , _vldt13 , _vldt14 , _vldt15 , _vldt16 , _vldt17 , _vldt18 , _vldt19 , _vldt1A , _vldt1B , _vldt1C , _vldt1D , _vldt1E , _vldt1F , _vldt20 , _vldt21 , _vldt22 , _vldt23 , _vldt24 , _vldt25 , _vldt26 , _vldt27 , _vldt28 , _vldt29 , _vldt2A , _vldt2B , _vldt2C , _vldt2D , _vldt2E , _vldt2F , _vldt30 , _vldt31 , _vldt32 , _vldt33 , _vldt34 , _vldt35 , _vldt36 , _vldt37 , _vldt38 , _vldt39 , _vldt3A , _vldt3B , _vldt3C , _vldt3D , _vldt3E , _vldt3F , _vldt40 , _vldt41 , _vldt42 , _vldt43 , _vldt44 , _vldt45 , _vldt46 , _vldt47 , _vldt48 , _vldt49 , _vldt4A , _vldt4B , _vldt4C , _vldt4D , _vldt4E , _vldt4F , _vldt50 , _vldt51 , _vldt52 , _vldt53 , _vldt54 , _vldt55 , _vldt56 , _vldt57 , _vldt58 , _vldt59 , _vldt5A , _vldt5B , _vldt5C , _vldt5D , _vldt5E , _vldt5F , _vldt60 , _vldt61 , _vldt62 , _vldt63 , _vldt64 , _vldt65 , _vldt66 , _vldt67 , _vldt68 , _vldt69 , _vldt6A , _vldt6B , _vldt6C , _vldt6D , _vldt6E , _vldt6F , _vldt70 , _vldt71 , _vldt72 , _vldt73 , _vldt74 , _vldt75 , _vldt76 , _vldt77 , _vldt78 , _vldt79 , _vldt7A , _vldt7B , _vldt7C , _vldt7D , _vldt7E , _vldt7F , _vldt80 , _vldt81 , _vldt82 , _vldt83 , _vldt84 , _vldt85 , _vldt86 , _vldt87 , _vldt88 , _vldt89 , _vldt8A , _vldt8B , _vldt8C , _vldt8D , _vldt8E , _vldt8F , _vldt90 , _vldt91 , _vldt92 , _vldt93 , _vldt94 , _vldt95 , _vldt96 , _vldt97 , _vldt98 , _vldt99 , _vldt9A , _vldt9B , _vldt9C , _vldt9D , _vldt9E , _vldt9F , _vldtA0 , _vldtA1 , _vldtA2 , _vldtA3 , _vldtA4 , _vldtA5 , _vldtA6 , _vldtA7 , _vldtA8 , _vldtA9 , _vldtAA , _vldtAB , _vldtAC , _vldtAD , _vldtAE , _vldtAF , _vldtB0 , _vldtB1 , _vldtB2 , _vldtB3 , _vldtB4 , _vldtB5 , _vldtB6 , _vldtB7 , _vldtB8 , _vldtB9 , _vldtBA , _vldtBB , _vldtBC , _vldtBD , _vldtBE , _vldtBF , _vldtC0 , _vldtC1 , _vldtC2 , _vldtC3 , _vldtC4 , _vldtC5 , _vldtC6 , _vldtC7 , _vldtC8 , _vldtC9 , _vldtCA , _vldtCB , _vldtCC , _vldtCD , _vldtCE , _vldtCF , _vldtD0 , _vldtD1 , _vldtD2 , _vldtD3 , _vldtD4 , _vldtD5 , _vldtD6 , _vldtD7 , _vldtD8 , _vldtD9 , _vldtDA , _vldtDB , _vldtDC , _vldtDD , _vldtDE , _vldtDF , _vldtE0 , _vldtE1 , _vldtE2 , _vldtE3 , _vldtE4 , _vldtE5 , _vldtE6 , _vldtE7 , _vldtE8 , _vldtE9 , _vldtEA , _vldtEB , _vldtEC , _vldtED , _vldtEE , _vldtEF , _vldtF0 , _vldtF1 , _vldtF2 , _vldtF3 , _vldtF4 , _vldtF5 , _vldtF6 , _vldtF7 , _vldtF8 , _vldtF9 , _vldtFA , _vldtFB , _vldtFC , _vldtFD , _vldtFE , _vldtFF (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι_processNewStake_А_validatorKey_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι_processNewStake_А_validatorKey_bs_def) StakingContract_ι_processNewStake_А_validatorKey = StakingContract_ι_processNewStake_А_validatorKey_bs_def.
Lemma StakingContract_ι_processNewStake_А_validatorKey_bs : Z2IBS_pos 256 StakingContract_ι_processNewStake_А_validatorKey = StakingContract_ι_processNewStake_А_validatorKey_bs_def.
Proof.
 rewrite <- StakingContract_ι_processNewStake_А_validatorKey_bs'. auto. Qed.
Axiom StakingContract_ι_processNewStake_А_validatorKey_pos: (0 <= StakingContract_ι_processNewStake_А_validatorKey )%Z.
Axiom StakingContract_ι_processNewStake_А_validatorKey_fits: zFitN_pos (tvmBitStringLen StakingContract_ι_processNewStake_А_validatorKey_bs_def) StakingContract_ι_processNewStake_А_validatorKey = true.
Lemma StakingContract_ι_processNewStake_А_validatorKey_bs_rev : I2ZBS_pos' StakingContract_ι_processNewStake_А_validatorKey_bs_def = StakingContract_ι_processNewStake_А_validatorKey .
Proof.
  prove_bs_rev StakingContract_ι_processNewStake_А_validatorKey_bs StakingContract_ι_processNewStake_А_validatorKey_pos StakingContract_ι_processNewStake_А_validatorKey_fits. 
Qed.
Lemma StakingContract_ι_processNewStake_А_validatorKey_bs257 : Z2IN 257 StakingContract_ι_processNewStake_А_validatorKey = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι_processNewStake_А_validatorKey_bs_def)) StakingContract_ι_processNewStake_А_validatorKey_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι_processNewStake_А_validatorKey_bs_rev StakingContract_ι_processNewStake_А_validatorKey_bs_def.
Qed. 
Variables StakingContract_ι_processNewStake_А_stakeAt : Z . 
Variables (*! { _stkt !*) _stkt00 _stkt01 _stkt02 _stkt03 _stkt04 _stkt05 _stkt06 _stkt07 _stkt08 _stkt09 _stkt0A _stkt0B _stkt0C _stkt0D _stkt0E _stkt0F _stkt10 _stkt11 _stkt12 _stkt13 _stkt14 _stkt15 _stkt16 _stkt17 _stkt18 _stkt19 _stkt1A _stkt1B _stkt1C _stkt1D _stkt1E _stkt1F  : TVMBit . 
Definition StakingContract_ι_processNewStake_А_stakeAt_bs_def := [> _stkt00 , _stkt01 , _stkt02 , _stkt03 , _stkt04 , _stkt05 , _stkt06 , _stkt07 , _stkt08 , _stkt09 , _stkt0A , _stkt0B , _stkt0C , _stkt0D , _stkt0E , _stkt0F , _stkt10 , _stkt11 , _stkt12 , _stkt13 , _stkt14 , _stkt15 , _stkt16 , _stkt17 , _stkt18 , _stkt19 , _stkt1A , _stkt1B , _stkt1C , _stkt1D , _stkt1E , _stkt1F <] .
Lemma StakingContract_ι_processNewStake_А_stakeAt_bs_id: StakingContract_ι_processNewStake_А_stakeAt_bs_def = [> _stkt00 , _stkt01 , _stkt02 , _stkt03 , _stkt04 , _stkt05 , _stkt06 , _stkt07 , _stkt08 , _stkt09 , _stkt0A , _stkt0B , _stkt0C , _stkt0D , _stkt0E , _stkt0F , _stkt10 , _stkt11 , _stkt12 , _stkt13 , _stkt14 , _stkt15 , _stkt16 , _stkt17 , _stkt18 , _stkt19 , _stkt1A , _stkt1B , _stkt1C , _stkt1D , _stkt1E , _stkt1F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι_processNewStake_А_stakeAt_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι_processNewStake_А_stakeAt_bs_def) StakingContract_ι_processNewStake_А_stakeAt = StakingContract_ι_processNewStake_А_stakeAt_bs_def.
Lemma StakingContract_ι_processNewStake_А_stakeAt_bs : Z2IBS_pos 32 StakingContract_ι_processNewStake_А_stakeAt = StakingContract_ι_processNewStake_А_stakeAt_bs_def.
Proof.
 rewrite <- StakingContract_ι_processNewStake_А_stakeAt_bs'. auto. Qed.
Axiom StakingContract_ι_processNewStake_А_stakeAt_pos: (0 <= StakingContract_ι_processNewStake_А_stakeAt )%Z.
Axiom StakingContract_ι_processNewStake_А_stakeAt_fits: zFitN_pos (tvmBitStringLen StakingContract_ι_processNewStake_А_stakeAt_bs_def) StakingContract_ι_processNewStake_А_stakeAt = true.
Lemma StakingContract_ι_processNewStake_А_stakeAt_bs_rev : I2ZBS_pos' StakingContract_ι_processNewStake_А_stakeAt_bs_def = StakingContract_ι_processNewStake_А_stakeAt .
Proof.
  prove_bs_rev StakingContract_ι_processNewStake_А_stakeAt_bs StakingContract_ι_processNewStake_А_stakeAt_pos StakingContract_ι_processNewStake_А_stakeAt_fits. 
Qed.
Lemma StakingContract_ι_processNewStake_А_stakeAt_bs257 : Z2IN 257 StakingContract_ι_processNewStake_А_stakeAt = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι_processNewStake_А_stakeAt_bs_def)) StakingContract_ι_processNewStake_А_stakeAt_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι_processNewStake_А_stakeAt_bs_rev StakingContract_ι_processNewStake_А_stakeAt_bs_def.
Qed. 
Variables StakingContract_ι_processNewStake_А_maxFactor : Z . 
Variables (*! { _mxFc !*) _mxFc00 _mxFc01 _mxFc02 _mxFc03 _mxFc04 _mxFc05 _mxFc06 _mxFc07 _mxFc08 _mxFc09 _mxFc0A _mxFc0B _mxFc0C _mxFc0D _mxFc0E _mxFc0F _mxFc10 _mxFc11 _mxFc12 _mxFc13 _mxFc14 _mxFc15 _mxFc16 _mxFc17 _mxFc18 _mxFc19 _mxFc1A _mxFc1B _mxFc1C _mxFc1D _mxFc1E _mxFc1F  : TVMBit . 
Definition StakingContract_ι_processNewStake_А_maxFactor_bs_def := [> _mxFc00 , _mxFc01 , _mxFc02 , _mxFc03 , _mxFc04 , _mxFc05 , _mxFc06 , _mxFc07 , _mxFc08 , _mxFc09 , _mxFc0A , _mxFc0B , _mxFc0C , _mxFc0D , _mxFc0E , _mxFc0F , _mxFc10 , _mxFc11 , _mxFc12 , _mxFc13 , _mxFc14 , _mxFc15 , _mxFc16 , _mxFc17 , _mxFc18 , _mxFc19 , _mxFc1A , _mxFc1B , _mxFc1C , _mxFc1D , _mxFc1E , _mxFc1F <] .
Lemma StakingContract_ι_processNewStake_А_maxFactor_bs_id: StakingContract_ι_processNewStake_А_maxFactor_bs_def = [> _mxFc00 , _mxFc01 , _mxFc02 , _mxFc03 , _mxFc04 , _mxFc05 , _mxFc06 , _mxFc07 , _mxFc08 , _mxFc09 , _mxFc0A , _mxFc0B , _mxFc0C , _mxFc0D , _mxFc0E , _mxFc0F , _mxFc10 , _mxFc11 , _mxFc12 , _mxFc13 , _mxFc14 , _mxFc15 , _mxFc16 , _mxFc17 , _mxFc18 , _mxFc19 , _mxFc1A , _mxFc1B , _mxFc1C , _mxFc1D , _mxFc1E , _mxFc1F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι_processNewStake_А_maxFactor_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι_processNewStake_А_maxFactor_bs_def) StakingContract_ι_processNewStake_А_maxFactor = StakingContract_ι_processNewStake_А_maxFactor_bs_def.
Lemma StakingContract_ι_processNewStake_А_maxFactor_bs : Z2IBS_pos 32 StakingContract_ι_processNewStake_А_maxFactor = StakingContract_ι_processNewStake_А_maxFactor_bs_def.
Proof.
 rewrite <- StakingContract_ι_processNewStake_А_maxFactor_bs'. auto. Qed.
Axiom StakingContract_ι_processNewStake_А_maxFactor_pos: (0 <= StakingContract_ι_processNewStake_А_maxFactor )%Z.
Axiom StakingContract_ι_processNewStake_А_maxFactor_fits: zFitN_pos (tvmBitStringLen StakingContract_ι_processNewStake_А_maxFactor_bs_def) StakingContract_ι_processNewStake_А_maxFactor = true.
Lemma StakingContract_ι_processNewStake_А_maxFactor_bs_rev : I2ZBS_pos' StakingContract_ι_processNewStake_А_maxFactor_bs_def = StakingContract_ι_processNewStake_А_maxFactor .
Proof.
  prove_bs_rev StakingContract_ι_processNewStake_А_maxFactor_bs StakingContract_ι_processNewStake_А_maxFactor_pos StakingContract_ι_processNewStake_А_maxFactor_fits. 
Qed.
Lemma StakingContract_ι_processNewStake_А_maxFactor_bs257 : Z2IN 257 StakingContract_ι_processNewStake_А_maxFactor = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι_processNewStake_А_maxFactor_bs_def)) StakingContract_ι_processNewStake_А_maxFactor_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι_processNewStake_А_maxFactor_bs_rev StakingContract_ι_processNewStake_А_maxFactor_bs_def.
Qed. 
Variables StakingContract_ι_processNewStake_А_adnlAddr : Z . 
Variables (*! { _dnld !*) _dnld00 _dnld01 _dnld02 _dnld03 _dnld04 _dnld05 _dnld06 _dnld07 _dnld08 _dnld09 _dnld0A _dnld0B _dnld0C _dnld0D _dnld0E _dnld0F _dnld10 _dnld11 _dnld12 _dnld13 _dnld14 _dnld15 _dnld16 _dnld17 _dnld18 _dnld19 _dnld1A _dnld1B _dnld1C _dnld1D _dnld1E _dnld1F _dnld20 _dnld21 _dnld22 _dnld23 _dnld24 _dnld25 _dnld26 _dnld27 _dnld28 _dnld29 _dnld2A _dnld2B _dnld2C _dnld2D _dnld2E _dnld2F _dnld30 _dnld31 _dnld32 _dnld33 _dnld34 _dnld35 _dnld36 _dnld37 _dnld38 _dnld39 _dnld3A _dnld3B _dnld3C _dnld3D _dnld3E _dnld3F _dnld40 _dnld41 _dnld42 _dnld43 _dnld44 _dnld45 _dnld46 _dnld47 _dnld48 _dnld49 _dnld4A _dnld4B _dnld4C _dnld4D _dnld4E _dnld4F _dnld50 _dnld51 _dnld52 _dnld53 _dnld54 _dnld55 _dnld56 _dnld57 _dnld58 _dnld59 _dnld5A _dnld5B _dnld5C _dnld5D _dnld5E _dnld5F _dnld60 _dnld61 _dnld62 _dnld63 _dnld64 _dnld65 _dnld66 _dnld67 _dnld68 _dnld69 _dnld6A _dnld6B _dnld6C _dnld6D _dnld6E _dnld6F _dnld70 _dnld71 _dnld72 _dnld73 _dnld74 _dnld75 _dnld76 _dnld77 _dnld78 _dnld79 _dnld7A _dnld7B _dnld7C _dnld7D _dnld7E _dnld7F _dnld80 _dnld81 _dnld82 _dnld83 _dnld84 _dnld85 _dnld86 _dnld87 _dnld88 _dnld89 _dnld8A _dnld8B _dnld8C _dnld8D _dnld8E _dnld8F _dnld90 _dnld91 _dnld92 _dnld93 _dnld94 _dnld95 _dnld96 _dnld97 _dnld98 _dnld99 _dnld9A _dnld9B _dnld9C _dnld9D _dnld9E _dnld9F _dnldA0 _dnldA1 _dnldA2 _dnldA3 _dnldA4 _dnldA5 _dnldA6 _dnldA7 _dnldA8 _dnldA9 _dnldAA _dnldAB _dnldAC _dnldAD _dnldAE _dnldAF _dnldB0 _dnldB1 _dnldB2 _dnldB3 _dnldB4 _dnldB5 _dnldB6 _dnldB7 _dnldB8 _dnldB9 _dnldBA _dnldBB _dnldBC _dnldBD _dnldBE _dnldBF _dnldC0 _dnldC1 _dnldC2 _dnldC3 _dnldC4 _dnldC5 _dnldC6 _dnldC7 _dnldC8 _dnldC9 _dnldCA _dnldCB _dnldCC _dnldCD _dnldCE _dnldCF _dnldD0 _dnldD1 _dnldD2 _dnldD3 _dnldD4 _dnldD5 _dnldD6 _dnldD7 _dnldD8 _dnldD9 _dnldDA _dnldDB _dnldDC _dnldDD _dnldDE _dnldDF _dnldE0 _dnldE1 _dnldE2 _dnldE3 _dnldE4 _dnldE5 _dnldE6 _dnldE7 _dnldE8 _dnldE9 _dnldEA _dnldEB _dnldEC _dnldED _dnldEE _dnldEF _dnldF0 _dnldF1 _dnldF2 _dnldF3 _dnldF4 _dnldF5 _dnldF6 _dnldF7 _dnldF8 _dnldF9 _dnldFA _dnldFB _dnldFC _dnldFD _dnldFE _dnldFF  : TVMBit . 
Definition StakingContract_ι_processNewStake_А_adnlAddr_bs_def := [> _dnld00 , _dnld01 , _dnld02 , _dnld03 , _dnld04 , _dnld05 , _dnld06 , _dnld07 , _dnld08 , _dnld09 , _dnld0A , _dnld0B , _dnld0C , _dnld0D , _dnld0E , _dnld0F , _dnld10 , _dnld11 , _dnld12 , _dnld13 , _dnld14 , _dnld15 , _dnld16 , _dnld17 , _dnld18 , _dnld19 , _dnld1A , _dnld1B , _dnld1C , _dnld1D , _dnld1E , _dnld1F , _dnld20 , _dnld21 , _dnld22 , _dnld23 , _dnld24 , _dnld25 , _dnld26 , _dnld27 , _dnld28 , _dnld29 , _dnld2A , _dnld2B , _dnld2C , _dnld2D , _dnld2E , _dnld2F , _dnld30 , _dnld31 , _dnld32 , _dnld33 , _dnld34 , _dnld35 , _dnld36 , _dnld37 , _dnld38 , _dnld39 , _dnld3A , _dnld3B , _dnld3C , _dnld3D , _dnld3E , _dnld3F , _dnld40 , _dnld41 , _dnld42 , _dnld43 , _dnld44 , _dnld45 , _dnld46 , _dnld47 , _dnld48 , _dnld49 , _dnld4A , _dnld4B , _dnld4C , _dnld4D , _dnld4E , _dnld4F , _dnld50 , _dnld51 , _dnld52 , _dnld53 , _dnld54 , _dnld55 , _dnld56 , _dnld57 , _dnld58 , _dnld59 , _dnld5A , _dnld5B , _dnld5C , _dnld5D , _dnld5E , _dnld5F , _dnld60 , _dnld61 , _dnld62 , _dnld63 , _dnld64 , _dnld65 , _dnld66 , _dnld67 , _dnld68 , _dnld69 , _dnld6A , _dnld6B , _dnld6C , _dnld6D , _dnld6E , _dnld6F , _dnld70 , _dnld71 , _dnld72 , _dnld73 , _dnld74 , _dnld75 , _dnld76 , _dnld77 , _dnld78 , _dnld79 , _dnld7A , _dnld7B , _dnld7C , _dnld7D , _dnld7E , _dnld7F , _dnld80 , _dnld81 , _dnld82 , _dnld83 , _dnld84 , _dnld85 , _dnld86 , _dnld87 , _dnld88 , _dnld89 , _dnld8A , _dnld8B , _dnld8C , _dnld8D , _dnld8E , _dnld8F , _dnld90 , _dnld91 , _dnld92 , _dnld93 , _dnld94 , _dnld95 , _dnld96 , _dnld97 , _dnld98 , _dnld99 , _dnld9A , _dnld9B , _dnld9C , _dnld9D , _dnld9E , _dnld9F , _dnldA0 , _dnldA1 , _dnldA2 , _dnldA3 , _dnldA4 , _dnldA5 , _dnldA6 , _dnldA7 , _dnldA8 , _dnldA9 , _dnldAA , _dnldAB , _dnldAC , _dnldAD , _dnldAE , _dnldAF , _dnldB0 , _dnldB1 , _dnldB2 , _dnldB3 , _dnldB4 , _dnldB5 , _dnldB6 , _dnldB7 , _dnldB8 , _dnldB9 , _dnldBA , _dnldBB , _dnldBC , _dnldBD , _dnldBE , _dnldBF , _dnldC0 , _dnldC1 , _dnldC2 , _dnldC3 , _dnldC4 , _dnldC5 , _dnldC6 , _dnldC7 , _dnldC8 , _dnldC9 , _dnldCA , _dnldCB , _dnldCC , _dnldCD , _dnldCE , _dnldCF , _dnldD0 , _dnldD1 , _dnldD2 , _dnldD3 , _dnldD4 , _dnldD5 , _dnldD6 , _dnldD7 , _dnldD8 , _dnldD9 , _dnldDA , _dnldDB , _dnldDC , _dnldDD , _dnldDE , _dnldDF , _dnldE0 , _dnldE1 , _dnldE2 , _dnldE3 , _dnldE4 , _dnldE5 , _dnldE6 , _dnldE7 , _dnldE8 , _dnldE9 , _dnldEA , _dnldEB , _dnldEC , _dnldED , _dnldEE , _dnldEF , _dnldF0 , _dnldF1 , _dnldF2 , _dnldF3 , _dnldF4 , _dnldF5 , _dnldF6 , _dnldF7 , _dnldF8 , _dnldF9 , _dnldFA , _dnldFB , _dnldFC , _dnldFD , _dnldFE , _dnldFF <] .
Lemma StakingContract_ι_processNewStake_А_adnlAddr_bs_id: StakingContract_ι_processNewStake_А_adnlAddr_bs_def = [> _dnld00 , _dnld01 , _dnld02 , _dnld03 , _dnld04 , _dnld05 , _dnld06 , _dnld07 , _dnld08 , _dnld09 , _dnld0A , _dnld0B , _dnld0C , _dnld0D , _dnld0E , _dnld0F , _dnld10 , _dnld11 , _dnld12 , _dnld13 , _dnld14 , _dnld15 , _dnld16 , _dnld17 , _dnld18 , _dnld19 , _dnld1A , _dnld1B , _dnld1C , _dnld1D , _dnld1E , _dnld1F , _dnld20 , _dnld21 , _dnld22 , _dnld23 , _dnld24 , _dnld25 , _dnld26 , _dnld27 , _dnld28 , _dnld29 , _dnld2A , _dnld2B , _dnld2C , _dnld2D , _dnld2E , _dnld2F , _dnld30 , _dnld31 , _dnld32 , _dnld33 , _dnld34 , _dnld35 , _dnld36 , _dnld37 , _dnld38 , _dnld39 , _dnld3A , _dnld3B , _dnld3C , _dnld3D , _dnld3E , _dnld3F , _dnld40 , _dnld41 , _dnld42 , _dnld43 , _dnld44 , _dnld45 , _dnld46 , _dnld47 , _dnld48 , _dnld49 , _dnld4A , _dnld4B , _dnld4C , _dnld4D , _dnld4E , _dnld4F , _dnld50 , _dnld51 , _dnld52 , _dnld53 , _dnld54 , _dnld55 , _dnld56 , _dnld57 , _dnld58 , _dnld59 , _dnld5A , _dnld5B , _dnld5C , _dnld5D , _dnld5E , _dnld5F , _dnld60 , _dnld61 , _dnld62 , _dnld63 , _dnld64 , _dnld65 , _dnld66 , _dnld67 , _dnld68 , _dnld69 , _dnld6A , _dnld6B , _dnld6C , _dnld6D , _dnld6E , _dnld6F , _dnld70 , _dnld71 , _dnld72 , _dnld73 , _dnld74 , _dnld75 , _dnld76 , _dnld77 , _dnld78 , _dnld79 , _dnld7A , _dnld7B , _dnld7C , _dnld7D , _dnld7E , _dnld7F , _dnld80 , _dnld81 , _dnld82 , _dnld83 , _dnld84 , _dnld85 , _dnld86 , _dnld87 , _dnld88 , _dnld89 , _dnld8A , _dnld8B , _dnld8C , _dnld8D , _dnld8E , _dnld8F , _dnld90 , _dnld91 , _dnld92 , _dnld93 , _dnld94 , _dnld95 , _dnld96 , _dnld97 , _dnld98 , _dnld99 , _dnld9A , _dnld9B , _dnld9C , _dnld9D , _dnld9E , _dnld9F , _dnldA0 , _dnldA1 , _dnldA2 , _dnldA3 , _dnldA4 , _dnldA5 , _dnldA6 , _dnldA7 , _dnldA8 , _dnldA9 , _dnldAA , _dnldAB , _dnldAC , _dnldAD , _dnldAE , _dnldAF , _dnldB0 , _dnldB1 , _dnldB2 , _dnldB3 , _dnldB4 , _dnldB5 , _dnldB6 , _dnldB7 , _dnldB8 , _dnldB9 , _dnldBA , _dnldBB , _dnldBC , _dnldBD , _dnldBE , _dnldBF , _dnldC0 , _dnldC1 , _dnldC2 , _dnldC3 , _dnldC4 , _dnldC5 , _dnldC6 , _dnldC7 , _dnldC8 , _dnldC9 , _dnldCA , _dnldCB , _dnldCC , _dnldCD , _dnldCE , _dnldCF , _dnldD0 , _dnldD1 , _dnldD2 , _dnldD3 , _dnldD4 , _dnldD5 , _dnldD6 , _dnldD7 , _dnldD8 , _dnldD9 , _dnldDA , _dnldDB , _dnldDC , _dnldDD , _dnldDE , _dnldDF , _dnldE0 , _dnldE1 , _dnldE2 , _dnldE3 , _dnldE4 , _dnldE5 , _dnldE6 , _dnldE7 , _dnldE8 , _dnldE9 , _dnldEA , _dnldEB , _dnldEC , _dnldED , _dnldEE , _dnldEF , _dnldF0 , _dnldF1 , _dnldF2 , _dnldF3 , _dnldF4 , _dnldF5 , _dnldF6 , _dnldF7 , _dnldF8 , _dnldF9 , _dnldFA , _dnldFB , _dnldFC , _dnldFD , _dnldFE , _dnldFF (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι_processNewStake_А_adnlAddr_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι_processNewStake_А_adnlAddr_bs_def) StakingContract_ι_processNewStake_А_adnlAddr = StakingContract_ι_processNewStake_А_adnlAddr_bs_def.
Lemma StakingContract_ι_processNewStake_А_adnlAddr_bs : Z2IBS_pos 256 StakingContract_ι_processNewStake_А_adnlAddr = StakingContract_ι_processNewStake_А_adnlAddr_bs_def.
Proof.
 rewrite <- StakingContract_ι_processNewStake_А_adnlAddr_bs'. auto. Qed.
Axiom StakingContract_ι_processNewStake_А_adnlAddr_pos: (0 <= StakingContract_ι_processNewStake_А_adnlAddr )%Z.
Axiom StakingContract_ι_processNewStake_А_adnlAddr_fits: zFitN_pos (tvmBitStringLen StakingContract_ι_processNewStake_А_adnlAddr_bs_def) StakingContract_ι_processNewStake_А_adnlAddr = true.
Lemma StakingContract_ι_processNewStake_А_adnlAddr_bs_rev : I2ZBS_pos' StakingContract_ι_processNewStake_А_adnlAddr_bs_def = StakingContract_ι_processNewStake_А_adnlAddr .
Proof.
  prove_bs_rev StakingContract_ι_processNewStake_А_adnlAddr_bs StakingContract_ι_processNewStake_А_adnlAddr_pos StakingContract_ι_processNewStake_А_adnlAddr_fits. 
Qed.
Lemma StakingContract_ι_processNewStake_А_adnlAddr_bs257 : Z2IN 257 StakingContract_ι_processNewStake_А_adnlAddr = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι_processNewStake_А_adnlAddr_bs_def)) StakingContract_ι_processNewStake_А_adnlAddr_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι_processNewStake_А_adnlAddr_bs_rev StakingContract_ι_processNewStake_А_adnlAddr_bs_def.
Qed. 
Variables StakingContract_ι_processNewStake_А_signature : Z . 
Variables (*! { _sgnt !*) _sgnt00 _sgnt01 _sgnt02 _sgnt03 _sgnt04 _sgnt05 _sgnt06 _sgnt07  : TVMBit . 
Definition StakingContract_ι_processNewStake_А_signature_bs_def := [> _sgnt00 , _sgnt01 , _sgnt02 , _sgnt03 , _sgnt04 , _sgnt05 , _sgnt06 , _sgnt07 <] .
Lemma StakingContract_ι_processNewStake_А_signature_bs_id: StakingContract_ι_processNewStake_А_signature_bs_def = [> _sgnt00 , _sgnt01 , _sgnt02 , _sgnt03 , _sgnt04 , _sgnt05 , _sgnt06 , _sgnt07 (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι_processNewStake_А_signature_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι_processNewStake_А_signature_bs_def) StakingContract_ι_processNewStake_А_signature = StakingContract_ι_processNewStake_А_signature_bs_def.
Lemma StakingContract_ι_processNewStake_А_signature_bs : Z2IBS_pos 8 StakingContract_ι_processNewStake_А_signature = StakingContract_ι_processNewStake_А_signature_bs_def.
Proof.
 rewrite <- StakingContract_ι_processNewStake_А_signature_bs'. auto. Qed.
Axiom StakingContract_ι_processNewStake_А_signature_pos: (0 <= StakingContract_ι_processNewStake_А_signature )%Z.
Axiom StakingContract_ι_processNewStake_А_signature_fits: zFitN_pos (tvmBitStringLen StakingContract_ι_processNewStake_А_signature_bs_def) StakingContract_ι_processNewStake_А_signature = true.
Lemma StakingContract_ι_processNewStake_А_signature_bs_rev : I2ZBS_pos' StakingContract_ι_processNewStake_А_signature_bs_def = StakingContract_ι_processNewStake_А_signature .
Proof.
  prove_bs_rev StakingContract_ι_processNewStake_А_signature_bs StakingContract_ι_processNewStake_А_signature_pos StakingContract_ι_processNewStake_А_signature_fits. 
Qed.
Lemma StakingContract_ι_processNewStake_А_signature_bs257 : Z2IN 257 StakingContract_ι_processNewStake_А_signature = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι_processNewStake_А_signature_bs_def)) StakingContract_ι_processNewStake_А_signature_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι_processNewStake_А_signature_bs_rev StakingContract_ι_processNewStake_А_signature_bs_def.
Qed.

Variables StakingContract_ι_completePendingRound_А_roundId : Z . 
Variables (*! { _rndd !*) _rndd00 _rndd01 _rndd02 _rndd03 _rndd04 _rndd05 _rndd06 _rndd07 _rndd08 _rndd09 _rndd0A _rndd0B _rndd0C _rndd0D _rndd0E _rndd0F _rndd10 _rndd11 _rndd12 _rndd13 _rndd14 _rndd15 _rndd16 _rndd17 _rndd18 _rndd19 _rndd1A _rndd1B _rndd1C _rndd1D _rndd1E _rndd1F  : TVMBit . 
Definition StakingContract_ι_completePendingRound_А_roundId_bs_def := [> _rndd00 , _rndd01 , _rndd02 , _rndd03 , _rndd04 , _rndd05 , _rndd06 , _rndd07 , _rndd08 , _rndd09 , _rndd0A , _rndd0B , _rndd0C , _rndd0D , _rndd0E , _rndd0F , _rndd10 , _rndd11 , _rndd12 , _rndd13 , _rndd14 , _rndd15 , _rndd16 , _rndd17 , _rndd18 , _rndd19 , _rndd1A , _rndd1B , _rndd1C , _rndd1D , _rndd1E , _rndd1F <] .
Lemma StakingContract_ι_completePendingRound_А_roundId_bs_id: StakingContract_ι_completePendingRound_А_roundId_bs_def = [> _rndd00 , _rndd01 , _rndd02 , _rndd03 , _rndd04 , _rndd05 , _rndd06 , _rndd07 , _rndd08 , _rndd09 , _rndd0A , _rndd0B , _rndd0C , _rndd0D , _rndd0E , _rndd0F , _rndd10 , _rndd11 , _rndd12 , _rndd13 , _rndd14 , _rndd15 , _rndd16 , _rndd17 , _rndd18 , _rndd19 , _rndd1A , _rndd1B , _rndd1C , _rndd1D , _rndd1E , _rndd1F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι_completePendingRound_А_roundId_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι_completePendingRound_А_roundId_bs_def) StakingContract_ι_completePendingRound_А_roundId = StakingContract_ι_completePendingRound_А_roundId_bs_def.
Lemma StakingContract_ι_completePendingRound_А_roundId_bs : Z2IBS_pos 32 StakingContract_ι_completePendingRound_А_roundId = StakingContract_ι_completePendingRound_А_roundId_bs_def.
Proof.
 rewrite <- StakingContract_ι_completePendingRound_А_roundId_bs'. auto. Qed.
Axiom StakingContract_ι_completePendingRound_А_roundId_pos: (0 <= StakingContract_ι_completePendingRound_А_roundId )%Z.
Axiom StakingContract_ι_completePendingRound_А_roundId_fits: zFitN_pos (tvmBitStringLen StakingContract_ι_completePendingRound_А_roundId_bs_def) StakingContract_ι_completePendingRound_А_roundId = true.
Lemma StakingContract_ι_completePendingRound_А_roundId_bs_rev : I2ZBS_pos' StakingContract_ι_completePendingRound_А_roundId_bs_def = StakingContract_ι_completePendingRound_А_roundId .
Proof.
  prove_bs_rev StakingContract_ι_completePendingRound_А_roundId_bs StakingContract_ι_completePendingRound_А_roundId_pos StakingContract_ι_completePendingRound_А_roundId_fits. 
Qed.
Lemma StakingContract_ι_completePendingRound_А_roundId_bs257 : Z2IN 257 StakingContract_ι_completePendingRound_А_roundId = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι_completePendingRound_А_roundId_bs_def)) StakingContract_ι_completePendingRound_А_roundId_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι_completePendingRound_А_roundId_bs_rev StakingContract_ι_completePendingRound_А_roundId_bs_def.
Qed.

Variables StakingContract_ι_receiveConfirmation_А_queryId : Z . 
Variables (*! { _qrd !*) _qrd00 _qrd01 _qrd02 _qrd03 _qrd04 _qrd05 _qrd06 _qrd07 _qrd08 _qrd09 _qrd0A _qrd0B _qrd0C _qrd0D _qrd0E _qrd0F _qrd10 _qrd11 _qrd12 _qrd13 _qrd14 _qrd15 _qrd16 _qrd17 _qrd18 _qrd19 _qrd1A _qrd1B _qrd1C _qrd1D _qrd1E _qrd1F _qrd20 _qrd21 _qrd22 _qrd23 _qrd24 _qrd25 _qrd26 _qrd27 _qrd28 _qrd29 _qrd2A _qrd2B _qrd2C _qrd2D _qrd2E _qrd2F _qrd30 _qrd31 _qrd32 _qrd33 _qrd34 _qrd35 _qrd36 _qrd37 _qrd38 _qrd39 _qrd3A _qrd3B _qrd3C _qrd3D _qrd3E _qrd3F  : TVMBit . 
Definition StakingContract_ι_receiveConfirmation_А_queryId_bs_def := [> _qrd00 , _qrd01 , _qrd02 , _qrd03 , _qrd04 , _qrd05 , _qrd06 , _qrd07 , _qrd08 , _qrd09 , _qrd0A , _qrd0B , _qrd0C , _qrd0D , _qrd0E , _qrd0F , _qrd10 , _qrd11 , _qrd12 , _qrd13 , _qrd14 , _qrd15 , _qrd16 , _qrd17 , _qrd18 , _qrd19 , _qrd1A , _qrd1B , _qrd1C , _qrd1D , _qrd1E , _qrd1F , _qrd20 , _qrd21 , _qrd22 , _qrd23 , _qrd24 , _qrd25 , _qrd26 , _qrd27 , _qrd28 , _qrd29 , _qrd2A , _qrd2B , _qrd2C , _qrd2D , _qrd2E , _qrd2F , _qrd30 , _qrd31 , _qrd32 , _qrd33 , _qrd34 , _qrd35 , _qrd36 , _qrd37 , _qrd38 , _qrd39 , _qrd3A , _qrd3B , _qrd3C , _qrd3D , _qrd3E , _qrd3F <] .
Lemma StakingContract_ι_receiveConfirmation_А_queryId_bs_id: StakingContract_ι_receiveConfirmation_А_queryId_bs_def = [> _qrd00 , _qrd01 , _qrd02 , _qrd03 , _qrd04 , _qrd05 , _qrd06 , _qrd07 , _qrd08 , _qrd09 , _qrd0A , _qrd0B , _qrd0C , _qrd0D , _qrd0E , _qrd0F , _qrd10 , _qrd11 , _qrd12 , _qrd13 , _qrd14 , _qrd15 , _qrd16 , _qrd17 , _qrd18 , _qrd19 , _qrd1A , _qrd1B , _qrd1C , _qrd1D , _qrd1E , _qrd1F , _qrd20 , _qrd21 , _qrd22 , _qrd23 , _qrd24 , _qrd25 , _qrd26 , _qrd27 , _qrd28 , _qrd29 , _qrd2A , _qrd2B , _qrd2C , _qrd2D , _qrd2E , _qrd2F , _qrd30 , _qrd31 , _qrd32 , _qrd33 , _qrd34 , _qrd35 , _qrd36 , _qrd37 , _qrd38 , _qrd39 , _qrd3A , _qrd3B , _qrd3C , _qrd3D , _qrd3E , _qrd3F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι_receiveConfirmation_А_queryId_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι_receiveConfirmation_А_queryId_bs_def) StakingContract_ι_receiveConfirmation_А_queryId = StakingContract_ι_receiveConfirmation_А_queryId_bs_def.
Lemma StakingContract_ι_receiveConfirmation_А_queryId_bs : Z2IBS_pos 64 StakingContract_ι_receiveConfirmation_А_queryId = StakingContract_ι_receiveConfirmation_А_queryId_bs_def.
Proof.
 rewrite <- StakingContract_ι_receiveConfirmation_А_queryId_bs'. auto. Qed.
Axiom StakingContract_ι_receiveConfirmation_А_queryId_pos: (0 <= StakingContract_ι_receiveConfirmation_А_queryId )%Z.
Axiom StakingContract_ι_receiveConfirmation_А_queryId_fits: zFitN_pos (tvmBitStringLen StakingContract_ι_receiveConfirmation_А_queryId_bs_def) StakingContract_ι_receiveConfirmation_А_queryId = true.
Lemma StakingContract_ι_receiveConfirmation_А_queryId_bs_rev : I2ZBS_pos' StakingContract_ι_receiveConfirmation_А_queryId_bs_def = StakingContract_ι_receiveConfirmation_А_queryId .
Proof.
  prove_bs_rev StakingContract_ι_receiveConfirmation_А_queryId_bs StakingContract_ι_receiveConfirmation_А_queryId_pos StakingContract_ι_receiveConfirmation_А_queryId_fits. 
Qed.
Lemma StakingContract_ι_receiveConfirmation_А_queryId_bs257 : Z2IN 257 StakingContract_ι_receiveConfirmation_А_queryId = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι_receiveConfirmation_А_queryId_bs_def)) StakingContract_ι_receiveConfirmation_А_queryId_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι_receiveConfirmation_А_queryId_bs_rev StakingContract_ι_receiveConfirmation_А_queryId_bs_def.
Qed. 
Variables StakingContract_ι_receiveConfirmation_А_comment : Z . 
Variables (*! { _cmmn !*) _cmmn00 _cmmn01 _cmmn02 _cmmn03 _cmmn04 _cmmn05 _cmmn06 _cmmn07 _cmmn08 _cmmn09 _cmmn0A _cmmn0B _cmmn0C _cmmn0D _cmmn0E _cmmn0F _cmmn10 _cmmn11 _cmmn12 _cmmn13 _cmmn14 _cmmn15 _cmmn16 _cmmn17 _cmmn18 _cmmn19 _cmmn1A _cmmn1B _cmmn1C _cmmn1D _cmmn1E _cmmn1F  : TVMBit . 
Definition StakingContract_ι_receiveConfirmation_А_comment_bs_def := [> _cmmn00 , _cmmn01 , _cmmn02 , _cmmn03 , _cmmn04 , _cmmn05 , _cmmn06 , _cmmn07 , _cmmn08 , _cmmn09 , _cmmn0A , _cmmn0B , _cmmn0C , _cmmn0D , _cmmn0E , _cmmn0F , _cmmn10 , _cmmn11 , _cmmn12 , _cmmn13 , _cmmn14 , _cmmn15 , _cmmn16 , _cmmn17 , _cmmn18 , _cmmn19 , _cmmn1A , _cmmn1B , _cmmn1C , _cmmn1D , _cmmn1E , _cmmn1F <] .
Lemma StakingContract_ι_receiveConfirmation_А_comment_bs_id: StakingContract_ι_receiveConfirmation_А_comment_bs_def = [> _cmmn00 , _cmmn01 , _cmmn02 , _cmmn03 , _cmmn04 , _cmmn05 , _cmmn06 , _cmmn07 , _cmmn08 , _cmmn09 , _cmmn0A , _cmmn0B , _cmmn0C , _cmmn0D , _cmmn0E , _cmmn0F , _cmmn10 , _cmmn11 , _cmmn12 , _cmmn13 , _cmmn14 , _cmmn15 , _cmmn16 , _cmmn17 , _cmmn18 , _cmmn19 , _cmmn1A , _cmmn1B , _cmmn1C , _cmmn1D , _cmmn1E , _cmmn1F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι_receiveConfirmation_А_comment_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι_receiveConfirmation_А_comment_bs_def) StakingContract_ι_receiveConfirmation_А_comment = StakingContract_ι_receiveConfirmation_А_comment_bs_def.
Lemma StakingContract_ι_receiveConfirmation_А_comment_bs : Z2IBS_pos 32 StakingContract_ι_receiveConfirmation_А_comment = StakingContract_ι_receiveConfirmation_А_comment_bs_def.
Proof.
 rewrite <- StakingContract_ι_receiveConfirmation_А_comment_bs'. auto. Qed.
Axiom StakingContract_ι_receiveConfirmation_А_comment_pos: (0 <= StakingContract_ι_receiveConfirmation_А_comment )%Z.
Axiom StakingContract_ι_receiveConfirmation_А_comment_fits: zFitN_pos (tvmBitStringLen StakingContract_ι_receiveConfirmation_А_comment_bs_def) StakingContract_ι_receiveConfirmation_А_comment = true.
Lemma StakingContract_ι_receiveConfirmation_А_comment_bs_rev : I2ZBS_pos' StakingContract_ι_receiveConfirmation_А_comment_bs_def = StakingContract_ι_receiveConfirmation_А_comment .
Proof.
  prove_bs_rev StakingContract_ι_receiveConfirmation_А_comment_bs StakingContract_ι_receiveConfirmation_А_comment_pos StakingContract_ι_receiveConfirmation_А_comment_fits. 
Qed.
Lemma StakingContract_ι_receiveConfirmation_А_comment_bs257 : Z2IN 257 StakingContract_ι_receiveConfirmation_А_comment = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι_receiveConfirmation_А_comment_bs_def)) StakingContract_ι_receiveConfirmation_А_comment_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι_receiveConfirmation_А_comment_bs_rev StakingContract_ι_receiveConfirmation_А_comment_bs_def.
Qed.

Variables StakingContract_ι_receiveReturnedStake_А_queryId : Z . 
Variables (*! { _qrd !*) _qrd00 _qrd01 _qrd02 _qrd03 _qrd04 _qrd05 _qrd06 _qrd07 _qrd08 _qrd09 _qrd0A _qrd0B _qrd0C _qrd0D _qrd0E _qrd0F _qrd10 _qrd11 _qrd12 _qrd13 _qrd14 _qrd15 _qrd16 _qrd17 _qrd18 _qrd19 _qrd1A _qrd1B _qrd1C _qrd1D _qrd1E _qrd1F _qrd20 _qrd21 _qrd22 _qrd23 _qrd24 _qrd25 _qrd26 _qrd27 _qrd28 _qrd29 _qrd2A _qrd2B _qrd2C _qrd2D _qrd2E _qrd2F _qrd30 _qrd31 _qrd32 _qrd33 _qrd34 _qrd35 _qrd36 _qrd37 _qrd38 _qrd39 _qrd3A _qrd3B _qrd3C _qrd3D _qrd3E _qrd3F  : TVMBit . 
Definition StakingContract_ι_receiveReturnedStake_А_queryId_bs_def := [> _qrd00 , _qrd01 , _qrd02 , _qrd03 , _qrd04 , _qrd05 , _qrd06 , _qrd07 , _qrd08 , _qrd09 , _qrd0A , _qrd0B , _qrd0C , _qrd0D , _qrd0E , _qrd0F , _qrd10 , _qrd11 , _qrd12 , _qrd13 , _qrd14 , _qrd15 , _qrd16 , _qrd17 , _qrd18 , _qrd19 , _qrd1A , _qrd1B , _qrd1C , _qrd1D , _qrd1E , _qrd1F , _qrd20 , _qrd21 , _qrd22 , _qrd23 , _qrd24 , _qrd25 , _qrd26 , _qrd27 , _qrd28 , _qrd29 , _qrd2A , _qrd2B , _qrd2C , _qrd2D , _qrd2E , _qrd2F , _qrd30 , _qrd31 , _qrd32 , _qrd33 , _qrd34 , _qrd35 , _qrd36 , _qrd37 , _qrd38 , _qrd39 , _qrd3A , _qrd3B , _qrd3C , _qrd3D , _qrd3E , _qrd3F <] .
Lemma StakingContract_ι_receiveReturnedStake_А_queryId_bs_id: StakingContract_ι_receiveReturnedStake_А_queryId_bs_def = [> _qrd00 , _qrd01 , _qrd02 , _qrd03 , _qrd04 , _qrd05 , _qrd06 , _qrd07 , _qrd08 , _qrd09 , _qrd0A , _qrd0B , _qrd0C , _qrd0D , _qrd0E , _qrd0F , _qrd10 , _qrd11 , _qrd12 , _qrd13 , _qrd14 , _qrd15 , _qrd16 , _qrd17 , _qrd18 , _qrd19 , _qrd1A , _qrd1B , _qrd1C , _qrd1D , _qrd1E , _qrd1F , _qrd20 , _qrd21 , _qrd22 , _qrd23 , _qrd24 , _qrd25 , _qrd26 , _qrd27 , _qrd28 , _qrd29 , _qrd2A , _qrd2B , _qrd2C , _qrd2D , _qrd2E , _qrd2F , _qrd30 , _qrd31 , _qrd32 , _qrd33 , _qrd34 , _qrd35 , _qrd36 , _qrd37 , _qrd38 , _qrd39 , _qrd3A , _qrd3B , _qrd3C , _qrd3D , _qrd3E , _qrd3F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι_receiveReturnedStake_А_queryId_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι_receiveReturnedStake_А_queryId_bs_def) StakingContract_ι_receiveReturnedStake_А_queryId = StakingContract_ι_receiveReturnedStake_А_queryId_bs_def.
Lemma StakingContract_ι_receiveReturnedStake_А_queryId_bs : Z2IBS_pos 64 StakingContract_ι_receiveReturnedStake_А_queryId = StakingContract_ι_receiveReturnedStake_А_queryId_bs_def.
Proof.
 rewrite <- StakingContract_ι_receiveReturnedStake_А_queryId_bs'. auto. Qed.
Axiom StakingContract_ι_receiveReturnedStake_А_queryId_pos: (0 <= StakingContract_ι_receiveReturnedStake_А_queryId )%Z.
Axiom StakingContract_ι_receiveReturnedStake_А_queryId_fits: zFitN_pos (tvmBitStringLen StakingContract_ι_receiveReturnedStake_А_queryId_bs_def) StakingContract_ι_receiveReturnedStake_А_queryId = true.
Lemma StakingContract_ι_receiveReturnedStake_А_queryId_bs_rev : I2ZBS_pos' StakingContract_ι_receiveReturnedStake_А_queryId_bs_def = StakingContract_ι_receiveReturnedStake_А_queryId .
Proof.
  prove_bs_rev StakingContract_ι_receiveReturnedStake_А_queryId_bs StakingContract_ι_receiveReturnedStake_А_queryId_pos StakingContract_ι_receiveReturnedStake_А_queryId_fits. 
Qed.
Lemma StakingContract_ι_receiveReturnedStake_А_queryId_bs257 : Z2IN 257 StakingContract_ι_receiveReturnedStake_А_queryId = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι_receiveReturnedStake_А_queryId_bs_def)) StakingContract_ι_receiveReturnedStake_А_queryId_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι_receiveReturnedStake_А_queryId_bs_rev StakingContract_ι_receiveReturnedStake_А_queryId_bs_def.
Qed. 
Variables StakingContract_ι_receiveReturnedStake_А_comment : Z . 
Variables (*! { _cmmn !*) _cmmn00 _cmmn01 _cmmn02 _cmmn03 _cmmn04 _cmmn05 _cmmn06 _cmmn07 _cmmn08 _cmmn09 _cmmn0A _cmmn0B _cmmn0C _cmmn0D _cmmn0E _cmmn0F _cmmn10 _cmmn11 _cmmn12 _cmmn13 _cmmn14 _cmmn15 _cmmn16 _cmmn17 _cmmn18 _cmmn19 _cmmn1A _cmmn1B _cmmn1C _cmmn1D _cmmn1E _cmmn1F  : TVMBit . 
Definition StakingContract_ι_receiveReturnedStake_А_comment_bs_def := [> _cmmn00 , _cmmn01 , _cmmn02 , _cmmn03 , _cmmn04 , _cmmn05 , _cmmn06 , _cmmn07 , _cmmn08 , _cmmn09 , _cmmn0A , _cmmn0B , _cmmn0C , _cmmn0D , _cmmn0E , _cmmn0F , _cmmn10 , _cmmn11 , _cmmn12 , _cmmn13 , _cmmn14 , _cmmn15 , _cmmn16 , _cmmn17 , _cmmn18 , _cmmn19 , _cmmn1A , _cmmn1B , _cmmn1C , _cmmn1D , _cmmn1E , _cmmn1F <] .
Lemma StakingContract_ι_receiveReturnedStake_А_comment_bs_id: StakingContract_ι_receiveReturnedStake_А_comment_bs_def = [> _cmmn00 , _cmmn01 , _cmmn02 , _cmmn03 , _cmmn04 , _cmmn05 , _cmmn06 , _cmmn07 , _cmmn08 , _cmmn09 , _cmmn0A , _cmmn0B , _cmmn0C , _cmmn0D , _cmmn0E , _cmmn0F , _cmmn10 , _cmmn11 , _cmmn12 , _cmmn13 , _cmmn14 , _cmmn15 , _cmmn16 , _cmmn17 , _cmmn18 , _cmmn19 , _cmmn1A , _cmmn1B , _cmmn1C , _cmmn1D , _cmmn1E , _cmmn1F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι_receiveReturnedStake_А_comment_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι_receiveReturnedStake_А_comment_bs_def) StakingContract_ι_receiveReturnedStake_А_comment = StakingContract_ι_receiveReturnedStake_А_comment_bs_def.
Lemma StakingContract_ι_receiveReturnedStake_А_comment_bs : Z2IBS_pos 32 StakingContract_ι_receiveReturnedStake_А_comment = StakingContract_ι_receiveReturnedStake_А_comment_bs_def.
Proof.
 rewrite <- StakingContract_ι_receiveReturnedStake_А_comment_bs'. auto. Qed.
Axiom StakingContract_ι_receiveReturnedStake_А_comment_pos: (0 <= StakingContract_ι_receiveReturnedStake_А_comment )%Z.
Axiom StakingContract_ι_receiveReturnedStake_А_comment_fits: zFitN_pos (tvmBitStringLen StakingContract_ι_receiveReturnedStake_А_comment_bs_def) StakingContract_ι_receiveReturnedStake_А_comment = true.
Lemma StakingContract_ι_receiveReturnedStake_А_comment_bs_rev : I2ZBS_pos' StakingContract_ι_receiveReturnedStake_А_comment_bs_def = StakingContract_ι_receiveReturnedStake_А_comment .
Proof.
  prove_bs_rev StakingContract_ι_receiveReturnedStake_А_comment_bs StakingContract_ι_receiveReturnedStake_А_comment_pos StakingContract_ι_receiveReturnedStake_А_comment_fits. 
Qed.
Lemma StakingContract_ι_receiveReturnedStake_А_comment_bs257 : Z2IN 257 StakingContract_ι_receiveReturnedStake_А_comment = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι_receiveReturnedStake_А_comment_bs_def)) StakingContract_ι_receiveReturnedStake_А_comment_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι_receiveReturnedStake_А_comment_bs_rev StakingContract_ι_receiveReturnedStake_А_comment_bs_def.
Qed.

Variables StakingContract_ι_acceptRecoveredStake_А_queryId : Z . 
Variables (*! { _qrd !*) _qrd00 _qrd01 _qrd02 _qrd03 _qrd04 _qrd05 _qrd06 _qrd07 _qrd08 _qrd09 _qrd0A _qrd0B _qrd0C _qrd0D _qrd0E _qrd0F _qrd10 _qrd11 _qrd12 _qrd13 _qrd14 _qrd15 _qrd16 _qrd17 _qrd18 _qrd19 _qrd1A _qrd1B _qrd1C _qrd1D _qrd1E _qrd1F _qrd20 _qrd21 _qrd22 _qrd23 _qrd24 _qrd25 _qrd26 _qrd27 _qrd28 _qrd29 _qrd2A _qrd2B _qrd2C _qrd2D _qrd2E _qrd2F _qrd30 _qrd31 _qrd32 _qrd33 _qrd34 _qrd35 _qrd36 _qrd37 _qrd38 _qrd39 _qrd3A _qrd3B _qrd3C _qrd3D _qrd3E _qrd3F  : TVMBit . 
Definition StakingContract_ι_acceptRecoveredStake_А_queryId_bs_def := [> _qrd00 , _qrd01 , _qrd02 , _qrd03 , _qrd04 , _qrd05 , _qrd06 , _qrd07 , _qrd08 , _qrd09 , _qrd0A , _qrd0B , _qrd0C , _qrd0D , _qrd0E , _qrd0F , _qrd10 , _qrd11 , _qrd12 , _qrd13 , _qrd14 , _qrd15 , _qrd16 , _qrd17 , _qrd18 , _qrd19 , _qrd1A , _qrd1B , _qrd1C , _qrd1D , _qrd1E , _qrd1F , _qrd20 , _qrd21 , _qrd22 , _qrd23 , _qrd24 , _qrd25 , _qrd26 , _qrd27 , _qrd28 , _qrd29 , _qrd2A , _qrd2B , _qrd2C , _qrd2D , _qrd2E , _qrd2F , _qrd30 , _qrd31 , _qrd32 , _qrd33 , _qrd34 , _qrd35 , _qrd36 , _qrd37 , _qrd38 , _qrd39 , _qrd3A , _qrd3B , _qrd3C , _qrd3D , _qrd3E , _qrd3F <] .
Lemma StakingContract_ι_acceptRecoveredStake_А_queryId_bs_id: StakingContract_ι_acceptRecoveredStake_А_queryId_bs_def = [> _qrd00 , _qrd01 , _qrd02 , _qrd03 , _qrd04 , _qrd05 , _qrd06 , _qrd07 , _qrd08 , _qrd09 , _qrd0A , _qrd0B , _qrd0C , _qrd0D , _qrd0E , _qrd0F , _qrd10 , _qrd11 , _qrd12 , _qrd13 , _qrd14 , _qrd15 , _qrd16 , _qrd17 , _qrd18 , _qrd19 , _qrd1A , _qrd1B , _qrd1C , _qrd1D , _qrd1E , _qrd1F , _qrd20 , _qrd21 , _qrd22 , _qrd23 , _qrd24 , _qrd25 , _qrd26 , _qrd27 , _qrd28 , _qrd29 , _qrd2A , _qrd2B , _qrd2C , _qrd2D , _qrd2E , _qrd2F , _qrd30 , _qrd31 , _qrd32 , _qrd33 , _qrd34 , _qrd35 , _qrd36 , _qrd37 , _qrd38 , _qrd39 , _qrd3A , _qrd3B , _qrd3C , _qrd3D , _qrd3E , _qrd3F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι_acceptRecoveredStake_А_queryId_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι_acceptRecoveredStake_А_queryId_bs_def) StakingContract_ι_acceptRecoveredStake_А_queryId = StakingContract_ι_acceptRecoveredStake_А_queryId_bs_def.
Lemma StakingContract_ι_acceptRecoveredStake_А_queryId_bs : Z2IBS_pos 64 StakingContract_ι_acceptRecoveredStake_А_queryId = StakingContract_ι_acceptRecoveredStake_А_queryId_bs_def.
Proof.
 rewrite <- StakingContract_ι_acceptRecoveredStake_А_queryId_bs'. auto. Qed.
Axiom StakingContract_ι_acceptRecoveredStake_А_queryId_pos: (0 <= StakingContract_ι_acceptRecoveredStake_А_queryId )%Z.
Axiom StakingContract_ι_acceptRecoveredStake_А_queryId_fits: zFitN_pos (tvmBitStringLen StakingContract_ι_acceptRecoveredStake_А_queryId_bs_def) StakingContract_ι_acceptRecoveredStake_А_queryId = true.
Lemma StakingContract_ι_acceptRecoveredStake_А_queryId_bs_rev : I2ZBS_pos' StakingContract_ι_acceptRecoveredStake_А_queryId_bs_def = StakingContract_ι_acceptRecoveredStake_А_queryId .
Proof.
  prove_bs_rev StakingContract_ι_acceptRecoveredStake_А_queryId_bs StakingContract_ι_acceptRecoveredStake_А_queryId_pos StakingContract_ι_acceptRecoveredStake_А_queryId_fits. 
Qed.
Lemma StakingContract_ι_acceptRecoveredStake_А_queryId_bs257 : Z2IN 257 StakingContract_ι_acceptRecoveredStake_А_queryId = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι_acceptRecoveredStake_А_queryId_bs_def)) StakingContract_ι_acceptRecoveredStake_А_queryId_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι_acceptRecoveredStake_А_queryId_bs_rev StakingContract_ι_acceptRecoveredStake_А_queryId_bs_def.
Qed.

 
Variables OwnerBase_ι_Owner_ι_reward : Z . 
Variables (*! { _rwrd !*) _rwrd00 _rwrd01 _rwrd02 _rwrd03 _rwrd04 _rwrd05 _rwrd06 _rwrd07 _rwrd08 _rwrd09 _rwrd0A _rwrd0B _rwrd0C _rwrd0D _rwrd0E _rwrd0F _rwrd10 _rwrd11 _rwrd12 _rwrd13 _rwrd14 _rwrd15 _rwrd16 _rwrd17 _rwrd18 _rwrd19 _rwrd1A _rwrd1B _rwrd1C _rwrd1D _rwrd1E _rwrd1F _rwrd20 _rwrd21 _rwrd22 _rwrd23 _rwrd24 _rwrd25 _rwrd26 _rwrd27 _rwrd28 _rwrd29 _rwrd2A _rwrd2B _rwrd2C _rwrd2D _rwrd2E _rwrd2F _rwrd30 _rwrd31 _rwrd32 _rwrd33 _rwrd34 _rwrd35 _rwrd36 _rwrd37 _rwrd38 _rwrd39 _rwrd3A _rwrd3B _rwrd3C _rwrd3D _rwrd3E _rwrd3F  : TVMBit . 
Definition OwnerBase_ι_Owner_ι_reward_bs_def := [> _rwrd00 , _rwrd01 , _rwrd02 , _rwrd03 , _rwrd04 , _rwrd05 , _rwrd06 , _rwrd07 , _rwrd08 , _rwrd09 , _rwrd0A , _rwrd0B , _rwrd0C , _rwrd0D , _rwrd0E , _rwrd0F , _rwrd10 , _rwrd11 , _rwrd12 , _rwrd13 , _rwrd14 , _rwrd15 , _rwrd16 , _rwrd17 , _rwrd18 , _rwrd19 , _rwrd1A , _rwrd1B , _rwrd1C , _rwrd1D , _rwrd1E , _rwrd1F , _rwrd20 , _rwrd21 , _rwrd22 , _rwrd23 , _rwrd24 , _rwrd25 , _rwrd26 , _rwrd27 , _rwrd28 , _rwrd29 , _rwrd2A , _rwrd2B , _rwrd2C , _rwrd2D , _rwrd2E , _rwrd2F , _rwrd30 , _rwrd31 , _rwrd32 , _rwrd33 , _rwrd34 , _rwrd35 , _rwrd36 , _rwrd37 , _rwrd38 , _rwrd39 , _rwrd3A , _rwrd3B , _rwrd3C , _rwrd3D , _rwrd3E , _rwrd3F <] .
Lemma OwnerBase_ι_Owner_ι_reward_bs_id: OwnerBase_ι_Owner_ι_reward_bs_def = [> _rwrd00 , _rwrd01 , _rwrd02 , _rwrd03 , _rwrd04 , _rwrd05 , _rwrd06 , _rwrd07 , _rwrd08 , _rwrd09 , _rwrd0A , _rwrd0B , _rwrd0C , _rwrd0D , _rwrd0E , _rwrd0F , _rwrd10 , _rwrd11 , _rwrd12 , _rwrd13 , _rwrd14 , _rwrd15 , _rwrd16 , _rwrd17 , _rwrd18 , _rwrd19 , _rwrd1A , _rwrd1B , _rwrd1C , _rwrd1D , _rwrd1E , _rwrd1F , _rwrd20 , _rwrd21 , _rwrd22 , _rwrd23 , _rwrd24 , _rwrd25 , _rwrd26 , _rwrd27 , _rwrd28 , _rwrd29 , _rwrd2A , _rwrd2B , _rwrd2C , _rwrd2D , _rwrd2E , _rwrd2F , _rwrd30 , _rwrd31 , _rwrd32 , _rwrd33 , _rwrd34 , _rwrd35 , _rwrd36 , _rwrd37 , _rwrd38 , _rwrd39 , _rwrd3A , _rwrd3B , _rwrd3C , _rwrd3D , _rwrd3E , _rwrd3F (* } !*)  <] .
Proof. auto. Qed.
Axiom OwnerBase_ι_Owner_ι_reward_bs' : Z2IBS_pos (tvmBitStringLen OwnerBase_ι_Owner_ι_reward_bs_def) OwnerBase_ι_Owner_ι_reward = OwnerBase_ι_Owner_ι_reward_bs_def.
Lemma OwnerBase_ι_Owner_ι_reward_bs : Z2IBS_pos 64 OwnerBase_ι_Owner_ι_reward = OwnerBase_ι_Owner_ι_reward_bs_def.
Proof.
 rewrite <- OwnerBase_ι_Owner_ι_reward_bs'. auto. Qed.
Axiom OwnerBase_ι_Owner_ι_reward_pos: (0 <= OwnerBase_ι_Owner_ι_reward )%Z.
Axiom OwnerBase_ι_Owner_ι_reward_fits: zFitN_pos (tvmBitStringLen OwnerBase_ι_Owner_ι_reward_bs_def) OwnerBase_ι_Owner_ι_reward = true.
Lemma OwnerBase_ι_Owner_ι_reward_bs_rev : I2ZBS_pos' OwnerBase_ι_Owner_ι_reward_bs_def = OwnerBase_ι_Owner_ι_reward .
Proof.
  prove_bs_rev OwnerBase_ι_Owner_ι_reward_bs OwnerBase_ι_Owner_ι_reward_pos OwnerBase_ι_Owner_ι_reward_fits. 
Qed.
Lemma OwnerBase_ι_Owner_ι_reward_bs257 : Z2IN 257 OwnerBase_ι_Owner_ι_reward = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    OwnerBase_ι_Owner_ι_reward_bs_def)) OwnerBase_ι_Owner_ι_reward_bs_def)).
Proof.
  prove_bs_rev OwnerBase_ι_Owner_ι_reward_bs_rev OwnerBase_ι_Owner_ι_reward_bs_def.
Qed.

Variables ElectorBase_ι_Request_ι_queryId : Z . 
Variables (*! { _qrd !*) _qrd00 _qrd01 _qrd02 _qrd03 _qrd04 _qrd05 _qrd06 _qrd07 _qrd08 _qrd09 _qrd0A _qrd0B _qrd0C _qrd0D _qrd0E _qrd0F _qrd10 _qrd11 _qrd12 _qrd13 _qrd14 _qrd15 _qrd16 _qrd17 _qrd18 _qrd19 _qrd1A _qrd1B _qrd1C _qrd1D _qrd1E _qrd1F _qrd20 _qrd21 _qrd22 _qrd23 _qrd24 _qrd25 _qrd26 _qrd27 _qrd28 _qrd29 _qrd2A _qrd2B _qrd2C _qrd2D _qrd2E _qrd2F _qrd30 _qrd31 _qrd32 _qrd33 _qrd34 _qrd35 _qrd36 _qrd37 _qrd38 _qrd39 _qrd3A _qrd3B _qrd3C _qrd3D _qrd3E _qrd3F  : TVMBit . 
Definition ElectorBase_ι_Request_ι_queryId_bs_def := [> _qrd00 , _qrd01 , _qrd02 , _qrd03 , _qrd04 , _qrd05 , _qrd06 , _qrd07 , _qrd08 , _qrd09 , _qrd0A , _qrd0B , _qrd0C , _qrd0D , _qrd0E , _qrd0F , _qrd10 , _qrd11 , _qrd12 , _qrd13 , _qrd14 , _qrd15 , _qrd16 , _qrd17 , _qrd18 , _qrd19 , _qrd1A , _qrd1B , _qrd1C , _qrd1D , _qrd1E , _qrd1F , _qrd20 , _qrd21 , _qrd22 , _qrd23 , _qrd24 , _qrd25 , _qrd26 , _qrd27 , _qrd28 , _qrd29 , _qrd2A , _qrd2B , _qrd2C , _qrd2D , _qrd2E , _qrd2F , _qrd30 , _qrd31 , _qrd32 , _qrd33 , _qrd34 , _qrd35 , _qrd36 , _qrd37 , _qrd38 , _qrd39 , _qrd3A , _qrd3B , _qrd3C , _qrd3D , _qrd3E , _qrd3F <] .
Lemma ElectorBase_ι_Request_ι_queryId_bs_id: ElectorBase_ι_Request_ι_queryId_bs_def = [> _qrd00 , _qrd01 , _qrd02 , _qrd03 , _qrd04 , _qrd05 , _qrd06 , _qrd07 , _qrd08 , _qrd09 , _qrd0A , _qrd0B , _qrd0C , _qrd0D , _qrd0E , _qrd0F , _qrd10 , _qrd11 , _qrd12 , _qrd13 , _qrd14 , _qrd15 , _qrd16 , _qrd17 , _qrd18 , _qrd19 , _qrd1A , _qrd1B , _qrd1C , _qrd1D , _qrd1E , _qrd1F , _qrd20 , _qrd21 , _qrd22 , _qrd23 , _qrd24 , _qrd25 , _qrd26 , _qrd27 , _qrd28 , _qrd29 , _qrd2A , _qrd2B , _qrd2C , _qrd2D , _qrd2E , _qrd2F , _qrd30 , _qrd31 , _qrd32 , _qrd33 , _qrd34 , _qrd35 , _qrd36 , _qrd37 , _qrd38 , _qrd39 , _qrd3A , _qrd3B , _qrd3C , _qrd3D , _qrd3E , _qrd3F (* } !*)  <] .
Proof. auto. Qed.
Axiom ElectorBase_ι_Request_ι_queryId_bs' : Z2IBS_pos (tvmBitStringLen ElectorBase_ι_Request_ι_queryId_bs_def) ElectorBase_ι_Request_ι_queryId = ElectorBase_ι_Request_ι_queryId_bs_def.
Lemma ElectorBase_ι_Request_ι_queryId_bs : Z2IBS_pos 64 ElectorBase_ι_Request_ι_queryId = ElectorBase_ι_Request_ι_queryId_bs_def.
Proof.
 rewrite <- ElectorBase_ι_Request_ι_queryId_bs'. auto. Qed.
Axiom ElectorBase_ι_Request_ι_queryId_pos: (0 <= ElectorBase_ι_Request_ι_queryId )%Z.
Axiom ElectorBase_ι_Request_ι_queryId_fits: zFitN_pos (tvmBitStringLen ElectorBase_ι_Request_ι_queryId_bs_def) ElectorBase_ι_Request_ι_queryId = true.
Lemma ElectorBase_ι_Request_ι_queryId_bs_rev : I2ZBS_pos' ElectorBase_ι_Request_ι_queryId_bs_def = ElectorBase_ι_Request_ι_queryId .
Proof.
  prove_bs_rev ElectorBase_ι_Request_ι_queryId_bs ElectorBase_ι_Request_ι_queryId_pos ElectorBase_ι_Request_ι_queryId_fits. 
Qed.
Lemma ElectorBase_ι_Request_ι_queryId_bs257 : Z2IN 257 ElectorBase_ι_Request_ι_queryId = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    ElectorBase_ι_Request_ι_queryId_bs_def)) ElectorBase_ι_Request_ι_queryId_bs_def)).
Proof.
  prove_bs_rev ElectorBase_ι_Request_ι_queryId_bs_rev ElectorBase_ι_Request_ι_queryId_bs_def.
Qed. 
Variables ElectorBase_ι_Request_ι_validatorKey : Z . 
Variables (*! { _vldt !*) _vldt00 _vldt01 _vldt02 _vldt03 _vldt04 _vldt05 _vldt06 _vldt07 _vldt08 _vldt09 _vldt0A _vldt0B _vldt0C _vldt0D _vldt0E _vldt0F _vldt10 _vldt11 _vldt12 _vldt13 _vldt14 _vldt15 _vldt16 _vldt17 _vldt18 _vldt19 _vldt1A _vldt1B _vldt1C _vldt1D _vldt1E _vldt1F _vldt20 _vldt21 _vldt22 _vldt23 _vldt24 _vldt25 _vldt26 _vldt27 _vldt28 _vldt29 _vldt2A _vldt2B _vldt2C _vldt2D _vldt2E _vldt2F _vldt30 _vldt31 _vldt32 _vldt33 _vldt34 _vldt35 _vldt36 _vldt37 _vldt38 _vldt39 _vldt3A _vldt3B _vldt3C _vldt3D _vldt3E _vldt3F _vldt40 _vldt41 _vldt42 _vldt43 _vldt44 _vldt45 _vldt46 _vldt47 _vldt48 _vldt49 _vldt4A _vldt4B _vldt4C _vldt4D _vldt4E _vldt4F _vldt50 _vldt51 _vldt52 _vldt53 _vldt54 _vldt55 _vldt56 _vldt57 _vldt58 _vldt59 _vldt5A _vldt5B _vldt5C _vldt5D _vldt5E _vldt5F _vldt60 _vldt61 _vldt62 _vldt63 _vldt64 _vldt65 _vldt66 _vldt67 _vldt68 _vldt69 _vldt6A _vldt6B _vldt6C _vldt6D _vldt6E _vldt6F _vldt70 _vldt71 _vldt72 _vldt73 _vldt74 _vldt75 _vldt76 _vldt77 _vldt78 _vldt79 _vldt7A _vldt7B _vldt7C _vldt7D _vldt7E _vldt7F _vldt80 _vldt81 _vldt82 _vldt83 _vldt84 _vldt85 _vldt86 _vldt87 _vldt88 _vldt89 _vldt8A _vldt8B _vldt8C _vldt8D _vldt8E _vldt8F _vldt90 _vldt91 _vldt92 _vldt93 _vldt94 _vldt95 _vldt96 _vldt97 _vldt98 _vldt99 _vldt9A _vldt9B _vldt9C _vldt9D _vldt9E _vldt9F _vldtA0 _vldtA1 _vldtA2 _vldtA3 _vldtA4 _vldtA5 _vldtA6 _vldtA7 _vldtA8 _vldtA9 _vldtAA _vldtAB _vldtAC _vldtAD _vldtAE _vldtAF _vldtB0 _vldtB1 _vldtB2 _vldtB3 _vldtB4 _vldtB5 _vldtB6 _vldtB7 _vldtB8 _vldtB9 _vldtBA _vldtBB _vldtBC _vldtBD _vldtBE _vldtBF _vldtC0 _vldtC1 _vldtC2 _vldtC3 _vldtC4 _vldtC5 _vldtC6 _vldtC7 _vldtC8 _vldtC9 _vldtCA _vldtCB _vldtCC _vldtCD _vldtCE _vldtCF _vldtD0 _vldtD1 _vldtD2 _vldtD3 _vldtD4 _vldtD5 _vldtD6 _vldtD7 _vldtD8 _vldtD9 _vldtDA _vldtDB _vldtDC _vldtDD _vldtDE _vldtDF _vldtE0 _vldtE1 _vldtE2 _vldtE3 _vldtE4 _vldtE5 _vldtE6 _vldtE7 _vldtE8 _vldtE9 _vldtEA _vldtEB _vldtEC _vldtED _vldtEE _vldtEF _vldtF0 _vldtF1 _vldtF2 _vldtF3 _vldtF4 _vldtF5 _vldtF6 _vldtF7 _vldtF8 _vldtF9 _vldtFA _vldtFB _vldtFC _vldtFD _vldtFE _vldtFF  : TVMBit . 
Definition ElectorBase_ι_Request_ι_validatorKey_bs_def := [> _vldt00 , _vldt01 , _vldt02 , _vldt03 , _vldt04 , _vldt05 , _vldt06 , _vldt07 , _vldt08 , _vldt09 , _vldt0A , _vldt0B , _vldt0C , _vldt0D , _vldt0E , _vldt0F , _vldt10 , _vldt11 , _vldt12 , _vldt13 , _vldt14 , _vldt15 , _vldt16 , _vldt17 , _vldt18 , _vldt19 , _vldt1A , _vldt1B , _vldt1C , _vldt1D , _vldt1E , _vldt1F , _vldt20 , _vldt21 , _vldt22 , _vldt23 , _vldt24 , _vldt25 , _vldt26 , _vldt27 , _vldt28 , _vldt29 , _vldt2A , _vldt2B , _vldt2C , _vldt2D , _vldt2E , _vldt2F , _vldt30 , _vldt31 , _vldt32 , _vldt33 , _vldt34 , _vldt35 , _vldt36 , _vldt37 , _vldt38 , _vldt39 , _vldt3A , _vldt3B , _vldt3C , _vldt3D , _vldt3E , _vldt3F , _vldt40 , _vldt41 , _vldt42 , _vldt43 , _vldt44 , _vldt45 , _vldt46 , _vldt47 , _vldt48 , _vldt49 , _vldt4A , _vldt4B , _vldt4C , _vldt4D , _vldt4E , _vldt4F , _vldt50 , _vldt51 , _vldt52 , _vldt53 , _vldt54 , _vldt55 , _vldt56 , _vldt57 , _vldt58 , _vldt59 , _vldt5A , _vldt5B , _vldt5C , _vldt5D , _vldt5E , _vldt5F , _vldt60 , _vldt61 , _vldt62 , _vldt63 , _vldt64 , _vldt65 , _vldt66 , _vldt67 , _vldt68 , _vldt69 , _vldt6A , _vldt6B , _vldt6C , _vldt6D , _vldt6E , _vldt6F , _vldt70 , _vldt71 , _vldt72 , _vldt73 , _vldt74 , _vldt75 , _vldt76 , _vldt77 , _vldt78 , _vldt79 , _vldt7A , _vldt7B , _vldt7C , _vldt7D , _vldt7E , _vldt7F , _vldt80 , _vldt81 , _vldt82 , _vldt83 , _vldt84 , _vldt85 , _vldt86 , _vldt87 , _vldt88 , _vldt89 , _vldt8A , _vldt8B , _vldt8C , _vldt8D , _vldt8E , _vldt8F , _vldt90 , _vldt91 , _vldt92 , _vldt93 , _vldt94 , _vldt95 , _vldt96 , _vldt97 , _vldt98 , _vldt99 , _vldt9A , _vldt9B , _vldt9C , _vldt9D , _vldt9E , _vldt9F , _vldtA0 , _vldtA1 , _vldtA2 , _vldtA3 , _vldtA4 , _vldtA5 , _vldtA6 , _vldtA7 , _vldtA8 , _vldtA9 , _vldtAA , _vldtAB , _vldtAC , _vldtAD , _vldtAE , _vldtAF , _vldtB0 , _vldtB1 , _vldtB2 , _vldtB3 , _vldtB4 , _vldtB5 , _vldtB6 , _vldtB7 , _vldtB8 , _vldtB9 , _vldtBA , _vldtBB , _vldtBC , _vldtBD , _vldtBE , _vldtBF , _vldtC0 , _vldtC1 , _vldtC2 , _vldtC3 , _vldtC4 , _vldtC5 , _vldtC6 , _vldtC7 , _vldtC8 , _vldtC9 , _vldtCA , _vldtCB , _vldtCC , _vldtCD , _vldtCE , _vldtCF , _vldtD0 , _vldtD1 , _vldtD2 , _vldtD3 , _vldtD4 , _vldtD5 , _vldtD6 , _vldtD7 , _vldtD8 , _vldtD9 , _vldtDA , _vldtDB , _vldtDC , _vldtDD , _vldtDE , _vldtDF , _vldtE0 , _vldtE1 , _vldtE2 , _vldtE3 , _vldtE4 , _vldtE5 , _vldtE6 , _vldtE7 , _vldtE8 , _vldtE9 , _vldtEA , _vldtEB , _vldtEC , _vldtED , _vldtEE , _vldtEF , _vldtF0 , _vldtF1 , _vldtF2 , _vldtF3 , _vldtF4 , _vldtF5 , _vldtF6 , _vldtF7 , _vldtF8 , _vldtF9 , _vldtFA , _vldtFB , _vldtFC , _vldtFD , _vldtFE , _vldtFF <] .
Lemma ElectorBase_ι_Request_ι_validatorKey_bs_id: ElectorBase_ι_Request_ι_validatorKey_bs_def = [> _vldt00 , _vldt01 , _vldt02 , _vldt03 , _vldt04 , _vldt05 , _vldt06 , _vldt07 , _vldt08 , _vldt09 , _vldt0A , _vldt0B , _vldt0C , _vldt0D , _vldt0E , _vldt0F , _vldt10 , _vldt11 , _vldt12 , _vldt13 , _vldt14 , _vldt15 , _vldt16 , _vldt17 , _vldt18 , _vldt19 , _vldt1A , _vldt1B , _vldt1C , _vldt1D , _vldt1E , _vldt1F , _vldt20 , _vldt21 , _vldt22 , _vldt23 , _vldt24 , _vldt25 , _vldt26 , _vldt27 , _vldt28 , _vldt29 , _vldt2A , _vldt2B , _vldt2C , _vldt2D , _vldt2E , _vldt2F , _vldt30 , _vldt31 , _vldt32 , _vldt33 , _vldt34 , _vldt35 , _vldt36 , _vldt37 , _vldt38 , _vldt39 , _vldt3A , _vldt3B , _vldt3C , _vldt3D , _vldt3E , _vldt3F , _vldt40 , _vldt41 , _vldt42 , _vldt43 , _vldt44 , _vldt45 , _vldt46 , _vldt47 , _vldt48 , _vldt49 , _vldt4A , _vldt4B , _vldt4C , _vldt4D , _vldt4E , _vldt4F , _vldt50 , _vldt51 , _vldt52 , _vldt53 , _vldt54 , _vldt55 , _vldt56 , _vldt57 , _vldt58 , _vldt59 , _vldt5A , _vldt5B , _vldt5C , _vldt5D , _vldt5E , _vldt5F , _vldt60 , _vldt61 , _vldt62 , _vldt63 , _vldt64 , _vldt65 , _vldt66 , _vldt67 , _vldt68 , _vldt69 , _vldt6A , _vldt6B , _vldt6C , _vldt6D , _vldt6E , _vldt6F , _vldt70 , _vldt71 , _vldt72 , _vldt73 , _vldt74 , _vldt75 , _vldt76 , _vldt77 , _vldt78 , _vldt79 , _vldt7A , _vldt7B , _vldt7C , _vldt7D , _vldt7E , _vldt7F , _vldt80 , _vldt81 , _vldt82 , _vldt83 , _vldt84 , _vldt85 , _vldt86 , _vldt87 , _vldt88 , _vldt89 , _vldt8A , _vldt8B , _vldt8C , _vldt8D , _vldt8E , _vldt8F , _vldt90 , _vldt91 , _vldt92 , _vldt93 , _vldt94 , _vldt95 , _vldt96 , _vldt97 , _vldt98 , _vldt99 , _vldt9A , _vldt9B , _vldt9C , _vldt9D , _vldt9E , _vldt9F , _vldtA0 , _vldtA1 , _vldtA2 , _vldtA3 , _vldtA4 , _vldtA5 , _vldtA6 , _vldtA7 , _vldtA8 , _vldtA9 , _vldtAA , _vldtAB , _vldtAC , _vldtAD , _vldtAE , _vldtAF , _vldtB0 , _vldtB1 , _vldtB2 , _vldtB3 , _vldtB4 , _vldtB5 , _vldtB6 , _vldtB7 , _vldtB8 , _vldtB9 , _vldtBA , _vldtBB , _vldtBC , _vldtBD , _vldtBE , _vldtBF , _vldtC0 , _vldtC1 , _vldtC2 , _vldtC3 , _vldtC4 , _vldtC5 , _vldtC6 , _vldtC7 , _vldtC8 , _vldtC9 , _vldtCA , _vldtCB , _vldtCC , _vldtCD , _vldtCE , _vldtCF , _vldtD0 , _vldtD1 , _vldtD2 , _vldtD3 , _vldtD4 , _vldtD5 , _vldtD6 , _vldtD7 , _vldtD8 , _vldtD9 , _vldtDA , _vldtDB , _vldtDC , _vldtDD , _vldtDE , _vldtDF , _vldtE0 , _vldtE1 , _vldtE2 , _vldtE3 , _vldtE4 , _vldtE5 , _vldtE6 , _vldtE7 , _vldtE8 , _vldtE9 , _vldtEA , _vldtEB , _vldtEC , _vldtED , _vldtEE , _vldtEF , _vldtF0 , _vldtF1 , _vldtF2 , _vldtF3 , _vldtF4 , _vldtF5 , _vldtF6 , _vldtF7 , _vldtF8 , _vldtF9 , _vldtFA , _vldtFB , _vldtFC , _vldtFD , _vldtFE , _vldtFF (* } !*)  <] .
Proof. auto. Qed.
Axiom ElectorBase_ι_Request_ι_validatorKey_bs' : Z2IBS_pos (tvmBitStringLen ElectorBase_ι_Request_ι_validatorKey_bs_def) ElectorBase_ι_Request_ι_validatorKey = ElectorBase_ι_Request_ι_validatorKey_bs_def.
Lemma ElectorBase_ι_Request_ι_validatorKey_bs : Z2IBS_pos 256 ElectorBase_ι_Request_ι_validatorKey = ElectorBase_ι_Request_ι_validatorKey_bs_def.
Proof.
 rewrite <- ElectorBase_ι_Request_ι_validatorKey_bs'. auto. Qed.
Axiom ElectorBase_ι_Request_ι_validatorKey_pos: (0 <= ElectorBase_ι_Request_ι_validatorKey )%Z.
Axiom ElectorBase_ι_Request_ι_validatorKey_fits: zFitN_pos (tvmBitStringLen ElectorBase_ι_Request_ι_validatorKey_bs_def) ElectorBase_ι_Request_ι_validatorKey = true.
Lemma ElectorBase_ι_Request_ι_validatorKey_bs_rev : I2ZBS_pos' ElectorBase_ι_Request_ι_validatorKey_bs_def = ElectorBase_ι_Request_ι_validatorKey .
Proof.
  prove_bs_rev ElectorBase_ι_Request_ι_validatorKey_bs ElectorBase_ι_Request_ι_validatorKey_pos ElectorBase_ι_Request_ι_validatorKey_fits. 
Qed.
Lemma ElectorBase_ι_Request_ι_validatorKey_bs257 : Z2IN 257 ElectorBase_ι_Request_ι_validatorKey = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    ElectorBase_ι_Request_ι_validatorKey_bs_def)) ElectorBase_ι_Request_ι_validatorKey_bs_def)).
Proof.
  prove_bs_rev ElectorBase_ι_Request_ι_validatorKey_bs_rev ElectorBase_ι_Request_ι_validatorKey_bs_def.
Qed. 
Variables ElectorBase_ι_Request_ι_stakeAt : Z . 
Variables (*! { _stkt !*) _stkt00 _stkt01 _stkt02 _stkt03 _stkt04 _stkt05 _stkt06 _stkt07 _stkt08 _stkt09 _stkt0A _stkt0B _stkt0C _stkt0D _stkt0E _stkt0F _stkt10 _stkt11 _stkt12 _stkt13 _stkt14 _stkt15 _stkt16 _stkt17 _stkt18 _stkt19 _stkt1A _stkt1B _stkt1C _stkt1D _stkt1E _stkt1F  : TVMBit . 
Definition ElectorBase_ι_Request_ι_stakeAt_bs_def := [> _stkt00 , _stkt01 , _stkt02 , _stkt03 , _stkt04 , _stkt05 , _stkt06 , _stkt07 , _stkt08 , _stkt09 , _stkt0A , _stkt0B , _stkt0C , _stkt0D , _stkt0E , _stkt0F , _stkt10 , _stkt11 , _stkt12 , _stkt13 , _stkt14 , _stkt15 , _stkt16 , _stkt17 , _stkt18 , _stkt19 , _stkt1A , _stkt1B , _stkt1C , _stkt1D , _stkt1E , _stkt1F <] .
Lemma ElectorBase_ι_Request_ι_stakeAt_bs_id: ElectorBase_ι_Request_ι_stakeAt_bs_def = [> _stkt00 , _stkt01 , _stkt02 , _stkt03 , _stkt04 , _stkt05 , _stkt06 , _stkt07 , _stkt08 , _stkt09 , _stkt0A , _stkt0B , _stkt0C , _stkt0D , _stkt0E , _stkt0F , _stkt10 , _stkt11 , _stkt12 , _stkt13 , _stkt14 , _stkt15 , _stkt16 , _stkt17 , _stkt18 , _stkt19 , _stkt1A , _stkt1B , _stkt1C , _stkt1D , _stkt1E , _stkt1F (* } !*)  <] .
Proof. auto. Qed.
Axiom ElectorBase_ι_Request_ι_stakeAt_bs' : Z2IBS_pos (tvmBitStringLen ElectorBase_ι_Request_ι_stakeAt_bs_def) ElectorBase_ι_Request_ι_stakeAt = ElectorBase_ι_Request_ι_stakeAt_bs_def.
Lemma ElectorBase_ι_Request_ι_stakeAt_bs : Z2IBS_pos 32 ElectorBase_ι_Request_ι_stakeAt = ElectorBase_ι_Request_ι_stakeAt_bs_def.
Proof.
 rewrite <- ElectorBase_ι_Request_ι_stakeAt_bs'. auto. Qed.
Axiom ElectorBase_ι_Request_ι_stakeAt_pos: (0 <= ElectorBase_ι_Request_ι_stakeAt )%Z.
Axiom ElectorBase_ι_Request_ι_stakeAt_fits: zFitN_pos (tvmBitStringLen ElectorBase_ι_Request_ι_stakeAt_bs_def) ElectorBase_ι_Request_ι_stakeAt = true.
Lemma ElectorBase_ι_Request_ι_stakeAt_bs_rev : I2ZBS_pos' ElectorBase_ι_Request_ι_stakeAt_bs_def = ElectorBase_ι_Request_ι_stakeAt .
Proof.
  prove_bs_rev ElectorBase_ι_Request_ι_stakeAt_bs ElectorBase_ι_Request_ι_stakeAt_pos ElectorBase_ι_Request_ι_stakeAt_fits. 
Qed.
Lemma ElectorBase_ι_Request_ι_stakeAt_bs257 : Z2IN 257 ElectorBase_ι_Request_ι_stakeAt = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    ElectorBase_ι_Request_ι_stakeAt_bs_def)) ElectorBase_ι_Request_ι_stakeAt_bs_def)).
Proof.
  prove_bs_rev ElectorBase_ι_Request_ι_stakeAt_bs_rev ElectorBase_ι_Request_ι_stakeAt_bs_def.
Qed. 
Variables ElectorBase_ι_Request_ι_maxFactor : Z . 
Variables (*! { _mxFc !*) _mxFc00 _mxFc01 _mxFc02 _mxFc03 _mxFc04 _mxFc05 _mxFc06 _mxFc07 _mxFc08 _mxFc09 _mxFc0A _mxFc0B _mxFc0C _mxFc0D _mxFc0E _mxFc0F _mxFc10 _mxFc11 _mxFc12 _mxFc13 _mxFc14 _mxFc15 _mxFc16 _mxFc17 _mxFc18 _mxFc19 _mxFc1A _mxFc1B _mxFc1C _mxFc1D _mxFc1E _mxFc1F  : TVMBit . 
Definition ElectorBase_ι_Request_ι_maxFactor_bs_def := [> _mxFc00 , _mxFc01 , _mxFc02 , _mxFc03 , _mxFc04 , _mxFc05 , _mxFc06 , _mxFc07 , _mxFc08 , _mxFc09 , _mxFc0A , _mxFc0B , _mxFc0C , _mxFc0D , _mxFc0E , _mxFc0F , _mxFc10 , _mxFc11 , _mxFc12 , _mxFc13 , _mxFc14 , _mxFc15 , _mxFc16 , _mxFc17 , _mxFc18 , _mxFc19 , _mxFc1A , _mxFc1B , _mxFc1C , _mxFc1D , _mxFc1E , _mxFc1F <] .
Lemma ElectorBase_ι_Request_ι_maxFactor_bs_id: ElectorBase_ι_Request_ι_maxFactor_bs_def = [> _mxFc00 , _mxFc01 , _mxFc02 , _mxFc03 , _mxFc04 , _mxFc05 , _mxFc06 , _mxFc07 , _mxFc08 , _mxFc09 , _mxFc0A , _mxFc0B , _mxFc0C , _mxFc0D , _mxFc0E , _mxFc0F , _mxFc10 , _mxFc11 , _mxFc12 , _mxFc13 , _mxFc14 , _mxFc15 , _mxFc16 , _mxFc17 , _mxFc18 , _mxFc19 , _mxFc1A , _mxFc1B , _mxFc1C , _mxFc1D , _mxFc1E , _mxFc1F (* } !*)  <] .
Proof. auto. Qed.
Axiom ElectorBase_ι_Request_ι_maxFactor_bs' : Z2IBS_pos (tvmBitStringLen ElectorBase_ι_Request_ι_maxFactor_bs_def) ElectorBase_ι_Request_ι_maxFactor = ElectorBase_ι_Request_ι_maxFactor_bs_def.
Lemma ElectorBase_ι_Request_ι_maxFactor_bs : Z2IBS_pos 32 ElectorBase_ι_Request_ι_maxFactor = ElectorBase_ι_Request_ι_maxFactor_bs_def.
Proof.
 rewrite <- ElectorBase_ι_Request_ι_maxFactor_bs'. auto. Qed.
Axiom ElectorBase_ι_Request_ι_maxFactor_pos: (0 <= ElectorBase_ι_Request_ι_maxFactor )%Z.
Axiom ElectorBase_ι_Request_ι_maxFactor_fits: zFitN_pos (tvmBitStringLen ElectorBase_ι_Request_ι_maxFactor_bs_def) ElectorBase_ι_Request_ι_maxFactor = true.
Lemma ElectorBase_ι_Request_ι_maxFactor_bs_rev : I2ZBS_pos' ElectorBase_ι_Request_ι_maxFactor_bs_def = ElectorBase_ι_Request_ι_maxFactor .
Proof.
  prove_bs_rev ElectorBase_ι_Request_ι_maxFactor_bs ElectorBase_ι_Request_ι_maxFactor_pos ElectorBase_ι_Request_ι_maxFactor_fits. 
Qed.
Lemma ElectorBase_ι_Request_ι_maxFactor_bs257 : Z2IN 257 ElectorBase_ι_Request_ι_maxFactor = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    ElectorBase_ι_Request_ι_maxFactor_bs_def)) ElectorBase_ι_Request_ι_maxFactor_bs_def)).
Proof.
  prove_bs_rev ElectorBase_ι_Request_ι_maxFactor_bs_rev ElectorBase_ι_Request_ι_maxFactor_bs_def.
Qed. 
Variables ElectorBase_ι_Request_ι_adnlAddr : Z . 
Variables (*! { _dnld !*) _dnld00 _dnld01 _dnld02 _dnld03 _dnld04 _dnld05 _dnld06 _dnld07 _dnld08 _dnld09 _dnld0A _dnld0B _dnld0C _dnld0D _dnld0E _dnld0F _dnld10 _dnld11 _dnld12 _dnld13 _dnld14 _dnld15 _dnld16 _dnld17 _dnld18 _dnld19 _dnld1A _dnld1B _dnld1C _dnld1D _dnld1E _dnld1F _dnld20 _dnld21 _dnld22 _dnld23 _dnld24 _dnld25 _dnld26 _dnld27 _dnld28 _dnld29 _dnld2A _dnld2B _dnld2C _dnld2D _dnld2E _dnld2F _dnld30 _dnld31 _dnld32 _dnld33 _dnld34 _dnld35 _dnld36 _dnld37 _dnld38 _dnld39 _dnld3A _dnld3B _dnld3C _dnld3D _dnld3E _dnld3F _dnld40 _dnld41 _dnld42 _dnld43 _dnld44 _dnld45 _dnld46 _dnld47 _dnld48 _dnld49 _dnld4A _dnld4B _dnld4C _dnld4D _dnld4E _dnld4F _dnld50 _dnld51 _dnld52 _dnld53 _dnld54 _dnld55 _dnld56 _dnld57 _dnld58 _dnld59 _dnld5A _dnld5B _dnld5C _dnld5D _dnld5E _dnld5F _dnld60 _dnld61 _dnld62 _dnld63 _dnld64 _dnld65 _dnld66 _dnld67 _dnld68 _dnld69 _dnld6A _dnld6B _dnld6C _dnld6D _dnld6E _dnld6F _dnld70 _dnld71 _dnld72 _dnld73 _dnld74 _dnld75 _dnld76 _dnld77 _dnld78 _dnld79 _dnld7A _dnld7B _dnld7C _dnld7D _dnld7E _dnld7F _dnld80 _dnld81 _dnld82 _dnld83 _dnld84 _dnld85 _dnld86 _dnld87 _dnld88 _dnld89 _dnld8A _dnld8B _dnld8C _dnld8D _dnld8E _dnld8F _dnld90 _dnld91 _dnld92 _dnld93 _dnld94 _dnld95 _dnld96 _dnld97 _dnld98 _dnld99 _dnld9A _dnld9B _dnld9C _dnld9D _dnld9E _dnld9F _dnldA0 _dnldA1 _dnldA2 _dnldA3 _dnldA4 _dnldA5 _dnldA6 _dnldA7 _dnldA8 _dnldA9 _dnldAA _dnldAB _dnldAC _dnldAD _dnldAE _dnldAF _dnldB0 _dnldB1 _dnldB2 _dnldB3 _dnldB4 _dnldB5 _dnldB6 _dnldB7 _dnldB8 _dnldB9 _dnldBA _dnldBB _dnldBC _dnldBD _dnldBE _dnldBF _dnldC0 _dnldC1 _dnldC2 _dnldC3 _dnldC4 _dnldC5 _dnldC6 _dnldC7 _dnldC8 _dnldC9 _dnldCA _dnldCB _dnldCC _dnldCD _dnldCE _dnldCF _dnldD0 _dnldD1 _dnldD2 _dnldD3 _dnldD4 _dnldD5 _dnldD6 _dnldD7 _dnldD8 _dnldD9 _dnldDA _dnldDB _dnldDC _dnldDD _dnldDE _dnldDF _dnldE0 _dnldE1 _dnldE2 _dnldE3 _dnldE4 _dnldE5 _dnldE6 _dnldE7 _dnldE8 _dnldE9 _dnldEA _dnldEB _dnldEC _dnldED _dnldEE _dnldEF _dnldF0 _dnldF1 _dnldF2 _dnldF3 _dnldF4 _dnldF5 _dnldF6 _dnldF7 _dnldF8 _dnldF9 _dnldFA _dnldFB _dnldFC _dnldFD _dnldFE _dnldFF  : TVMBit . 
Definition ElectorBase_ι_Request_ι_adnlAddr_bs_def := [> _dnld00 , _dnld01 , _dnld02 , _dnld03 , _dnld04 , _dnld05 , _dnld06 , _dnld07 , _dnld08 , _dnld09 , _dnld0A , _dnld0B , _dnld0C , _dnld0D , _dnld0E , _dnld0F , _dnld10 , _dnld11 , _dnld12 , _dnld13 , _dnld14 , _dnld15 , _dnld16 , _dnld17 , _dnld18 , _dnld19 , _dnld1A , _dnld1B , _dnld1C , _dnld1D , _dnld1E , _dnld1F , _dnld20 , _dnld21 , _dnld22 , _dnld23 , _dnld24 , _dnld25 , _dnld26 , _dnld27 , _dnld28 , _dnld29 , _dnld2A , _dnld2B , _dnld2C , _dnld2D , _dnld2E , _dnld2F , _dnld30 , _dnld31 , _dnld32 , _dnld33 , _dnld34 , _dnld35 , _dnld36 , _dnld37 , _dnld38 , _dnld39 , _dnld3A , _dnld3B , _dnld3C , _dnld3D , _dnld3E , _dnld3F , _dnld40 , _dnld41 , _dnld42 , _dnld43 , _dnld44 , _dnld45 , _dnld46 , _dnld47 , _dnld48 , _dnld49 , _dnld4A , _dnld4B , _dnld4C , _dnld4D , _dnld4E , _dnld4F , _dnld50 , _dnld51 , _dnld52 , _dnld53 , _dnld54 , _dnld55 , _dnld56 , _dnld57 , _dnld58 , _dnld59 , _dnld5A , _dnld5B , _dnld5C , _dnld5D , _dnld5E , _dnld5F , _dnld60 , _dnld61 , _dnld62 , _dnld63 , _dnld64 , _dnld65 , _dnld66 , _dnld67 , _dnld68 , _dnld69 , _dnld6A , _dnld6B , _dnld6C , _dnld6D , _dnld6E , _dnld6F , _dnld70 , _dnld71 , _dnld72 , _dnld73 , _dnld74 , _dnld75 , _dnld76 , _dnld77 , _dnld78 , _dnld79 , _dnld7A , _dnld7B , _dnld7C , _dnld7D , _dnld7E , _dnld7F , _dnld80 , _dnld81 , _dnld82 , _dnld83 , _dnld84 , _dnld85 , _dnld86 , _dnld87 , _dnld88 , _dnld89 , _dnld8A , _dnld8B , _dnld8C , _dnld8D , _dnld8E , _dnld8F , _dnld90 , _dnld91 , _dnld92 , _dnld93 , _dnld94 , _dnld95 , _dnld96 , _dnld97 , _dnld98 , _dnld99 , _dnld9A , _dnld9B , _dnld9C , _dnld9D , _dnld9E , _dnld9F , _dnldA0 , _dnldA1 , _dnldA2 , _dnldA3 , _dnldA4 , _dnldA5 , _dnldA6 , _dnldA7 , _dnldA8 , _dnldA9 , _dnldAA , _dnldAB , _dnldAC , _dnldAD , _dnldAE , _dnldAF , _dnldB0 , _dnldB1 , _dnldB2 , _dnldB3 , _dnldB4 , _dnldB5 , _dnldB6 , _dnldB7 , _dnldB8 , _dnldB9 , _dnldBA , _dnldBB , _dnldBC , _dnldBD , _dnldBE , _dnldBF , _dnldC0 , _dnldC1 , _dnldC2 , _dnldC3 , _dnldC4 , _dnldC5 , _dnldC6 , _dnldC7 , _dnldC8 , _dnldC9 , _dnldCA , _dnldCB , _dnldCC , _dnldCD , _dnldCE , _dnldCF , _dnldD0 , _dnldD1 , _dnldD2 , _dnldD3 , _dnldD4 , _dnldD5 , _dnldD6 , _dnldD7 , _dnldD8 , _dnldD9 , _dnldDA , _dnldDB , _dnldDC , _dnldDD , _dnldDE , _dnldDF , _dnldE0 , _dnldE1 , _dnldE2 , _dnldE3 , _dnldE4 , _dnldE5 , _dnldE6 , _dnldE7 , _dnldE8 , _dnldE9 , _dnldEA , _dnldEB , _dnldEC , _dnldED , _dnldEE , _dnldEF , _dnldF0 , _dnldF1 , _dnldF2 , _dnldF3 , _dnldF4 , _dnldF5 , _dnldF6 , _dnldF7 , _dnldF8 , _dnldF9 , _dnldFA , _dnldFB , _dnldFC , _dnldFD , _dnldFE , _dnldFF <] .
Lemma ElectorBase_ι_Request_ι_adnlAddr_bs_id: ElectorBase_ι_Request_ι_adnlAddr_bs_def = [> _dnld00 , _dnld01 , _dnld02 , _dnld03 , _dnld04 , _dnld05 , _dnld06 , _dnld07 , _dnld08 , _dnld09 , _dnld0A , _dnld0B , _dnld0C , _dnld0D , _dnld0E , _dnld0F , _dnld10 , _dnld11 , _dnld12 , _dnld13 , _dnld14 , _dnld15 , _dnld16 , _dnld17 , _dnld18 , _dnld19 , _dnld1A , _dnld1B , _dnld1C , _dnld1D , _dnld1E , _dnld1F , _dnld20 , _dnld21 , _dnld22 , _dnld23 , _dnld24 , _dnld25 , _dnld26 , _dnld27 , _dnld28 , _dnld29 , _dnld2A , _dnld2B , _dnld2C , _dnld2D , _dnld2E , _dnld2F , _dnld30 , _dnld31 , _dnld32 , _dnld33 , _dnld34 , _dnld35 , _dnld36 , _dnld37 , _dnld38 , _dnld39 , _dnld3A , _dnld3B , _dnld3C , _dnld3D , _dnld3E , _dnld3F , _dnld40 , _dnld41 , _dnld42 , _dnld43 , _dnld44 , _dnld45 , _dnld46 , _dnld47 , _dnld48 , _dnld49 , _dnld4A , _dnld4B , _dnld4C , _dnld4D , _dnld4E , _dnld4F , _dnld50 , _dnld51 , _dnld52 , _dnld53 , _dnld54 , _dnld55 , _dnld56 , _dnld57 , _dnld58 , _dnld59 , _dnld5A , _dnld5B , _dnld5C , _dnld5D , _dnld5E , _dnld5F , _dnld60 , _dnld61 , _dnld62 , _dnld63 , _dnld64 , _dnld65 , _dnld66 , _dnld67 , _dnld68 , _dnld69 , _dnld6A , _dnld6B , _dnld6C , _dnld6D , _dnld6E , _dnld6F , _dnld70 , _dnld71 , _dnld72 , _dnld73 , _dnld74 , _dnld75 , _dnld76 , _dnld77 , _dnld78 , _dnld79 , _dnld7A , _dnld7B , _dnld7C , _dnld7D , _dnld7E , _dnld7F , _dnld80 , _dnld81 , _dnld82 , _dnld83 , _dnld84 , _dnld85 , _dnld86 , _dnld87 , _dnld88 , _dnld89 , _dnld8A , _dnld8B , _dnld8C , _dnld8D , _dnld8E , _dnld8F , _dnld90 , _dnld91 , _dnld92 , _dnld93 , _dnld94 , _dnld95 , _dnld96 , _dnld97 , _dnld98 , _dnld99 , _dnld9A , _dnld9B , _dnld9C , _dnld9D , _dnld9E , _dnld9F , _dnldA0 , _dnldA1 , _dnldA2 , _dnldA3 , _dnldA4 , _dnldA5 , _dnldA6 , _dnldA7 , _dnldA8 , _dnldA9 , _dnldAA , _dnldAB , _dnldAC , _dnldAD , _dnldAE , _dnldAF , _dnldB0 , _dnldB1 , _dnldB2 , _dnldB3 , _dnldB4 , _dnldB5 , _dnldB6 , _dnldB7 , _dnldB8 , _dnldB9 , _dnldBA , _dnldBB , _dnldBC , _dnldBD , _dnldBE , _dnldBF , _dnldC0 , _dnldC1 , _dnldC2 , _dnldC3 , _dnldC4 , _dnldC5 , _dnldC6 , _dnldC7 , _dnldC8 , _dnldC9 , _dnldCA , _dnldCB , _dnldCC , _dnldCD , _dnldCE , _dnldCF , _dnldD0 , _dnldD1 , _dnldD2 , _dnldD3 , _dnldD4 , _dnldD5 , _dnldD6 , _dnldD7 , _dnldD8 , _dnldD9 , _dnldDA , _dnldDB , _dnldDC , _dnldDD , _dnldDE , _dnldDF , _dnldE0 , _dnldE1 , _dnldE2 , _dnldE3 , _dnldE4 , _dnldE5 , _dnldE6 , _dnldE7 , _dnldE8 , _dnldE9 , _dnldEA , _dnldEB , _dnldEC , _dnldED , _dnldEE , _dnldEF , _dnldF0 , _dnldF1 , _dnldF2 , _dnldF3 , _dnldF4 , _dnldF5 , _dnldF6 , _dnldF7 , _dnldF8 , _dnldF9 , _dnldFA , _dnldFB , _dnldFC , _dnldFD , _dnldFE , _dnldFF (* } !*)  <] .
Proof. auto. Qed.
Axiom ElectorBase_ι_Request_ι_adnlAddr_bs' : Z2IBS_pos (tvmBitStringLen ElectorBase_ι_Request_ι_adnlAddr_bs_def) ElectorBase_ι_Request_ι_adnlAddr = ElectorBase_ι_Request_ι_adnlAddr_bs_def.
Lemma ElectorBase_ι_Request_ι_adnlAddr_bs : Z2IBS_pos 256 ElectorBase_ι_Request_ι_adnlAddr = ElectorBase_ι_Request_ι_adnlAddr_bs_def.
Proof.
 rewrite <- ElectorBase_ι_Request_ι_adnlAddr_bs'. auto. Qed.
Axiom ElectorBase_ι_Request_ι_adnlAddr_pos: (0 <= ElectorBase_ι_Request_ι_adnlAddr )%Z.
Axiom ElectorBase_ι_Request_ι_adnlAddr_fits: zFitN_pos (tvmBitStringLen ElectorBase_ι_Request_ι_adnlAddr_bs_def) ElectorBase_ι_Request_ι_adnlAddr = true.
Lemma ElectorBase_ι_Request_ι_adnlAddr_bs_rev : I2ZBS_pos' ElectorBase_ι_Request_ι_adnlAddr_bs_def = ElectorBase_ι_Request_ι_adnlAddr .
Proof.
  prove_bs_rev ElectorBase_ι_Request_ι_adnlAddr_bs ElectorBase_ι_Request_ι_adnlAddr_pos ElectorBase_ι_Request_ι_adnlAddr_fits. 
Qed.
Lemma ElectorBase_ι_Request_ι_adnlAddr_bs257 : Z2IN 257 ElectorBase_ι_Request_ι_adnlAddr = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    ElectorBase_ι_Request_ι_adnlAddr_bs_def)) ElectorBase_ι_Request_ι_adnlAddr_bs_def)).
Proof.
  prove_bs_rev ElectorBase_ι_Request_ι_adnlAddr_bs_rev ElectorBase_ι_Request_ι_adnlAddr_bs_def.
Qed. 
Variables ElectorBase_ι_Request_ι_signature : Z . 
Variables (*! { _sgnt !*) _sgnt00 _sgnt01 _sgnt02 _sgnt03 _sgnt04 _sgnt05 _sgnt06 _sgnt07  : TVMBit . 
Definition ElectorBase_ι_Request_ι_signature_bs_def := [> _sgnt00 , _sgnt01 , _sgnt02 , _sgnt03 , _sgnt04 , _sgnt05 , _sgnt06 , _sgnt07 <] .
Lemma ElectorBase_ι_Request_ι_signature_bs_id: ElectorBase_ι_Request_ι_signature_bs_def = [> _sgnt00 , _sgnt01 , _sgnt02 , _sgnt03 , _sgnt04 , _sgnt05 , _sgnt06 , _sgnt07 (* } !*)  <] .
Proof. auto. Qed.
Axiom ElectorBase_ι_Request_ι_signature_bs' : Z2IBS_pos (tvmBitStringLen ElectorBase_ι_Request_ι_signature_bs_def) ElectorBase_ι_Request_ι_signature = ElectorBase_ι_Request_ι_signature_bs_def.
Lemma ElectorBase_ι_Request_ι_signature_bs : Z2IBS_pos 8 ElectorBase_ι_Request_ι_signature = ElectorBase_ι_Request_ι_signature_bs_def.
Proof.
 rewrite <- ElectorBase_ι_Request_ι_signature_bs'. auto. Qed.
Axiom ElectorBase_ι_Request_ι_signature_pos: (0 <= ElectorBase_ι_Request_ι_signature )%Z.
Axiom ElectorBase_ι_Request_ι_signature_fits: zFitN_pos (tvmBitStringLen ElectorBase_ι_Request_ι_signature_bs_def) ElectorBase_ι_Request_ι_signature = true.
Lemma ElectorBase_ι_Request_ι_signature_bs_rev : I2ZBS_pos' ElectorBase_ι_Request_ι_signature_bs_def = ElectorBase_ι_Request_ι_signature .
Proof.
  prove_bs_rev ElectorBase_ι_Request_ι_signature_bs ElectorBase_ι_Request_ι_signature_pos ElectorBase_ι_Request_ι_signature_fits. 
Qed.
Lemma ElectorBase_ι_Request_ι_signature_bs257 : Z2IN 257 ElectorBase_ι_Request_ι_signature = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    ElectorBase_ι_Request_ι_signature_bs_def)) ElectorBase_ι_Request_ι_signature_bs_def)).
Proof.
  prove_bs_rev ElectorBase_ι_Request_ι_signature_bs_rev ElectorBase_ι_Request_ι_signature_bs_def.
Qed.

Variables ElectionParams_ι_ValidatorDescr73_ι_validator_addr73 : Z . 
Variables (*! { _vldt !*) _vldt00 _vldt01 _vldt02 _vldt03 _vldt04 _vldt05 _vldt06 _vldt07  : TVMBit . 
Definition ElectionParams_ι_ValidatorDescr73_ι_validator_addr73_bs_def := [> _vldt00 , _vldt01 , _vldt02 , _vldt03 , _vldt04 , _vldt05 , _vldt06 , _vldt07 <] .
Lemma ElectionParams_ι_ValidatorDescr73_ι_validator_addr73_bs_id: ElectionParams_ι_ValidatorDescr73_ι_validator_addr73_bs_def = [> _vldt00 , _vldt01 , _vldt02 , _vldt03 , _vldt04 , _vldt05 , _vldt06 , _vldt07 (* } !*)  <] .
Proof. auto. Qed.
Axiom ElectionParams_ι_ValidatorDescr73_ι_validator_addr73_bs' : Z2IBS_pos (tvmBitStringLen ElectionParams_ι_ValidatorDescr73_ι_validator_addr73_bs_def) ElectionParams_ι_ValidatorDescr73_ι_validator_addr73 = ElectionParams_ι_ValidatorDescr73_ι_validator_addr73_bs_def.
Lemma ElectionParams_ι_ValidatorDescr73_ι_validator_addr73_bs : Z2IBS_pos 8 ElectionParams_ι_ValidatorDescr73_ι_validator_addr73 = ElectionParams_ι_ValidatorDescr73_ι_validator_addr73_bs_def.
Proof.
 rewrite <- ElectionParams_ι_ValidatorDescr73_ι_validator_addr73_bs'. auto. Qed.
Axiom ElectionParams_ι_ValidatorDescr73_ι_validator_addr73_pos: (0 <= ElectionParams_ι_ValidatorDescr73_ι_validator_addr73 )%Z.
Axiom ElectionParams_ι_ValidatorDescr73_ι_validator_addr73_fits: zFitN_pos (tvmBitStringLen ElectionParams_ι_ValidatorDescr73_ι_validator_addr73_bs_def) ElectionParams_ι_ValidatorDescr73_ι_validator_addr73 = true.
Lemma ElectionParams_ι_ValidatorDescr73_ι_validator_addr73_bs_rev : I2ZBS_pos' ElectionParams_ι_ValidatorDescr73_ι_validator_addr73_bs_def = ElectionParams_ι_ValidatorDescr73_ι_validator_addr73 .
Proof.
  prove_bs_rev ElectionParams_ι_ValidatorDescr73_ι_validator_addr73_bs ElectionParams_ι_ValidatorDescr73_ι_validator_addr73_pos ElectionParams_ι_ValidatorDescr73_ι_validator_addr73_fits. 
Qed.
Lemma ElectionParams_ι_ValidatorDescr73_ι_validator_addr73_bs257 : Z2IN 257 ElectionParams_ι_ValidatorDescr73_ι_validator_addr73 = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    ElectionParams_ι_ValidatorDescr73_ι_validator_addr73_bs_def)) ElectionParams_ι_ValidatorDescr73_ι_validator_addr73_bs_def)).
Proof.
  prove_bs_rev ElectionParams_ι_ValidatorDescr73_ι_validator_addr73_bs_rev ElectionParams_ι_ValidatorDescr73_ι_validator_addr73_bs_def.
Qed. 
Variables ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey : Z . 
Variables (*! { _d255 !*) _d25500 _d25501 _d25502 _d25503 _d25504 _d25505 _d25506 _d25507 _d25508 _d25509 _d2550A _d2550B _d2550C _d2550D _d2550E _d2550F _d25510 _d25511 _d25512 _d25513 _d25514 _d25515 _d25516 _d25517 _d25518 _d25519 _d2551A _d2551B _d2551C _d2551D _d2551E _d2551F  : TVMBit . 
Definition ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey_bs_def := [> _d25500 , _d25501 , _d25502 , _d25503 , _d25504 , _d25505 , _d25506 , _d25507 , _d25508 , _d25509 , _d2550A , _d2550B , _d2550C , _d2550D , _d2550E , _d2550F , _d25510 , _d25511 , _d25512 , _d25513 , _d25514 , _d25515 , _d25516 , _d25517 , _d25518 , _d25519 , _d2551A , _d2551B , _d2551C , _d2551D , _d2551E , _d2551F <] .
Lemma ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey_bs_id: ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey_bs_def = [> _d25500 , _d25501 , _d25502 , _d25503 , _d25504 , _d25505 , _d25506 , _d25507 , _d25508 , _d25509 , _d2550A , _d2550B , _d2550C , _d2550D , _d2550E , _d2550F , _d25510 , _d25511 , _d25512 , _d25513 , _d25514 , _d25515 , _d25516 , _d25517 , _d25518 , _d25519 , _d2551A , _d2551B , _d2551C , _d2551D , _d2551E , _d2551F (* } !*)  <] .
Proof. auto. Qed.
Axiom ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey_bs' : Z2IBS_pos (tvmBitStringLen ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey_bs_def) ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey = ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey_bs_def.
Lemma ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey_bs : Z2IBS_pos 32 ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey = ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey_bs_def.
Proof.
 rewrite <- ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey_bs'. auto. Qed.
Axiom ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey_pos: (0 <= ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey )%Z.
Axiom ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey_fits: zFitN_pos (tvmBitStringLen ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey_bs_def) ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey = true.
Lemma ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey_bs_rev : I2ZBS_pos' ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey_bs_def = ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey .
Proof.
  prove_bs_rev ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey_bs ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey_pos ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey_fits. 
Qed.
Lemma ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey_bs257 : Z2IN 257 ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey_bs_def)) ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey_bs_def)).
Proof.
  prove_bs_rev ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey_bs_rev ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey_bs_def.
Qed. 
Variables ElectionParams_ι_ValidatorDescr73_ι_pubkey : Z . 
Variables (*! { _pbk !*) _pbk00 _pbk01 _pbk02 _pbk03 _pbk04 _pbk05 _pbk06 _pbk07 _pbk08 _pbk09 _pbk0A _pbk0B _pbk0C _pbk0D _pbk0E _pbk0F _pbk10 _pbk11 _pbk12 _pbk13 _pbk14 _pbk15 _pbk16 _pbk17 _pbk18 _pbk19 _pbk1A _pbk1B _pbk1C _pbk1D _pbk1E _pbk1F _pbk20 _pbk21 _pbk22 _pbk23 _pbk24 _pbk25 _pbk26 _pbk27 _pbk28 _pbk29 _pbk2A _pbk2B _pbk2C _pbk2D _pbk2E _pbk2F _pbk30 _pbk31 _pbk32 _pbk33 _pbk34 _pbk35 _pbk36 _pbk37 _pbk38 _pbk39 _pbk3A _pbk3B _pbk3C _pbk3D _pbk3E _pbk3F _pbk40 _pbk41 _pbk42 _pbk43 _pbk44 _pbk45 _pbk46 _pbk47 _pbk48 _pbk49 _pbk4A _pbk4B _pbk4C _pbk4D _pbk4E _pbk4F _pbk50 _pbk51 _pbk52 _pbk53 _pbk54 _pbk55 _pbk56 _pbk57 _pbk58 _pbk59 _pbk5A _pbk5B _pbk5C _pbk5D _pbk5E _pbk5F _pbk60 _pbk61 _pbk62 _pbk63 _pbk64 _pbk65 _pbk66 _pbk67 _pbk68 _pbk69 _pbk6A _pbk6B _pbk6C _pbk6D _pbk6E _pbk6F _pbk70 _pbk71 _pbk72 _pbk73 _pbk74 _pbk75 _pbk76 _pbk77 _pbk78 _pbk79 _pbk7A _pbk7B _pbk7C _pbk7D _pbk7E _pbk7F _pbk80 _pbk81 _pbk82 _pbk83 _pbk84 _pbk85 _pbk86 _pbk87 _pbk88 _pbk89 _pbk8A _pbk8B _pbk8C _pbk8D _pbk8E _pbk8F _pbk90 _pbk91 _pbk92 _pbk93 _pbk94 _pbk95 _pbk96 _pbk97 _pbk98 _pbk99 _pbk9A _pbk9B _pbk9C _pbk9D _pbk9E _pbk9F _pbkA0 _pbkA1 _pbkA2 _pbkA3 _pbkA4 _pbkA5 _pbkA6 _pbkA7 _pbkA8 _pbkA9 _pbkAA _pbkAB _pbkAC _pbkAD _pbkAE _pbkAF _pbkB0 _pbkB1 _pbkB2 _pbkB3 _pbkB4 _pbkB5 _pbkB6 _pbkB7 _pbkB8 _pbkB9 _pbkBA _pbkBB _pbkBC _pbkBD _pbkBE _pbkBF _pbkC0 _pbkC1 _pbkC2 _pbkC3 _pbkC4 _pbkC5 _pbkC6 _pbkC7 _pbkC8 _pbkC9 _pbkCA _pbkCB _pbkCC _pbkCD _pbkCE _pbkCF _pbkD0 _pbkD1 _pbkD2 _pbkD3 _pbkD4 _pbkD5 _pbkD6 _pbkD7 _pbkD8 _pbkD9 _pbkDA _pbkDB _pbkDC _pbkDD _pbkDE _pbkDF _pbkE0 _pbkE1 _pbkE2 _pbkE3 _pbkE4 _pbkE5 _pbkE6 _pbkE7 _pbkE8 _pbkE9 _pbkEA _pbkEB _pbkEC _pbkED _pbkEE _pbkEF _pbkF0 _pbkF1 _pbkF2 _pbkF3 _pbkF4 _pbkF5 _pbkF6 _pbkF7 _pbkF8 _pbkF9 _pbkFA _pbkFB _pbkFC _pbkFD _pbkFE _pbkFF  : TVMBit . 
Definition ElectionParams_ι_ValidatorDescr73_ι_pubkey_bs_def := [> _pbk00 , _pbk01 , _pbk02 , _pbk03 , _pbk04 , _pbk05 , _pbk06 , _pbk07 , _pbk08 , _pbk09 , _pbk0A , _pbk0B , _pbk0C , _pbk0D , _pbk0E , _pbk0F , _pbk10 , _pbk11 , _pbk12 , _pbk13 , _pbk14 , _pbk15 , _pbk16 , _pbk17 , _pbk18 , _pbk19 , _pbk1A , _pbk1B , _pbk1C , _pbk1D , _pbk1E , _pbk1F , _pbk20 , _pbk21 , _pbk22 , _pbk23 , _pbk24 , _pbk25 , _pbk26 , _pbk27 , _pbk28 , _pbk29 , _pbk2A , _pbk2B , _pbk2C , _pbk2D , _pbk2E , _pbk2F , _pbk30 , _pbk31 , _pbk32 , _pbk33 , _pbk34 , _pbk35 , _pbk36 , _pbk37 , _pbk38 , _pbk39 , _pbk3A , _pbk3B , _pbk3C , _pbk3D , _pbk3E , _pbk3F , _pbk40 , _pbk41 , _pbk42 , _pbk43 , _pbk44 , _pbk45 , _pbk46 , _pbk47 , _pbk48 , _pbk49 , _pbk4A , _pbk4B , _pbk4C , _pbk4D , _pbk4E , _pbk4F , _pbk50 , _pbk51 , _pbk52 , _pbk53 , _pbk54 , _pbk55 , _pbk56 , _pbk57 , _pbk58 , _pbk59 , _pbk5A , _pbk5B , _pbk5C , _pbk5D , _pbk5E , _pbk5F , _pbk60 , _pbk61 , _pbk62 , _pbk63 , _pbk64 , _pbk65 , _pbk66 , _pbk67 , _pbk68 , _pbk69 , _pbk6A , _pbk6B , _pbk6C , _pbk6D , _pbk6E , _pbk6F , _pbk70 , _pbk71 , _pbk72 , _pbk73 , _pbk74 , _pbk75 , _pbk76 , _pbk77 , _pbk78 , _pbk79 , _pbk7A , _pbk7B , _pbk7C , _pbk7D , _pbk7E , _pbk7F , _pbk80 , _pbk81 , _pbk82 , _pbk83 , _pbk84 , _pbk85 , _pbk86 , _pbk87 , _pbk88 , _pbk89 , _pbk8A , _pbk8B , _pbk8C , _pbk8D , _pbk8E , _pbk8F , _pbk90 , _pbk91 , _pbk92 , _pbk93 , _pbk94 , _pbk95 , _pbk96 , _pbk97 , _pbk98 , _pbk99 , _pbk9A , _pbk9B , _pbk9C , _pbk9D , _pbk9E , _pbk9F , _pbkA0 , _pbkA1 , _pbkA2 , _pbkA3 , _pbkA4 , _pbkA5 , _pbkA6 , _pbkA7 , _pbkA8 , _pbkA9 , _pbkAA , _pbkAB , _pbkAC , _pbkAD , _pbkAE , _pbkAF , _pbkB0 , _pbkB1 , _pbkB2 , _pbkB3 , _pbkB4 , _pbkB5 , _pbkB6 , _pbkB7 , _pbkB8 , _pbkB9 , _pbkBA , _pbkBB , _pbkBC , _pbkBD , _pbkBE , _pbkBF , _pbkC0 , _pbkC1 , _pbkC2 , _pbkC3 , _pbkC4 , _pbkC5 , _pbkC6 , _pbkC7 , _pbkC8 , _pbkC9 , _pbkCA , _pbkCB , _pbkCC , _pbkCD , _pbkCE , _pbkCF , _pbkD0 , _pbkD1 , _pbkD2 , _pbkD3 , _pbkD4 , _pbkD5 , _pbkD6 , _pbkD7 , _pbkD8 , _pbkD9 , _pbkDA , _pbkDB , _pbkDC , _pbkDD , _pbkDE , _pbkDF , _pbkE0 , _pbkE1 , _pbkE2 , _pbkE3 , _pbkE4 , _pbkE5 , _pbkE6 , _pbkE7 , _pbkE8 , _pbkE9 , _pbkEA , _pbkEB , _pbkEC , _pbkED , _pbkEE , _pbkEF , _pbkF0 , _pbkF1 , _pbkF2 , _pbkF3 , _pbkF4 , _pbkF5 , _pbkF6 , _pbkF7 , _pbkF8 , _pbkF9 , _pbkFA , _pbkFB , _pbkFC , _pbkFD , _pbkFE , _pbkFF <] .
Lemma ElectionParams_ι_ValidatorDescr73_ι_pubkey_bs_id: ElectionParams_ι_ValidatorDescr73_ι_pubkey_bs_def = [> _pbk00 , _pbk01 , _pbk02 , _pbk03 , _pbk04 , _pbk05 , _pbk06 , _pbk07 , _pbk08 , _pbk09 , _pbk0A , _pbk0B , _pbk0C , _pbk0D , _pbk0E , _pbk0F , _pbk10 , _pbk11 , _pbk12 , _pbk13 , _pbk14 , _pbk15 , _pbk16 , _pbk17 , _pbk18 , _pbk19 , _pbk1A , _pbk1B , _pbk1C , _pbk1D , _pbk1E , _pbk1F , _pbk20 , _pbk21 , _pbk22 , _pbk23 , _pbk24 , _pbk25 , _pbk26 , _pbk27 , _pbk28 , _pbk29 , _pbk2A , _pbk2B , _pbk2C , _pbk2D , _pbk2E , _pbk2F , _pbk30 , _pbk31 , _pbk32 , _pbk33 , _pbk34 , _pbk35 , _pbk36 , _pbk37 , _pbk38 , _pbk39 , _pbk3A , _pbk3B , _pbk3C , _pbk3D , _pbk3E , _pbk3F , _pbk40 , _pbk41 , _pbk42 , _pbk43 , _pbk44 , _pbk45 , _pbk46 , _pbk47 , _pbk48 , _pbk49 , _pbk4A , _pbk4B , _pbk4C , _pbk4D , _pbk4E , _pbk4F , _pbk50 , _pbk51 , _pbk52 , _pbk53 , _pbk54 , _pbk55 , _pbk56 , _pbk57 , _pbk58 , _pbk59 , _pbk5A , _pbk5B , _pbk5C , _pbk5D , _pbk5E , _pbk5F , _pbk60 , _pbk61 , _pbk62 , _pbk63 , _pbk64 , _pbk65 , _pbk66 , _pbk67 , _pbk68 , _pbk69 , _pbk6A , _pbk6B , _pbk6C , _pbk6D , _pbk6E , _pbk6F , _pbk70 , _pbk71 , _pbk72 , _pbk73 , _pbk74 , _pbk75 , _pbk76 , _pbk77 , _pbk78 , _pbk79 , _pbk7A , _pbk7B , _pbk7C , _pbk7D , _pbk7E , _pbk7F , _pbk80 , _pbk81 , _pbk82 , _pbk83 , _pbk84 , _pbk85 , _pbk86 , _pbk87 , _pbk88 , _pbk89 , _pbk8A , _pbk8B , _pbk8C , _pbk8D , _pbk8E , _pbk8F , _pbk90 , _pbk91 , _pbk92 , _pbk93 , _pbk94 , _pbk95 , _pbk96 , _pbk97 , _pbk98 , _pbk99 , _pbk9A , _pbk9B , _pbk9C , _pbk9D , _pbk9E , _pbk9F , _pbkA0 , _pbkA1 , _pbkA2 , _pbkA3 , _pbkA4 , _pbkA5 , _pbkA6 , _pbkA7 , _pbkA8 , _pbkA9 , _pbkAA , _pbkAB , _pbkAC , _pbkAD , _pbkAE , _pbkAF , _pbkB0 , _pbkB1 , _pbkB2 , _pbkB3 , _pbkB4 , _pbkB5 , _pbkB6 , _pbkB7 , _pbkB8 , _pbkB9 , _pbkBA , _pbkBB , _pbkBC , _pbkBD , _pbkBE , _pbkBF , _pbkC0 , _pbkC1 , _pbkC2 , _pbkC3 , _pbkC4 , _pbkC5 , _pbkC6 , _pbkC7 , _pbkC8 , _pbkC9 , _pbkCA , _pbkCB , _pbkCC , _pbkCD , _pbkCE , _pbkCF , _pbkD0 , _pbkD1 , _pbkD2 , _pbkD3 , _pbkD4 , _pbkD5 , _pbkD6 , _pbkD7 , _pbkD8 , _pbkD9 , _pbkDA , _pbkDB , _pbkDC , _pbkDD , _pbkDE , _pbkDF , _pbkE0 , _pbkE1 , _pbkE2 , _pbkE3 , _pbkE4 , _pbkE5 , _pbkE6 , _pbkE7 , _pbkE8 , _pbkE9 , _pbkEA , _pbkEB , _pbkEC , _pbkED , _pbkEE , _pbkEF , _pbkF0 , _pbkF1 , _pbkF2 , _pbkF3 , _pbkF4 , _pbkF5 , _pbkF6 , _pbkF7 , _pbkF8 , _pbkF9 , _pbkFA , _pbkFB , _pbkFC , _pbkFD , _pbkFE , _pbkFF (* } !*)  <] .
Proof. auto. Qed.
Axiom ElectionParams_ι_ValidatorDescr73_ι_pubkey_bs' : Z2IBS_pos (tvmBitStringLen ElectionParams_ι_ValidatorDescr73_ι_pubkey_bs_def) ElectionParams_ι_ValidatorDescr73_ι_pubkey = ElectionParams_ι_ValidatorDescr73_ι_pubkey_bs_def.
Lemma ElectionParams_ι_ValidatorDescr73_ι_pubkey_bs : Z2IBS_pos 256 ElectionParams_ι_ValidatorDescr73_ι_pubkey = ElectionParams_ι_ValidatorDescr73_ι_pubkey_bs_def.
Proof.
 rewrite <- ElectionParams_ι_ValidatorDescr73_ι_pubkey_bs'. auto. Qed.
Axiom ElectionParams_ι_ValidatorDescr73_ι_pubkey_pos: (0 <= ElectionParams_ι_ValidatorDescr73_ι_pubkey )%Z.
Axiom ElectionParams_ι_ValidatorDescr73_ι_pubkey_fits: zFitN_pos (tvmBitStringLen ElectionParams_ι_ValidatorDescr73_ι_pubkey_bs_def) ElectionParams_ι_ValidatorDescr73_ι_pubkey = true.
Lemma ElectionParams_ι_ValidatorDescr73_ι_pubkey_bs_rev : I2ZBS_pos' ElectionParams_ι_ValidatorDescr73_ι_pubkey_bs_def = ElectionParams_ι_ValidatorDescr73_ι_pubkey .
Proof.
  prove_bs_rev ElectionParams_ι_ValidatorDescr73_ι_pubkey_bs ElectionParams_ι_ValidatorDescr73_ι_pubkey_pos ElectionParams_ι_ValidatorDescr73_ι_pubkey_fits. 
Qed.
Lemma ElectionParams_ι_ValidatorDescr73_ι_pubkey_bs257 : Z2IN 257 ElectionParams_ι_ValidatorDescr73_ι_pubkey = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    ElectionParams_ι_ValidatorDescr73_ι_pubkey_bs_def)) ElectionParams_ι_ValidatorDescr73_ι_pubkey_bs_def)).
Proof.
  prove_bs_rev ElectionParams_ι_ValidatorDescr73_ι_pubkey_bs_rev ElectionParams_ι_ValidatorDescr73_ι_pubkey_bs_def.
Qed. 
Variables ElectionParams_ι_ValidatorDescr73_ι_weight : Z . 
Variables (*! { _wght !*) _wght00 _wght01 _wght02 _wght03 _wght04 _wght05 _wght06 _wght07 _wght08 _wght09 _wght0A _wght0B _wght0C _wght0D _wght0E _wght0F _wght10 _wght11 _wght12 _wght13 _wght14 _wght15 _wght16 _wght17 _wght18 _wght19 _wght1A _wght1B _wght1C _wght1D _wght1E _wght1F _wght20 _wght21 _wght22 _wght23 _wght24 _wght25 _wght26 _wght27 _wght28 _wght29 _wght2A _wght2B _wght2C _wght2D _wght2E _wght2F _wght30 _wght31 _wght32 _wght33 _wght34 _wght35 _wght36 _wght37 _wght38 _wght39 _wght3A _wght3B _wght3C _wght3D _wght3E _wght3F  : TVMBit . 
Definition ElectionParams_ι_ValidatorDescr73_ι_weight_bs_def := [> _wght00 , _wght01 , _wght02 , _wght03 , _wght04 , _wght05 , _wght06 , _wght07 , _wght08 , _wght09 , _wght0A , _wght0B , _wght0C , _wght0D , _wght0E , _wght0F , _wght10 , _wght11 , _wght12 , _wght13 , _wght14 , _wght15 , _wght16 , _wght17 , _wght18 , _wght19 , _wght1A , _wght1B , _wght1C , _wght1D , _wght1E , _wght1F , _wght20 , _wght21 , _wght22 , _wght23 , _wght24 , _wght25 , _wght26 , _wght27 , _wght28 , _wght29 , _wght2A , _wght2B , _wght2C , _wght2D , _wght2E , _wght2F , _wght30 , _wght31 , _wght32 , _wght33 , _wght34 , _wght35 , _wght36 , _wght37 , _wght38 , _wght39 , _wght3A , _wght3B , _wght3C , _wght3D , _wght3E , _wght3F <] .
Lemma ElectionParams_ι_ValidatorDescr73_ι_weight_bs_id: ElectionParams_ι_ValidatorDescr73_ι_weight_bs_def = [> _wght00 , _wght01 , _wght02 , _wght03 , _wght04 , _wght05 , _wght06 , _wght07 , _wght08 , _wght09 , _wght0A , _wght0B , _wght0C , _wght0D , _wght0E , _wght0F , _wght10 , _wght11 , _wght12 , _wght13 , _wght14 , _wght15 , _wght16 , _wght17 , _wght18 , _wght19 , _wght1A , _wght1B , _wght1C , _wght1D , _wght1E , _wght1F , _wght20 , _wght21 , _wght22 , _wght23 , _wght24 , _wght25 , _wght26 , _wght27 , _wght28 , _wght29 , _wght2A , _wght2B , _wght2C , _wght2D , _wght2E , _wght2F , _wght30 , _wght31 , _wght32 , _wght33 , _wght34 , _wght35 , _wght36 , _wght37 , _wght38 , _wght39 , _wght3A , _wght3B , _wght3C , _wght3D , _wght3E , _wght3F (* } !*)  <] .
Proof. auto. Qed.
Axiom ElectionParams_ι_ValidatorDescr73_ι_weight_bs' : Z2IBS_pos (tvmBitStringLen ElectionParams_ι_ValidatorDescr73_ι_weight_bs_def) ElectionParams_ι_ValidatorDescr73_ι_weight = ElectionParams_ι_ValidatorDescr73_ι_weight_bs_def.
Lemma ElectionParams_ι_ValidatorDescr73_ι_weight_bs : Z2IBS_pos 64 ElectionParams_ι_ValidatorDescr73_ι_weight = ElectionParams_ι_ValidatorDescr73_ι_weight_bs_def.
Proof.
 rewrite <- ElectionParams_ι_ValidatorDescr73_ι_weight_bs'. auto. Qed.
Axiom ElectionParams_ι_ValidatorDescr73_ι_weight_pos: (0 <= ElectionParams_ι_ValidatorDescr73_ι_weight )%Z.
Axiom ElectionParams_ι_ValidatorDescr73_ι_weight_fits: zFitN_pos (tvmBitStringLen ElectionParams_ι_ValidatorDescr73_ι_weight_bs_def) ElectionParams_ι_ValidatorDescr73_ι_weight = true.
Lemma ElectionParams_ι_ValidatorDescr73_ι_weight_bs_rev : I2ZBS_pos' ElectionParams_ι_ValidatorDescr73_ι_weight_bs_def = ElectionParams_ι_ValidatorDescr73_ι_weight .
Proof.
  prove_bs_rev ElectionParams_ι_ValidatorDescr73_ι_weight_bs ElectionParams_ι_ValidatorDescr73_ι_weight_pos ElectionParams_ι_ValidatorDescr73_ι_weight_fits. 
Qed.
Lemma ElectionParams_ι_ValidatorDescr73_ι_weight_bs257 : Z2IN 257 ElectionParams_ι_ValidatorDescr73_ι_weight = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    ElectionParams_ι_ValidatorDescr73_ι_weight_bs_def)) ElectionParams_ι_ValidatorDescr73_ι_weight_bs_def)).
Proof.
  prove_bs_rev ElectionParams_ι_ValidatorDescr73_ι_weight_bs_rev ElectionParams_ι_ValidatorDescr73_ι_weight_bs_def.
Qed. 
Variables ElectionParams_ι_ValidatorDescr73_ι_adnl_addr : Z . 
Variables (*! { _dnl_ !*) _dnl_00 _dnl_01 _dnl_02 _dnl_03 _dnl_04 _dnl_05 _dnl_06 _dnl_07 _dnl_08 _dnl_09 _dnl_0A _dnl_0B _dnl_0C _dnl_0D _dnl_0E _dnl_0F _dnl_10 _dnl_11 _dnl_12 _dnl_13 _dnl_14 _dnl_15 _dnl_16 _dnl_17 _dnl_18 _dnl_19 _dnl_1A _dnl_1B _dnl_1C _dnl_1D _dnl_1E _dnl_1F _dnl_20 _dnl_21 _dnl_22 _dnl_23 _dnl_24 _dnl_25 _dnl_26 _dnl_27 _dnl_28 _dnl_29 _dnl_2A _dnl_2B _dnl_2C _dnl_2D _dnl_2E _dnl_2F _dnl_30 _dnl_31 _dnl_32 _dnl_33 _dnl_34 _dnl_35 _dnl_36 _dnl_37 _dnl_38 _dnl_39 _dnl_3A _dnl_3B _dnl_3C _dnl_3D _dnl_3E _dnl_3F _dnl_40 _dnl_41 _dnl_42 _dnl_43 _dnl_44 _dnl_45 _dnl_46 _dnl_47 _dnl_48 _dnl_49 _dnl_4A _dnl_4B _dnl_4C _dnl_4D _dnl_4E _dnl_4F _dnl_50 _dnl_51 _dnl_52 _dnl_53 _dnl_54 _dnl_55 _dnl_56 _dnl_57 _dnl_58 _dnl_59 _dnl_5A _dnl_5B _dnl_5C _dnl_5D _dnl_5E _dnl_5F _dnl_60 _dnl_61 _dnl_62 _dnl_63 _dnl_64 _dnl_65 _dnl_66 _dnl_67 _dnl_68 _dnl_69 _dnl_6A _dnl_6B _dnl_6C _dnl_6D _dnl_6E _dnl_6F _dnl_70 _dnl_71 _dnl_72 _dnl_73 _dnl_74 _dnl_75 _dnl_76 _dnl_77 _dnl_78 _dnl_79 _dnl_7A _dnl_7B _dnl_7C _dnl_7D _dnl_7E _dnl_7F _dnl_80 _dnl_81 _dnl_82 _dnl_83 _dnl_84 _dnl_85 _dnl_86 _dnl_87 _dnl_88 _dnl_89 _dnl_8A _dnl_8B _dnl_8C _dnl_8D _dnl_8E _dnl_8F _dnl_90 _dnl_91 _dnl_92 _dnl_93 _dnl_94 _dnl_95 _dnl_96 _dnl_97 _dnl_98 _dnl_99 _dnl_9A _dnl_9B _dnl_9C _dnl_9D _dnl_9E _dnl_9F _dnl_A0 _dnl_A1 _dnl_A2 _dnl_A3 _dnl_A4 _dnl_A5 _dnl_A6 _dnl_A7 _dnl_A8 _dnl_A9 _dnl_AA _dnl_AB _dnl_AC _dnl_AD _dnl_AE _dnl_AF _dnl_B0 _dnl_B1 _dnl_B2 _dnl_B3 _dnl_B4 _dnl_B5 _dnl_B6 _dnl_B7 _dnl_B8 _dnl_B9 _dnl_BA _dnl_BB _dnl_BC _dnl_BD _dnl_BE _dnl_BF _dnl_C0 _dnl_C1 _dnl_C2 _dnl_C3 _dnl_C4 _dnl_C5 _dnl_C6 _dnl_C7 _dnl_C8 _dnl_C9 _dnl_CA _dnl_CB _dnl_CC _dnl_CD _dnl_CE _dnl_CF _dnl_D0 _dnl_D1 _dnl_D2 _dnl_D3 _dnl_D4 _dnl_D5 _dnl_D6 _dnl_D7 _dnl_D8 _dnl_D9 _dnl_DA _dnl_DB _dnl_DC _dnl_DD _dnl_DE _dnl_DF _dnl_E0 _dnl_E1 _dnl_E2 _dnl_E3 _dnl_E4 _dnl_E5 _dnl_E6 _dnl_E7 _dnl_E8 _dnl_E9 _dnl_EA _dnl_EB _dnl_EC _dnl_ED _dnl_EE _dnl_EF _dnl_F0 _dnl_F1 _dnl_F2 _dnl_F3 _dnl_F4 _dnl_F5 _dnl_F6 _dnl_F7 _dnl_F8 _dnl_F9 _dnl_FA _dnl_FB _dnl_FC _dnl_FD _dnl_FE _dnl_FF  : TVMBit . 
Definition ElectionParams_ι_ValidatorDescr73_ι_adnl_addr_bs_def := [> _dnl_00 , _dnl_01 , _dnl_02 , _dnl_03 , _dnl_04 , _dnl_05 , _dnl_06 , _dnl_07 , _dnl_08 , _dnl_09 , _dnl_0A , _dnl_0B , _dnl_0C , _dnl_0D , _dnl_0E , _dnl_0F , _dnl_10 , _dnl_11 , _dnl_12 , _dnl_13 , _dnl_14 , _dnl_15 , _dnl_16 , _dnl_17 , _dnl_18 , _dnl_19 , _dnl_1A , _dnl_1B , _dnl_1C , _dnl_1D , _dnl_1E , _dnl_1F , _dnl_20 , _dnl_21 , _dnl_22 , _dnl_23 , _dnl_24 , _dnl_25 , _dnl_26 , _dnl_27 , _dnl_28 , _dnl_29 , _dnl_2A , _dnl_2B , _dnl_2C , _dnl_2D , _dnl_2E , _dnl_2F , _dnl_30 , _dnl_31 , _dnl_32 , _dnl_33 , _dnl_34 , _dnl_35 , _dnl_36 , _dnl_37 , _dnl_38 , _dnl_39 , _dnl_3A , _dnl_3B , _dnl_3C , _dnl_3D , _dnl_3E , _dnl_3F , _dnl_40 , _dnl_41 , _dnl_42 , _dnl_43 , _dnl_44 , _dnl_45 , _dnl_46 , _dnl_47 , _dnl_48 , _dnl_49 , _dnl_4A , _dnl_4B , _dnl_4C , _dnl_4D , _dnl_4E , _dnl_4F , _dnl_50 , _dnl_51 , _dnl_52 , _dnl_53 , _dnl_54 , _dnl_55 , _dnl_56 , _dnl_57 , _dnl_58 , _dnl_59 , _dnl_5A , _dnl_5B , _dnl_5C , _dnl_5D , _dnl_5E , _dnl_5F , _dnl_60 , _dnl_61 , _dnl_62 , _dnl_63 , _dnl_64 , _dnl_65 , _dnl_66 , _dnl_67 , _dnl_68 , _dnl_69 , _dnl_6A , _dnl_6B , _dnl_6C , _dnl_6D , _dnl_6E , _dnl_6F , _dnl_70 , _dnl_71 , _dnl_72 , _dnl_73 , _dnl_74 , _dnl_75 , _dnl_76 , _dnl_77 , _dnl_78 , _dnl_79 , _dnl_7A , _dnl_7B , _dnl_7C , _dnl_7D , _dnl_7E , _dnl_7F , _dnl_80 , _dnl_81 , _dnl_82 , _dnl_83 , _dnl_84 , _dnl_85 , _dnl_86 , _dnl_87 , _dnl_88 , _dnl_89 , _dnl_8A , _dnl_8B , _dnl_8C , _dnl_8D , _dnl_8E , _dnl_8F , _dnl_90 , _dnl_91 , _dnl_92 , _dnl_93 , _dnl_94 , _dnl_95 , _dnl_96 , _dnl_97 , _dnl_98 , _dnl_99 , _dnl_9A , _dnl_9B , _dnl_9C , _dnl_9D , _dnl_9E , _dnl_9F , _dnl_A0 , _dnl_A1 , _dnl_A2 , _dnl_A3 , _dnl_A4 , _dnl_A5 , _dnl_A6 , _dnl_A7 , _dnl_A8 , _dnl_A9 , _dnl_AA , _dnl_AB , _dnl_AC , _dnl_AD , _dnl_AE , _dnl_AF , _dnl_B0 , _dnl_B1 , _dnl_B2 , _dnl_B3 , _dnl_B4 , _dnl_B5 , _dnl_B6 , _dnl_B7 , _dnl_B8 , _dnl_B9 , _dnl_BA , _dnl_BB , _dnl_BC , _dnl_BD , _dnl_BE , _dnl_BF , _dnl_C0 , _dnl_C1 , _dnl_C2 , _dnl_C3 , _dnl_C4 , _dnl_C5 , _dnl_C6 , _dnl_C7 , _dnl_C8 , _dnl_C9 , _dnl_CA , _dnl_CB , _dnl_CC , _dnl_CD , _dnl_CE , _dnl_CF , _dnl_D0 , _dnl_D1 , _dnl_D2 , _dnl_D3 , _dnl_D4 , _dnl_D5 , _dnl_D6 , _dnl_D7 , _dnl_D8 , _dnl_D9 , _dnl_DA , _dnl_DB , _dnl_DC , _dnl_DD , _dnl_DE , _dnl_DF , _dnl_E0 , _dnl_E1 , _dnl_E2 , _dnl_E3 , _dnl_E4 , _dnl_E5 , _dnl_E6 , _dnl_E7 , _dnl_E8 , _dnl_E9 , _dnl_EA , _dnl_EB , _dnl_EC , _dnl_ED , _dnl_EE , _dnl_EF , _dnl_F0 , _dnl_F1 , _dnl_F2 , _dnl_F3 , _dnl_F4 , _dnl_F5 , _dnl_F6 , _dnl_F7 , _dnl_F8 , _dnl_F9 , _dnl_FA , _dnl_FB , _dnl_FC , _dnl_FD , _dnl_FE , _dnl_FF <] .
Lemma ElectionParams_ι_ValidatorDescr73_ι_adnl_addr_bs_id: ElectionParams_ι_ValidatorDescr73_ι_adnl_addr_bs_def = [> _dnl_00 , _dnl_01 , _dnl_02 , _dnl_03 , _dnl_04 , _dnl_05 , _dnl_06 , _dnl_07 , _dnl_08 , _dnl_09 , _dnl_0A , _dnl_0B , _dnl_0C , _dnl_0D , _dnl_0E , _dnl_0F , _dnl_10 , _dnl_11 , _dnl_12 , _dnl_13 , _dnl_14 , _dnl_15 , _dnl_16 , _dnl_17 , _dnl_18 , _dnl_19 , _dnl_1A , _dnl_1B , _dnl_1C , _dnl_1D , _dnl_1E , _dnl_1F , _dnl_20 , _dnl_21 , _dnl_22 , _dnl_23 , _dnl_24 , _dnl_25 , _dnl_26 , _dnl_27 , _dnl_28 , _dnl_29 , _dnl_2A , _dnl_2B , _dnl_2C , _dnl_2D , _dnl_2E , _dnl_2F , _dnl_30 , _dnl_31 , _dnl_32 , _dnl_33 , _dnl_34 , _dnl_35 , _dnl_36 , _dnl_37 , _dnl_38 , _dnl_39 , _dnl_3A , _dnl_3B , _dnl_3C , _dnl_3D , _dnl_3E , _dnl_3F , _dnl_40 , _dnl_41 , _dnl_42 , _dnl_43 , _dnl_44 , _dnl_45 , _dnl_46 , _dnl_47 , _dnl_48 , _dnl_49 , _dnl_4A , _dnl_4B , _dnl_4C , _dnl_4D , _dnl_4E , _dnl_4F , _dnl_50 , _dnl_51 , _dnl_52 , _dnl_53 , _dnl_54 , _dnl_55 , _dnl_56 , _dnl_57 , _dnl_58 , _dnl_59 , _dnl_5A , _dnl_5B , _dnl_5C , _dnl_5D , _dnl_5E , _dnl_5F , _dnl_60 , _dnl_61 , _dnl_62 , _dnl_63 , _dnl_64 , _dnl_65 , _dnl_66 , _dnl_67 , _dnl_68 , _dnl_69 , _dnl_6A , _dnl_6B , _dnl_6C , _dnl_6D , _dnl_6E , _dnl_6F , _dnl_70 , _dnl_71 , _dnl_72 , _dnl_73 , _dnl_74 , _dnl_75 , _dnl_76 , _dnl_77 , _dnl_78 , _dnl_79 , _dnl_7A , _dnl_7B , _dnl_7C , _dnl_7D , _dnl_7E , _dnl_7F , _dnl_80 , _dnl_81 , _dnl_82 , _dnl_83 , _dnl_84 , _dnl_85 , _dnl_86 , _dnl_87 , _dnl_88 , _dnl_89 , _dnl_8A , _dnl_8B , _dnl_8C , _dnl_8D , _dnl_8E , _dnl_8F , _dnl_90 , _dnl_91 , _dnl_92 , _dnl_93 , _dnl_94 , _dnl_95 , _dnl_96 , _dnl_97 , _dnl_98 , _dnl_99 , _dnl_9A , _dnl_9B , _dnl_9C , _dnl_9D , _dnl_9E , _dnl_9F , _dnl_A0 , _dnl_A1 , _dnl_A2 , _dnl_A3 , _dnl_A4 , _dnl_A5 , _dnl_A6 , _dnl_A7 , _dnl_A8 , _dnl_A9 , _dnl_AA , _dnl_AB , _dnl_AC , _dnl_AD , _dnl_AE , _dnl_AF , _dnl_B0 , _dnl_B1 , _dnl_B2 , _dnl_B3 , _dnl_B4 , _dnl_B5 , _dnl_B6 , _dnl_B7 , _dnl_B8 , _dnl_B9 , _dnl_BA , _dnl_BB , _dnl_BC , _dnl_BD , _dnl_BE , _dnl_BF , _dnl_C0 , _dnl_C1 , _dnl_C2 , _dnl_C3 , _dnl_C4 , _dnl_C5 , _dnl_C6 , _dnl_C7 , _dnl_C8 , _dnl_C9 , _dnl_CA , _dnl_CB , _dnl_CC , _dnl_CD , _dnl_CE , _dnl_CF , _dnl_D0 , _dnl_D1 , _dnl_D2 , _dnl_D3 , _dnl_D4 , _dnl_D5 , _dnl_D6 , _dnl_D7 , _dnl_D8 , _dnl_D9 , _dnl_DA , _dnl_DB , _dnl_DC , _dnl_DD , _dnl_DE , _dnl_DF , _dnl_E0 , _dnl_E1 , _dnl_E2 , _dnl_E3 , _dnl_E4 , _dnl_E5 , _dnl_E6 , _dnl_E7 , _dnl_E8 , _dnl_E9 , _dnl_EA , _dnl_EB , _dnl_EC , _dnl_ED , _dnl_EE , _dnl_EF , _dnl_F0 , _dnl_F1 , _dnl_F2 , _dnl_F3 , _dnl_F4 , _dnl_F5 , _dnl_F6 , _dnl_F7 , _dnl_F8 , _dnl_F9 , _dnl_FA , _dnl_FB , _dnl_FC , _dnl_FD , _dnl_FE , _dnl_FF (* } !*)  <] .
Proof. auto. Qed.
Axiom ElectionParams_ι_ValidatorDescr73_ι_adnl_addr_bs' : Z2IBS_pos (tvmBitStringLen ElectionParams_ι_ValidatorDescr73_ι_adnl_addr_bs_def) ElectionParams_ι_ValidatorDescr73_ι_adnl_addr = ElectionParams_ι_ValidatorDescr73_ι_adnl_addr_bs_def.
Lemma ElectionParams_ι_ValidatorDescr73_ι_adnl_addr_bs : Z2IBS_pos 256 ElectionParams_ι_ValidatorDescr73_ι_adnl_addr = ElectionParams_ι_ValidatorDescr73_ι_adnl_addr_bs_def.
Proof.
 rewrite <- ElectionParams_ι_ValidatorDescr73_ι_adnl_addr_bs'. auto. Qed.
Axiom ElectionParams_ι_ValidatorDescr73_ι_adnl_addr_pos: (0 <= ElectionParams_ι_ValidatorDescr73_ι_adnl_addr )%Z.
Axiom ElectionParams_ι_ValidatorDescr73_ι_adnl_addr_fits: zFitN_pos (tvmBitStringLen ElectionParams_ι_ValidatorDescr73_ι_adnl_addr_bs_def) ElectionParams_ι_ValidatorDescr73_ι_adnl_addr = true.
Lemma ElectionParams_ι_ValidatorDescr73_ι_adnl_addr_bs_rev : I2ZBS_pos' ElectionParams_ι_ValidatorDescr73_ι_adnl_addr_bs_def = ElectionParams_ι_ValidatorDescr73_ι_adnl_addr .
Proof.
  prove_bs_rev ElectionParams_ι_ValidatorDescr73_ι_adnl_addr_bs ElectionParams_ι_ValidatorDescr73_ι_adnl_addr_pos ElectionParams_ι_ValidatorDescr73_ι_adnl_addr_fits. 
Qed.
Lemma ElectionParams_ι_ValidatorDescr73_ι_adnl_addr_bs257 : Z2IN 257 ElectionParams_ι_ValidatorDescr73_ι_adnl_addr = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    ElectionParams_ι_ValidatorDescr73_ι_adnl_addr_bs_def)) ElectionParams_ι_ValidatorDescr73_ι_adnl_addr_bs_def)).
Proof.
  prove_bs_rev ElectionParams_ι_ValidatorDescr73_ι_adnl_addr_bs_rev ElectionParams_ι_ValidatorDescr73_ι_adnl_addr_bs_def.
Qed.

Variables StakeholderBase_ι_Stakeholder_ι_totalStake : Z . 
Variables (*! { _ttlS !*) _ttlS00 _ttlS01 _ttlS02 _ttlS03 _ttlS04 _ttlS05 _ttlS06 _ttlS07 _ttlS08 _ttlS09 _ttlS0A _ttlS0B _ttlS0C _ttlS0D _ttlS0E _ttlS0F _ttlS10 _ttlS11 _ttlS12 _ttlS13 _ttlS14 _ttlS15 _ttlS16 _ttlS17 _ttlS18 _ttlS19 _ttlS1A _ttlS1B _ttlS1C _ttlS1D _ttlS1E _ttlS1F _ttlS20 _ttlS21 _ttlS22 _ttlS23 _ttlS24 _ttlS25 _ttlS26 _ttlS27 _ttlS28 _ttlS29 _ttlS2A _ttlS2B _ttlS2C _ttlS2D _ttlS2E _ttlS2F _ttlS30 _ttlS31 _ttlS32 _ttlS33 _ttlS34 _ttlS35 _ttlS36 _ttlS37 _ttlS38 _ttlS39 _ttlS3A _ttlS3B _ttlS3C _ttlS3D _ttlS3E _ttlS3F  : TVMBit . 
Definition StakeholderBase_ι_Stakeholder_ι_totalStake_bs_def := [> _ttlS00 , _ttlS01 , _ttlS02 , _ttlS03 , _ttlS04 , _ttlS05 , _ttlS06 , _ttlS07 , _ttlS08 , _ttlS09 , _ttlS0A , _ttlS0B , _ttlS0C , _ttlS0D , _ttlS0E , _ttlS0F , _ttlS10 , _ttlS11 , _ttlS12 , _ttlS13 , _ttlS14 , _ttlS15 , _ttlS16 , _ttlS17 , _ttlS18 , _ttlS19 , _ttlS1A , _ttlS1B , _ttlS1C , _ttlS1D , _ttlS1E , _ttlS1F , _ttlS20 , _ttlS21 , _ttlS22 , _ttlS23 , _ttlS24 , _ttlS25 , _ttlS26 , _ttlS27 , _ttlS28 , _ttlS29 , _ttlS2A , _ttlS2B , _ttlS2C , _ttlS2D , _ttlS2E , _ttlS2F , _ttlS30 , _ttlS31 , _ttlS32 , _ttlS33 , _ttlS34 , _ttlS35 , _ttlS36 , _ttlS37 , _ttlS38 , _ttlS39 , _ttlS3A , _ttlS3B , _ttlS3C , _ttlS3D , _ttlS3E , _ttlS3F <] .
Lemma StakeholderBase_ι_Stakeholder_ι_totalStake_bs_id: StakeholderBase_ι_Stakeholder_ι_totalStake_bs_def = [> _ttlS00 , _ttlS01 , _ttlS02 , _ttlS03 , _ttlS04 , _ttlS05 , _ttlS06 , _ttlS07 , _ttlS08 , _ttlS09 , _ttlS0A , _ttlS0B , _ttlS0C , _ttlS0D , _ttlS0E , _ttlS0F , _ttlS10 , _ttlS11 , _ttlS12 , _ttlS13 , _ttlS14 , _ttlS15 , _ttlS16 , _ttlS17 , _ttlS18 , _ttlS19 , _ttlS1A , _ttlS1B , _ttlS1C , _ttlS1D , _ttlS1E , _ttlS1F , _ttlS20 , _ttlS21 , _ttlS22 , _ttlS23 , _ttlS24 , _ttlS25 , _ttlS26 , _ttlS27 , _ttlS28 , _ttlS29 , _ttlS2A , _ttlS2B , _ttlS2C , _ttlS2D , _ttlS2E , _ttlS2F , _ttlS30 , _ttlS31 , _ttlS32 , _ttlS33 , _ttlS34 , _ttlS35 , _ttlS36 , _ttlS37 , _ttlS38 , _ttlS39 , _ttlS3A , _ttlS3B , _ttlS3C , _ttlS3D , _ttlS3E , _ttlS3F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakeholderBase_ι_Stakeholder_ι_totalStake_bs' : Z2IBS_pos (tvmBitStringLen StakeholderBase_ι_Stakeholder_ι_totalStake_bs_def) StakeholderBase_ι_Stakeholder_ι_totalStake = StakeholderBase_ι_Stakeholder_ι_totalStake_bs_def.
Lemma StakeholderBase_ι_Stakeholder_ι_totalStake_bs : Z2IBS_pos 64 StakeholderBase_ι_Stakeholder_ι_totalStake = StakeholderBase_ι_Stakeholder_ι_totalStake_bs_def.
Proof.
 rewrite <- StakeholderBase_ι_Stakeholder_ι_totalStake_bs'. auto. Qed.
Axiom StakeholderBase_ι_Stakeholder_ι_totalStake_pos: (0 <= StakeholderBase_ι_Stakeholder_ι_totalStake )%Z.
Axiom StakeholderBase_ι_Stakeholder_ι_totalStake_fits: zFitN_pos (tvmBitStringLen StakeholderBase_ι_Stakeholder_ι_totalStake_bs_def) StakeholderBase_ι_Stakeholder_ι_totalStake = true.
Lemma StakeholderBase_ι_Stakeholder_ι_totalStake_bs_rev : I2ZBS_pos' StakeholderBase_ι_Stakeholder_ι_totalStake_bs_def = StakeholderBase_ι_Stakeholder_ι_totalStake .
Proof.
  prove_bs_rev StakeholderBase_ι_Stakeholder_ι_totalStake_bs StakeholderBase_ι_Stakeholder_ι_totalStake_pos StakeholderBase_ι_Stakeholder_ι_totalStake_fits. 
Qed.
Lemma StakeholderBase_ι_Stakeholder_ι_totalStake_bs257 : Z2IN 257 StakeholderBase_ι_Stakeholder_ι_totalStake = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakeholderBase_ι_Stakeholder_ι_totalStake_bs_def)) StakeholderBase_ι_Stakeholder_ι_totalStake_bs_def)).
Proof.
  prove_bs_rev StakeholderBase_ι_Stakeholder_ι_totalStake_bs_rev StakeholderBase_ι_Stakeholder_ι_totalStake_bs_def.
Qed. 
Variables StakeholderBase_ι_Stakeholder_ι_unusedStake : Z . 
Variables (*! { _nsdS !*) _nsdS00 _nsdS01 _nsdS02 _nsdS03 _nsdS04 _nsdS05 _nsdS06 _nsdS07 _nsdS08 _nsdS09 _nsdS0A _nsdS0B _nsdS0C _nsdS0D _nsdS0E _nsdS0F _nsdS10 _nsdS11 _nsdS12 _nsdS13 _nsdS14 _nsdS15 _nsdS16 _nsdS17 _nsdS18 _nsdS19 _nsdS1A _nsdS1B _nsdS1C _nsdS1D _nsdS1E _nsdS1F _nsdS20 _nsdS21 _nsdS22 _nsdS23 _nsdS24 _nsdS25 _nsdS26 _nsdS27 _nsdS28 _nsdS29 _nsdS2A _nsdS2B _nsdS2C _nsdS2D _nsdS2E _nsdS2F _nsdS30 _nsdS31 _nsdS32 _nsdS33 _nsdS34 _nsdS35 _nsdS36 _nsdS37 _nsdS38 _nsdS39 _nsdS3A _nsdS3B _nsdS3C _nsdS3D _nsdS3E _nsdS3F  : TVMBit . 
Definition StakeholderBase_ι_Stakeholder_ι_unusedStake_bs_def := [> _nsdS00 , _nsdS01 , _nsdS02 , _nsdS03 , _nsdS04 , _nsdS05 , _nsdS06 , _nsdS07 , _nsdS08 , _nsdS09 , _nsdS0A , _nsdS0B , _nsdS0C , _nsdS0D , _nsdS0E , _nsdS0F , _nsdS10 , _nsdS11 , _nsdS12 , _nsdS13 , _nsdS14 , _nsdS15 , _nsdS16 , _nsdS17 , _nsdS18 , _nsdS19 , _nsdS1A , _nsdS1B , _nsdS1C , _nsdS1D , _nsdS1E , _nsdS1F , _nsdS20 , _nsdS21 , _nsdS22 , _nsdS23 , _nsdS24 , _nsdS25 , _nsdS26 , _nsdS27 , _nsdS28 , _nsdS29 , _nsdS2A , _nsdS2B , _nsdS2C , _nsdS2D , _nsdS2E , _nsdS2F , _nsdS30 , _nsdS31 , _nsdS32 , _nsdS33 , _nsdS34 , _nsdS35 , _nsdS36 , _nsdS37 , _nsdS38 , _nsdS39 , _nsdS3A , _nsdS3B , _nsdS3C , _nsdS3D , _nsdS3E , _nsdS3F <] .
Lemma StakeholderBase_ι_Stakeholder_ι_unusedStake_bs_id: StakeholderBase_ι_Stakeholder_ι_unusedStake_bs_def = [> _nsdS00 , _nsdS01 , _nsdS02 , _nsdS03 , _nsdS04 , _nsdS05 , _nsdS06 , _nsdS07 , _nsdS08 , _nsdS09 , _nsdS0A , _nsdS0B , _nsdS0C , _nsdS0D , _nsdS0E , _nsdS0F , _nsdS10 , _nsdS11 , _nsdS12 , _nsdS13 , _nsdS14 , _nsdS15 , _nsdS16 , _nsdS17 , _nsdS18 , _nsdS19 , _nsdS1A , _nsdS1B , _nsdS1C , _nsdS1D , _nsdS1E , _nsdS1F , _nsdS20 , _nsdS21 , _nsdS22 , _nsdS23 , _nsdS24 , _nsdS25 , _nsdS26 , _nsdS27 , _nsdS28 , _nsdS29 , _nsdS2A , _nsdS2B , _nsdS2C , _nsdS2D , _nsdS2E , _nsdS2F , _nsdS30 , _nsdS31 , _nsdS32 , _nsdS33 , _nsdS34 , _nsdS35 , _nsdS36 , _nsdS37 , _nsdS38 , _nsdS39 , _nsdS3A , _nsdS3B , _nsdS3C , _nsdS3D , _nsdS3E , _nsdS3F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakeholderBase_ι_Stakeholder_ι_unusedStake_bs' : Z2IBS_pos (tvmBitStringLen StakeholderBase_ι_Stakeholder_ι_unusedStake_bs_def) StakeholderBase_ι_Stakeholder_ι_unusedStake = StakeholderBase_ι_Stakeholder_ι_unusedStake_bs_def.
Lemma StakeholderBase_ι_Stakeholder_ι_unusedStake_bs : Z2IBS_pos 64 StakeholderBase_ι_Stakeholder_ι_unusedStake = StakeholderBase_ι_Stakeholder_ι_unusedStake_bs_def.
Proof.
 rewrite <- StakeholderBase_ι_Stakeholder_ι_unusedStake_bs'. auto. Qed.
Axiom StakeholderBase_ι_Stakeholder_ι_unusedStake_pos: (0 <= StakeholderBase_ι_Stakeholder_ι_unusedStake )%Z.
Axiom StakeholderBase_ι_Stakeholder_ι_unusedStake_fits: zFitN_pos (tvmBitStringLen StakeholderBase_ι_Stakeholder_ι_unusedStake_bs_def) StakeholderBase_ι_Stakeholder_ι_unusedStake = true.
Lemma StakeholderBase_ι_Stakeholder_ι_unusedStake_bs_rev : I2ZBS_pos' StakeholderBase_ι_Stakeholder_ι_unusedStake_bs_def = StakeholderBase_ι_Stakeholder_ι_unusedStake .
Proof.
  prove_bs_rev StakeholderBase_ι_Stakeholder_ι_unusedStake_bs StakeholderBase_ι_Stakeholder_ι_unusedStake_pos StakeholderBase_ι_Stakeholder_ι_unusedStake_fits. 
Qed.
Lemma StakeholderBase_ι_Stakeholder_ι_unusedStake_bs257 : Z2IN 257 StakeholderBase_ι_Stakeholder_ι_unusedStake = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakeholderBase_ι_Stakeholder_ι_unusedStake_bs_def)) StakeholderBase_ι_Stakeholder_ι_unusedStake_bs_def)).
Proof.
  prove_bs_rev StakeholderBase_ι_Stakeholder_ι_unusedStake_bs_rev StakeholderBase_ι_Stakeholder_ι_unusedStake_bs_def.
Qed.  
Variables StakeholderBase_ι_Stakeholder_ι_reward : Z . 
Variables (*! { _rwrd !*) _rwrd00 _rwrd01 _rwrd02 _rwrd03 _rwrd04 _rwrd05 _rwrd06 _rwrd07 _rwrd08 _rwrd09 _rwrd0A _rwrd0B _rwrd0C _rwrd0D _rwrd0E _rwrd0F _rwrd10 _rwrd11 _rwrd12 _rwrd13 _rwrd14 _rwrd15 _rwrd16 _rwrd17 _rwrd18 _rwrd19 _rwrd1A _rwrd1B _rwrd1C _rwrd1D _rwrd1E _rwrd1F _rwrd20 _rwrd21 _rwrd22 _rwrd23 _rwrd24 _rwrd25 _rwrd26 _rwrd27 _rwrd28 _rwrd29 _rwrd2A _rwrd2B _rwrd2C _rwrd2D _rwrd2E _rwrd2F _rwrd30 _rwrd31 _rwrd32 _rwrd33 _rwrd34 _rwrd35 _rwrd36 _rwrd37 _rwrd38 _rwrd39 _rwrd3A _rwrd3B _rwrd3C _rwrd3D _rwrd3E _rwrd3F  : TVMBit . 
Definition StakeholderBase_ι_Stakeholder_ι_reward_bs_def := [> _rwrd00 , _rwrd01 , _rwrd02 , _rwrd03 , _rwrd04 , _rwrd05 , _rwrd06 , _rwrd07 , _rwrd08 , _rwrd09 , _rwrd0A , _rwrd0B , _rwrd0C , _rwrd0D , _rwrd0E , _rwrd0F , _rwrd10 , _rwrd11 , _rwrd12 , _rwrd13 , _rwrd14 , _rwrd15 , _rwrd16 , _rwrd17 , _rwrd18 , _rwrd19 , _rwrd1A , _rwrd1B , _rwrd1C , _rwrd1D , _rwrd1E , _rwrd1F , _rwrd20 , _rwrd21 , _rwrd22 , _rwrd23 , _rwrd24 , _rwrd25 , _rwrd26 , _rwrd27 , _rwrd28 , _rwrd29 , _rwrd2A , _rwrd2B , _rwrd2C , _rwrd2D , _rwrd2E , _rwrd2F , _rwrd30 , _rwrd31 , _rwrd32 , _rwrd33 , _rwrd34 , _rwrd35 , _rwrd36 , _rwrd37 , _rwrd38 , _rwrd39 , _rwrd3A , _rwrd3B , _rwrd3C , _rwrd3D , _rwrd3E , _rwrd3F <] .
Lemma StakeholderBase_ι_Stakeholder_ι_reward_bs_id: StakeholderBase_ι_Stakeholder_ι_reward_bs_def = [> _rwrd00 , _rwrd01 , _rwrd02 , _rwrd03 , _rwrd04 , _rwrd05 , _rwrd06 , _rwrd07 , _rwrd08 , _rwrd09 , _rwrd0A , _rwrd0B , _rwrd0C , _rwrd0D , _rwrd0E , _rwrd0F , _rwrd10 , _rwrd11 , _rwrd12 , _rwrd13 , _rwrd14 , _rwrd15 , _rwrd16 , _rwrd17 , _rwrd18 , _rwrd19 , _rwrd1A , _rwrd1B , _rwrd1C , _rwrd1D , _rwrd1E , _rwrd1F , _rwrd20 , _rwrd21 , _rwrd22 , _rwrd23 , _rwrd24 , _rwrd25 , _rwrd26 , _rwrd27 , _rwrd28 , _rwrd29 , _rwrd2A , _rwrd2B , _rwrd2C , _rwrd2D , _rwrd2E , _rwrd2F , _rwrd30 , _rwrd31 , _rwrd32 , _rwrd33 , _rwrd34 , _rwrd35 , _rwrd36 , _rwrd37 , _rwrd38 , _rwrd39 , _rwrd3A , _rwrd3B , _rwrd3C , _rwrd3D , _rwrd3E , _rwrd3F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakeholderBase_ι_Stakeholder_ι_reward_bs' : Z2IBS_pos (tvmBitStringLen StakeholderBase_ι_Stakeholder_ι_reward_bs_def) StakeholderBase_ι_Stakeholder_ι_reward = StakeholderBase_ι_Stakeholder_ι_reward_bs_def.
Lemma StakeholderBase_ι_Stakeholder_ι_reward_bs : Z2IBS_pos 64 StakeholderBase_ι_Stakeholder_ι_reward = StakeholderBase_ι_Stakeholder_ι_reward_bs_def.
Proof.
 rewrite <- StakeholderBase_ι_Stakeholder_ι_reward_bs'. auto. Qed.
Axiom StakeholderBase_ι_Stakeholder_ι_reward_pos: (0 <= StakeholderBase_ι_Stakeholder_ι_reward )%Z.
Axiom StakeholderBase_ι_Stakeholder_ι_reward_fits: zFitN_pos (tvmBitStringLen StakeholderBase_ι_Stakeholder_ι_reward_bs_def) StakeholderBase_ι_Stakeholder_ι_reward = true.
Lemma StakeholderBase_ι_Stakeholder_ι_reward_bs_rev : I2ZBS_pos' StakeholderBase_ι_Stakeholder_ι_reward_bs_def = StakeholderBase_ι_Stakeholder_ι_reward .
Proof.
  prove_bs_rev StakeholderBase_ι_Stakeholder_ι_reward_bs StakeholderBase_ι_Stakeholder_ι_reward_pos StakeholderBase_ι_Stakeholder_ι_reward_fits. 
Qed.
Lemma StakeholderBase_ι_Stakeholder_ι_reward_bs257 : Z2IN 257 StakeholderBase_ι_Stakeholder_ι_reward = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakeholderBase_ι_Stakeholder_ι_reward_bs_def)) StakeholderBase_ι_Stakeholder_ι_reward_bs_def)).
Proof.
  prove_bs_rev StakeholderBase_ι_Stakeholder_ι_reward_bs_rev StakeholderBase_ι_Stakeholder_ι_reward_bs_def.
Qed.

Variables RoundsBase_ι_Round_ι_id : Z . 
Variables (*! { _d !*) _d00 _d01 _d02 _d03 _d04 _d05 _d06 _d07 _d08 _d09 _d0A _d0B _d0C _d0D _d0E _d0F _d10 _d11 _d12 _d13 _d14 _d15 _d16 _d17 _d18 _d19 _d1A _d1B _d1C _d1D _d1E _d1F  : TVMBit . 
Definition RoundsBase_ι_Round_ι_id_bs_def := [> _d00 , _d01 , _d02 , _d03 , _d04 , _d05 , _d06 , _d07 , _d08 , _d09 , _d0A , _d0B , _d0C , _d0D , _d0E , _d0F , _d10 , _d11 , _d12 , _d13 , _d14 , _d15 , _d16 , _d17 , _d18 , _d19 , _d1A , _d1B , _d1C , _d1D , _d1E , _d1F <] .
Lemma RoundsBase_ι_Round_ι_id_bs_id: RoundsBase_ι_Round_ι_id_bs_def = [> _d00 , _d01 , _d02 , _d03 , _d04 , _d05 , _d06 , _d07 , _d08 , _d09 , _d0A , _d0B , _d0C , _d0D , _d0E , _d0F , _d10 , _d11 , _d12 , _d13 , _d14 , _d15 , _d16 , _d17 , _d18 , _d19 , _d1A , _d1B , _d1C , _d1D , _d1E , _d1F (* } !*)  <] .
Proof. auto. Qed.
Axiom RoundsBase_ι_Round_ι_id_bs' : Z2IBS_pos (tvmBitStringLen RoundsBase_ι_Round_ι_id_bs_def) RoundsBase_ι_Round_ι_id = RoundsBase_ι_Round_ι_id_bs_def.
Lemma RoundsBase_ι_Round_ι_id_bs : Z2IBS_pos 32 RoundsBase_ι_Round_ι_id = RoundsBase_ι_Round_ι_id_bs_def.
Proof.
 rewrite <- RoundsBase_ι_Round_ι_id_bs'. auto. Qed.
Axiom RoundsBase_ι_Round_ι_id_pos: (0 <= RoundsBase_ι_Round_ι_id )%Z.
Axiom RoundsBase_ι_Round_ι_id_fits: zFitN_pos (tvmBitStringLen RoundsBase_ι_Round_ι_id_bs_def) RoundsBase_ι_Round_ι_id = true.
Lemma RoundsBase_ι_Round_ι_id_bs_rev : I2ZBS_pos' RoundsBase_ι_Round_ι_id_bs_def = RoundsBase_ι_Round_ι_id .
Proof.
  prove_bs_rev RoundsBase_ι_Round_ι_id_bs RoundsBase_ι_Round_ι_id_pos RoundsBase_ι_Round_ι_id_fits. 
Qed.
Lemma RoundsBase_ι_Round_ι_id_bs257 : Z2IN 257 RoundsBase_ι_Round_ι_id = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    RoundsBase_ι_Round_ι_id_bs_def)) RoundsBase_ι_Round_ι_id_bs_def)).
Proof.
  prove_bs_rev RoundsBase_ι_Round_ι_id_bs_rev RoundsBase_ι_Round_ι_id_bs_def.
Qed. 
Variables RoundsBase_ι_Round_ι_step : Z . 
Variables (*! { _stp !*) _stp00 _stp01 _stp02 _stp03 _stp04 _stp05 _stp06 _stp07  : TVMBit . 
Definition RoundsBase_ι_Round_ι_step_bs_def := [> _stp00 , _stp01 , _stp02 , _stp03 , _stp04 , _stp05 , _stp06 , _stp07 <] .
Lemma RoundsBase_ι_Round_ι_step_bs_id: RoundsBase_ι_Round_ι_step_bs_def = [> _stp00 , _stp01 , _stp02 , _stp03 , _stp04 , _stp05 , _stp06 , _stp07 (* } !*)  <] .
Proof. auto. Qed.
Axiom RoundsBase_ι_Round_ι_step_bs' : Z2IBS_pos (tvmBitStringLen RoundsBase_ι_Round_ι_step_bs_def) RoundsBase_ι_Round_ι_step = RoundsBase_ι_Round_ι_step_bs_def.
Lemma RoundsBase_ι_Round_ι_step_bs : Z2IBS_pos 8 RoundsBase_ι_Round_ι_step = RoundsBase_ι_Round_ι_step_bs_def.
Proof.
 rewrite <- RoundsBase_ι_Round_ι_step_bs'. auto. Qed.
Axiom RoundsBase_ι_Round_ι_step_pos: (0 <= RoundsBase_ι_Round_ι_step )%Z.
Axiom RoundsBase_ι_Round_ι_step_fits: zFitN_pos (tvmBitStringLen RoundsBase_ι_Round_ι_step_bs_def) RoundsBase_ι_Round_ι_step = true.
Lemma RoundsBase_ι_Round_ι_step_bs_rev : I2ZBS_pos' RoundsBase_ι_Round_ι_step_bs_def = RoundsBase_ι_Round_ι_step .
Proof.
  prove_bs_rev RoundsBase_ι_Round_ι_step_bs RoundsBase_ι_Round_ι_step_pos RoundsBase_ι_Round_ι_step_fits. 
Qed.
Lemma RoundsBase_ι_Round_ι_step_bs257 : Z2IN 257 RoundsBase_ι_Round_ι_step = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    RoundsBase_ι_Round_ι_step_bs_def)) RoundsBase_ι_Round_ι_step_bs_def)).
Proof.
  prove_bs_rev RoundsBase_ι_Round_ι_step_bs_rev RoundsBase_ι_Round_ι_step_bs_def.
Qed. 
Variables RoundsBase_ι_Round_ι_count : Z . 
Variables (*! { _cnt !*) _cnt00 _cnt01 _cnt02 _cnt03 _cnt04 _cnt05 _cnt06 _cnt07 _cnt08 _cnt09 _cnt0A _cnt0B _cnt0C _cnt0D _cnt0E _cnt0F _cnt10 _cnt11 _cnt12 _cnt13 _cnt14 _cnt15 _cnt16 _cnt17 _cnt18 _cnt19 _cnt1A _cnt1B _cnt1C _cnt1D _cnt1E _cnt1F  : TVMBit . 
Definition RoundsBase_ι_Round_ι_count_bs_def := [> _cnt00 , _cnt01 , _cnt02 , _cnt03 , _cnt04 , _cnt05 , _cnt06 , _cnt07 , _cnt08 , _cnt09 , _cnt0A , _cnt0B , _cnt0C , _cnt0D , _cnt0E , _cnt0F , _cnt10 , _cnt11 , _cnt12 , _cnt13 , _cnt14 , _cnt15 , _cnt16 , _cnt17 , _cnt18 , _cnt19 , _cnt1A , _cnt1B , _cnt1C , _cnt1D , _cnt1E , _cnt1F <] .
Lemma RoundsBase_ι_Round_ι_count_bs_id: RoundsBase_ι_Round_ι_count_bs_def = [> _cnt00 , _cnt01 , _cnt02 , _cnt03 , _cnt04 , _cnt05 , _cnt06 , _cnt07 , _cnt08 , _cnt09 , _cnt0A , _cnt0B , _cnt0C , _cnt0D , _cnt0E , _cnt0F , _cnt10 , _cnt11 , _cnt12 , _cnt13 , _cnt14 , _cnt15 , _cnt16 , _cnt17 , _cnt18 , _cnt19 , _cnt1A , _cnt1B , _cnt1C , _cnt1D , _cnt1E , _cnt1F (* } !*)  <] .
Proof. auto. Qed.
Axiom RoundsBase_ι_Round_ι_count_bs' : Z2IBS_pos (tvmBitStringLen RoundsBase_ι_Round_ι_count_bs_def) RoundsBase_ι_Round_ι_count = RoundsBase_ι_Round_ι_count_bs_def.
Lemma RoundsBase_ι_Round_ι_count_bs : Z2IBS_pos 32 RoundsBase_ι_Round_ι_count = RoundsBase_ι_Round_ι_count_bs_def.
Proof.
 rewrite <- RoundsBase_ι_Round_ι_count_bs'. auto. Qed.
Axiom RoundsBase_ι_Round_ι_count_pos: (0 <= RoundsBase_ι_Round_ι_count )%Z.
Axiom RoundsBase_ι_Round_ι_count_fits: zFitN_pos (tvmBitStringLen RoundsBase_ι_Round_ι_count_bs_def) RoundsBase_ι_Round_ι_count = true.
Lemma RoundsBase_ι_Round_ι_count_bs_rev : I2ZBS_pos' RoundsBase_ι_Round_ι_count_bs_def = RoundsBase_ι_Round_ι_count .
Proof.
  prove_bs_rev RoundsBase_ι_Round_ι_count_bs RoundsBase_ι_Round_ι_count_pos RoundsBase_ι_Round_ι_count_fits. 
Qed.
Lemma RoundsBase_ι_Round_ι_count_bs257 : Z2IN 257 RoundsBase_ι_Round_ι_count = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    RoundsBase_ι_Round_ι_count_bs_def)) RoundsBase_ι_Round_ι_count_bs_def)).
Proof.
  prove_bs_rev RoundsBase_ι_Round_ι_count_bs_rev RoundsBase_ι_Round_ι_count_bs_def.
Qed. 
Variables RoundsBase_ι_Round_ι_totalStake : Z . 
Variables (*! { _ttlS !*) _ttlS00 _ttlS01 _ttlS02 _ttlS03 _ttlS04 _ttlS05 _ttlS06 _ttlS07 _ttlS08 _ttlS09 _ttlS0A _ttlS0B _ttlS0C _ttlS0D _ttlS0E _ttlS0F _ttlS10 _ttlS11 _ttlS12 _ttlS13 _ttlS14 _ttlS15 _ttlS16 _ttlS17 _ttlS18 _ttlS19 _ttlS1A _ttlS1B _ttlS1C _ttlS1D _ttlS1E _ttlS1F _ttlS20 _ttlS21 _ttlS22 _ttlS23 _ttlS24 _ttlS25 _ttlS26 _ttlS27 _ttlS28 _ttlS29 _ttlS2A _ttlS2B _ttlS2C _ttlS2D _ttlS2E _ttlS2F _ttlS30 _ttlS31 _ttlS32 _ttlS33 _ttlS34 _ttlS35 _ttlS36 _ttlS37 _ttlS38 _ttlS39 _ttlS3A _ttlS3B _ttlS3C _ttlS3D _ttlS3E _ttlS3F  : TVMBit . 
Definition RoundsBase_ι_Round_ι_totalStake_bs_def := [> _ttlS00 , _ttlS01 , _ttlS02 , _ttlS03 , _ttlS04 , _ttlS05 , _ttlS06 , _ttlS07 , _ttlS08 , _ttlS09 , _ttlS0A , _ttlS0B , _ttlS0C , _ttlS0D , _ttlS0E , _ttlS0F , _ttlS10 , _ttlS11 , _ttlS12 , _ttlS13 , _ttlS14 , _ttlS15 , _ttlS16 , _ttlS17 , _ttlS18 , _ttlS19 , _ttlS1A , _ttlS1B , _ttlS1C , _ttlS1D , _ttlS1E , _ttlS1F , _ttlS20 , _ttlS21 , _ttlS22 , _ttlS23 , _ttlS24 , _ttlS25 , _ttlS26 , _ttlS27 , _ttlS28 , _ttlS29 , _ttlS2A , _ttlS2B , _ttlS2C , _ttlS2D , _ttlS2E , _ttlS2F , _ttlS30 , _ttlS31 , _ttlS32 , _ttlS33 , _ttlS34 , _ttlS35 , _ttlS36 , _ttlS37 , _ttlS38 , _ttlS39 , _ttlS3A , _ttlS3B , _ttlS3C , _ttlS3D , _ttlS3E , _ttlS3F <] .
Lemma RoundsBase_ι_Round_ι_totalStake_bs_id: RoundsBase_ι_Round_ι_totalStake_bs_def = [> _ttlS00 , _ttlS01 , _ttlS02 , _ttlS03 , _ttlS04 , _ttlS05 , _ttlS06 , _ttlS07 , _ttlS08 , _ttlS09 , _ttlS0A , _ttlS0B , _ttlS0C , _ttlS0D , _ttlS0E , _ttlS0F , _ttlS10 , _ttlS11 , _ttlS12 , _ttlS13 , _ttlS14 , _ttlS15 , _ttlS16 , _ttlS17 , _ttlS18 , _ttlS19 , _ttlS1A , _ttlS1B , _ttlS1C , _ttlS1D , _ttlS1E , _ttlS1F , _ttlS20 , _ttlS21 , _ttlS22 , _ttlS23 , _ttlS24 , _ttlS25 , _ttlS26 , _ttlS27 , _ttlS28 , _ttlS29 , _ttlS2A , _ttlS2B , _ttlS2C , _ttlS2D , _ttlS2E , _ttlS2F , _ttlS30 , _ttlS31 , _ttlS32 , _ttlS33 , _ttlS34 , _ttlS35 , _ttlS36 , _ttlS37 , _ttlS38 , _ttlS39 , _ttlS3A , _ttlS3B , _ttlS3C , _ttlS3D , _ttlS3E , _ttlS3F (* } !*)  <] .
Proof. auto. Qed.
Axiom RoundsBase_ι_Round_ι_totalStake_bs' : Z2IBS_pos (tvmBitStringLen RoundsBase_ι_Round_ι_totalStake_bs_def) RoundsBase_ι_Round_ι_totalStake = RoundsBase_ι_Round_ι_totalStake_bs_def.
Lemma RoundsBase_ι_Round_ι_totalStake_bs : Z2IBS_pos 64 RoundsBase_ι_Round_ι_totalStake = RoundsBase_ι_Round_ι_totalStake_bs_def.
Proof.
 rewrite <- RoundsBase_ι_Round_ι_totalStake_bs'. auto. Qed.
Axiom RoundsBase_ι_Round_ι_totalStake_pos: (0 <= RoundsBase_ι_Round_ι_totalStake )%Z.
Axiom RoundsBase_ι_Round_ι_totalStake_fits: zFitN_pos (tvmBitStringLen RoundsBase_ι_Round_ι_totalStake_bs_def) RoundsBase_ι_Round_ι_totalStake = true.
Lemma RoundsBase_ι_Round_ι_totalStake_bs_rev : I2ZBS_pos' RoundsBase_ι_Round_ι_totalStake_bs_def = RoundsBase_ι_Round_ι_totalStake .
Proof.
  prove_bs_rev RoundsBase_ι_Round_ι_totalStake_bs RoundsBase_ι_Round_ι_totalStake_pos RoundsBase_ι_Round_ι_totalStake_fits. 
Qed.
Lemma RoundsBase_ι_Round_ι_totalStake_bs257 : Z2IN 257 RoundsBase_ι_Round_ι_totalStake = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    RoundsBase_ι_Round_ι_totalStake_bs_def)) RoundsBase_ι_Round_ι_totalStake_bs_def)).
Proof.
  prove_bs_rev RoundsBase_ι_Round_ι_totalStake_bs_rev RoundsBase_ι_Round_ι_totalStake_bs_def.
Qed. 
Variables RoundsBase_ι_Round_ι_rewards : Z . 
Variables (*! { _rwrd !*) _rwrd00 _rwrd01 _rwrd02 _rwrd03 _rwrd04 _rwrd05 _rwrd06 _rwrd07 _rwrd08 _rwrd09 _rwrd0A _rwrd0B _rwrd0C _rwrd0D _rwrd0E _rwrd0F _rwrd10 _rwrd11 _rwrd12 _rwrd13 _rwrd14 _rwrd15 _rwrd16 _rwrd17 _rwrd18 _rwrd19 _rwrd1A _rwrd1B _rwrd1C _rwrd1D _rwrd1E _rwrd1F _rwrd20 _rwrd21 _rwrd22 _rwrd23 _rwrd24 _rwrd25 _rwrd26 _rwrd27 _rwrd28 _rwrd29 _rwrd2A _rwrd2B _rwrd2C _rwrd2D _rwrd2E _rwrd2F _rwrd30 _rwrd31 _rwrd32 _rwrd33 _rwrd34 _rwrd35 _rwrd36 _rwrd37 _rwrd38 _rwrd39 _rwrd3A _rwrd3B _rwrd3C _rwrd3D _rwrd3E _rwrd3F  : TVMBit . 
Definition RoundsBase_ι_Round_ι_rewards_bs_def := [> _rwrd00 , _rwrd01 , _rwrd02 , _rwrd03 , _rwrd04 , _rwrd05 , _rwrd06 , _rwrd07 , _rwrd08 , _rwrd09 , _rwrd0A , _rwrd0B , _rwrd0C , _rwrd0D , _rwrd0E , _rwrd0F , _rwrd10 , _rwrd11 , _rwrd12 , _rwrd13 , _rwrd14 , _rwrd15 , _rwrd16 , _rwrd17 , _rwrd18 , _rwrd19 , _rwrd1A , _rwrd1B , _rwrd1C , _rwrd1D , _rwrd1E , _rwrd1F , _rwrd20 , _rwrd21 , _rwrd22 , _rwrd23 , _rwrd24 , _rwrd25 , _rwrd26 , _rwrd27 , _rwrd28 , _rwrd29 , _rwrd2A , _rwrd2B , _rwrd2C , _rwrd2D , _rwrd2E , _rwrd2F , _rwrd30 , _rwrd31 , _rwrd32 , _rwrd33 , _rwrd34 , _rwrd35 , _rwrd36 , _rwrd37 , _rwrd38 , _rwrd39 , _rwrd3A , _rwrd3B , _rwrd3C , _rwrd3D , _rwrd3E , _rwrd3F <] .
Lemma RoundsBase_ι_Round_ι_rewards_bs_id: RoundsBase_ι_Round_ι_rewards_bs_def = [> _rwrd00 , _rwrd01 , _rwrd02 , _rwrd03 , _rwrd04 , _rwrd05 , _rwrd06 , _rwrd07 , _rwrd08 , _rwrd09 , _rwrd0A , _rwrd0B , _rwrd0C , _rwrd0D , _rwrd0E , _rwrd0F , _rwrd10 , _rwrd11 , _rwrd12 , _rwrd13 , _rwrd14 , _rwrd15 , _rwrd16 , _rwrd17 , _rwrd18 , _rwrd19 , _rwrd1A , _rwrd1B , _rwrd1C , _rwrd1D , _rwrd1E , _rwrd1F , _rwrd20 , _rwrd21 , _rwrd22 , _rwrd23 , _rwrd24 , _rwrd25 , _rwrd26 , _rwrd27 , _rwrd28 , _rwrd29 , _rwrd2A , _rwrd2B , _rwrd2C , _rwrd2D , _rwrd2E , _rwrd2F , _rwrd30 , _rwrd31 , _rwrd32 , _rwrd33 , _rwrd34 , _rwrd35 , _rwrd36 , _rwrd37 , _rwrd38 , _rwrd39 , _rwrd3A , _rwrd3B , _rwrd3C , _rwrd3D , _rwrd3E , _rwrd3F (* } !*)  <] .
Proof. auto. Qed.
Axiom RoundsBase_ι_Round_ι_rewards_bs' : Z2IBS_pos (tvmBitStringLen RoundsBase_ι_Round_ι_rewards_bs_def) RoundsBase_ι_Round_ι_rewards = RoundsBase_ι_Round_ι_rewards_bs_def.
Lemma RoundsBase_ι_Round_ι_rewards_bs : Z2IBS_pos 64 RoundsBase_ι_Round_ι_rewards = RoundsBase_ι_Round_ι_rewards_bs_def.
Proof.
 rewrite <- RoundsBase_ι_Round_ι_rewards_bs'. auto. Qed.
Axiom RoundsBase_ι_Round_ι_rewards_pos: (0 <= RoundsBase_ι_Round_ι_rewards )%Z.
Axiom RoundsBase_ι_Round_ι_rewards_fits: zFitN_pos (tvmBitStringLen RoundsBase_ι_Round_ι_rewards_bs_def) RoundsBase_ι_Round_ι_rewards = true.
Lemma RoundsBase_ι_Round_ι_rewards_bs_rev : I2ZBS_pos' RoundsBase_ι_Round_ι_rewards_bs_def = RoundsBase_ι_Round_ι_rewards .
Proof.
  prove_bs_rev RoundsBase_ι_Round_ι_rewards_bs RoundsBase_ι_Round_ι_rewards_pos RoundsBase_ι_Round_ι_rewards_fits. 
Qed.
Lemma RoundsBase_ι_Round_ι_rewards_bs257 : Z2IN 257 RoundsBase_ι_Round_ι_rewards = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    RoundsBase_ι_Round_ι_rewards_bs_def)) RoundsBase_ι_Round_ι_rewards_bs_def)).
Proof.
  prove_bs_rev RoundsBase_ι_Round_ι_rewards_bs_rev RoundsBase_ι_Round_ι_rewards_bs_def.
Qed. 
Variables RoundsBase_ι_Round_ι_unused : Z . 
Variables (*! { _nsd !*) _nsd00 _nsd01 _nsd02 _nsd03 _nsd04 _nsd05 _nsd06 _nsd07 _nsd08 _nsd09 _nsd0A _nsd0B _nsd0C _nsd0D _nsd0E _nsd0F _nsd10 _nsd11 _nsd12 _nsd13 _nsd14 _nsd15 _nsd16 _nsd17 _nsd18 _nsd19 _nsd1A _nsd1B _nsd1C _nsd1D _nsd1E _nsd1F _nsd20 _nsd21 _nsd22 _nsd23 _nsd24 _nsd25 _nsd26 _nsd27 _nsd28 _nsd29 _nsd2A _nsd2B _nsd2C _nsd2D _nsd2E _nsd2F _nsd30 _nsd31 _nsd32 _nsd33 _nsd34 _nsd35 _nsd36 _nsd37 _nsd38 _nsd39 _nsd3A _nsd3B _nsd3C _nsd3D _nsd3E _nsd3F  : TVMBit . 
Definition RoundsBase_ι_Round_ι_unused_bs_def := [> _nsd00 , _nsd01 , _nsd02 , _nsd03 , _nsd04 , _nsd05 , _nsd06 , _nsd07 , _nsd08 , _nsd09 , _nsd0A , _nsd0B , _nsd0C , _nsd0D , _nsd0E , _nsd0F , _nsd10 , _nsd11 , _nsd12 , _nsd13 , _nsd14 , _nsd15 , _nsd16 , _nsd17 , _nsd18 , _nsd19 , _nsd1A , _nsd1B , _nsd1C , _nsd1D , _nsd1E , _nsd1F , _nsd20 , _nsd21 , _nsd22 , _nsd23 , _nsd24 , _nsd25 , _nsd26 , _nsd27 , _nsd28 , _nsd29 , _nsd2A , _nsd2B , _nsd2C , _nsd2D , _nsd2E , _nsd2F , _nsd30 , _nsd31 , _nsd32 , _nsd33 , _nsd34 , _nsd35 , _nsd36 , _nsd37 , _nsd38 , _nsd39 , _nsd3A , _nsd3B , _nsd3C , _nsd3D , _nsd3E , _nsd3F <] .
Lemma RoundsBase_ι_Round_ι_unused_bs_id: RoundsBase_ι_Round_ι_unused_bs_def = [> _nsd00 , _nsd01 , _nsd02 , _nsd03 , _nsd04 , _nsd05 , _nsd06 , _nsd07 , _nsd08 , _nsd09 , _nsd0A , _nsd0B , _nsd0C , _nsd0D , _nsd0E , _nsd0F , _nsd10 , _nsd11 , _nsd12 , _nsd13 , _nsd14 , _nsd15 , _nsd16 , _nsd17 , _nsd18 , _nsd19 , _nsd1A , _nsd1B , _nsd1C , _nsd1D , _nsd1E , _nsd1F , _nsd20 , _nsd21 , _nsd22 , _nsd23 , _nsd24 , _nsd25 , _nsd26 , _nsd27 , _nsd28 , _nsd29 , _nsd2A , _nsd2B , _nsd2C , _nsd2D , _nsd2E , _nsd2F , _nsd30 , _nsd31 , _nsd32 , _nsd33 , _nsd34 , _nsd35 , _nsd36 , _nsd37 , _nsd38 , _nsd39 , _nsd3A , _nsd3B , _nsd3C , _nsd3D , _nsd3E , _nsd3F (* } !*)  <] .
Proof. auto. Qed.
Axiom RoundsBase_ι_Round_ι_unused_bs' : Z2IBS_pos (tvmBitStringLen RoundsBase_ι_Round_ι_unused_bs_def) RoundsBase_ι_Round_ι_unused = RoundsBase_ι_Round_ι_unused_bs_def.
Lemma RoundsBase_ι_Round_ι_unused_bs : Z2IBS_pos 64 RoundsBase_ι_Round_ι_unused = RoundsBase_ι_Round_ι_unused_bs_def.
Proof.
 rewrite <- RoundsBase_ι_Round_ι_unused_bs'. auto. Qed.
Axiom RoundsBase_ι_Round_ι_unused_pos: (0 <= RoundsBase_ι_Round_ι_unused )%Z.
Axiom RoundsBase_ι_Round_ι_unused_fits: zFitN_pos (tvmBitStringLen RoundsBase_ι_Round_ι_unused_bs_def) RoundsBase_ι_Round_ι_unused = true.
Lemma RoundsBase_ι_Round_ι_unused_bs_rev : I2ZBS_pos' RoundsBase_ι_Round_ι_unused_bs_def = RoundsBase_ι_Round_ι_unused .
Proof.
  prove_bs_rev RoundsBase_ι_Round_ι_unused_bs RoundsBase_ι_Round_ι_unused_pos RoundsBase_ι_Round_ι_unused_fits. 
Qed.
Lemma RoundsBase_ι_Round_ι_unused_bs257 : Z2IN 257 RoundsBase_ι_Round_ι_unused = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    RoundsBase_ι_Round_ι_unused_bs_def)) RoundsBase_ι_Round_ι_unused_bs_def)).
Proof.
  prove_bs_rev RoundsBase_ι_Round_ι_unused_bs_rev RoundsBase_ι_Round_ι_unused_bs_def.
Qed. 
Variables RoundsBase_ι_Round_ι_completionStatus : Z . 
Variables (*! { _cmpl !*) _cmpl00 _cmpl01 _cmpl02 _cmpl03 _cmpl04 _cmpl05 _cmpl06 _cmpl07  : TVMBit . 
Definition RoundsBase_ι_Round_ι_completionStatus_bs_def := [> _cmpl00 , _cmpl01 , _cmpl02 , _cmpl03 , _cmpl04 , _cmpl05 , _cmpl06 , _cmpl07 <] .
Lemma RoundsBase_ι_Round_ι_completionStatus_bs_id: RoundsBase_ι_Round_ι_completionStatus_bs_def = [> _cmpl00 , _cmpl01 , _cmpl02 , _cmpl03 , _cmpl04 , _cmpl05 , _cmpl06 , _cmpl07 (* } !*)  <] .
Proof. auto. Qed.
Axiom RoundsBase_ι_Round_ι_completionStatus_bs' : Z2IBS_pos (tvmBitStringLen RoundsBase_ι_Round_ι_completionStatus_bs_def) RoundsBase_ι_Round_ι_completionStatus = RoundsBase_ι_Round_ι_completionStatus_bs_def.
Lemma RoundsBase_ι_Round_ι_completionStatus_bs : Z2IBS_pos 8 RoundsBase_ι_Round_ι_completionStatus = RoundsBase_ι_Round_ι_completionStatus_bs_def.
Proof.
 rewrite <- RoundsBase_ι_Round_ι_completionStatus_bs'. auto. Qed.
Axiom RoundsBase_ι_Round_ι_completionStatus_pos: (0 <= RoundsBase_ι_Round_ι_completionStatus )%Z.
Axiom RoundsBase_ι_Round_ι_completionStatus_fits: zFitN_pos (tvmBitStringLen RoundsBase_ι_Round_ι_completionStatus_bs_def) RoundsBase_ι_Round_ι_completionStatus = true.
Lemma RoundsBase_ι_Round_ι_completionStatus_bs_rev : I2ZBS_pos' RoundsBase_ι_Round_ι_completionStatus_bs_def = RoundsBase_ι_Round_ι_completionStatus .
Proof.
  prove_bs_rev RoundsBase_ι_Round_ι_completionStatus_bs RoundsBase_ι_Round_ι_completionStatus_pos RoundsBase_ι_Round_ι_completionStatus_fits. 
Qed.
Lemma RoundsBase_ι_Round_ι_completionStatus_bs257 : Z2IN 257 RoundsBase_ι_Round_ι_completionStatus = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    RoundsBase_ι_Round_ι_completionStatus_bs_def)) RoundsBase_ι_Round_ι_completionStatus_bs_def)).
Proof.
  prove_bs_rev RoundsBase_ι_Round_ι_completionStatus_bs_rev RoundsBase_ι_Round_ι_completionStatus_bs_def.
Qed. 
Variables RoundsBase_ι_Round_ι_start : Z . 
Variables (*! { _strt !*) _strt00 _strt01 _strt02 _strt03 _strt04 _strt05 _strt06 _strt07 _strt08 _strt09 _strt0A _strt0B _strt0C _strt0D _strt0E _strt0F _strt10 _strt11 _strt12 _strt13 _strt14 _strt15 _strt16 _strt17 _strt18 _strt19 _strt1A _strt1B _strt1C _strt1D _strt1E _strt1F  : TVMBit . 
Definition RoundsBase_ι_Round_ι_start_bs_def := [> _strt00 , _strt01 , _strt02 , _strt03 , _strt04 , _strt05 , _strt06 , _strt07 , _strt08 , _strt09 , _strt0A , _strt0B , _strt0C , _strt0D , _strt0E , _strt0F , _strt10 , _strt11 , _strt12 , _strt13 , _strt14 , _strt15 , _strt16 , _strt17 , _strt18 , _strt19 , _strt1A , _strt1B , _strt1C , _strt1D , _strt1E , _strt1F <] .
Lemma RoundsBase_ι_Round_ι_start_bs_id: RoundsBase_ι_Round_ι_start_bs_def = [> _strt00 , _strt01 , _strt02 , _strt03 , _strt04 , _strt05 , _strt06 , _strt07 , _strt08 , _strt09 , _strt0A , _strt0B , _strt0C , _strt0D , _strt0E , _strt0F , _strt10 , _strt11 , _strt12 , _strt13 , _strt14 , _strt15 , _strt16 , _strt17 , _strt18 , _strt19 , _strt1A , _strt1B , _strt1C , _strt1D , _strt1E , _strt1F (* } !*)  <] .
Proof. auto. Qed.
Axiom RoundsBase_ι_Round_ι_start_bs' : Z2IBS_pos (tvmBitStringLen RoundsBase_ι_Round_ι_start_bs_def) RoundsBase_ι_Round_ι_start = RoundsBase_ι_Round_ι_start_bs_def.
Lemma RoundsBase_ι_Round_ι_start_bs : Z2IBS_pos 32 RoundsBase_ι_Round_ι_start = RoundsBase_ι_Round_ι_start_bs_def.
Proof.
 rewrite <- RoundsBase_ι_Round_ι_start_bs'. auto. Qed.
Axiom RoundsBase_ι_Round_ι_start_pos: (0 <= RoundsBase_ι_Round_ι_start )%Z.
Axiom RoundsBase_ι_Round_ι_start_fits: zFitN_pos (tvmBitStringLen RoundsBase_ι_Round_ι_start_bs_def) RoundsBase_ι_Round_ι_start = true.
Lemma RoundsBase_ι_Round_ι_start_bs_rev : I2ZBS_pos' RoundsBase_ι_Round_ι_start_bs_def = RoundsBase_ι_Round_ι_start .
Proof.
  prove_bs_rev RoundsBase_ι_Round_ι_start_bs RoundsBase_ι_Round_ι_start_pos RoundsBase_ι_Round_ι_start_fits. 
Qed.
Lemma RoundsBase_ι_Round_ι_start_bs257 : Z2IN 257 RoundsBase_ι_Round_ι_start = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    RoundsBase_ι_Round_ι_start_bs_def)) RoundsBase_ι_Round_ι_start_bs_def)).
Proof.
  prove_bs_rev RoundsBase_ι_Round_ι_start_bs_rev RoundsBase_ι_Round_ι_start_bs_def.
Qed. 
Variables RoundsBase_ι_Round_ι_end : Z . 
Variables (*! { _nd !*) _nd00 _nd01 _nd02 _nd03 _nd04 _nd05 _nd06 _nd07 _nd08 _nd09 _nd0A _nd0B _nd0C _nd0D _nd0E _nd0F _nd10 _nd11 _nd12 _nd13 _nd14 _nd15 _nd16 _nd17 _nd18 _nd19 _nd1A _nd1B _nd1C _nd1D _nd1E _nd1F  : TVMBit . 
Definition RoundsBase_ι_Round_ι_end_bs_def := [> _nd00 , _nd01 , _nd02 , _nd03 , _nd04 , _nd05 , _nd06 , _nd07 , _nd08 , _nd09 , _nd0A , _nd0B , _nd0C , _nd0D , _nd0E , _nd0F , _nd10 , _nd11 , _nd12 , _nd13 , _nd14 , _nd15 , _nd16 , _nd17 , _nd18 , _nd19 , _nd1A , _nd1B , _nd1C , _nd1D , _nd1E , _nd1F <] .
Lemma RoundsBase_ι_Round_ι_end_bs_id: RoundsBase_ι_Round_ι_end_bs_def = [> _nd00 , _nd01 , _nd02 , _nd03 , _nd04 , _nd05 , _nd06 , _nd07 , _nd08 , _nd09 , _nd0A , _nd0B , _nd0C , _nd0D , _nd0E , _nd0F , _nd10 , _nd11 , _nd12 , _nd13 , _nd14 , _nd15 , _nd16 , _nd17 , _nd18 , _nd19 , _nd1A , _nd1B , _nd1C , _nd1D , _nd1E , _nd1F (* } !*)  <] .
Proof. auto. Qed.
Axiom RoundsBase_ι_Round_ι_end_bs' : Z2IBS_pos (tvmBitStringLen RoundsBase_ι_Round_ι_end_bs_def) RoundsBase_ι_Round_ι_end = RoundsBase_ι_Round_ι_end_bs_def.
Lemma RoundsBase_ι_Round_ι_end_bs : Z2IBS_pos 32 RoundsBase_ι_Round_ι_end = RoundsBase_ι_Round_ι_end_bs_def.
Proof.
 rewrite <- RoundsBase_ι_Round_ι_end_bs'. auto. Qed.
Axiom RoundsBase_ι_Round_ι_end_pos: (0 <= RoundsBase_ι_Round_ι_end )%Z.
Axiom RoundsBase_ι_Round_ι_end_fits: zFitN_pos (tvmBitStringLen RoundsBase_ι_Round_ι_end_bs_def) RoundsBase_ι_Round_ι_end = true.
Lemma RoundsBase_ι_Round_ι_end_bs_rev : I2ZBS_pos' RoundsBase_ι_Round_ι_end_bs_def = RoundsBase_ι_Round_ι_end .
Proof.
  prove_bs_rev RoundsBase_ι_Round_ι_end_bs RoundsBase_ι_Round_ι_end_pos RoundsBase_ι_Round_ι_end_fits. 
Qed.
Lemma RoundsBase_ι_Round_ι_end_bs257 : Z2IN 257 RoundsBase_ι_Round_ι_end = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    RoundsBase_ι_Round_ι_end_bs_def)) RoundsBase_ι_Round_ι_end_bs_def)).
Proof.
  prove_bs_rev RoundsBase_ι_Round_ι_end_bs_rev RoundsBase_ι_Round_ι_end_bs_def.
Qed.

Variables RoundsBase_ι_RoundInfo_ι_id : Z . 
Variables (*! { _d !*) _d00 _d01 _d02 _d03 _d04 _d05 _d06 _d07 _d08 _d09 _d0A _d0B _d0C _d0D _d0E _d0F _d10 _d11 _d12 _d13 _d14 _d15 _d16 _d17 _d18 _d19 _d1A _d1B _d1C _d1D _d1E _d1F  : TVMBit . 
Definition RoundsBase_ι_RoundInfo_ι_id_bs_def := [> _d00 , _d01 , _d02 , _d03 , _d04 , _d05 , _d06 , _d07 , _d08 , _d09 , _d0A , _d0B , _d0C , _d0D , _d0E , _d0F , _d10 , _d11 , _d12 , _d13 , _d14 , _d15 , _d16 , _d17 , _d18 , _d19 , _d1A , _d1B , _d1C , _d1D , _d1E , _d1F <] .
Lemma RoundsBase_ι_RoundInfo_ι_id_bs_id: RoundsBase_ι_RoundInfo_ι_id_bs_def = [> _d00 , _d01 , _d02 , _d03 , _d04 , _d05 , _d06 , _d07 , _d08 , _d09 , _d0A , _d0B , _d0C , _d0D , _d0E , _d0F , _d10 , _d11 , _d12 , _d13 , _d14 , _d15 , _d16 , _d17 , _d18 , _d19 , _d1A , _d1B , _d1C , _d1D , _d1E , _d1F (* } !*)  <] .
Proof. auto. Qed.
Axiom RoundsBase_ι_RoundInfo_ι_id_bs' : Z2IBS_pos (tvmBitStringLen RoundsBase_ι_RoundInfo_ι_id_bs_def) RoundsBase_ι_RoundInfo_ι_id = RoundsBase_ι_RoundInfo_ι_id_bs_def.
Lemma RoundsBase_ι_RoundInfo_ι_id_bs : Z2IBS_pos 32 RoundsBase_ι_RoundInfo_ι_id = RoundsBase_ι_RoundInfo_ι_id_bs_def.
Proof.
 rewrite <- RoundsBase_ι_RoundInfo_ι_id_bs'. auto. Qed.
Axiom RoundsBase_ι_RoundInfo_ι_id_pos: (0 <= RoundsBase_ι_RoundInfo_ι_id )%Z.
Axiom RoundsBase_ι_RoundInfo_ι_id_fits: zFitN_pos (tvmBitStringLen RoundsBase_ι_RoundInfo_ι_id_bs_def) RoundsBase_ι_RoundInfo_ι_id = true.
Lemma RoundsBase_ι_RoundInfo_ι_id_bs_rev : I2ZBS_pos' RoundsBase_ι_RoundInfo_ι_id_bs_def = RoundsBase_ι_RoundInfo_ι_id .
Proof.
  prove_bs_rev RoundsBase_ι_RoundInfo_ι_id_bs RoundsBase_ι_RoundInfo_ι_id_pos RoundsBase_ι_RoundInfo_ι_id_fits. 
Qed.
Lemma RoundsBase_ι_RoundInfo_ι_id_bs257 : Z2IN 257 RoundsBase_ι_RoundInfo_ι_id = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    RoundsBase_ι_RoundInfo_ι_id_bs_def)) RoundsBase_ι_RoundInfo_ι_id_bs_def)).
Proof.
  prove_bs_rev RoundsBase_ι_RoundInfo_ι_id_bs_rev RoundsBase_ι_RoundInfo_ι_id_bs_def.
Qed. 
Variables RoundsBase_ι_RoundInfo_ι_start : Z . 
Variables (*! { _strt !*) _strt00 _strt01 _strt02 _strt03 _strt04 _strt05 _strt06 _strt07 _strt08 _strt09 _strt0A _strt0B _strt0C _strt0D _strt0E _strt0F _strt10 _strt11 _strt12 _strt13 _strt14 _strt15 _strt16 _strt17 _strt18 _strt19 _strt1A _strt1B _strt1C _strt1D _strt1E _strt1F  : TVMBit . 
Definition RoundsBase_ι_RoundInfo_ι_start_bs_def := [> _strt00 , _strt01 , _strt02 , _strt03 , _strt04 , _strt05 , _strt06 , _strt07 , _strt08 , _strt09 , _strt0A , _strt0B , _strt0C , _strt0D , _strt0E , _strt0F , _strt10 , _strt11 , _strt12 , _strt13 , _strt14 , _strt15 , _strt16 , _strt17 , _strt18 , _strt19 , _strt1A , _strt1B , _strt1C , _strt1D , _strt1E , _strt1F <] .
Lemma RoundsBase_ι_RoundInfo_ι_start_bs_id: RoundsBase_ι_RoundInfo_ι_start_bs_def = [> _strt00 , _strt01 , _strt02 , _strt03 , _strt04 , _strt05 , _strt06 , _strt07 , _strt08 , _strt09 , _strt0A , _strt0B , _strt0C , _strt0D , _strt0E , _strt0F , _strt10 , _strt11 , _strt12 , _strt13 , _strt14 , _strt15 , _strt16 , _strt17 , _strt18 , _strt19 , _strt1A , _strt1B , _strt1C , _strt1D , _strt1E , _strt1F (* } !*)  <] .
Proof. auto. Qed.
Axiom RoundsBase_ι_RoundInfo_ι_start_bs' : Z2IBS_pos (tvmBitStringLen RoundsBase_ι_RoundInfo_ι_start_bs_def) RoundsBase_ι_RoundInfo_ι_start = RoundsBase_ι_RoundInfo_ι_start_bs_def.
Lemma RoundsBase_ι_RoundInfo_ι_start_bs : Z2IBS_pos 32 RoundsBase_ι_RoundInfo_ι_start = RoundsBase_ι_RoundInfo_ι_start_bs_def.
Proof.
 rewrite <- RoundsBase_ι_RoundInfo_ι_start_bs'. auto. Qed.
Axiom RoundsBase_ι_RoundInfo_ι_start_pos: (0 <= RoundsBase_ι_RoundInfo_ι_start )%Z.
Axiom RoundsBase_ι_RoundInfo_ι_start_fits: zFitN_pos (tvmBitStringLen RoundsBase_ι_RoundInfo_ι_start_bs_def) RoundsBase_ι_RoundInfo_ι_start = true.
Lemma RoundsBase_ι_RoundInfo_ι_start_bs_rev : I2ZBS_pos' RoundsBase_ι_RoundInfo_ι_start_bs_def = RoundsBase_ι_RoundInfo_ι_start .
Proof.
  prove_bs_rev RoundsBase_ι_RoundInfo_ι_start_bs RoundsBase_ι_RoundInfo_ι_start_pos RoundsBase_ι_RoundInfo_ι_start_fits. 
Qed.
Lemma RoundsBase_ι_RoundInfo_ι_start_bs257 : Z2IN 257 RoundsBase_ι_RoundInfo_ι_start = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    RoundsBase_ι_RoundInfo_ι_start_bs_def)) RoundsBase_ι_RoundInfo_ι_start_bs_def)).
Proof.
  prove_bs_rev RoundsBase_ι_RoundInfo_ι_start_bs_rev RoundsBase_ι_RoundInfo_ι_start_bs_def.
Qed. 
Variables RoundsBase_ι_RoundInfo_ι_end : Z . 
Variables (*! { _nd !*) _nd00 _nd01 _nd02 _nd03 _nd04 _nd05 _nd06 _nd07 _nd08 _nd09 _nd0A _nd0B _nd0C _nd0D _nd0E _nd0F _nd10 _nd11 _nd12 _nd13 _nd14 _nd15 _nd16 _nd17 _nd18 _nd19 _nd1A _nd1B _nd1C _nd1D _nd1E _nd1F  : TVMBit . 
Definition RoundsBase_ι_RoundInfo_ι_end_bs_def := [> _nd00 , _nd01 , _nd02 , _nd03 , _nd04 , _nd05 , _nd06 , _nd07 , _nd08 , _nd09 , _nd0A , _nd0B , _nd0C , _nd0D , _nd0E , _nd0F , _nd10 , _nd11 , _nd12 , _nd13 , _nd14 , _nd15 , _nd16 , _nd17 , _nd18 , _nd19 , _nd1A , _nd1B , _nd1C , _nd1D , _nd1E , _nd1F <] .
Lemma RoundsBase_ι_RoundInfo_ι_end_bs_id: RoundsBase_ι_RoundInfo_ι_end_bs_def = [> _nd00 , _nd01 , _nd02 , _nd03 , _nd04 , _nd05 , _nd06 , _nd07 , _nd08 , _nd09 , _nd0A , _nd0B , _nd0C , _nd0D , _nd0E , _nd0F , _nd10 , _nd11 , _nd12 , _nd13 , _nd14 , _nd15 , _nd16 , _nd17 , _nd18 , _nd19 , _nd1A , _nd1B , _nd1C , _nd1D , _nd1E , _nd1F (* } !*)  <] .
Proof. auto. Qed.
Axiom RoundsBase_ι_RoundInfo_ι_end_bs' : Z2IBS_pos (tvmBitStringLen RoundsBase_ι_RoundInfo_ι_end_bs_def) RoundsBase_ι_RoundInfo_ι_end = RoundsBase_ι_RoundInfo_ι_end_bs_def.
Lemma RoundsBase_ι_RoundInfo_ι_end_bs : Z2IBS_pos 32 RoundsBase_ι_RoundInfo_ι_end = RoundsBase_ι_RoundInfo_ι_end_bs_def.
Proof.
 rewrite <- RoundsBase_ι_RoundInfo_ι_end_bs'. auto. Qed.
Axiom RoundsBase_ι_RoundInfo_ι_end_pos: (0 <= RoundsBase_ι_RoundInfo_ι_end )%Z.
Axiom RoundsBase_ι_RoundInfo_ι_end_fits: zFitN_pos (tvmBitStringLen RoundsBase_ι_RoundInfo_ι_end_bs_def) RoundsBase_ι_RoundInfo_ι_end = true.
Lemma RoundsBase_ι_RoundInfo_ι_end_bs_rev : I2ZBS_pos' RoundsBase_ι_RoundInfo_ι_end_bs_def = RoundsBase_ι_RoundInfo_ι_end .
Proof.
  prove_bs_rev RoundsBase_ι_RoundInfo_ι_end_bs RoundsBase_ι_RoundInfo_ι_end_pos RoundsBase_ι_RoundInfo_ι_end_fits. 
Qed.
Lemma RoundsBase_ι_RoundInfo_ι_end_bs257 : Z2IN 257 RoundsBase_ι_RoundInfo_ι_end = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    RoundsBase_ι_RoundInfo_ι_end_bs_def)) RoundsBase_ι_RoundInfo_ι_end_bs_def)).
Proof.
  prove_bs_rev RoundsBase_ι_RoundInfo_ι_end_bs_rev RoundsBase_ι_RoundInfo_ι_end_bs_def.
Qed. 
Variables RoundsBase_ι_RoundInfo_ι_step : Z . 
Variables (*! { _stp !*) _stp00 _stp01 _stp02 _stp03 _stp04 _stp05 _stp06 _stp07  : TVMBit . 
Definition RoundsBase_ι_RoundInfo_ι_step_bs_def := [> _stp00 , _stp01 , _stp02 , _stp03 , _stp04 , _stp05 , _stp06 , _stp07 <] .
Lemma RoundsBase_ι_RoundInfo_ι_step_bs_id: RoundsBase_ι_RoundInfo_ι_step_bs_def = [> _stp00 , _stp01 , _stp02 , _stp03 , _stp04 , _stp05 , _stp06 , _stp07 (* } !*)  <] .
Proof. auto. Qed.
Axiom RoundsBase_ι_RoundInfo_ι_step_bs' : Z2IBS_pos (tvmBitStringLen RoundsBase_ι_RoundInfo_ι_step_bs_def) RoundsBase_ι_RoundInfo_ι_step = RoundsBase_ι_RoundInfo_ι_step_bs_def.
Lemma RoundsBase_ι_RoundInfo_ι_step_bs : Z2IBS_pos 8 RoundsBase_ι_RoundInfo_ι_step = RoundsBase_ι_RoundInfo_ι_step_bs_def.
Proof.
 rewrite <- RoundsBase_ι_RoundInfo_ι_step_bs'. auto. Qed.
Axiom RoundsBase_ι_RoundInfo_ι_step_pos: (0 <= RoundsBase_ι_RoundInfo_ι_step )%Z.
Axiom RoundsBase_ι_RoundInfo_ι_step_fits: zFitN_pos (tvmBitStringLen RoundsBase_ι_RoundInfo_ι_step_bs_def) RoundsBase_ι_RoundInfo_ι_step = true.
Lemma RoundsBase_ι_RoundInfo_ι_step_bs_rev : I2ZBS_pos' RoundsBase_ι_RoundInfo_ι_step_bs_def = RoundsBase_ι_RoundInfo_ι_step .
Proof.
  prove_bs_rev RoundsBase_ι_RoundInfo_ι_step_bs RoundsBase_ι_RoundInfo_ι_step_pos RoundsBase_ι_RoundInfo_ι_step_fits. 
Qed.
Lemma RoundsBase_ι_RoundInfo_ι_step_bs257 : Z2IN 257 RoundsBase_ι_RoundInfo_ι_step = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    RoundsBase_ι_RoundInfo_ι_step_bs_def)) RoundsBase_ι_RoundInfo_ι_step_bs_def)).
Proof.
  prove_bs_rev RoundsBase_ι_RoundInfo_ι_step_bs_rev RoundsBase_ι_RoundInfo_ι_step_bs_def.
Qed. 
Variables RoundsBase_ι_RoundInfo_ι_completionStatus : Z . 
Variables (*! { _cmpl !*) _cmpl00 _cmpl01 _cmpl02 _cmpl03 _cmpl04 _cmpl05 _cmpl06 _cmpl07  : TVMBit . 
Definition RoundsBase_ι_RoundInfo_ι_completionStatus_bs_def := [> _cmpl00 , _cmpl01 , _cmpl02 , _cmpl03 , _cmpl04 , _cmpl05 , _cmpl06 , _cmpl07 <] .
Lemma RoundsBase_ι_RoundInfo_ι_completionStatus_bs_id: RoundsBase_ι_RoundInfo_ι_completionStatus_bs_def = [> _cmpl00 , _cmpl01 , _cmpl02 , _cmpl03 , _cmpl04 , _cmpl05 , _cmpl06 , _cmpl07 (* } !*)  <] .
Proof. auto. Qed.
Axiom RoundsBase_ι_RoundInfo_ι_completionStatus_bs' : Z2IBS_pos (tvmBitStringLen RoundsBase_ι_RoundInfo_ι_completionStatus_bs_def) RoundsBase_ι_RoundInfo_ι_completionStatus = RoundsBase_ι_RoundInfo_ι_completionStatus_bs_def.
Lemma RoundsBase_ι_RoundInfo_ι_completionStatus_bs : Z2IBS_pos 8 RoundsBase_ι_RoundInfo_ι_completionStatus = RoundsBase_ι_RoundInfo_ι_completionStatus_bs_def.
Proof.
 rewrite <- RoundsBase_ι_RoundInfo_ι_completionStatus_bs'. auto. Qed.
Axiom RoundsBase_ι_RoundInfo_ι_completionStatus_pos: (0 <= RoundsBase_ι_RoundInfo_ι_completionStatus )%Z.
Axiom RoundsBase_ι_RoundInfo_ι_completionStatus_fits: zFitN_pos (tvmBitStringLen RoundsBase_ι_RoundInfo_ι_completionStatus_bs_def) RoundsBase_ι_RoundInfo_ι_completionStatus = true.
Lemma RoundsBase_ι_RoundInfo_ι_completionStatus_bs_rev : I2ZBS_pos' RoundsBase_ι_RoundInfo_ι_completionStatus_bs_def = RoundsBase_ι_RoundInfo_ι_completionStatus .
Proof.
  prove_bs_rev RoundsBase_ι_RoundInfo_ι_completionStatus_bs RoundsBase_ι_RoundInfo_ι_completionStatus_pos RoundsBase_ι_RoundInfo_ι_completionStatus_fits. 
Qed.
Lemma RoundsBase_ι_RoundInfo_ι_completionStatus_bs257 : Z2IN 257 RoundsBase_ι_RoundInfo_ι_completionStatus = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    RoundsBase_ι_RoundInfo_ι_completionStatus_bs_def)) RoundsBase_ι_RoundInfo_ι_completionStatus_bs_def)).
Proof.
  prove_bs_rev RoundsBase_ι_RoundInfo_ι_completionStatus_bs_rev RoundsBase_ι_RoundInfo_ι_completionStatus_bs_def.
Qed. 
Variables RoundsBase_ι_RoundInfo_ι_stake : Z . 
Variables (*! { _stk !*) _stk00 _stk01 _stk02 _stk03 _stk04 _stk05 _stk06 _stk07 _stk08 _stk09 _stk0A _stk0B _stk0C _stk0D _stk0E _stk0F _stk10 _stk11 _stk12 _stk13 _stk14 _stk15 _stk16 _stk17 _stk18 _stk19 _stk1A _stk1B _stk1C _stk1D _stk1E _stk1F _stk20 _stk21 _stk22 _stk23 _stk24 _stk25 _stk26 _stk27 _stk28 _stk29 _stk2A _stk2B _stk2C _stk2D _stk2E _stk2F _stk30 _stk31 _stk32 _stk33 _stk34 _stk35 _stk36 _stk37 _stk38 _stk39 _stk3A _stk3B _stk3C _stk3D _stk3E _stk3F  : TVMBit . 
Definition RoundsBase_ι_RoundInfo_ι_stake_bs_def := [> _stk00 , _stk01 , _stk02 , _stk03 , _stk04 , _stk05 , _stk06 , _stk07 , _stk08 , _stk09 , _stk0A , _stk0B , _stk0C , _stk0D , _stk0E , _stk0F , _stk10 , _stk11 , _stk12 , _stk13 , _stk14 , _stk15 , _stk16 , _stk17 , _stk18 , _stk19 , _stk1A , _stk1B , _stk1C , _stk1D , _stk1E , _stk1F , _stk20 , _stk21 , _stk22 , _stk23 , _stk24 , _stk25 , _stk26 , _stk27 , _stk28 , _stk29 , _stk2A , _stk2B , _stk2C , _stk2D , _stk2E , _stk2F , _stk30 , _stk31 , _stk32 , _stk33 , _stk34 , _stk35 , _stk36 , _stk37 , _stk38 , _stk39 , _stk3A , _stk3B , _stk3C , _stk3D , _stk3E , _stk3F <] .
Lemma RoundsBase_ι_RoundInfo_ι_stake_bs_id: RoundsBase_ι_RoundInfo_ι_stake_bs_def = [> _stk00 , _stk01 , _stk02 , _stk03 , _stk04 , _stk05 , _stk06 , _stk07 , _stk08 , _stk09 , _stk0A , _stk0B , _stk0C , _stk0D , _stk0E , _stk0F , _stk10 , _stk11 , _stk12 , _stk13 , _stk14 , _stk15 , _stk16 , _stk17 , _stk18 , _stk19 , _stk1A , _stk1B , _stk1C , _stk1D , _stk1E , _stk1F , _stk20 , _stk21 , _stk22 , _stk23 , _stk24 , _stk25 , _stk26 , _stk27 , _stk28 , _stk29 , _stk2A , _stk2B , _stk2C , _stk2D , _stk2E , _stk2F , _stk30 , _stk31 , _stk32 , _stk33 , _stk34 , _stk35 , _stk36 , _stk37 , _stk38 , _stk39 , _stk3A , _stk3B , _stk3C , _stk3D , _stk3E , _stk3F (* } !*)  <] .
Proof. auto. Qed.
Axiom RoundsBase_ι_RoundInfo_ι_stake_bs' : Z2IBS_pos (tvmBitStringLen RoundsBase_ι_RoundInfo_ι_stake_bs_def) RoundsBase_ι_RoundInfo_ι_stake = RoundsBase_ι_RoundInfo_ι_stake_bs_def.
Lemma RoundsBase_ι_RoundInfo_ι_stake_bs : Z2IBS_pos 64 RoundsBase_ι_RoundInfo_ι_stake = RoundsBase_ι_RoundInfo_ι_stake_bs_def.
Proof.
 rewrite <- RoundsBase_ι_RoundInfo_ι_stake_bs'. auto. Qed.
Axiom RoundsBase_ι_RoundInfo_ι_stake_pos: (0 <= RoundsBase_ι_RoundInfo_ι_stake )%Z.
Axiom RoundsBase_ι_RoundInfo_ι_stake_fits: zFitN_pos (tvmBitStringLen RoundsBase_ι_RoundInfo_ι_stake_bs_def) RoundsBase_ι_RoundInfo_ι_stake = true.
Lemma RoundsBase_ι_RoundInfo_ι_stake_bs_rev : I2ZBS_pos' RoundsBase_ι_RoundInfo_ι_stake_bs_def = RoundsBase_ι_RoundInfo_ι_stake .
Proof.
  prove_bs_rev RoundsBase_ι_RoundInfo_ι_stake_bs RoundsBase_ι_RoundInfo_ι_stake_pos RoundsBase_ι_RoundInfo_ι_stake_fits. 
Qed.
Lemma RoundsBase_ι_RoundInfo_ι_stake_bs257 : Z2IN 257 RoundsBase_ι_RoundInfo_ι_stake = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    RoundsBase_ι_RoundInfo_ι_stake_bs_def)) RoundsBase_ι_RoundInfo_ι_stake_bs_def)).
Proof.
  prove_bs_rev RoundsBase_ι_RoundInfo_ι_stake_bs_rev RoundsBase_ι_RoundInfo_ι_stake_bs_def.
Qed. 
Variables RoundsBase_ι_RoundInfo_ι_stakeholderCount : Z . 
Variables (*! { _stkh !*) _stkh00 _stkh01 _stkh02 _stkh03 _stkh04 _stkh05 _stkh06 _stkh07 _stkh08 _stkh09 _stkh0A _stkh0B _stkh0C _stkh0D _stkh0E _stkh0F _stkh10 _stkh11 _stkh12 _stkh13 _stkh14 _stkh15 _stkh16 _stkh17 _stkh18 _stkh19 _stkh1A _stkh1B _stkh1C _stkh1D _stkh1E _stkh1F  : TVMBit . 
Definition RoundsBase_ι_RoundInfo_ι_stakeholderCount_bs_def := [> _stkh00 , _stkh01 , _stkh02 , _stkh03 , _stkh04 , _stkh05 , _stkh06 , _stkh07 , _stkh08 , _stkh09 , _stkh0A , _stkh0B , _stkh0C , _stkh0D , _stkh0E , _stkh0F , _stkh10 , _stkh11 , _stkh12 , _stkh13 , _stkh14 , _stkh15 , _stkh16 , _stkh17 , _stkh18 , _stkh19 , _stkh1A , _stkh1B , _stkh1C , _stkh1D , _stkh1E , _stkh1F <] .
Lemma RoundsBase_ι_RoundInfo_ι_stakeholderCount_bs_id: RoundsBase_ι_RoundInfo_ι_stakeholderCount_bs_def = [> _stkh00 , _stkh01 , _stkh02 , _stkh03 , _stkh04 , _stkh05 , _stkh06 , _stkh07 , _stkh08 , _stkh09 , _stkh0A , _stkh0B , _stkh0C , _stkh0D , _stkh0E , _stkh0F , _stkh10 , _stkh11 , _stkh12 , _stkh13 , _stkh14 , _stkh15 , _stkh16 , _stkh17 , _stkh18 , _stkh19 , _stkh1A , _stkh1B , _stkh1C , _stkh1D , _stkh1E , _stkh1F (* } !*)  <] .
Proof. auto. Qed.
Axiom RoundsBase_ι_RoundInfo_ι_stakeholderCount_bs' : Z2IBS_pos (tvmBitStringLen RoundsBase_ι_RoundInfo_ι_stakeholderCount_bs_def) RoundsBase_ι_RoundInfo_ι_stakeholderCount = RoundsBase_ι_RoundInfo_ι_stakeholderCount_bs_def.
Lemma RoundsBase_ι_RoundInfo_ι_stakeholderCount_bs : Z2IBS_pos 32 RoundsBase_ι_RoundInfo_ι_stakeholderCount = RoundsBase_ι_RoundInfo_ι_stakeholderCount_bs_def.
Proof.
 rewrite <- RoundsBase_ι_RoundInfo_ι_stakeholderCount_bs'. auto. Qed.
Axiom RoundsBase_ι_RoundInfo_ι_stakeholderCount_pos: (0 <= RoundsBase_ι_RoundInfo_ι_stakeholderCount )%Z.
Axiom RoundsBase_ι_RoundInfo_ι_stakeholderCount_fits: zFitN_pos (tvmBitStringLen RoundsBase_ι_RoundInfo_ι_stakeholderCount_bs_def) RoundsBase_ι_RoundInfo_ι_stakeholderCount = true.
Lemma RoundsBase_ι_RoundInfo_ι_stakeholderCount_bs_rev : I2ZBS_pos' RoundsBase_ι_RoundInfo_ι_stakeholderCount_bs_def = RoundsBase_ι_RoundInfo_ι_stakeholderCount .
Proof.
  prove_bs_rev RoundsBase_ι_RoundInfo_ι_stakeholderCount_bs RoundsBase_ι_RoundInfo_ι_stakeholderCount_pos RoundsBase_ι_RoundInfo_ι_stakeholderCount_fits. 
Qed.
Lemma RoundsBase_ι_RoundInfo_ι_stakeholderCount_bs257 : Z2IN 257 RoundsBase_ι_RoundInfo_ι_stakeholderCount = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    RoundsBase_ι_RoundInfo_ι_stakeholderCount_bs_def)) RoundsBase_ι_RoundInfo_ι_stakeholderCount_bs_def)).
Proof.
  prove_bs_rev RoundsBase_ι_RoundInfo_ι_stakeholderCount_bs_rev RoundsBase_ι_RoundInfo_ι_stakeholderCount_bs_def.
Qed. 
Variables RoundsBase_ι_RoundInfo_ι_rewards : Z . 
Variables (*! { _rwrd !*) _rwrd00 _rwrd01 _rwrd02 _rwrd03 _rwrd04 _rwrd05 _rwrd06 _rwrd07 _rwrd08 _rwrd09 _rwrd0A _rwrd0B _rwrd0C _rwrd0D _rwrd0E _rwrd0F _rwrd10 _rwrd11 _rwrd12 _rwrd13 _rwrd14 _rwrd15 _rwrd16 _rwrd17 _rwrd18 _rwrd19 _rwrd1A _rwrd1B _rwrd1C _rwrd1D _rwrd1E _rwrd1F _rwrd20 _rwrd21 _rwrd22 _rwrd23 _rwrd24 _rwrd25 _rwrd26 _rwrd27 _rwrd28 _rwrd29 _rwrd2A _rwrd2B _rwrd2C _rwrd2D _rwrd2E _rwrd2F _rwrd30 _rwrd31 _rwrd32 _rwrd33 _rwrd34 _rwrd35 _rwrd36 _rwrd37 _rwrd38 _rwrd39 _rwrd3A _rwrd3B _rwrd3C _rwrd3D _rwrd3E _rwrd3F  : TVMBit . 
Definition RoundsBase_ι_RoundInfo_ι_rewards_bs_def := [> _rwrd00 , _rwrd01 , _rwrd02 , _rwrd03 , _rwrd04 , _rwrd05 , _rwrd06 , _rwrd07 , _rwrd08 , _rwrd09 , _rwrd0A , _rwrd0B , _rwrd0C , _rwrd0D , _rwrd0E , _rwrd0F , _rwrd10 , _rwrd11 , _rwrd12 , _rwrd13 , _rwrd14 , _rwrd15 , _rwrd16 , _rwrd17 , _rwrd18 , _rwrd19 , _rwrd1A , _rwrd1B , _rwrd1C , _rwrd1D , _rwrd1E , _rwrd1F , _rwrd20 , _rwrd21 , _rwrd22 , _rwrd23 , _rwrd24 , _rwrd25 , _rwrd26 , _rwrd27 , _rwrd28 , _rwrd29 , _rwrd2A , _rwrd2B , _rwrd2C , _rwrd2D , _rwrd2E , _rwrd2F , _rwrd30 , _rwrd31 , _rwrd32 , _rwrd33 , _rwrd34 , _rwrd35 , _rwrd36 , _rwrd37 , _rwrd38 , _rwrd39 , _rwrd3A , _rwrd3B , _rwrd3C , _rwrd3D , _rwrd3E , _rwrd3F <] .
Lemma RoundsBase_ι_RoundInfo_ι_rewards_bs_id: RoundsBase_ι_RoundInfo_ι_rewards_bs_def = [> _rwrd00 , _rwrd01 , _rwrd02 , _rwrd03 , _rwrd04 , _rwrd05 , _rwrd06 , _rwrd07 , _rwrd08 , _rwrd09 , _rwrd0A , _rwrd0B , _rwrd0C , _rwrd0D , _rwrd0E , _rwrd0F , _rwrd10 , _rwrd11 , _rwrd12 , _rwrd13 , _rwrd14 , _rwrd15 , _rwrd16 , _rwrd17 , _rwrd18 , _rwrd19 , _rwrd1A , _rwrd1B , _rwrd1C , _rwrd1D , _rwrd1E , _rwrd1F , _rwrd20 , _rwrd21 , _rwrd22 , _rwrd23 , _rwrd24 , _rwrd25 , _rwrd26 , _rwrd27 , _rwrd28 , _rwrd29 , _rwrd2A , _rwrd2B , _rwrd2C , _rwrd2D , _rwrd2E , _rwrd2F , _rwrd30 , _rwrd31 , _rwrd32 , _rwrd33 , _rwrd34 , _rwrd35 , _rwrd36 , _rwrd37 , _rwrd38 , _rwrd39 , _rwrd3A , _rwrd3B , _rwrd3C , _rwrd3D , _rwrd3E , _rwrd3F (* } !*)  <] .
Proof. auto. Qed.
Axiom RoundsBase_ι_RoundInfo_ι_rewards_bs' : Z2IBS_pos (tvmBitStringLen RoundsBase_ι_RoundInfo_ι_rewards_bs_def) RoundsBase_ι_RoundInfo_ι_rewards = RoundsBase_ι_RoundInfo_ι_rewards_bs_def.
Lemma RoundsBase_ι_RoundInfo_ι_rewards_bs : Z2IBS_pos 64 RoundsBase_ι_RoundInfo_ι_rewards = RoundsBase_ι_RoundInfo_ι_rewards_bs_def.
Proof.
 rewrite <- RoundsBase_ι_RoundInfo_ι_rewards_bs'. auto. Qed.
Axiom RoundsBase_ι_RoundInfo_ι_rewards_pos: (0 <= RoundsBase_ι_RoundInfo_ι_rewards )%Z.
Axiom RoundsBase_ι_RoundInfo_ι_rewards_fits: zFitN_pos (tvmBitStringLen RoundsBase_ι_RoundInfo_ι_rewards_bs_def) RoundsBase_ι_RoundInfo_ι_rewards = true.
Lemma RoundsBase_ι_RoundInfo_ι_rewards_bs_rev : I2ZBS_pos' RoundsBase_ι_RoundInfo_ι_rewards_bs_def = RoundsBase_ι_RoundInfo_ι_rewards .
Proof.
  prove_bs_rev RoundsBase_ι_RoundInfo_ι_rewards_bs RoundsBase_ι_RoundInfo_ι_rewards_pos RoundsBase_ι_RoundInfo_ι_rewards_fits. 
Qed.
Lemma RoundsBase_ι_RoundInfo_ι_rewards_bs257 : Z2IN 257 RoundsBase_ι_RoundInfo_ι_rewards = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    RoundsBase_ι_RoundInfo_ι_rewards_bs_def)) RoundsBase_ι_RoundInfo_ι_rewards_bs_def)).
Proof.
  prove_bs_rev RoundsBase_ι_RoundInfo_ι_rewards_bs_rev RoundsBase_ι_RoundInfo_ι_rewards_bs_def.
Qed.
 
Variables StakingContract_ι_Node_ι_factor : Z . 
Variables (*! { _fctr !*) _fctr00 _fctr01 _fctr02 _fctr03 _fctr04 _fctr05 _fctr06 _fctr07 _fctr08 _fctr09 _fctr0A _fctr0B _fctr0C _fctr0D _fctr0E _fctr0F _fctr10 _fctr11 _fctr12 _fctr13 _fctr14 _fctr15 _fctr16 _fctr17 _fctr18 _fctr19 _fctr1A _fctr1B _fctr1C _fctr1D _fctr1E _fctr1F  : TVMBit . 
Definition StakingContract_ι_Node_ι_factor_bs_def := [> _fctr00 , _fctr01 , _fctr02 , _fctr03 , _fctr04 , _fctr05 , _fctr06 , _fctr07 , _fctr08 , _fctr09 , _fctr0A , _fctr0B , _fctr0C , _fctr0D , _fctr0E , _fctr0F , _fctr10 , _fctr11 , _fctr12 , _fctr13 , _fctr14 , _fctr15 , _fctr16 , _fctr17 , _fctr18 , _fctr19 , _fctr1A , _fctr1B , _fctr1C , _fctr1D , _fctr1E , _fctr1F <] .
Lemma StakingContract_ι_Node_ι_factor_bs_id: StakingContract_ι_Node_ι_factor_bs_def = [> _fctr00 , _fctr01 , _fctr02 , _fctr03 , _fctr04 , _fctr05 , _fctr06 , _fctr07 , _fctr08 , _fctr09 , _fctr0A , _fctr0B , _fctr0C , _fctr0D , _fctr0E , _fctr0F , _fctr10 , _fctr11 , _fctr12 , _fctr13 , _fctr14 , _fctr15 , _fctr16 , _fctr17 , _fctr18 , _fctr19 , _fctr1A , _fctr1B , _fctr1C , _fctr1D , _fctr1E , _fctr1F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι_Node_ι_factor_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι_Node_ι_factor_bs_def) StakingContract_ι_Node_ι_factor = StakingContract_ι_Node_ι_factor_bs_def.
Lemma StakingContract_ι_Node_ι_factor_bs : Z2IBS_pos 32 StakingContract_ι_Node_ι_factor = StakingContract_ι_Node_ι_factor_bs_def.
Proof.
 rewrite <- StakingContract_ι_Node_ι_factor_bs'. auto. Qed.
Axiom StakingContract_ι_Node_ι_factor_pos: (0 <= StakingContract_ι_Node_ι_factor )%Z.
Axiom StakingContract_ι_Node_ι_factor_fits: zFitN_pos (tvmBitStringLen StakingContract_ι_Node_ι_factor_bs_def) StakingContract_ι_Node_ι_factor = true.
Lemma StakingContract_ι_Node_ι_factor_bs_rev : I2ZBS_pos' StakingContract_ι_Node_ι_factor_bs_def = StakingContract_ι_Node_ι_factor .
Proof.
  prove_bs_rev StakingContract_ι_Node_ι_factor_bs StakingContract_ι_Node_ι_factor_pos StakingContract_ι_Node_ι_factor_fits. 
Qed.
Lemma StakingContract_ι_Node_ι_factor_bs257 : Z2IN 257 StakingContract_ι_Node_ι_factor = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι_Node_ι_factor_bs_def)) StakingContract_ι_Node_ι_factor_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι_Node_ι_factor_bs_rev StakingContract_ι_Node_ι_factor_bs_def.
Qed.

Variables StakingContract_ι_StakeInfo_ι_roundId : Z . 
Variables (*! { _rndd !*) _rndd00 _rndd01 _rndd02 _rndd03 _rndd04 _rndd05 _rndd06 _rndd07 _rndd08 _rndd09 _rndd0A _rndd0B _rndd0C _rndd0D _rndd0E _rndd0F _rndd10 _rndd11 _rndd12 _rndd13 _rndd14 _rndd15 _rndd16 _rndd17 _rndd18 _rndd19 _rndd1A _rndd1B _rndd1C _rndd1D _rndd1E _rndd1F  : TVMBit . 
Definition StakingContract_ι_StakeInfo_ι_roundId_bs_def := [> _rndd00 , _rndd01 , _rndd02 , _rndd03 , _rndd04 , _rndd05 , _rndd06 , _rndd07 , _rndd08 , _rndd09 , _rndd0A , _rndd0B , _rndd0C , _rndd0D , _rndd0E , _rndd0F , _rndd10 , _rndd11 , _rndd12 , _rndd13 , _rndd14 , _rndd15 , _rndd16 , _rndd17 , _rndd18 , _rndd19 , _rndd1A , _rndd1B , _rndd1C , _rndd1D , _rndd1E , _rndd1F <] .
Lemma StakingContract_ι_StakeInfo_ι_roundId_bs_id: StakingContract_ι_StakeInfo_ι_roundId_bs_def = [> _rndd00 , _rndd01 , _rndd02 , _rndd03 , _rndd04 , _rndd05 , _rndd06 , _rndd07 , _rndd08 , _rndd09 , _rndd0A , _rndd0B , _rndd0C , _rndd0D , _rndd0E , _rndd0F , _rndd10 , _rndd11 , _rndd12 , _rndd13 , _rndd14 , _rndd15 , _rndd16 , _rndd17 , _rndd18 , _rndd19 , _rndd1A , _rndd1B , _rndd1C , _rndd1D , _rndd1E , _rndd1F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι_StakeInfo_ι_roundId_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι_StakeInfo_ι_roundId_bs_def) StakingContract_ι_StakeInfo_ι_roundId = StakingContract_ι_StakeInfo_ι_roundId_bs_def.
Lemma StakingContract_ι_StakeInfo_ι_roundId_bs : Z2IBS_pos 32 StakingContract_ι_StakeInfo_ι_roundId = StakingContract_ι_StakeInfo_ι_roundId_bs_def.
Proof.
 rewrite <- StakingContract_ι_StakeInfo_ι_roundId_bs'. auto. Qed.
Axiom StakingContract_ι_StakeInfo_ι_roundId_pos: (0 <= StakingContract_ι_StakeInfo_ι_roundId )%Z.
Axiom StakingContract_ι_StakeInfo_ι_roundId_fits: zFitN_pos (tvmBitStringLen StakingContract_ι_StakeInfo_ι_roundId_bs_def) StakingContract_ι_StakeInfo_ι_roundId = true.
Lemma StakingContract_ι_StakeInfo_ι_roundId_bs_rev : I2ZBS_pos' StakingContract_ι_StakeInfo_ι_roundId_bs_def = StakingContract_ι_StakeInfo_ι_roundId .
Proof.
  prove_bs_rev StakingContract_ι_StakeInfo_ι_roundId_bs StakingContract_ι_StakeInfo_ι_roundId_pos StakingContract_ι_StakeInfo_ι_roundId_fits. 
Qed.
Lemma StakingContract_ι_StakeInfo_ι_roundId_bs257 : Z2IN 257 StakingContract_ι_StakeInfo_ι_roundId = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι_StakeInfo_ι_roundId_bs_def)) StakingContract_ι_StakeInfo_ι_roundId_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι_StakeInfo_ι_roundId_bs_rev StakingContract_ι_StakeInfo_ι_roundId_bs_def.
Qed. 
Variables StakingContract_ι_StakeInfo_ι_stake : Z . 
Variables (*! { _stk !*) _stk00 _stk01 _stk02 _stk03 _stk04 _stk05 _stk06 _stk07 _stk08 _stk09 _stk0A _stk0B _stk0C _stk0D _stk0E _stk0F _stk10 _stk11 _stk12 _stk13 _stk14 _stk15 _stk16 _stk17 _stk18 _stk19 _stk1A _stk1B _stk1C _stk1D _stk1E _stk1F _stk20 _stk21 _stk22 _stk23 _stk24 _stk25 _stk26 _stk27 _stk28 _stk29 _stk2A _stk2B _stk2C _stk2D _stk2E _stk2F _stk30 _stk31 _stk32 _stk33 _stk34 _stk35 _stk36 _stk37 _stk38 _stk39 _stk3A _stk3B _stk3C _stk3D _stk3E _stk3F  : TVMBit . 
Definition StakingContract_ι_StakeInfo_ι_stake_bs_def := [> _stk00 , _stk01 , _stk02 , _stk03 , _stk04 , _stk05 , _stk06 , _stk07 , _stk08 , _stk09 , _stk0A , _stk0B , _stk0C , _stk0D , _stk0E , _stk0F , _stk10 , _stk11 , _stk12 , _stk13 , _stk14 , _stk15 , _stk16 , _stk17 , _stk18 , _stk19 , _stk1A , _stk1B , _stk1C , _stk1D , _stk1E , _stk1F , _stk20 , _stk21 , _stk22 , _stk23 , _stk24 , _stk25 , _stk26 , _stk27 , _stk28 , _stk29 , _stk2A , _stk2B , _stk2C , _stk2D , _stk2E , _stk2F , _stk30 , _stk31 , _stk32 , _stk33 , _stk34 , _stk35 , _stk36 , _stk37 , _stk38 , _stk39 , _stk3A , _stk3B , _stk3C , _stk3D , _stk3E , _stk3F <] .
Lemma StakingContract_ι_StakeInfo_ι_stake_bs_id: StakingContract_ι_StakeInfo_ι_stake_bs_def = [> _stk00 , _stk01 , _stk02 , _stk03 , _stk04 , _stk05 , _stk06 , _stk07 , _stk08 , _stk09 , _stk0A , _stk0B , _stk0C , _stk0D , _stk0E , _stk0F , _stk10 , _stk11 , _stk12 , _stk13 , _stk14 , _stk15 , _stk16 , _stk17 , _stk18 , _stk19 , _stk1A , _stk1B , _stk1C , _stk1D , _stk1E , _stk1F , _stk20 , _stk21 , _stk22 , _stk23 , _stk24 , _stk25 , _stk26 , _stk27 , _stk28 , _stk29 , _stk2A , _stk2B , _stk2C , _stk2D , _stk2E , _stk2F , _stk30 , _stk31 , _stk32 , _stk33 , _stk34 , _stk35 , _stk36 , _stk37 , _stk38 , _stk39 , _stk3A , _stk3B , _stk3C , _stk3D , _stk3E , _stk3F (* } !*)  <] .
Proof. auto. Qed.
Axiom StakingContract_ι_StakeInfo_ι_stake_bs' : Z2IBS_pos (tvmBitStringLen StakingContract_ι_StakeInfo_ι_stake_bs_def) StakingContract_ι_StakeInfo_ι_stake = StakingContract_ι_StakeInfo_ι_stake_bs_def.
Lemma StakingContract_ι_StakeInfo_ι_stake_bs : Z2IBS_pos 64 StakingContract_ι_StakeInfo_ι_stake = StakingContract_ι_StakeInfo_ι_stake_bs_def.
Proof.
 rewrite <- StakingContract_ι_StakeInfo_ι_stake_bs'. auto. Qed.
Axiom StakingContract_ι_StakeInfo_ι_stake_pos: (0 <= StakingContract_ι_StakeInfo_ι_stake )%Z.
Axiom StakingContract_ι_StakeInfo_ι_stake_fits: zFitN_pos (tvmBitStringLen StakingContract_ι_StakeInfo_ι_stake_bs_def) StakingContract_ι_StakeInfo_ι_stake = true.
Lemma StakingContract_ι_StakeInfo_ι_stake_bs_rev : I2ZBS_pos' StakingContract_ι_StakeInfo_ι_stake_bs_def = StakingContract_ι_StakeInfo_ι_stake .
Proof.
  prove_bs_rev StakingContract_ι_StakeInfo_ι_stake_bs StakingContract_ι_StakeInfo_ι_stake_pos StakingContract_ι_StakeInfo_ι_stake_fits. 
Qed.
Lemma StakingContract_ι_StakeInfo_ι_stake_bs257 : Z2IN 257 StakingContract_ι_StakeInfo_ι_stake = 
      _TVMInteger _ (_TVMSimpleInteger _ (bsAddLeadingZeros (257 - (tvmBitStringLen 
                    StakingContract_ι_StakeInfo_ι_stake_bs_def)) StakingContract_ι_StakeInfo_ι_stake_bs_def)).
Proof.
  prove_bs_rev StakingContract_ι_StakeInfo_ι_stake_bs_rev StakingContract_ι_StakeInfo_ι_stake_bs_def.
Qed.

 Definition  OwnerBase_ι_OwnerP := 
 	 ( tvmBitStringCombine ( Z2IBS_pos 0 OwnerBase_ι_Owner_ι_addr ) 
 	 	 ( Z2IBS_pos 64 OwnerBase_ι_Owner_ι_reward ) ) . 
 
 Definition  ElectorBase_ι_RequestP := 
 	 ( tvmBitStringCombine ( Z2IBS_pos 64 ElectorBase_ι_Request_ι_queryId ) 
 	 ( tvmBitStringCombine ( Z2IBS_pos 256 ElectorBase_ι_Request_ι_validatorKey ) 
 	 ( tvmBitStringCombine ( Z2IBS_pos 32 ElectorBase_ι_Request_ι_stakeAt ) 
 	 ( tvmBitStringCombine ( Z2IBS_pos 32 ElectorBase_ι_Request_ι_maxFactor ) 
 	 ( tvmBitStringCombine ( Z2IBS_pos 256 ElectorBase_ι_Request_ι_adnlAddr ) 
 	 	 ( Z2IBS_pos 8 ElectorBase_ι_Request_ι_signature ) ))))) . 
 
 Definition  ElectionParams_ι_ValidatorDescr73P := 
 	 ( tvmBitStringCombine ( Z2IBS_pos 8 ElectionParams_ι_ValidatorDescr73_ι_validator_addr73 ) 
 	 ( tvmBitStringCombine ( Z2IBS_pos 32 ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey ) 
 	 ( tvmBitStringCombine ( Z2IBS_pos 256 ElectionParams_ι_ValidatorDescr73_ι_pubkey ) 
 	 ( tvmBitStringCombine ( Z2IBS_pos 64 ElectionParams_ι_ValidatorDescr73_ι_weight ) 
 	 	 ( Z2IBS_pos 256 ElectionParams_ι_ValidatorDescr73_ι_adnl_addr ) )))) . 
 
 Definition  StakeholderBase_ι_StakeholderP := 
 	 ( tvmBitStringCombine ( Z2IBS_pos 64 StakeholderBase_ι_Stakeholder_ι_totalStake ) 
 	 ( tvmBitStringCombine ( Z2IBS_pos 64 StakeholderBase_ι_Stakeholder_ι_unusedStake ) 
 	 ( tvmBitStringCombine ( Z2IBS_pos 0 StakeholderBase_ι_Stakeholder_ι_reinvest ) 
 	 	 ( Z2IBS_pos 64 StakeholderBase_ι_Stakeholder_ι_reward ) ))) . 
 
 Definition  RoundsBase_ι_RoundP := 
 	 ( tvmBitStringCombine ( Z2IBS_pos 32 RoundsBase_ι_Round_ι_id ) 
 	 ( tvmBitStringCombine ( Z2IBS_pos 8 RoundsBase_ι_Round_ι_step ) 
 	 ( tvmBitStringCombine ( Z2IBS_pos 32 RoundsBase_ι_Round_ι_count ) 
 	 ( tvmBitStringCombine ( Z2IBS_pos 64 RoundsBase_ι_Round_ι_totalStake ) 
 	 ( tvmBitStringCombine ( Z2IBS_pos 64 RoundsBase_ι_Round_ι_rewards ) 
 	 ( tvmBitStringCombine ( Z2IBS_pos 64 RoundsBase_ι_Round_ι_unused ) 
 	 ( tvmBitStringCombine ( Z2IBS_pos 8 RoundsBase_ι_Round_ι_completionStatus ) 
 	 ( tvmBitStringCombine ( Z2IBS_pos 32 RoundsBase_ι_Round_ι_start ) 
 	 	 ( Z2IBS_pos 32 RoundsBase_ι_Round_ι_end ) )))))))) . 
 
 Definition  RoundsBase_ι_RoundInfoP := 
 	 ( tvmBitStringCombine ( Z2IBS_pos 32 RoundsBase_ι_RoundInfo_ι_id ) 
 	 ( tvmBitStringCombine ( Z2IBS_pos 32 RoundsBase_ι_RoundInfo_ι_start ) 
 	 ( tvmBitStringCombine ( Z2IBS_pos 32 RoundsBase_ι_RoundInfo_ι_end ) 
 	 ( tvmBitStringCombine ( Z2IBS_pos 8 RoundsBase_ι_RoundInfo_ι_step ) 
 	 ( tvmBitStringCombine ( Z2IBS_pos 8 RoundsBase_ι_RoundInfo_ι_completionStatus ) 
 	 ( tvmBitStringCombine ( Z2IBS_pos 64 RoundsBase_ι_RoundInfo_ι_stake ) 
 	 ( tvmBitStringCombine ( Z2IBS_pos 32 RoundsBase_ι_RoundInfo_ι_stakeholderCount ) 
 	 	 ( Z2IBS_pos 64 RoundsBase_ι_RoundInfo_ι_rewards ) ))))))) . 
 
 Definition  StakingContract_ι_NodeP := 
 	 ( tvmBitStringCombine ( Z2IBS_pos 0 StakingContract_ι_Node_ι_wallet ) 
 	 	 ( Z2IBS_pos 32 StakingContract_ι_Node_ι_factor ) ) . 
 
 Definition  StakingContract_ι_StakeInfoP := 
 	 ( tvmBitStringCombine ( Z2IBS_pos 32 StakingContract_ι_StakeInfo_ι_roundId ) 
 	 	 ( Z2IBS_pos 64 StakingContract_ι_StakeInfo_ι_stake ) ) . 

