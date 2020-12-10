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
Variables lctt00 lctt01 lctt02 lctt03 lctt04 lctt05 lctt06 lctt07 lctt08 lctt09 lctt0A lctt0B lctt0C lctt0D lctt0E lctt0F lctt10 lctt11 lctt12 lctt13 lctt14 lctt15 lctt16 lctt17 lctt18 lctt19 lctt1A lctt1B lctt1C lctt1D lctt1E lctt1F  : TVMBit . 
Definition ElectionParams_ι_m_electAt_bs_def := [> lctt00 , lctt01 , lctt02 , lctt03 , lctt04 , lctt05 , lctt06 , lctt07 , lctt08 , lctt09 , lctt0A , lctt0B , lctt0C , lctt0D , lctt0E , lctt0F , lctt10 , lctt11 , lctt12 , lctt13 , lctt14 , lctt15 , lctt16 , lctt17 , lctt18 , lctt19 , lctt1A , lctt1B , lctt1C , lctt1D , lctt1E , lctt1F <] .
Lemma ElectionParams_ι_m_electAt_bs_id: ElectionParams_ι_m_electAt_bs_def = [> lctt00 , lctt01 , lctt02 , lctt03 , lctt04 , lctt05 , lctt06 , lctt07 , lctt08 , lctt09 , lctt0A , lctt0B , lctt0C , lctt0D , lctt0E , lctt0F , lctt10 , lctt11 , lctt12 , lctt13 , lctt14 , lctt15 , lctt16 , lctt17 , lctt18 , lctt19 , lctt1A , lctt1B , lctt1C , lctt1D , lctt1E , lctt1F <] .
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
Qed. Variables ElectionParams_ι_m_beginBefore : Z . 
Variables bgnBf00 bgnBf01 bgnBf02 bgnBf03 bgnBf04 bgnBf05 bgnBf06 bgnBf07 bgnBf08 bgnBf09 bgnBf0A bgnBf0B bgnBf0C bgnBf0D bgnBf0E bgnBf0F bgnBf10 bgnBf11 bgnBf12 bgnBf13 bgnBf14 bgnBf15 bgnBf16 bgnBf17 bgnBf18 bgnBf19 bgnBf1A bgnBf1B bgnBf1C bgnBf1D bgnBf1E bgnBf1F  : TVMBit . 
Definition ElectionParams_ι_m_beginBefore_bs_def := [> bgnBf00 , bgnBf01 , bgnBf02 , bgnBf03 , bgnBf04 , bgnBf05 , bgnBf06 , bgnBf07 , bgnBf08 , bgnBf09 , bgnBf0A , bgnBf0B , bgnBf0C , bgnBf0D , bgnBf0E , bgnBf0F , bgnBf10 , bgnBf11 , bgnBf12 , bgnBf13 , bgnBf14 , bgnBf15 , bgnBf16 , bgnBf17 , bgnBf18 , bgnBf19 , bgnBf1A , bgnBf1B , bgnBf1C , bgnBf1D , bgnBf1E , bgnBf1F <] .
Lemma ElectionParams_ι_m_beginBefore_bs_id: ElectionParams_ι_m_beginBefore_bs_def = [> bgnBf00 , bgnBf01 , bgnBf02 , bgnBf03 , bgnBf04 , bgnBf05 , bgnBf06 , bgnBf07 , bgnBf08 , bgnBf09 , bgnBf0A , bgnBf0B , bgnBf0C , bgnBf0D , bgnBf0E , bgnBf0F , bgnBf10 , bgnBf11 , bgnBf12 , bgnBf13 , bgnBf14 , bgnBf15 , bgnBf16 , bgnBf17 , bgnBf18 , bgnBf19 , bgnBf1A , bgnBf1B , bgnBf1C , bgnBf1D , bgnBf1E , bgnBf1F <] .
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
Qed. Variables ElectionParams_ι_m_endBefore : Z . 
Variables ndBfr00 ndBfr01 ndBfr02 ndBfr03 ndBfr04 ndBfr05 ndBfr06 ndBfr07 ndBfr08 ndBfr09 ndBfr0A ndBfr0B ndBfr0C ndBfr0D ndBfr0E ndBfr0F ndBfr10 ndBfr11 ndBfr12 ndBfr13 ndBfr14 ndBfr15 ndBfr16 ndBfr17 ndBfr18 ndBfr19 ndBfr1A ndBfr1B ndBfr1C ndBfr1D ndBfr1E ndBfr1F  : TVMBit . 
Definition ElectionParams_ι_m_endBefore_bs_def := [> ndBfr00 , ndBfr01 , ndBfr02 , ndBfr03 , ndBfr04 , ndBfr05 , ndBfr06 , ndBfr07 , ndBfr08 , ndBfr09 , ndBfr0A , ndBfr0B , ndBfr0C , ndBfr0D , ndBfr0E , ndBfr0F , ndBfr10 , ndBfr11 , ndBfr12 , ndBfr13 , ndBfr14 , ndBfr15 , ndBfr16 , ndBfr17 , ndBfr18 , ndBfr19 , ndBfr1A , ndBfr1B , ndBfr1C , ndBfr1D , ndBfr1E , ndBfr1F <] .
Lemma ElectionParams_ι_m_endBefore_bs_id: ElectionParams_ι_m_endBefore_bs_def = [> ndBfr00 , ndBfr01 , ndBfr02 , ndBfr03 , ndBfr04 , ndBfr05 , ndBfr06 , ndBfr07 , ndBfr08 , ndBfr09 , ndBfr0A , ndBfr0B , ndBfr0C , ndBfr0D , ndBfr0E , ndBfr0F , ndBfr10 , ndBfr11 , ndBfr12 , ndBfr13 , ndBfr14 , ndBfr15 , ndBfr16 , ndBfr17 , ndBfr18 , ndBfr19 , ndBfr1A , ndBfr1B , ndBfr1C , ndBfr1D , ndBfr1E , ndBfr1F <] .
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
Qed. Variables ElectionParams_ι_m_electedFor : Z . 
Variables lctdF00 lctdF01 lctdF02 lctdF03 lctdF04 lctdF05 lctdF06 lctdF07 lctdF08 lctdF09 lctdF0A lctdF0B lctdF0C lctdF0D lctdF0E lctdF0F lctdF10 lctdF11 lctdF12 lctdF13 lctdF14 lctdF15 lctdF16 lctdF17 lctdF18 lctdF19 lctdF1A lctdF1B lctdF1C lctdF1D lctdF1E lctdF1F  : TVMBit . 
Definition ElectionParams_ι_m_electedFor_bs_def := [> lctdF00 , lctdF01 , lctdF02 , lctdF03 , lctdF04 , lctdF05 , lctdF06 , lctdF07 , lctdF08 , lctdF09 , lctdF0A , lctdF0B , lctdF0C , lctdF0D , lctdF0E , lctdF0F , lctdF10 , lctdF11 , lctdF12 , lctdF13 , lctdF14 , lctdF15 , lctdF16 , lctdF17 , lctdF18 , lctdF19 , lctdF1A , lctdF1B , lctdF1C , lctdF1D , lctdF1E , lctdF1F <] .
Lemma ElectionParams_ι_m_electedFor_bs_id: ElectionParams_ι_m_electedFor_bs_def = [> lctdF00 , lctdF01 , lctdF02 , lctdF03 , lctdF04 , lctdF05 , lctdF06 , lctdF07 , lctdF08 , lctdF09 , lctdF0A , lctdF0B , lctdF0C , lctdF0D , lctdF0E , lctdF0F , lctdF10 , lctdF11 , lctdF12 , lctdF13 , lctdF14 , lctdF15 , lctdF16 , lctdF17 , lctdF18 , lctdF19 , lctdF1A , lctdF1B , lctdF1C , lctdF1D , lctdF1E , lctdF1F <] .
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
Qed. Variables ElectionParams_ι_m_heldFor : Z . 
Variables hldFr00 hldFr01 hldFr02 hldFr03 hldFr04 hldFr05 hldFr06 hldFr07 hldFr08 hldFr09 hldFr0A hldFr0B hldFr0C hldFr0D hldFr0E hldFr0F hldFr10 hldFr11 hldFr12 hldFr13 hldFr14 hldFr15 hldFr16 hldFr17 hldFr18 hldFr19 hldFr1A hldFr1B hldFr1C hldFr1D hldFr1E hldFr1F  : TVMBit . 
Definition ElectionParams_ι_m_heldFor_bs_def := [> hldFr00 , hldFr01 , hldFr02 , hldFr03 , hldFr04 , hldFr05 , hldFr06 , hldFr07 , hldFr08 , hldFr09 , hldFr0A , hldFr0B , hldFr0C , hldFr0D , hldFr0E , hldFr0F , hldFr10 , hldFr11 , hldFr12 , hldFr13 , hldFr14 , hldFr15 , hldFr16 , hldFr17 , hldFr18 , hldFr19 , hldFr1A , hldFr1B , hldFr1C , hldFr1D , hldFr1E , hldFr1F <] .
Lemma ElectionParams_ι_m_heldFor_bs_id: ElectionParams_ι_m_heldFor_bs_def = [> hldFr00 , hldFr01 , hldFr02 , hldFr03 , hldFr04 , hldFr05 , hldFr06 , hldFr07 , hldFr08 , hldFr09 , hldFr0A , hldFr0B , hldFr0C , hldFr0D , hldFr0E , hldFr0F , hldFr10 , hldFr11 , hldFr12 , hldFr13 , hldFr14 , hldFr15 , hldFr16 , hldFr17 , hldFr18 , hldFr19 , hldFr1A , hldFr1B , hldFr1C , hldFr1D , hldFr1E , hldFr1F <] .
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
Variables strtd00 strtd01 strtd02 strtd03 strtd04 strtd05 strtd06 strtd07 strtd08 strtd09 strtd0A strtd0B strtd0C strtd0D strtd0E strtd0F strtd10 strtd11 strtd12 strtd13 strtd14 strtd15 strtd16 strtd17 strtd18 strtd19 strtd1A strtd1B strtd1C strtd1D strtd1E strtd1F strtd20 strtd21 strtd22 strtd23 strtd24 strtd25 strtd26 strtd27 strtd28 strtd29 strtd2A strtd2B strtd2C strtd2D strtd2E strtd2F strtd30 strtd31 strtd32 strtd33 strtd34 strtd35 strtd36 strtd37 strtd38 strtd39 strtd3A strtd3B strtd3C strtd3D strtd3E strtd3F  : TVMBit . 
Definition RoundsBase_ι_m_startIdx_bs_def := [> strtd00 , strtd01 , strtd02 , strtd03 , strtd04 , strtd05 , strtd06 , strtd07 , strtd08 , strtd09 , strtd0A , strtd0B , strtd0C , strtd0D , strtd0E , strtd0F , strtd10 , strtd11 , strtd12 , strtd13 , strtd14 , strtd15 , strtd16 , strtd17 , strtd18 , strtd19 , strtd1A , strtd1B , strtd1C , strtd1D , strtd1E , strtd1F , strtd20 , strtd21 , strtd22 , strtd23 , strtd24 , strtd25 , strtd26 , strtd27 , strtd28 , strtd29 , strtd2A , strtd2B , strtd2C , strtd2D , strtd2E , strtd2F , strtd30 , strtd31 , strtd32 , strtd33 , strtd34 , strtd35 , strtd36 , strtd37 , strtd38 , strtd39 , strtd3A , strtd3B , strtd3C , strtd3D , strtd3E , strtd3F <] .
Lemma RoundsBase_ι_m_startIdx_bs_id: RoundsBase_ι_m_startIdx_bs_def = [> strtd00 , strtd01 , strtd02 , strtd03 , strtd04 , strtd05 , strtd06 , strtd07 , strtd08 , strtd09 , strtd0A , strtd0B , strtd0C , strtd0D , strtd0E , strtd0F , strtd10 , strtd11 , strtd12 , strtd13 , strtd14 , strtd15 , strtd16 , strtd17 , strtd18 , strtd19 , strtd1A , strtd1B , strtd1C , strtd1D , strtd1E , strtd1F , strtd20 , strtd21 , strtd22 , strtd23 , strtd24 , strtd25 , strtd26 , strtd27 , strtd28 , strtd29 , strtd2A , strtd2B , strtd2C , strtd2D , strtd2E , strtd2F , strtd30 , strtd31 , strtd32 , strtd33 , strtd34 , strtd35 , strtd36 , strtd37 , strtd38 , strtd39 , strtd3A , strtd3B , strtd3C , strtd3D , strtd3E , strtd3F <] .
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
Qed. Variables RoundsBase_ι_m_roundsCount : Z . 
Variables rndsC00 rndsC01 rndsC02 rndsC03 rndsC04 rndsC05 rndsC06 rndsC07  : TVMBit . 
Definition RoundsBase_ι_m_roundsCount_bs_def := [> rndsC00 , rndsC01 , rndsC02 , rndsC03 , rndsC04 , rndsC05 , rndsC06 , rndsC07 <] .
Lemma RoundsBase_ι_m_roundsCount_bs_id: RoundsBase_ι_m_roundsCount_bs_def = [> rndsC00 , rndsC01 , rndsC02 , rndsC03 , rndsC04 , rndsC05 , rndsC06 , rndsC07 <] .
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
Variables mnStk00 mnStk01 mnStk02 mnStk03 mnStk04 mnStk05 mnStk06 mnStk07 mnStk08 mnStk09 mnStk0A mnStk0B mnStk0C mnStk0D mnStk0E mnStk0F mnStk10 mnStk11 mnStk12 mnStk13 mnStk14 mnStk15 mnStk16 mnStk17 mnStk18 mnStk19 mnStk1A mnStk1B mnStk1C mnStk1D mnStk1E mnStk1F mnStk20 mnStk21 mnStk22 mnStk23 mnStk24 mnStk25 mnStk26 mnStk27 mnStk28 mnStk29 mnStk2A mnStk2B mnStk2C mnStk2D mnStk2E mnStk2F mnStk30 mnStk31 mnStk32 mnStk33 mnStk34 mnStk35 mnStk36 mnStk37 mnStk38 mnStk39 mnStk3A mnStk3B mnStk3C mnStk3D mnStk3E mnStk3F  : TVMBit . 
Definition StakingContract_ι_m_minStake_bs_def := [> mnStk00 , mnStk01 , mnStk02 , mnStk03 , mnStk04 , mnStk05 , mnStk06 , mnStk07 , mnStk08 , mnStk09 , mnStk0A , mnStk0B , mnStk0C , mnStk0D , mnStk0E , mnStk0F , mnStk10 , mnStk11 , mnStk12 , mnStk13 , mnStk14 , mnStk15 , mnStk16 , mnStk17 , mnStk18 , mnStk19 , mnStk1A , mnStk1B , mnStk1C , mnStk1D , mnStk1E , mnStk1F , mnStk20 , mnStk21 , mnStk22 , mnStk23 , mnStk24 , mnStk25 , mnStk26 , mnStk27 , mnStk28 , mnStk29 , mnStk2A , mnStk2B , mnStk2C , mnStk2D , mnStk2E , mnStk2F , mnStk30 , mnStk31 , mnStk32 , mnStk33 , mnStk34 , mnStk35 , mnStk36 , mnStk37 , mnStk38 , mnStk39 , mnStk3A , mnStk3B , mnStk3C , mnStk3D , mnStk3E , mnStk3F <] .
Lemma StakingContract_ι_m_minStake_bs_id: StakingContract_ι_m_minStake_bs_def = [> mnStk00 , mnStk01 , mnStk02 , mnStk03 , mnStk04 , mnStk05 , mnStk06 , mnStk07 , mnStk08 , mnStk09 , mnStk0A , mnStk0B , mnStk0C , mnStk0D , mnStk0E , mnStk0F , mnStk10 , mnStk11 , mnStk12 , mnStk13 , mnStk14 , mnStk15 , mnStk16 , mnStk17 , mnStk18 , mnStk19 , mnStk1A , mnStk1B , mnStk1C , mnStk1D , mnStk1E , mnStk1F , mnStk20 , mnStk21 , mnStk22 , mnStk23 , mnStk24 , mnStk25 , mnStk26 , mnStk27 , mnStk28 , mnStk29 , mnStk2A , mnStk2B , mnStk2C , mnStk2D , mnStk2E , mnStk2F , mnStk30 , mnStk31 , mnStk32 , mnStk33 , mnStk34 , mnStk35 , mnStk36 , mnStk37 , mnStk38 , mnStk39 , mnStk3A , mnStk3B , mnStk3C , mnStk3D , mnStk3E , mnStk3F <] .
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
Qed. Variables StakingContract_ι_m_minRoundStake : Z . 
Variables mnRnd00 mnRnd01 mnRnd02 mnRnd03 mnRnd04 mnRnd05 mnRnd06 mnRnd07 mnRnd08 mnRnd09 mnRnd0A mnRnd0B mnRnd0C mnRnd0D mnRnd0E mnRnd0F mnRnd10 mnRnd11 mnRnd12 mnRnd13 mnRnd14 mnRnd15 mnRnd16 mnRnd17 mnRnd18 mnRnd19 mnRnd1A mnRnd1B mnRnd1C mnRnd1D mnRnd1E mnRnd1F mnRnd20 mnRnd21 mnRnd22 mnRnd23 mnRnd24 mnRnd25 mnRnd26 mnRnd27 mnRnd28 mnRnd29 mnRnd2A mnRnd2B mnRnd2C mnRnd2D mnRnd2E mnRnd2F mnRnd30 mnRnd31 mnRnd32 mnRnd33 mnRnd34 mnRnd35 mnRnd36 mnRnd37 mnRnd38 mnRnd39 mnRnd3A mnRnd3B mnRnd3C mnRnd3D mnRnd3E mnRnd3F  : TVMBit . 
Definition StakingContract_ι_m_minRoundStake_bs_def := [> mnRnd00 , mnRnd01 , mnRnd02 , mnRnd03 , mnRnd04 , mnRnd05 , mnRnd06 , mnRnd07 , mnRnd08 , mnRnd09 , mnRnd0A , mnRnd0B , mnRnd0C , mnRnd0D , mnRnd0E , mnRnd0F , mnRnd10 , mnRnd11 , mnRnd12 , mnRnd13 , mnRnd14 , mnRnd15 , mnRnd16 , mnRnd17 , mnRnd18 , mnRnd19 , mnRnd1A , mnRnd1B , mnRnd1C , mnRnd1D , mnRnd1E , mnRnd1F , mnRnd20 , mnRnd21 , mnRnd22 , mnRnd23 , mnRnd24 , mnRnd25 , mnRnd26 , mnRnd27 , mnRnd28 , mnRnd29 , mnRnd2A , mnRnd2B , mnRnd2C , mnRnd2D , mnRnd2E , mnRnd2F , mnRnd30 , mnRnd31 , mnRnd32 , mnRnd33 , mnRnd34 , mnRnd35 , mnRnd36 , mnRnd37 , mnRnd38 , mnRnd39 , mnRnd3A , mnRnd3B , mnRnd3C , mnRnd3D , mnRnd3E , mnRnd3F <] .
Lemma StakingContract_ι_m_minRoundStake_bs_id: StakingContract_ι_m_minRoundStake_bs_def = [> mnRnd00 , mnRnd01 , mnRnd02 , mnRnd03 , mnRnd04 , mnRnd05 , mnRnd06 , mnRnd07 , mnRnd08 , mnRnd09 , mnRnd0A , mnRnd0B , mnRnd0C , mnRnd0D , mnRnd0E , mnRnd0F , mnRnd10 , mnRnd11 , mnRnd12 , mnRnd13 , mnRnd14 , mnRnd15 , mnRnd16 , mnRnd17 , mnRnd18 , mnRnd19 , mnRnd1A , mnRnd1B , mnRnd1C , mnRnd1D , mnRnd1E , mnRnd1F , mnRnd20 , mnRnd21 , mnRnd22 , mnRnd23 , mnRnd24 , mnRnd25 , mnRnd26 , mnRnd27 , mnRnd28 , mnRnd29 , mnRnd2A , mnRnd2B , mnRnd2C , mnRnd2D , mnRnd2E , mnRnd2F , mnRnd30 , mnRnd31 , mnRnd32 , mnRnd33 , mnRnd34 , mnRnd35 , mnRnd36 , mnRnd37 , mnRnd38 , mnRnd39 , mnRnd3A , mnRnd3B , mnRnd3C , mnRnd3D , mnRnd3E , mnRnd3F <] .
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
Qed. Variables StakingContract_ι_m_maxRoundStake : Z . 
Variables mxRnd00 mxRnd01 mxRnd02 mxRnd03 mxRnd04 mxRnd05 mxRnd06 mxRnd07 mxRnd08 mxRnd09 mxRnd0A mxRnd0B mxRnd0C mxRnd0D mxRnd0E mxRnd0F mxRnd10 mxRnd11 mxRnd12 mxRnd13 mxRnd14 mxRnd15 mxRnd16 mxRnd17 mxRnd18 mxRnd19 mxRnd1A mxRnd1B mxRnd1C mxRnd1D mxRnd1E mxRnd1F mxRnd20 mxRnd21 mxRnd22 mxRnd23 mxRnd24 mxRnd25 mxRnd26 mxRnd27 mxRnd28 mxRnd29 mxRnd2A mxRnd2B mxRnd2C mxRnd2D mxRnd2E mxRnd2F mxRnd30 mxRnd31 mxRnd32 mxRnd33 mxRnd34 mxRnd35 mxRnd36 mxRnd37 mxRnd38 mxRnd39 mxRnd3A mxRnd3B mxRnd3C mxRnd3D mxRnd3E mxRnd3F  : TVMBit . 
Definition StakingContract_ι_m_maxRoundStake_bs_def := [> mxRnd00 , mxRnd01 , mxRnd02 , mxRnd03 , mxRnd04 , mxRnd05 , mxRnd06 , mxRnd07 , mxRnd08 , mxRnd09 , mxRnd0A , mxRnd0B , mxRnd0C , mxRnd0D , mxRnd0E , mxRnd0F , mxRnd10 , mxRnd11 , mxRnd12 , mxRnd13 , mxRnd14 , mxRnd15 , mxRnd16 , mxRnd17 , mxRnd18 , mxRnd19 , mxRnd1A , mxRnd1B , mxRnd1C , mxRnd1D , mxRnd1E , mxRnd1F , mxRnd20 , mxRnd21 , mxRnd22 , mxRnd23 , mxRnd24 , mxRnd25 , mxRnd26 , mxRnd27 , mxRnd28 , mxRnd29 , mxRnd2A , mxRnd2B , mxRnd2C , mxRnd2D , mxRnd2E , mxRnd2F , mxRnd30 , mxRnd31 , mxRnd32 , mxRnd33 , mxRnd34 , mxRnd35 , mxRnd36 , mxRnd37 , mxRnd38 , mxRnd39 , mxRnd3A , mxRnd3B , mxRnd3C , mxRnd3D , mxRnd3E , mxRnd3F <] .
Lemma StakingContract_ι_m_maxRoundStake_bs_id: StakingContract_ι_m_maxRoundStake_bs_def = [> mxRnd00 , mxRnd01 , mxRnd02 , mxRnd03 , mxRnd04 , mxRnd05 , mxRnd06 , mxRnd07 , mxRnd08 , mxRnd09 , mxRnd0A , mxRnd0B , mxRnd0C , mxRnd0D , mxRnd0E , mxRnd0F , mxRnd10 , mxRnd11 , mxRnd12 , mxRnd13 , mxRnd14 , mxRnd15 , mxRnd16 , mxRnd17 , mxRnd18 , mxRnd19 , mxRnd1A , mxRnd1B , mxRnd1C , mxRnd1D , mxRnd1E , mxRnd1F , mxRnd20 , mxRnd21 , mxRnd22 , mxRnd23 , mxRnd24 , mxRnd25 , mxRnd26 , mxRnd27 , mxRnd28 , mxRnd29 , mxRnd2A , mxRnd2B , mxRnd2C , mxRnd2D , mxRnd2E , mxRnd2F , mxRnd30 , mxRnd31 , mxRnd32 , mxRnd33 , mxRnd34 , mxRnd35 , mxRnd36 , mxRnd37 , mxRnd38 , mxRnd39 , mxRnd3A , mxRnd3B , mxRnd3C , mxRnd3D , mxRnd3E , mxRnd3F <] .
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
Qed. Variables StakingContract_ι_m_lastRoundInterest : Z . 
Variables lstRn00 lstRn01 lstRn02 lstRn03 lstRn04 lstRn05 lstRn06 lstRn07 lstRn08 lstRn09 lstRn0A lstRn0B lstRn0C lstRn0D lstRn0E lstRn0F lstRn10 lstRn11 lstRn12 lstRn13 lstRn14 lstRn15 lstRn16 lstRn17 lstRn18 lstRn19 lstRn1A lstRn1B lstRn1C lstRn1D lstRn1E lstRn1F lstRn20 lstRn21 lstRn22 lstRn23 lstRn24 lstRn25 lstRn26 lstRn27 lstRn28 lstRn29 lstRn2A lstRn2B lstRn2C lstRn2D lstRn2E lstRn2F lstRn30 lstRn31 lstRn32 lstRn33 lstRn34 lstRn35 lstRn36 lstRn37 lstRn38 lstRn39 lstRn3A lstRn3B lstRn3C lstRn3D lstRn3E lstRn3F  : TVMBit . 
Definition StakingContract_ι_m_lastRoundInterest_bs_def := [> lstRn00 , lstRn01 , lstRn02 , lstRn03 , lstRn04 , lstRn05 , lstRn06 , lstRn07 , lstRn08 , lstRn09 , lstRn0A , lstRn0B , lstRn0C , lstRn0D , lstRn0E , lstRn0F , lstRn10 , lstRn11 , lstRn12 , lstRn13 , lstRn14 , lstRn15 , lstRn16 , lstRn17 , lstRn18 , lstRn19 , lstRn1A , lstRn1B , lstRn1C , lstRn1D , lstRn1E , lstRn1F , lstRn20 , lstRn21 , lstRn22 , lstRn23 , lstRn24 , lstRn25 , lstRn26 , lstRn27 , lstRn28 , lstRn29 , lstRn2A , lstRn2B , lstRn2C , lstRn2D , lstRn2E , lstRn2F , lstRn30 , lstRn31 , lstRn32 , lstRn33 , lstRn34 , lstRn35 , lstRn36 , lstRn37 , lstRn38 , lstRn39 , lstRn3A , lstRn3B , lstRn3C , lstRn3D , lstRn3E , lstRn3F <] .
Lemma StakingContract_ι_m_lastRoundInterest_bs_id: StakingContract_ι_m_lastRoundInterest_bs_def = [> lstRn00 , lstRn01 , lstRn02 , lstRn03 , lstRn04 , lstRn05 , lstRn06 , lstRn07 , lstRn08 , lstRn09 , lstRn0A , lstRn0B , lstRn0C , lstRn0D , lstRn0E , lstRn0F , lstRn10 , lstRn11 , lstRn12 , lstRn13 , lstRn14 , lstRn15 , lstRn16 , lstRn17 , lstRn18 , lstRn19 , lstRn1A , lstRn1B , lstRn1C , lstRn1D , lstRn1E , lstRn1F , lstRn20 , lstRn21 , lstRn22 , lstRn23 , lstRn24 , lstRn25 , lstRn26 , lstRn27 , lstRn28 , lstRn29 , lstRn2A , lstRn2B , lstRn2C , lstRn2D , lstRn2E , lstRn2F , lstRn30 , lstRn31 , lstRn32 , lstRn33 , lstRn34 , lstRn35 , lstRn36 , lstRn37 , lstRn38 , lstRn39 , lstRn3A , lstRn3B , lstRn3C , lstRn3D , lstRn3E , lstRn3F <] .
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
Variables mnt00 mnt01 mnt02 mnt03 mnt04 mnt05 mnt06 mnt07 mnt08 mnt09 mnt0A mnt0B mnt0C mnt0D mnt0E mnt0F mnt10 mnt11 mnt12 mnt13 mnt14 mnt15 mnt16 mnt17 mnt18 mnt19 mnt1A mnt1B mnt1C mnt1D mnt1E mnt1F mnt20 mnt21 mnt22 mnt23 mnt24 mnt25 mnt26 mnt27 mnt28 mnt29 mnt2A mnt2B mnt2C mnt2D mnt2E mnt2F mnt30 mnt31 mnt32 mnt33 mnt34 mnt35 mnt36 mnt37 mnt38 mnt39 mnt3A mnt3B mnt3C mnt3D mnt3E mnt3F  : TVMBit . 
Definition OwnerBase_ι_withdrawOwnerReward_А_amount_bs_def := [> mnt00 , mnt01 , mnt02 , mnt03 , mnt04 , mnt05 , mnt06 , mnt07 , mnt08 , mnt09 , mnt0A , mnt0B , mnt0C , mnt0D , mnt0E , mnt0F , mnt10 , mnt11 , mnt12 , mnt13 , mnt14 , mnt15 , mnt16 , mnt17 , mnt18 , mnt19 , mnt1A , mnt1B , mnt1C , mnt1D , mnt1E , mnt1F , mnt20 , mnt21 , mnt22 , mnt23 , mnt24 , mnt25 , mnt26 , mnt27 , mnt28 , mnt29 , mnt2A , mnt2B , mnt2C , mnt2D , mnt2E , mnt2F , mnt30 , mnt31 , mnt32 , mnt33 , mnt34 , mnt35 , mnt36 , mnt37 , mnt38 , mnt39 , mnt3A , mnt3B , mnt3C , mnt3D , mnt3E , mnt3F <] .
Lemma OwnerBase_ι_withdrawOwnerReward_А_amount_bs_id: OwnerBase_ι_withdrawOwnerReward_А_amount_bs_def = [> mnt00 , mnt01 , mnt02 , mnt03 , mnt04 , mnt05 , mnt06 , mnt07 , mnt08 , mnt09 , mnt0A , mnt0B , mnt0C , mnt0D , mnt0E , mnt0F , mnt10 , mnt11 , mnt12 , mnt13 , mnt14 , mnt15 , mnt16 , mnt17 , mnt18 , mnt19 , mnt1A , mnt1B , mnt1C , mnt1D , mnt1E , mnt1F , mnt20 , mnt21 , mnt22 , mnt23 , mnt24 , mnt25 , mnt26 , mnt27 , mnt28 , mnt29 , mnt2A , mnt2B , mnt2C , mnt2D , mnt2E , mnt2F , mnt30 , mnt31 , mnt32 , mnt33 , mnt34 , mnt35 , mnt36 , mnt37 , mnt38 , mnt39 , mnt3A , mnt3B , mnt3C , mnt3D , mnt3E , mnt3F <] .
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
Variables wnrRw00 wnrRw01 wnrRw02 wnrRw03 wnrRw04 wnrRw05 wnrRw06 wnrRw07 wnrRw08 wnrRw09 wnrRw0A wnrRw0B wnrRw0C wnrRw0D wnrRw0E wnrRw0F wnrRw10 wnrRw11 wnrRw12 wnrRw13 wnrRw14 wnrRw15 wnrRw16 wnrRw17 wnrRw18 wnrRw19 wnrRw1A wnrRw1B wnrRw1C wnrRw1D wnrRw1E wnrRw1F wnrRw20 wnrRw21 wnrRw22 wnrRw23 wnrRw24 wnrRw25 wnrRw26 wnrRw27 wnrRw28 wnrRw29 wnrRw2A wnrRw2B wnrRw2C wnrRw2D wnrRw2E wnrRw2F wnrRw30 wnrRw31 wnrRw32 wnrRw33 wnrRw34 wnrRw35 wnrRw36 wnrRw37 wnrRw38 wnrRw39 wnrRw3A wnrRw3B wnrRw3C wnrRw3D wnrRw3E wnrRw3F  : TVMBit . 
Definition OwnerBase_ι__increaseOwnerReward_А_ownerReward_bs_def := [> wnrRw00 , wnrRw01 , wnrRw02 , wnrRw03 , wnrRw04 , wnrRw05 , wnrRw06 , wnrRw07 , wnrRw08 , wnrRw09 , wnrRw0A , wnrRw0B , wnrRw0C , wnrRw0D , wnrRw0E , wnrRw0F , wnrRw10 , wnrRw11 , wnrRw12 , wnrRw13 , wnrRw14 , wnrRw15 , wnrRw16 , wnrRw17 , wnrRw18 , wnrRw19 , wnrRw1A , wnrRw1B , wnrRw1C , wnrRw1D , wnrRw1E , wnrRw1F , wnrRw20 , wnrRw21 , wnrRw22 , wnrRw23 , wnrRw24 , wnrRw25 , wnrRw26 , wnrRw27 , wnrRw28 , wnrRw29 , wnrRw2A , wnrRw2B , wnrRw2C , wnrRw2D , wnrRw2E , wnrRw2F , wnrRw30 , wnrRw31 , wnrRw32 , wnrRw33 , wnrRw34 , wnrRw35 , wnrRw36 , wnrRw37 , wnrRw38 , wnrRw39 , wnrRw3A , wnrRw3B , wnrRw3C , wnrRw3D , wnrRw3E , wnrRw3F <] .
Lemma OwnerBase_ι__increaseOwnerReward_А_ownerReward_bs_id: OwnerBase_ι__increaseOwnerReward_А_ownerReward_bs_def = [> wnrRw00 , wnrRw01 , wnrRw02 , wnrRw03 , wnrRw04 , wnrRw05 , wnrRw06 , wnrRw07 , wnrRw08 , wnrRw09 , wnrRw0A , wnrRw0B , wnrRw0C , wnrRw0D , wnrRw0E , wnrRw0F , wnrRw10 , wnrRw11 , wnrRw12 , wnrRw13 , wnrRw14 , wnrRw15 , wnrRw16 , wnrRw17 , wnrRw18 , wnrRw19 , wnrRw1A , wnrRw1B , wnrRw1C , wnrRw1D , wnrRw1E , wnrRw1F , wnrRw20 , wnrRw21 , wnrRw22 , wnrRw23 , wnrRw24 , wnrRw25 , wnrRw26 , wnrRw27 , wnrRw28 , wnrRw29 , wnrRw2A , wnrRw2B , wnrRw2C , wnrRw2D , wnrRw2E , wnrRw2F , wnrRw30 , wnrRw31 , wnrRw32 , wnrRw33 , wnrRw34 , wnrRw35 , wnrRw36 , wnrRw37 , wnrRw38 , wnrRw39 , wnrRw3A , wnrRw3B , wnrRw3C , wnrRw3D , wnrRw3E , wnrRw3F <] .
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
Variables pndng00 pndng01 pndng02 pndng03 pndng04 pndng05 pndng06 pndng07 pndng08 pndng09 pndng0A pndng0B pndng0C pndng0D pndng0E pndng0F pndng10 pndng11 pndng12 pndng13 pndng14 pndng15 pndng16 pndng17 pndng18 pndng19 pndng1A pndng1B pndng1C pndng1D pndng1E pndng1F  : TVMBit . 
Definition ElectorBase_ι__recoverPendingRoundStakes_А_pendingId_bs_def := [> pndng00 , pndng01 , pndng02 , pndng03 , pndng04 , pndng05 , pndng06 , pndng07 , pndng08 , pndng09 , pndng0A , pndng0B , pndng0C , pndng0D , pndng0E , pndng0F , pndng10 , pndng11 , pndng12 , pndng13 , pndng14 , pndng15 , pndng16 , pndng17 , pndng18 , pndng19 , pndng1A , pndng1B , pndng1C , pndng1D , pndng1E , pndng1F <] .
Lemma ElectorBase_ι__recoverPendingRoundStakes_А_pendingId_bs_id: ElectorBase_ι__recoverPendingRoundStakes_А_pendingId_bs_def = [> pndng00 , pndng01 , pndng02 , pndng03 , pndng04 , pndng05 , pndng06 , pndng07 , pndng08 , pndng09 , pndng0A , pndng0B , pndng0C , pndng0D , pndng0E , pndng0F , pndng10 , pndng11 , pndng12 , pndng13 , pndng14 , pndng15 , pndng16 , pndng17 , pndng18 , pndng19 , pndng1A , pndng1B , pndng1C , pndng1D , pndng1E , pndng1F <] .
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
Variables ndStk00 ndStk01 ndStk02 ndStk03 ndStk04 ndStk05 ndStk06 ndStk07 ndStk08 ndStk09 ndStk0A ndStk0B ndStk0C ndStk0D ndStk0E ndStk0F ndStk10 ndStk11 ndStk12 ndStk13 ndStk14 ndStk15 ndStk16 ndStk17 ndStk18 ndStk19 ndStk1A ndStk1B ndStk1C ndStk1D ndStk1E ndStk1F ndStk20 ndStk21 ndStk22 ndStk23 ndStk24 ndStk25 ndStk26 ndStk27 ndStk28 ndStk29 ndStk2A ndStk2B ndStk2C ndStk2D ndStk2E ndStk2F ndStk30 ndStk31 ndStk32 ndStk33 ndStk34 ndStk35 ndStk36 ndStk37 ndStk38 ndStk39 ndStk3A ndStk3B ndStk3C ndStk3D ndStk3E ndStk3F  : TVMBit . 
Definition ElectorBase_ι__runForElection_А_nodeStake_bs_def := [> ndStk00 , ndStk01 , ndStk02 , ndStk03 , ndStk04 , ndStk05 , ndStk06 , ndStk07 , ndStk08 , ndStk09 , ndStk0A , ndStk0B , ndStk0C , ndStk0D , ndStk0E , ndStk0F , ndStk10 , ndStk11 , ndStk12 , ndStk13 , ndStk14 , ndStk15 , ndStk16 , ndStk17 , ndStk18 , ndStk19 , ndStk1A , ndStk1B , ndStk1C , ndStk1D , ndStk1E , ndStk1F , ndStk20 , ndStk21 , ndStk22 , ndStk23 , ndStk24 , ndStk25 , ndStk26 , ndStk27 , ndStk28 , ndStk29 , ndStk2A , ndStk2B , ndStk2C , ndStk2D , ndStk2E , ndStk2F , ndStk30 , ndStk31 , ndStk32 , ndStk33 , ndStk34 , ndStk35 , ndStk36 , ndStk37 , ndStk38 , ndStk39 , ndStk3A , ndStk3B , ndStk3C , ndStk3D , ndStk3E , ndStk3F <] .
Lemma ElectorBase_ι__runForElection_А_nodeStake_bs_id: ElectorBase_ι__runForElection_А_nodeStake_bs_def = [> ndStk00 , ndStk01 , ndStk02 , ndStk03 , ndStk04 , ndStk05 , ndStk06 , ndStk07 , ndStk08 , ndStk09 , ndStk0A , ndStk0B , ndStk0C , ndStk0D , ndStk0E , ndStk0F , ndStk10 , ndStk11 , ndStk12 , ndStk13 , ndStk14 , ndStk15 , ndStk16 , ndStk17 , ndStk18 , ndStk19 , ndStk1A , ndStk1B , ndStk1C , ndStk1D , ndStk1E , ndStk1F , ndStk20 , ndStk21 , ndStk22 , ndStk23 , ndStk24 , ndStk25 , ndStk26 , ndStk27 , ndStk28 , ndStk29 , ndStk2A , ndStk2B , ndStk2C , ndStk2D , ndStk2E , ndStk2F , ndStk30 , ndStk31 , ndStk32 , ndStk33 , ndStk34 , ndStk35 , ndStk36 , ndStk37 , ndStk38 , ndStk39 , ndStk3A , ndStk3B , ndStk3C , ndStk3D , ndStk3E , ndStk3F <] .
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
Variables ldstR00 ldstR01 ldstR02 ldstR03 ldstR04 ldstR05 ldstR06 ldstR07 ldstR08 ldstR09 ldstR0A ldstR0B ldstR0C ldstR0D ldstR0E ldstR0F ldstR10 ldstR11 ldstR12 ldstR13 ldstR14 ldstR15 ldstR16 ldstR17 ldstR18 ldstR19 ldstR1A ldstR1B ldstR1C ldstR1D ldstR1E ldstR1F  : TVMBit . 
Definition ElectionParams_ι__isRoundUnfrozen_А_oldestRoundId_bs_def := [> ldstR00 , ldstR01 , ldstR02 , ldstR03 , ldstR04 , ldstR05 , ldstR06 , ldstR07 , ldstR08 , ldstR09 , ldstR0A , ldstR0B , ldstR0C , ldstR0D , ldstR0E , ldstR0F , ldstR10 , ldstR11 , ldstR12 , ldstR13 , ldstR14 , ldstR15 , ldstR16 , ldstR17 , ldstR18 , ldstR19 , ldstR1A , ldstR1B , ldstR1C , ldstR1D , ldstR1E , ldstR1F <] .
Lemma ElectionParams_ι__isRoundUnfrozen_А_oldestRoundId_bs_id: ElectionParams_ι__isRoundUnfrozen_А_oldestRoundId_bs_def = [> ldstR00 , ldstR01 , ldstR02 , ldstR03 , ldstR04 , ldstR05 , ldstR06 , ldstR07 , ldstR08 , ldstR09 , ldstR0A , ldstR0B , ldstR0C , ldstR0D , ldstR0E , ldstR0F , ldstR10 , ldstR11 , ldstR12 , ldstR13 , ldstR14 , ldstR15 , ldstR16 , ldstR17 , ldstR18 , ldstR19 , ldstR1A , ldstR1B , ldstR1C , ldstR1D , ldstR1E , ldstR1F <] .
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
Variables crrnt00 crrnt01 crrnt02 crrnt03 crrnt04 crrnt05 crrnt06 crrnt07 crrnt08 crrnt09 crrnt0A crrnt0B crrnt0C crrnt0D crrnt0E crrnt0F crrnt10 crrnt11 crrnt12 crrnt13 crrnt14 crrnt15 crrnt16 crrnt17 crrnt18 crrnt19 crrnt1A crrnt1B crrnt1C crrnt1D crrnt1E crrnt1F  : TVMBit . 
Definition ElectionParams_ι__isElectionOver_А_currentElectAt_bs_def := [> crrnt00 , crrnt01 , crrnt02 , crrnt03 , crrnt04 , crrnt05 , crrnt06 , crrnt07 , crrnt08 , crrnt09 , crrnt0A , crrnt0B , crrnt0C , crrnt0D , crrnt0E , crrnt0F , crrnt10 , crrnt11 , crrnt12 , crrnt13 , crrnt14 , crrnt15 , crrnt16 , crrnt17 , crrnt18 , crrnt19 , crrnt1A , crrnt1B , crrnt1C , crrnt1D , crrnt1E , crrnt1F <] .
Lemma ElectionParams_ι__isElectionOver_А_currentElectAt_bs_id: ElectionParams_ι__isElectionOver_А_currentElectAt_bs_def = [> crrnt00 , crrnt01 , crrnt02 , crrnt03 , crrnt04 , crrnt05 , crrnt06 , crrnt07 , crrnt08 , crrnt09 , crrnt0A , crrnt0B , crrnt0C , crrnt0D , crrnt0E , crrnt0F , crrnt10 , crrnt11 , crrnt12 , crrnt13 , crrnt14 , crrnt15 , crrnt16 , crrnt17 , crrnt18 , crrnt19 , crrnt1A , crrnt1B , crrnt1C , crrnt1D , crrnt1E , crrnt1F <] .
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
Variables ttlSt00 ttlSt01 ttlSt02 ttlSt03 ttlSt04 ttlSt05 ttlSt06 ttlSt07 ttlSt08 ttlSt09 ttlSt0A ttlSt0B ttlSt0C ttlSt0D ttlSt0E ttlSt0F ttlSt10 ttlSt11 ttlSt12 ttlSt13 ttlSt14 ttlSt15 ttlSt16 ttlSt17 ttlSt18 ttlSt19 ttlSt1A ttlSt1B ttlSt1C ttlSt1D ttlSt1E ttlSt1F ttlSt20 ttlSt21 ttlSt22 ttlSt23 ttlSt24 ttlSt25 ttlSt26 ttlSt27 ttlSt28 ttlSt29 ttlSt2A ttlSt2B ttlSt2C ttlSt2D ttlSt2E ttlSt2F ttlSt30 ttlSt31 ttlSt32 ttlSt33 ttlSt34 ttlSt35 ttlSt36 ttlSt37 ttlSt38 ttlSt39 ttlSt3A ttlSt3B ttlSt3C ttlSt3D ttlSt3E ttlSt3F  : TVMBit . 
Definition StakeholderBase_ι__stakeholderUpdateStake_А_totalStake_bs_def := [> ttlSt00 , ttlSt01 , ttlSt02 , ttlSt03 , ttlSt04 , ttlSt05 , ttlSt06 , ttlSt07 , ttlSt08 , ttlSt09 , ttlSt0A , ttlSt0B , ttlSt0C , ttlSt0D , ttlSt0E , ttlSt0F , ttlSt10 , ttlSt11 , ttlSt12 , ttlSt13 , ttlSt14 , ttlSt15 , ttlSt16 , ttlSt17 , ttlSt18 , ttlSt19 , ttlSt1A , ttlSt1B , ttlSt1C , ttlSt1D , ttlSt1E , ttlSt1F , ttlSt20 , ttlSt21 , ttlSt22 , ttlSt23 , ttlSt24 , ttlSt25 , ttlSt26 , ttlSt27 , ttlSt28 , ttlSt29 , ttlSt2A , ttlSt2B , ttlSt2C , ttlSt2D , ttlSt2E , ttlSt2F , ttlSt30 , ttlSt31 , ttlSt32 , ttlSt33 , ttlSt34 , ttlSt35 , ttlSt36 , ttlSt37 , ttlSt38 , ttlSt39 , ttlSt3A , ttlSt3B , ttlSt3C , ttlSt3D , ttlSt3E , ttlSt3F <] .
Lemma StakeholderBase_ι__stakeholderUpdateStake_А_totalStake_bs_id: StakeholderBase_ι__stakeholderUpdateStake_А_totalStake_bs_def = [> ttlSt00 , ttlSt01 , ttlSt02 , ttlSt03 , ttlSt04 , ttlSt05 , ttlSt06 , ttlSt07 , ttlSt08 , ttlSt09 , ttlSt0A , ttlSt0B , ttlSt0C , ttlSt0D , ttlSt0E , ttlSt0F , ttlSt10 , ttlSt11 , ttlSt12 , ttlSt13 , ttlSt14 , ttlSt15 , ttlSt16 , ttlSt17 , ttlSt18 , ttlSt19 , ttlSt1A , ttlSt1B , ttlSt1C , ttlSt1D , ttlSt1E , ttlSt1F , ttlSt20 , ttlSt21 , ttlSt22 , ttlSt23 , ttlSt24 , ttlSt25 , ttlSt26 , ttlSt27 , ttlSt28 , ttlSt29 , ttlSt2A , ttlSt2B , ttlSt2C , ttlSt2D , ttlSt2E , ttlSt2F , ttlSt30 , ttlSt31 , ttlSt32 , ttlSt33 , ttlSt34 , ttlSt35 , ttlSt36 , ttlSt37 , ttlSt38 , ttlSt39 , ttlSt3A , ttlSt3B , ttlSt3C , ttlSt3D , ttlSt3E , ttlSt3F <] .
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
Variables rmvdS00 rmvdS01 rmvdS02 rmvdS03 rmvdS04 rmvdS05 rmvdS06 rmvdS07 rmvdS08 rmvdS09 rmvdS0A rmvdS0B rmvdS0C rmvdS0D rmvdS0E rmvdS0F rmvdS10 rmvdS11 rmvdS12 rmvdS13 rmvdS14 rmvdS15 rmvdS16 rmvdS17 rmvdS18 rmvdS19 rmvdS1A rmvdS1B rmvdS1C rmvdS1D rmvdS1E rmvdS1F rmvdS20 rmvdS21 rmvdS22 rmvdS23 rmvdS24 rmvdS25 rmvdS26 rmvdS27 rmvdS28 rmvdS29 rmvdS2A rmvdS2B rmvdS2C rmvdS2D rmvdS2E rmvdS2F rmvdS30 rmvdS31 rmvdS32 rmvdS33 rmvdS34 rmvdS35 rmvdS36 rmvdS37 rmvdS38 rmvdS39 rmvdS3A rmvdS3B rmvdS3C rmvdS3D rmvdS3E rmvdS3F  : TVMBit . 
Definition StakeholderBase_ι__stakeholderRemoveStake_А_removedStake_bs_def := [> rmvdS00 , rmvdS01 , rmvdS02 , rmvdS03 , rmvdS04 , rmvdS05 , rmvdS06 , rmvdS07 , rmvdS08 , rmvdS09 , rmvdS0A , rmvdS0B , rmvdS0C , rmvdS0D , rmvdS0E , rmvdS0F , rmvdS10 , rmvdS11 , rmvdS12 , rmvdS13 , rmvdS14 , rmvdS15 , rmvdS16 , rmvdS17 , rmvdS18 , rmvdS19 , rmvdS1A , rmvdS1B , rmvdS1C , rmvdS1D , rmvdS1E , rmvdS1F , rmvdS20 , rmvdS21 , rmvdS22 , rmvdS23 , rmvdS24 , rmvdS25 , rmvdS26 , rmvdS27 , rmvdS28 , rmvdS29 , rmvdS2A , rmvdS2B , rmvdS2C , rmvdS2D , rmvdS2E , rmvdS2F , rmvdS30 , rmvdS31 , rmvdS32 , rmvdS33 , rmvdS34 , rmvdS35 , rmvdS36 , rmvdS37 , rmvdS38 , rmvdS39 , rmvdS3A , rmvdS3B , rmvdS3C , rmvdS3D , rmvdS3E , rmvdS3F <] .
Lemma StakeholderBase_ι__stakeholderRemoveStake_А_removedStake_bs_id: StakeholderBase_ι__stakeholderRemoveStake_А_removedStake_bs_def = [> rmvdS00 , rmvdS01 , rmvdS02 , rmvdS03 , rmvdS04 , rmvdS05 , rmvdS06 , rmvdS07 , rmvdS08 , rmvdS09 , rmvdS0A , rmvdS0B , rmvdS0C , rmvdS0D , rmvdS0E , rmvdS0F , rmvdS10 , rmvdS11 , rmvdS12 , rmvdS13 , rmvdS14 , rmvdS15 , rmvdS16 , rmvdS17 , rmvdS18 , rmvdS19 , rmvdS1A , rmvdS1B , rmvdS1C , rmvdS1D , rmvdS1E , rmvdS1F , rmvdS20 , rmvdS21 , rmvdS22 , rmvdS23 , rmvdS24 , rmvdS25 , rmvdS26 , rmvdS27 , rmvdS28 , rmvdS29 , rmvdS2A , rmvdS2B , rmvdS2C , rmvdS2D , rmvdS2E , rmvdS2F , rmvdS30 , rmvdS31 , rmvdS32 , rmvdS33 , rmvdS34 , rmvdS35 , rmvdS36 , rmvdS37 , rmvdS38 , rmvdS39 , rmvdS3A , rmvdS3B , rmvdS3C , rmvdS3D , rmvdS3E , rmvdS3F <] .
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
Qed. Variables StakeholderBase_ι__stakeholderRemoveStake_А_unusedStake : Z . 
Variables nsdSt00 nsdSt01 nsdSt02 nsdSt03 nsdSt04 nsdSt05 nsdSt06 nsdSt07 nsdSt08 nsdSt09 nsdSt0A nsdSt0B nsdSt0C nsdSt0D nsdSt0E nsdSt0F nsdSt10 nsdSt11 nsdSt12 nsdSt13 nsdSt14 nsdSt15 nsdSt16 nsdSt17 nsdSt18 nsdSt19 nsdSt1A nsdSt1B nsdSt1C nsdSt1D nsdSt1E nsdSt1F nsdSt20 nsdSt21 nsdSt22 nsdSt23 nsdSt24 nsdSt25 nsdSt26 nsdSt27 nsdSt28 nsdSt29 nsdSt2A nsdSt2B nsdSt2C nsdSt2D nsdSt2E nsdSt2F nsdSt30 nsdSt31 nsdSt32 nsdSt33 nsdSt34 nsdSt35 nsdSt36 nsdSt37 nsdSt38 nsdSt39 nsdSt3A nsdSt3B nsdSt3C nsdSt3D nsdSt3E nsdSt3F  : TVMBit . 
Definition StakeholderBase_ι__stakeholderRemoveStake_А_unusedStake_bs_def := [> nsdSt00 , nsdSt01 , nsdSt02 , nsdSt03 , nsdSt04 , nsdSt05 , nsdSt06 , nsdSt07 , nsdSt08 , nsdSt09 , nsdSt0A , nsdSt0B , nsdSt0C , nsdSt0D , nsdSt0E , nsdSt0F , nsdSt10 , nsdSt11 , nsdSt12 , nsdSt13 , nsdSt14 , nsdSt15 , nsdSt16 , nsdSt17 , nsdSt18 , nsdSt19 , nsdSt1A , nsdSt1B , nsdSt1C , nsdSt1D , nsdSt1E , nsdSt1F , nsdSt20 , nsdSt21 , nsdSt22 , nsdSt23 , nsdSt24 , nsdSt25 , nsdSt26 , nsdSt27 , nsdSt28 , nsdSt29 , nsdSt2A , nsdSt2B , nsdSt2C , nsdSt2D , nsdSt2E , nsdSt2F , nsdSt30 , nsdSt31 , nsdSt32 , nsdSt33 , nsdSt34 , nsdSt35 , nsdSt36 , nsdSt37 , nsdSt38 , nsdSt39 , nsdSt3A , nsdSt3B , nsdSt3C , nsdSt3D , nsdSt3E , nsdSt3F <] .
Lemma StakeholderBase_ι__stakeholderRemoveStake_А_unusedStake_bs_id: StakeholderBase_ι__stakeholderRemoveStake_А_unusedStake_bs_def = [> nsdSt00 , nsdSt01 , nsdSt02 , nsdSt03 , nsdSt04 , nsdSt05 , nsdSt06 , nsdSt07 , nsdSt08 , nsdSt09 , nsdSt0A , nsdSt0B , nsdSt0C , nsdSt0D , nsdSt0E , nsdSt0F , nsdSt10 , nsdSt11 , nsdSt12 , nsdSt13 , nsdSt14 , nsdSt15 , nsdSt16 , nsdSt17 , nsdSt18 , nsdSt19 , nsdSt1A , nsdSt1B , nsdSt1C , nsdSt1D , nsdSt1E , nsdSt1F , nsdSt20 , nsdSt21 , nsdSt22 , nsdSt23 , nsdSt24 , nsdSt25 , nsdSt26 , nsdSt27 , nsdSt28 , nsdSt29 , nsdSt2A , nsdSt2B , nsdSt2C , nsdSt2D , nsdSt2E , nsdSt2F , nsdSt30 , nsdSt31 , nsdSt32 , nsdSt33 , nsdSt34 , nsdSt35 , nsdSt36 , nsdSt37 , nsdSt38 , nsdSt39 , nsdSt3A , nsdSt3B , nsdSt3C , nsdSt3D , nsdSt3E , nsdSt3F <] .
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
Variables rwrd00 rwrd01 rwrd02 rwrd03 rwrd04 rwrd05 rwrd06 rwrd07 rwrd08 rwrd09 rwrd0A rwrd0B rwrd0C rwrd0D rwrd0E rwrd0F rwrd10 rwrd11 rwrd12 rwrd13 rwrd14 rwrd15 rwrd16 rwrd17 rwrd18 rwrd19 rwrd1A rwrd1B rwrd1C rwrd1D rwrd1E rwrd1F rwrd20 rwrd21 rwrd22 rwrd23 rwrd24 rwrd25 rwrd26 rwrd27 rwrd28 rwrd29 rwrd2A rwrd2B rwrd2C rwrd2D rwrd2E rwrd2F rwrd30 rwrd31 rwrd32 rwrd33 rwrd34 rwrd35 rwrd36 rwrd37 rwrd38 rwrd39 rwrd3A rwrd3B rwrd3C rwrd3D rwrd3E rwrd3F  : TVMBit . 
Definition StakeholderBase_ι__stakeholderUpdateReward_А_reward_bs_def := [> rwrd00 , rwrd01 , rwrd02 , rwrd03 , rwrd04 , rwrd05 , rwrd06 , rwrd07 , rwrd08 , rwrd09 , rwrd0A , rwrd0B , rwrd0C , rwrd0D , rwrd0E , rwrd0F , rwrd10 , rwrd11 , rwrd12 , rwrd13 , rwrd14 , rwrd15 , rwrd16 , rwrd17 , rwrd18 , rwrd19 , rwrd1A , rwrd1B , rwrd1C , rwrd1D , rwrd1E , rwrd1F , rwrd20 , rwrd21 , rwrd22 , rwrd23 , rwrd24 , rwrd25 , rwrd26 , rwrd27 , rwrd28 , rwrd29 , rwrd2A , rwrd2B , rwrd2C , rwrd2D , rwrd2E , rwrd2F , rwrd30 , rwrd31 , rwrd32 , rwrd33 , rwrd34 , rwrd35 , rwrd36 , rwrd37 , rwrd38 , rwrd39 , rwrd3A , rwrd3B , rwrd3C , rwrd3D , rwrd3E , rwrd3F <] .
Lemma StakeholderBase_ι__stakeholderUpdateReward_А_reward_bs_id: StakeholderBase_ι__stakeholderUpdateReward_А_reward_bs_def = [> rwrd00 , rwrd01 , rwrd02 , rwrd03 , rwrd04 , rwrd05 , rwrd06 , rwrd07 , rwrd08 , rwrd09 , rwrd0A , rwrd0B , rwrd0C , rwrd0D , rwrd0E , rwrd0F , rwrd10 , rwrd11 , rwrd12 , rwrd13 , rwrd14 , rwrd15 , rwrd16 , rwrd17 , rwrd18 , rwrd19 , rwrd1A , rwrd1B , rwrd1C , rwrd1D , rwrd1E , rwrd1F , rwrd20 , rwrd21 , rwrd22 , rwrd23 , rwrd24 , rwrd25 , rwrd26 , rwrd27 , rwrd28 , rwrd29 , rwrd2A , rwrd2B , rwrd2C , rwrd2D , rwrd2E , rwrd2F , rwrd30 , rwrd31 , rwrd32 , rwrd33 , rwrd34 , rwrd35 , rwrd36 , rwrd37 , rwrd38 , rwrd39 , rwrd3A , rwrd3B , rwrd3C , rwrd3D , rwrd3E , rwrd3F <] .
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
Qed. Variables StakeholderBase_ι__stakeholderUpdateReward_А_fee : Z . 
Variables f00 f01 f02 f03 f04 f05 f06 f07 f08 f09 f0A f0B f0C f0D f0E f0F f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f1A f1B f1C f1D f1E f1F f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f2A f2B f2C f2D f2E f2F f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f3A f3B f3C f3D f3E f3F  : TVMBit . 
Definition StakeholderBase_ι__stakeholderUpdateReward_А_fee_bs_def := [> f00 , f01 , f02 , f03 , f04 , f05 , f06 , f07 , f08 , f09 , f0A , f0B , f0C , f0D , f0E , f0F , f10 , f11 , f12 , f13 , f14 , f15 , f16 , f17 , f18 , f19 , f1A , f1B , f1C , f1D , f1E , f1F , f20 , f21 , f22 , f23 , f24 , f25 , f26 , f27 , f28 , f29 , f2A , f2B , f2C , f2D , f2E , f2F , f30 , f31 , f32 , f33 , f34 , f35 , f36 , f37 , f38 , f39 , f3A , f3B , f3C , f3D , f3E , f3F <] .
Lemma StakeholderBase_ι__stakeholderUpdateReward_А_fee_bs_id: StakeholderBase_ι__stakeholderUpdateReward_А_fee_bs_def = [> f00 , f01 , f02 , f03 , f04 , f05 , f06 , f07 , f08 , f09 , f0A , f0B , f0C , f0D , f0E , f0F , f10 , f11 , f12 , f13 , f14 , f15 , f16 , f17 , f18 , f19 , f1A , f1B , f1C , f1D , f1E , f1F , f20 , f21 , f22 , f23 , f24 , f25 , f26 , f27 , f28 , f29 , f2A , f2B , f2C , f2D , f2E , f2F , f30 , f31 , f32 , f33 , f34 , f35 , f36 , f37 , f38 , f39 , f3A , f3B , f3C , f3D , f3E , f3F <] .
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
Variables dd00 dd01 dd02 dd03 dd04 dd05 dd06 dd07 dd08 dd09 dd0A dd0B dd0C dd0D dd0E dd0F dd10 dd11 dd12 dd13 dd14 dd15 dd16 dd17 dd18 dd19 dd1A dd1B dd1C dd1D dd1E dd1F dd20 dd21 dd22 dd23 dd24 dd25 dd26 dd27 dd28 dd29 dd2A dd2B dd2C dd2D dd2E dd2F dd30 dd31 dd32 dd33 dd34 dd35 dd36 dd37 dd38 dd39 dd3A dd3B dd3C dd3D dd3E dd3F  : TVMBit . 
Definition StakeholderBase_ι__stakeholderUpdateUnusedStake_А_add_bs_def := [> dd00 , dd01 , dd02 , dd03 , dd04 , dd05 , dd06 , dd07 , dd08 , dd09 , dd0A , dd0B , dd0C , dd0D , dd0E , dd0F , dd10 , dd11 , dd12 , dd13 , dd14 , dd15 , dd16 , dd17 , dd18 , dd19 , dd1A , dd1B , dd1C , dd1D , dd1E , dd1F , dd20 , dd21 , dd22 , dd23 , dd24 , dd25 , dd26 , dd27 , dd28 , dd29 , dd2A , dd2B , dd2C , dd2D , dd2E , dd2F , dd30 , dd31 , dd32 , dd33 , dd34 , dd35 , dd36 , dd37 , dd38 , dd39 , dd3A , dd3B , dd3C , dd3D , dd3E , dd3F <] .
Lemma StakeholderBase_ι__stakeholderUpdateUnusedStake_А_add_bs_id: StakeholderBase_ι__stakeholderUpdateUnusedStake_А_add_bs_def = [> dd00 , dd01 , dd02 , dd03 , dd04 , dd05 , dd06 , dd07 , dd08 , dd09 , dd0A , dd0B , dd0C , dd0D , dd0E , dd0F , dd10 , dd11 , dd12 , dd13 , dd14 , dd15 , dd16 , dd17 , dd18 , dd19 , dd1A , dd1B , dd1C , dd1D , dd1E , dd1F , dd20 , dd21 , dd22 , dd23 , dd24 , dd25 , dd26 , dd27 , dd28 , dd29 , dd2A , dd2B , dd2C , dd2D , dd2E , dd2F , dd30 , dd31 , dd32 , dd33 , dd34 , dd35 , dd36 , dd37 , dd38 , dd39 , dd3A , dd3B , dd3C , dd3D , dd3E , dd3F <] .
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
Qed. Variables StakeholderBase_ι__stakeholderUpdateUnusedStake_А_remove : Z . 
Variables rmv00 rmv01 rmv02 rmv03 rmv04 rmv05 rmv06 rmv07 rmv08 rmv09 rmv0A rmv0B rmv0C rmv0D rmv0E rmv0F rmv10 rmv11 rmv12 rmv13 rmv14 rmv15 rmv16 rmv17 rmv18 rmv19 rmv1A rmv1B rmv1C rmv1D rmv1E rmv1F rmv20 rmv21 rmv22 rmv23 rmv24 rmv25 rmv26 rmv27 rmv28 rmv29 rmv2A rmv2B rmv2C rmv2D rmv2E rmv2F rmv30 rmv31 rmv32 rmv33 rmv34 rmv35 rmv36 rmv37 rmv38 rmv39 rmv3A rmv3B rmv3C rmv3D rmv3E rmv3F  : TVMBit . 
Definition StakeholderBase_ι__stakeholderUpdateUnusedStake_А_remove_bs_def := [> rmv00 , rmv01 , rmv02 , rmv03 , rmv04 , rmv05 , rmv06 , rmv07 , rmv08 , rmv09 , rmv0A , rmv0B , rmv0C , rmv0D , rmv0E , rmv0F , rmv10 , rmv11 , rmv12 , rmv13 , rmv14 , rmv15 , rmv16 , rmv17 , rmv18 , rmv19 , rmv1A , rmv1B , rmv1C , rmv1D , rmv1E , rmv1F , rmv20 , rmv21 , rmv22 , rmv23 , rmv24 , rmv25 , rmv26 , rmv27 , rmv28 , rmv29 , rmv2A , rmv2B , rmv2C , rmv2D , rmv2E , rmv2F , rmv30 , rmv31 , rmv32 , rmv33 , rmv34 , rmv35 , rmv36 , rmv37 , rmv38 , rmv39 , rmv3A , rmv3B , rmv3C , rmv3D , rmv3E , rmv3F <] .
Lemma StakeholderBase_ι__stakeholderUpdateUnusedStake_А_remove_bs_id: StakeholderBase_ι__stakeholderUpdateUnusedStake_А_remove_bs_def = [> rmv00 , rmv01 , rmv02 , rmv03 , rmv04 , rmv05 , rmv06 , rmv07 , rmv08 , rmv09 , rmv0A , rmv0B , rmv0C , rmv0D , rmv0E , rmv0F , rmv10 , rmv11 , rmv12 , rmv13 , rmv14 , rmv15 , rmv16 , rmv17 , rmv18 , rmv19 , rmv1A , rmv1B , rmv1C , rmv1D , rmv1E , rmv1F , rmv20 , rmv21 , rmv22 , rmv23 , rmv24 , rmv25 , rmv26 , rmv27 , rmv28 , rmv29 , rmv2A , rmv2B , rmv2C , rmv2D , rmv2E , rmv2F , rmv30 , rmv31 , rmv32 , rmv33 , rmv34 , rmv35 , rmv36 , rmv37 , rmv38 , rmv39 , rmv3A , rmv3B , rmv3C , rmv3D , rmv3E , rmv3F <] .
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
Variables vldtn00 vldtn01 vldtn02 vldtn03 vldtn04 vldtn05 vldtn06 vldtn07 vldtn08 vldtn09 vldtn0A vldtn0B vldtn0C vldtn0D vldtn0E vldtn0F vldtn10 vldtn11 vldtn12 vldtn13 vldtn14 vldtn15 vldtn16 vldtn17 vldtn18 vldtn19 vldtn1A vldtn1B vldtn1C vldtn1D vldtn1E vldtn1F  : TVMBit . 
Definition RoundsBase_ι__addNewPoolingRound_А_validationStart_bs_def := [> vldtn00 , vldtn01 , vldtn02 , vldtn03 , vldtn04 , vldtn05 , vldtn06 , vldtn07 , vldtn08 , vldtn09 , vldtn0A , vldtn0B , vldtn0C , vldtn0D , vldtn0E , vldtn0F , vldtn10 , vldtn11 , vldtn12 , vldtn13 , vldtn14 , vldtn15 , vldtn16 , vldtn17 , vldtn18 , vldtn19 , vldtn1A , vldtn1B , vldtn1C , vldtn1D , vldtn1E , vldtn1F <] .
Lemma RoundsBase_ι__addNewPoolingRound_А_validationStart_bs_id: RoundsBase_ι__addNewPoolingRound_А_validationStart_bs_def = [> vldtn00 , vldtn01 , vldtn02 , vldtn03 , vldtn04 , vldtn05 , vldtn06 , vldtn07 , vldtn08 , vldtn09 , vldtn0A , vldtn0B , vldtn0C , vldtn0D , vldtn0E , vldtn0F , vldtn10 , vldtn11 , vldtn12 , vldtn13 , vldtn14 , vldtn15 , vldtn16 , vldtn17 , vldtn18 , vldtn19 , vldtn1A , vldtn1B , vldtn1C , vldtn1D , vldtn1E , vldtn1F <] .
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
Qed. Variables RoundsBase_ι__addNewPoolingRound_А_validationPeriod : Z . 
Variables vldtn00 vldtn01 vldtn02 vldtn03 vldtn04 vldtn05 vldtn06 vldtn07 vldtn08 vldtn09 vldtn0A vldtn0B vldtn0C vldtn0D vldtn0E vldtn0F vldtn10 vldtn11 vldtn12 vldtn13 vldtn14 vldtn15 vldtn16 vldtn17 vldtn18 vldtn19 vldtn1A vldtn1B vldtn1C vldtn1D vldtn1E vldtn1F  : TVMBit . 
Definition RoundsBase_ι__addNewPoolingRound_А_validationPeriod_bs_def := [> vldtn00 , vldtn01 , vldtn02 , vldtn03 , vldtn04 , vldtn05 , vldtn06 , vldtn07 , vldtn08 , vldtn09 , vldtn0A , vldtn0B , vldtn0C , vldtn0D , vldtn0E , vldtn0F , vldtn10 , vldtn11 , vldtn12 , vldtn13 , vldtn14 , vldtn15 , vldtn16 , vldtn17 , vldtn18 , vldtn19 , vldtn1A , vldtn1B , vldtn1C , vldtn1D , vldtn1E , vldtn1F <] .
Lemma RoundsBase_ι__addNewPoolingRound_А_validationPeriod_bs_id: RoundsBase_ι__addNewPoolingRound_А_validationPeriod_bs_def = [> vldtn00 , vldtn01 , vldtn02 , vldtn03 , vldtn04 , vldtn05 , vldtn06 , vldtn07 , vldtn08 , vldtn09 , vldtn0A , vldtn0B , vldtn0C , vldtn0D , vldtn0E , vldtn0F , vldtn10 , vldtn11 , vldtn12 , vldtn13 , vldtn14 , vldtn15 , vldtn16 , vldtn17 , vldtn18 , vldtn19 , vldtn1A , vldtn1B , vldtn1C , vldtn1D , vldtn1E , vldtn1F <] .
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
Variables stk00 stk01 stk02 stk03 stk04 stk05 stk06 stk07 stk08 stk09 stk0A stk0B stk0C stk0D stk0E stk0F stk10 stk11 stk12 stk13 stk14 stk15 stk16 stk17 stk18 stk19 stk1A stk1B stk1C stk1D stk1E stk1F stk20 stk21 stk22 stk23 stk24 stk25 stk26 stk27 stk28 stk29 stk2A stk2B stk2C stk2D stk2E stk2F stk30 stk31 stk32 stk33 stk34 stk35 stk36 stk37 stk38 stk39 stk3A stk3B stk3C stk3D stk3E stk3F  : TVMBit . 
Definition RoundsBase_ι__roundAddStake_А_stake_bs_def := [> stk00 , stk01 , stk02 , stk03 , stk04 , stk05 , stk06 , stk07 , stk08 , stk09 , stk0A , stk0B , stk0C , stk0D , stk0E , stk0F , stk10 , stk11 , stk12 , stk13 , stk14 , stk15 , stk16 , stk17 , stk18 , stk19 , stk1A , stk1B , stk1C , stk1D , stk1E , stk1F , stk20 , stk21 , stk22 , stk23 , stk24 , stk25 , stk26 , stk27 , stk28 , stk29 , stk2A , stk2B , stk2C , stk2D , stk2E , stk2F , stk30 , stk31 , stk32 , stk33 , stk34 , stk35 , stk36 , stk37 , stk38 , stk39 , stk3A , stk3B , stk3C , stk3D , stk3E , stk3F <] .
Lemma RoundsBase_ι__roundAddStake_А_stake_bs_id: RoundsBase_ι__roundAddStake_А_stake_bs_def = [> stk00 , stk01 , stk02 , stk03 , stk04 , stk05 , stk06 , stk07 , stk08 , stk09 , stk0A , stk0B , stk0C , stk0D , stk0E , stk0F , stk10 , stk11 , stk12 , stk13 , stk14 , stk15 , stk16 , stk17 , stk18 , stk19 , stk1A , stk1B , stk1C , stk1D , stk1E , stk1F , stk20 , stk21 , stk22 , stk23 , stk24 , stk25 , stk26 , stk27 , stk28 , stk29 , stk2A , stk2B , stk2C , stk2D , stk2E , stk2F , stk30 , stk31 , stk32 , stk33 , stk34 , stk35 , stk36 , stk37 , stk38 , stk39 , stk3A , stk3B , stk3C , stk3D , stk3E , stk3F <] .
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
Variables ndStk00 ndStk01 ndStk02 ndStk03 ndStk04 ndStk05 ndStk06 ndStk07 ndStk08 ndStk09 ndStk0A ndStk0B ndStk0C ndStk0D ndStk0E ndStk0F ndStk10 ndStk11 ndStk12 ndStk13 ndStk14 ndStk15 ndStk16 ndStk17 ndStk18 ndStk19 ndStk1A ndStk1B ndStk1C ndStk1D ndStk1E ndStk1F ndStk20 ndStk21 ndStk22 ndStk23 ndStk24 ndStk25 ndStk26 ndStk27 ndStk28 ndStk29 ndStk2A ndStk2B ndStk2C ndStk2D ndStk2E ndStk2F ndStk30 ndStk31 ndStk32 ndStk33 ndStk34 ndStk35 ndStk36 ndStk37 ndStk38 ndStk39 ndStk3A ndStk3B ndStk3C ndStk3D ndStk3E ndStk3F  : TVMBit . 
Definition RoundsBase_ι__roundSetStake_А_endStake_bs_def := [> ndStk00 , ndStk01 , ndStk02 , ndStk03 , ndStk04 , ndStk05 , ndStk06 , ndStk07 , ndStk08 , ndStk09 , ndStk0A , ndStk0B , ndStk0C , ndStk0D , ndStk0E , ndStk0F , ndStk10 , ndStk11 , ndStk12 , ndStk13 , ndStk14 , ndStk15 , ndStk16 , ndStk17 , ndStk18 , ndStk19 , ndStk1A , ndStk1B , ndStk1C , ndStk1D , ndStk1E , ndStk1F , ndStk20 , ndStk21 , ndStk22 , ndStk23 , ndStk24 , ndStk25 , ndStk26 , ndStk27 , ndStk28 , ndStk29 , ndStk2A , ndStk2B , ndStk2C , ndStk2D , ndStk2E , ndStk2F , ndStk30 , ndStk31 , ndStk32 , ndStk33 , ndStk34 , ndStk35 , ndStk36 , ndStk37 , ndStk38 , ndStk39 , ndStk3A , ndStk3B , ndStk3C , ndStk3D , ndStk3E , ndStk3F <] .
Lemma RoundsBase_ι__roundSetStake_А_endStake_bs_id: RoundsBase_ι__roundSetStake_А_endStake_bs_def = [> ndStk00 , ndStk01 , ndStk02 , ndStk03 , ndStk04 , ndStk05 , ndStk06 , ndStk07 , ndStk08 , ndStk09 , ndStk0A , ndStk0B , ndStk0C , ndStk0D , ndStk0E , ndStk0F , ndStk10 , ndStk11 , ndStk12 , ndStk13 , ndStk14 , ndStk15 , ndStk16 , ndStk17 , ndStk18 , ndStk19 , ndStk1A , ndStk1B , ndStk1C , ndStk1D , ndStk1E , ndStk1F , ndStk20 , ndStk21 , ndStk22 , ndStk23 , ndStk24 , ndStk25 , ndStk26 , ndStk27 , ndStk28 , ndStk29 , ndStk2A , ndStk2B , ndStk2C , ndStk2D , ndStk2E , ndStk2F , ndStk30 , ndStk31 , ndStk32 , ndStk33 , ndStk34 , ndStk35 , ndStk36 , ndStk37 , ndStk38 , ndStk39 , ndStk3A , ndStk3B , ndStk3C , ndStk3D , ndStk3E , ndStk3F <] .
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
Variables stk00 stk01 stk02 stk03 stk04 stk05 stk06 stk07 stk08 stk09 stk0A stk0B stk0C stk0D stk0E stk0F stk10 stk11 stk12 stk13 stk14 stk15 stk16 stk17 stk18 stk19 stk1A stk1B stk1C stk1D stk1E stk1F stk20 stk21 stk22 stk23 stk24 stk25 stk26 stk27 stk28 stk29 stk2A stk2B stk2C stk2D stk2E stk2F stk30 stk31 stk32 stk33 stk34 stk35 stk36 stk37 stk38 stk39 stk3A stk3B stk3C stk3D stk3E stk3F  : TVMBit . 
Definition RoundsBase_ι__roundInvestStake_А_stake_bs_def := [> stk00 , stk01 , stk02 , stk03 , stk04 , stk05 , stk06 , stk07 , stk08 , stk09 , stk0A , stk0B , stk0C , stk0D , stk0E , stk0F , stk10 , stk11 , stk12 , stk13 , stk14 , stk15 , stk16 , stk17 , stk18 , stk19 , stk1A , stk1B , stk1C , stk1D , stk1E , stk1F , stk20 , stk21 , stk22 , stk23 , stk24 , stk25 , stk26 , stk27 , stk28 , stk29 , stk2A , stk2B , stk2C , stk2D , stk2E , stk2F , stk30 , stk31 , stk32 , stk33 , stk34 , stk35 , stk36 , stk37 , stk38 , stk39 , stk3A , stk3B , stk3C , stk3D , stk3E , stk3F <] .
Lemma RoundsBase_ι__roundInvestStake_А_stake_bs_id: RoundsBase_ι__roundInvestStake_А_stake_bs_def = [> stk00 , stk01 , stk02 , stk03 , stk04 , stk05 , stk06 , stk07 , stk08 , stk09 , stk0A , stk0B , stk0C , stk0D , stk0E , stk0F , stk10 , stk11 , stk12 , stk13 , stk14 , stk15 , stk16 , stk17 , stk18 , stk19 , stk1A , stk1B , stk1C , stk1D , stk1E , stk1F , stk20 , stk21 , stk22 , stk23 , stk24 , stk25 , stk26 , stk27 , stk28 , stk29 , stk2A , stk2B , stk2C , stk2D , stk2E , stk2F , stk30 , stk31 , stk32 , stk33 , stk34 , stk35 , stk36 , stk37 , stk38 , stk39 , stk3A , stk3B , stk3C , stk3D , stk3E , stk3F <] .
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
Variables pndng00 pndng01 pndng02 pndng03 pndng04 pndng05 pndng06 pndng07 pndng08 pndng09 pndng0A pndng0B pndng0C pndng0D pndng0E pndng0F pndng10 pndng11 pndng12 pndng13 pndng14 pndng15 pndng16 pndng17 pndng18 pndng19 pndng1A pndng1B pndng1C pndng1D pndng1E pndng1F  : TVMBit . 
Definition RoundsBase_ι__removePendingRound_А_pendingId_bs_def := [> pndng00 , pndng01 , pndng02 , pndng03 , pndng04 , pndng05 , pndng06 , pndng07 , pndng08 , pndng09 , pndng0A , pndng0B , pndng0C , pndng0D , pndng0E , pndng0F , pndng10 , pndng11 , pndng12 , pndng13 , pndng14 , pndng15 , pndng16 , pndng17 , pndng18 , pndng19 , pndng1A , pndng1B , pndng1C , pndng1D , pndng1E , pndng1F <] .
Lemma RoundsBase_ι__removePendingRound_А_pendingId_bs_id: RoundsBase_ι__removePendingRound_А_pendingId_bs_def = [> pndng00 , pndng01 , pndng02 , pndng03 , pndng04 , pndng05 , pndng06 , pndng07 , pndng08 , pndng09 , pndng0A , pndng0B , pndng0C , pndng0D , pndng0E , pndng0F , pndng10 , pndng11 , pndng12 , pndng13 , pndng14 , pndng15 , pndng16 , pndng17 , pndng18 , pndng19 , pndng1A , pndng1B , pndng1C , pndng1D , pndng1E , pndng1F <] .
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
Variables ttlSt00 ttlSt01 ttlSt02 ttlSt03 ttlSt04 ttlSt05 ttlSt06 ttlSt07 ttlSt08 ttlSt09 ttlSt0A ttlSt0B ttlSt0C ttlSt0D ttlSt0E ttlSt0F ttlSt10 ttlSt11 ttlSt12 ttlSt13 ttlSt14 ttlSt15 ttlSt16 ttlSt17 ttlSt18 ttlSt19 ttlSt1A ttlSt1B ttlSt1C ttlSt1D ttlSt1E ttlSt1F ttlSt20 ttlSt21 ttlSt22 ttlSt23 ttlSt24 ttlSt25 ttlSt26 ttlSt27 ttlSt28 ttlSt29 ttlSt2A ttlSt2B ttlSt2C ttlSt2D ttlSt2E ttlSt2F ttlSt30 ttlSt31 ttlSt32 ttlSt33 ttlSt34 ttlSt35 ttlSt36 ttlSt37 ttlSt38 ttlSt39 ttlSt3A ttlSt3B ttlSt3C ttlSt3D ttlSt3E ttlSt3F  : TVMBit . 
Definition StakingContract_ι__calcLastRoundInterest_А_totalStake_bs_def := [> ttlSt00 , ttlSt01 , ttlSt02 , ttlSt03 , ttlSt04 , ttlSt05 , ttlSt06 , ttlSt07 , ttlSt08 , ttlSt09 , ttlSt0A , ttlSt0B , ttlSt0C , ttlSt0D , ttlSt0E , ttlSt0F , ttlSt10 , ttlSt11 , ttlSt12 , ttlSt13 , ttlSt14 , ttlSt15 , ttlSt16 , ttlSt17 , ttlSt18 , ttlSt19 , ttlSt1A , ttlSt1B , ttlSt1C , ttlSt1D , ttlSt1E , ttlSt1F , ttlSt20 , ttlSt21 , ttlSt22 , ttlSt23 , ttlSt24 , ttlSt25 , ttlSt26 , ttlSt27 , ttlSt28 , ttlSt29 , ttlSt2A , ttlSt2B , ttlSt2C , ttlSt2D , ttlSt2E , ttlSt2F , ttlSt30 , ttlSt31 , ttlSt32 , ttlSt33 , ttlSt34 , ttlSt35 , ttlSt36 , ttlSt37 , ttlSt38 , ttlSt39 , ttlSt3A , ttlSt3B , ttlSt3C , ttlSt3D , ttlSt3E , ttlSt3F <] .
Lemma StakingContract_ι__calcLastRoundInterest_А_totalStake_bs_id: StakingContract_ι__calcLastRoundInterest_А_totalStake_bs_def = [> ttlSt00 , ttlSt01 , ttlSt02 , ttlSt03 , ttlSt04 , ttlSt05 , ttlSt06 , ttlSt07 , ttlSt08 , ttlSt09 , ttlSt0A , ttlSt0B , ttlSt0C , ttlSt0D , ttlSt0E , ttlSt0F , ttlSt10 , ttlSt11 , ttlSt12 , ttlSt13 , ttlSt14 , ttlSt15 , ttlSt16 , ttlSt17 , ttlSt18 , ttlSt19 , ttlSt1A , ttlSt1B , ttlSt1C , ttlSt1D , ttlSt1E , ttlSt1F , ttlSt20 , ttlSt21 , ttlSt22 , ttlSt23 , ttlSt24 , ttlSt25 , ttlSt26 , ttlSt27 , ttlSt28 , ttlSt29 , ttlSt2A , ttlSt2B , ttlSt2C , ttlSt2D , ttlSt2E , ttlSt2F , ttlSt30 , ttlSt31 , ttlSt32 , ttlSt33 , ttlSt34 , ttlSt35 , ttlSt36 , ttlSt37 , ttlSt38 , ttlSt39 , ttlSt3A , ttlSt3B , ttlSt3C , ttlSt3D , ttlSt3E , ttlSt3F <] .
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
Qed. Variables StakingContract_ι__calcLastRoundInterest_А_rewards : Z . 
Variables rwrds00 rwrds01 rwrds02 rwrds03 rwrds04 rwrds05 rwrds06 rwrds07 rwrds08 rwrds09 rwrds0A rwrds0B rwrds0C rwrds0D rwrds0E rwrds0F rwrds10 rwrds11 rwrds12 rwrds13 rwrds14 rwrds15 rwrds16 rwrds17 rwrds18 rwrds19 rwrds1A rwrds1B rwrds1C rwrds1D rwrds1E rwrds1F rwrds20 rwrds21 rwrds22 rwrds23 rwrds24 rwrds25 rwrds26 rwrds27 rwrds28 rwrds29 rwrds2A rwrds2B rwrds2C rwrds2D rwrds2E rwrds2F rwrds30 rwrds31 rwrds32 rwrds33 rwrds34 rwrds35 rwrds36 rwrds37 rwrds38 rwrds39 rwrds3A rwrds3B rwrds3C rwrds3D rwrds3E rwrds3F  : TVMBit . 
Definition StakingContract_ι__calcLastRoundInterest_А_rewards_bs_def := [> rwrds00 , rwrds01 , rwrds02 , rwrds03 , rwrds04 , rwrds05 , rwrds06 , rwrds07 , rwrds08 , rwrds09 , rwrds0A , rwrds0B , rwrds0C , rwrds0D , rwrds0E , rwrds0F , rwrds10 , rwrds11 , rwrds12 , rwrds13 , rwrds14 , rwrds15 , rwrds16 , rwrds17 , rwrds18 , rwrds19 , rwrds1A , rwrds1B , rwrds1C , rwrds1D , rwrds1E , rwrds1F , rwrds20 , rwrds21 , rwrds22 , rwrds23 , rwrds24 , rwrds25 , rwrds26 , rwrds27 , rwrds28 , rwrds29 , rwrds2A , rwrds2B , rwrds2C , rwrds2D , rwrds2E , rwrds2F , rwrds30 , rwrds31 , rwrds32 , rwrds33 , rwrds34 , rwrds35 , rwrds36 , rwrds37 , rwrds38 , rwrds39 , rwrds3A , rwrds3B , rwrds3C , rwrds3D , rwrds3E , rwrds3F <] .
Lemma StakingContract_ι__calcLastRoundInterest_А_rewards_bs_id: StakingContract_ι__calcLastRoundInterest_А_rewards_bs_def = [> rwrds00 , rwrds01 , rwrds02 , rwrds03 , rwrds04 , rwrds05 , rwrds06 , rwrds07 , rwrds08 , rwrds09 , rwrds0A , rwrds0B , rwrds0C , rwrds0D , rwrds0E , rwrds0F , rwrds10 , rwrds11 , rwrds12 , rwrds13 , rwrds14 , rwrds15 , rwrds16 , rwrds17 , rwrds18 , rwrds19 , rwrds1A , rwrds1B , rwrds1C , rwrds1D , rwrds1E , rwrds1F , rwrds20 , rwrds21 , rwrds22 , rwrds23 , rwrds24 , rwrds25 , rwrds26 , rwrds27 , rwrds28 , rwrds29 , rwrds2A , rwrds2B , rwrds2C , rwrds2D , rwrds2E , rwrds2F , rwrds30 , rwrds31 , rwrds32 , rwrds33 , rwrds34 , rwrds35 , rwrds36 , rwrds37 , rwrds38 , rwrds39 , rwrds3A , rwrds3B , rwrds3C , rwrds3D , rwrds3E , rwrds3F <] .
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
Variables rrcd00 rrcd01 rrcd02 rrcd03 rrcd04 rrcd05 rrcd06 rrcd07 rrcd08 rrcd09 rrcd0A rrcd0B rrcd0C rrcd0D rrcd0E rrcd0F rrcd10 rrcd11 rrcd12 rrcd13 rrcd14 rrcd15 rrcd16 rrcd17 rrcd18 rrcd19 rrcd1A rrcd1B rrcd1C rrcd1D rrcd1E rrcd1F  : TVMBit . 
Definition StakingContract_ι__returnError_А_errcode_bs_def := [> rrcd00 , rrcd01 , rrcd02 , rrcd03 , rrcd04 , rrcd05 , rrcd06 , rrcd07 , rrcd08 , rrcd09 , rrcd0A , rrcd0B , rrcd0C , rrcd0D , rrcd0E , rrcd0F , rrcd10 , rrcd11 , rrcd12 , rrcd13 , rrcd14 , rrcd15 , rrcd16 , rrcd17 , rrcd18 , rrcd19 , rrcd1A , rrcd1B , rrcd1C , rrcd1D , rrcd1E , rrcd1F <] .
Lemma StakingContract_ι__returnError_А_errcode_bs_id: StakingContract_ι__returnError_А_errcode_bs_def = [> rrcd00 , rrcd01 , rrcd02 , rrcd03 , rrcd04 , rrcd05 , rrcd06 , rrcd07 , rrcd08 , rrcd09 , rrcd0A , rrcd0B , rrcd0C , rrcd0D , rrcd0E , rrcd0F , rrcd10 , rrcd11 , rrcd12 , rrcd13 , rrcd14 , rrcd15 , rrcd16 , rrcd17 , rrcd18 , rrcd19 , rrcd1A , rrcd1B , rrcd1C , rrcd1D , rrcd1E , rrcd1F <] .
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
Qed. Variables StakingContract_ι__returnError_А_amount : Z . 
Variables mnt00 mnt01 mnt02 mnt03 mnt04 mnt05 mnt06 mnt07 mnt08 mnt09 mnt0A mnt0B mnt0C mnt0D mnt0E mnt0F mnt10 mnt11 mnt12 mnt13 mnt14 mnt15 mnt16 mnt17 mnt18 mnt19 mnt1A mnt1B mnt1C mnt1D mnt1E mnt1F mnt20 mnt21 mnt22 mnt23 mnt24 mnt25 mnt26 mnt27 mnt28 mnt29 mnt2A mnt2B mnt2C mnt2D mnt2E mnt2F mnt30 mnt31 mnt32 mnt33 mnt34 mnt35 mnt36 mnt37 mnt38 mnt39 mnt3A mnt3B mnt3C mnt3D mnt3E mnt3F  : TVMBit . 
Definition StakingContract_ι__returnError_А_amount_bs_def := [> mnt00 , mnt01 , mnt02 , mnt03 , mnt04 , mnt05 , mnt06 , mnt07 , mnt08 , mnt09 , mnt0A , mnt0B , mnt0C , mnt0D , mnt0E , mnt0F , mnt10 , mnt11 , mnt12 , mnt13 , mnt14 , mnt15 , mnt16 , mnt17 , mnt18 , mnt19 , mnt1A , mnt1B , mnt1C , mnt1D , mnt1E , mnt1F , mnt20 , mnt21 , mnt22 , mnt23 , mnt24 , mnt25 , mnt26 , mnt27 , mnt28 , mnt29 , mnt2A , mnt2B , mnt2C , mnt2D , mnt2E , mnt2F , mnt30 , mnt31 , mnt32 , mnt33 , mnt34 , mnt35 , mnt36 , mnt37 , mnt38 , mnt39 , mnt3A , mnt3B , mnt3C , mnt3D , mnt3E , mnt3F <] .
Lemma StakingContract_ι__returnError_А_amount_bs_id: StakingContract_ι__returnError_А_amount_bs_def = [> mnt00 , mnt01 , mnt02 , mnt03 , mnt04 , mnt05 , mnt06 , mnt07 , mnt08 , mnt09 , mnt0A , mnt0B , mnt0C , mnt0D , mnt0E , mnt0F , mnt10 , mnt11 , mnt12 , mnt13 , mnt14 , mnt15 , mnt16 , mnt17 , mnt18 , mnt19 , mnt1A , mnt1B , mnt1C , mnt1D , mnt1E , mnt1F , mnt20 , mnt21 , mnt22 , mnt23 , mnt24 , mnt25 , mnt26 , mnt27 , mnt28 , mnt29 , mnt2A , mnt2B , mnt2C , mnt2D , mnt2E , mnt2F , mnt30 , mnt31 , mnt32 , mnt33 , mnt34 , mnt35 , mnt36 , mnt37 , mnt38 , mnt39 , mnt3A , mnt3B , mnt3C , mnt3D , mnt3E , mnt3F <] .
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
Qed. Variables StakingContract_ι__returnError_А_comment : Z . 
Variables cmmnt00 cmmnt01 cmmnt02 cmmnt03 cmmnt04 cmmnt05 cmmnt06 cmmnt07 cmmnt08 cmmnt09 cmmnt0A cmmnt0B cmmnt0C cmmnt0D cmmnt0E cmmnt0F cmmnt10 cmmnt11 cmmnt12 cmmnt13 cmmnt14 cmmnt15 cmmnt16 cmmnt17 cmmnt18 cmmnt19 cmmnt1A cmmnt1B cmmnt1C cmmnt1D cmmnt1E cmmnt1F cmmnt20 cmmnt21 cmmnt22 cmmnt23 cmmnt24 cmmnt25 cmmnt26 cmmnt27 cmmnt28 cmmnt29 cmmnt2A cmmnt2B cmmnt2C cmmnt2D cmmnt2E cmmnt2F cmmnt30 cmmnt31 cmmnt32 cmmnt33 cmmnt34 cmmnt35 cmmnt36 cmmnt37 cmmnt38 cmmnt39 cmmnt3A cmmnt3B cmmnt3C cmmnt3D cmmnt3E cmmnt3F  : TVMBit . 
Definition StakingContract_ι__returnError_А_comment_bs_def := [> cmmnt00 , cmmnt01 , cmmnt02 , cmmnt03 , cmmnt04 , cmmnt05 , cmmnt06 , cmmnt07 , cmmnt08 , cmmnt09 , cmmnt0A , cmmnt0B , cmmnt0C , cmmnt0D , cmmnt0E , cmmnt0F , cmmnt10 , cmmnt11 , cmmnt12 , cmmnt13 , cmmnt14 , cmmnt15 , cmmnt16 , cmmnt17 , cmmnt18 , cmmnt19 , cmmnt1A , cmmnt1B , cmmnt1C , cmmnt1D , cmmnt1E , cmmnt1F , cmmnt20 , cmmnt21 , cmmnt22 , cmmnt23 , cmmnt24 , cmmnt25 , cmmnt26 , cmmnt27 , cmmnt28 , cmmnt29 , cmmnt2A , cmmnt2B , cmmnt2C , cmmnt2D , cmmnt2E , cmmnt2F , cmmnt30 , cmmnt31 , cmmnt32 , cmmnt33 , cmmnt34 , cmmnt35 , cmmnt36 , cmmnt37 , cmmnt38 , cmmnt39 , cmmnt3A , cmmnt3B , cmmnt3C , cmmnt3D , cmmnt3E , cmmnt3F <] .
Lemma StakingContract_ι__returnError_А_comment_bs_id: StakingContract_ι__returnError_А_comment_bs_def = [> cmmnt00 , cmmnt01 , cmmnt02 , cmmnt03 , cmmnt04 , cmmnt05 , cmmnt06 , cmmnt07 , cmmnt08 , cmmnt09 , cmmnt0A , cmmnt0B , cmmnt0C , cmmnt0D , cmmnt0E , cmmnt0F , cmmnt10 , cmmnt11 , cmmnt12 , cmmnt13 , cmmnt14 , cmmnt15 , cmmnt16 , cmmnt17 , cmmnt18 , cmmnt19 , cmmnt1A , cmmnt1B , cmmnt1C , cmmnt1D , cmmnt1E , cmmnt1F , cmmnt20 , cmmnt21 , cmmnt22 , cmmnt23 , cmmnt24 , cmmnt25 , cmmnt26 , cmmnt27 , cmmnt28 , cmmnt29 , cmmnt2A , cmmnt2B , cmmnt2C , cmmnt2D , cmmnt2E , cmmnt2F , cmmnt30 , cmmnt31 , cmmnt32 , cmmnt33 , cmmnt34 , cmmnt35 , cmmnt36 , cmmnt37 , cmmnt38 , cmmnt39 , cmmnt3A , cmmnt3B , cmmnt3C , cmmnt3D , cmmnt3E , cmmnt3F <] .
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
Variables f00 f01 f02 f03 f04 f05 f06 f07 f08 f09 f0A f0B f0C f0D f0E f0F f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f1A f1B f1C f1D f1E f1F f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f2A f2B f2C f2D f2E f2F f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f3A f3B f3C f3D f3E f3F  : TVMBit . 
Definition StakingContract_ι__returnConfirmation_А_fee_bs_def := [> f00 , f01 , f02 , f03 , f04 , f05 , f06 , f07 , f08 , f09 , f0A , f0B , f0C , f0D , f0E , f0F , f10 , f11 , f12 , f13 , f14 , f15 , f16 , f17 , f18 , f19 , f1A , f1B , f1C , f1D , f1E , f1F , f20 , f21 , f22 , f23 , f24 , f25 , f26 , f27 , f28 , f29 , f2A , f2B , f2C , f2D , f2E , f2F , f30 , f31 , f32 , f33 , f34 , f35 , f36 , f37 , f38 , f39 , f3A , f3B , f3C , f3D , f3E , f3F <] .
Lemma StakingContract_ι__returnConfirmation_А_fee_bs_id: StakingContract_ι__returnConfirmation_А_fee_bs_def = [> f00 , f01 , f02 , f03 , f04 , f05 , f06 , f07 , f08 , f09 , f0A , f0B , f0C , f0D , f0E , f0F , f10 , f11 , f12 , f13 , f14 , f15 , f16 , f17 , f18 , f19 , f1A , f1B , f1C , f1D , f1E , f1F , f20 , f21 , f22 , f23 , f24 , f25 , f26 , f27 , f28 , f29 , f2A , f2B , f2C , f2D , f2E , f2F , f30 , f31 , f32 , f33 , f34 , f35 , f36 , f37 , f38 , f39 , f3A , f3B , f3C , f3D , f3E , f3F <] .
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
Variables nsdSt00 nsdSt01 nsdSt02 nsdSt03 nsdSt04 nsdSt05 nsdSt06 nsdSt07 nsdSt08 nsdSt09 nsdSt0A nsdSt0B nsdSt0C nsdSt0D nsdSt0E nsdSt0F nsdSt10 nsdSt11 nsdSt12 nsdSt13 nsdSt14 nsdSt15 nsdSt16 nsdSt17 nsdSt18 nsdSt19 nsdSt1A nsdSt1B nsdSt1C nsdSt1D nsdSt1E nsdSt1F nsdSt20 nsdSt21 nsdSt22 nsdSt23 nsdSt24 nsdSt25 nsdSt26 nsdSt27 nsdSt28 nsdSt29 nsdSt2A nsdSt2B nsdSt2C nsdSt2D nsdSt2E nsdSt2F nsdSt30 nsdSt31 nsdSt32 nsdSt33 nsdSt34 nsdSt35 nsdSt36 nsdSt37 nsdSt38 nsdSt39 nsdSt3A nsdSt3B nsdSt3C nsdSt3D nsdSt3E nsdSt3F  : TVMBit . 
Definition StakingContract_ι__investStake_А_unusedStake_bs_def := [> nsdSt00 , nsdSt01 , nsdSt02 , nsdSt03 , nsdSt04 , nsdSt05 , nsdSt06 , nsdSt07 , nsdSt08 , nsdSt09 , nsdSt0A , nsdSt0B , nsdSt0C , nsdSt0D , nsdSt0E , nsdSt0F , nsdSt10 , nsdSt11 , nsdSt12 , nsdSt13 , nsdSt14 , nsdSt15 , nsdSt16 , nsdSt17 , nsdSt18 , nsdSt19 , nsdSt1A , nsdSt1B , nsdSt1C , nsdSt1D , nsdSt1E , nsdSt1F , nsdSt20 , nsdSt21 , nsdSt22 , nsdSt23 , nsdSt24 , nsdSt25 , nsdSt26 , nsdSt27 , nsdSt28 , nsdSt29 , nsdSt2A , nsdSt2B , nsdSt2C , nsdSt2D , nsdSt2E , nsdSt2F , nsdSt30 , nsdSt31 , nsdSt32 , nsdSt33 , nsdSt34 , nsdSt35 , nsdSt36 , nsdSt37 , nsdSt38 , nsdSt39 , nsdSt3A , nsdSt3B , nsdSt3C , nsdSt3D , nsdSt3E , nsdSt3F <] .
Lemma StakingContract_ι__investStake_А_unusedStake_bs_id: StakingContract_ι__investStake_А_unusedStake_bs_def = [> nsdSt00 , nsdSt01 , nsdSt02 , nsdSt03 , nsdSt04 , nsdSt05 , nsdSt06 , nsdSt07 , nsdSt08 , nsdSt09 , nsdSt0A , nsdSt0B , nsdSt0C , nsdSt0D , nsdSt0E , nsdSt0F , nsdSt10 , nsdSt11 , nsdSt12 , nsdSt13 , nsdSt14 , nsdSt15 , nsdSt16 , nsdSt17 , nsdSt18 , nsdSt19 , nsdSt1A , nsdSt1B , nsdSt1C , nsdSt1D , nsdSt1E , nsdSt1F , nsdSt20 , nsdSt21 , nsdSt22 , nsdSt23 , nsdSt24 , nsdSt25 , nsdSt26 , nsdSt27 , nsdSt28 , nsdSt29 , nsdSt2A , nsdSt2B , nsdSt2C , nsdSt2D , nsdSt2E , nsdSt2F , nsdSt30 , nsdSt31 , nsdSt32 , nsdSt33 , nsdSt34 , nsdSt35 , nsdSt36 , nsdSt37 , nsdSt38 , nsdSt39 , nsdSt3A , nsdSt3B , nsdSt3C , nsdSt3D , nsdSt3E , nsdSt3F <] .
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
Qed. Variables StakingContract_ι__investStake_А_newStake : Z . 
Variables nwStk00 nwStk01 nwStk02 nwStk03 nwStk04 nwStk05 nwStk06 nwStk07 nwStk08 nwStk09 nwStk0A nwStk0B nwStk0C nwStk0D nwStk0E nwStk0F nwStk10 nwStk11 nwStk12 nwStk13 nwStk14 nwStk15 nwStk16 nwStk17 nwStk18 nwStk19 nwStk1A nwStk1B nwStk1C nwStk1D nwStk1E nwStk1F nwStk20 nwStk21 nwStk22 nwStk23 nwStk24 nwStk25 nwStk26 nwStk27 nwStk28 nwStk29 nwStk2A nwStk2B nwStk2C nwStk2D nwStk2E nwStk2F nwStk30 nwStk31 nwStk32 nwStk33 nwStk34 nwStk35 nwStk36 nwStk37 nwStk38 nwStk39 nwStk3A nwStk3B nwStk3C nwStk3D nwStk3E nwStk3F  : TVMBit . 
Definition StakingContract_ι__investStake_А_newStake_bs_def := [> nwStk00 , nwStk01 , nwStk02 , nwStk03 , nwStk04 , nwStk05 , nwStk06 , nwStk07 , nwStk08 , nwStk09 , nwStk0A , nwStk0B , nwStk0C , nwStk0D , nwStk0E , nwStk0F , nwStk10 , nwStk11 , nwStk12 , nwStk13 , nwStk14 , nwStk15 , nwStk16 , nwStk17 , nwStk18 , nwStk19 , nwStk1A , nwStk1B , nwStk1C , nwStk1D , nwStk1E , nwStk1F , nwStk20 , nwStk21 , nwStk22 , nwStk23 , nwStk24 , nwStk25 , nwStk26 , nwStk27 , nwStk28 , nwStk29 , nwStk2A , nwStk2B , nwStk2C , nwStk2D , nwStk2E , nwStk2F , nwStk30 , nwStk31 , nwStk32 , nwStk33 , nwStk34 , nwStk35 , nwStk36 , nwStk37 , nwStk38 , nwStk39 , nwStk3A , nwStk3B , nwStk3C , nwStk3D , nwStk3E , nwStk3F <] .
Lemma StakingContract_ι__investStake_А_newStake_bs_id: StakingContract_ι__investStake_А_newStake_bs_def = [> nwStk00 , nwStk01 , nwStk02 , nwStk03 , nwStk04 , nwStk05 , nwStk06 , nwStk07 , nwStk08 , nwStk09 , nwStk0A , nwStk0B , nwStk0C , nwStk0D , nwStk0E , nwStk0F , nwStk10 , nwStk11 , nwStk12 , nwStk13 , nwStk14 , nwStk15 , nwStk16 , nwStk17 , nwStk18 , nwStk19 , nwStk1A , nwStk1B , nwStk1C , nwStk1D , nwStk1E , nwStk1F , nwStk20 , nwStk21 , nwStk22 , nwStk23 , nwStk24 , nwStk25 , nwStk26 , nwStk27 , nwStk28 , nwStk29 , nwStk2A , nwStk2B , nwStk2C , nwStk2D , nwStk2E , nwStk2F , nwStk30 , nwStk31 , nwStk32 , nwStk33 , nwStk34 , nwStk35 , nwStk36 , nwStk37 , nwStk38 , nwStk39 , nwStk3A , nwStk3B , nwStk3C , nwStk3D , nwStk3E , nwStk3F <] .
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
Variables stkt00 stkt01 stkt02 stkt03 stkt04 stkt05 stkt06 stkt07 stkt08 stkt09 stkt0A stkt0B stkt0C stkt0D stkt0E stkt0F stkt10 stkt11 stkt12 stkt13 stkt14 stkt15 stkt16 stkt17 stkt18 stkt19 stkt1A stkt1B stkt1C stkt1D stkt1E stkt1F  : TVMBit . 
Definition StakingContract_ι__addRequest_А_stakeAt_bs_def := [> stkt00 , stkt01 , stkt02 , stkt03 , stkt04 , stkt05 , stkt06 , stkt07 , stkt08 , stkt09 , stkt0A , stkt0B , stkt0C , stkt0D , stkt0E , stkt0F , stkt10 , stkt11 , stkt12 , stkt13 , stkt14 , stkt15 , stkt16 , stkt17 , stkt18 , stkt19 , stkt1A , stkt1B , stkt1C , stkt1D , stkt1E , stkt1F <] .
Lemma StakingContract_ι__addRequest_А_stakeAt_bs_id: StakingContract_ι__addRequest_А_stakeAt_bs_def = [> stkt00 , stkt01 , stkt02 , stkt03 , stkt04 , stkt05 , stkt06 , stkt07 , stkt08 , stkt09 , stkt0A , stkt0B , stkt0C , stkt0D , stkt0E , stkt0F , stkt10 , stkt11 , stkt12 , stkt13 , stkt14 , stkt15 , stkt16 , stkt17 , stkt18 , stkt19 , stkt1A , stkt1B , stkt1C , stkt1D , stkt1E , stkt1F <] .
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
Variables pndng00 pndng01 pndng02 pndng03 pndng04 pndng05 pndng06 pndng07 pndng08 pndng09 pndng0A pndng0B pndng0C pndng0D pndng0E pndng0F pndng10 pndng11 pndng12 pndng13 pndng14 pndng15 pndng16 pndng17 pndng18 pndng19 pndng1A pndng1B pndng1C pndng1D pndng1E pndng1F  : TVMBit . 
Definition StakingContract_ι__acceptPendingRoundStake_А_pendingId_bs_def := [> pndng00 , pndng01 , pndng02 , pndng03 , pndng04 , pndng05 , pndng06 , pndng07 , pndng08 , pndng09 , pndng0A , pndng0B , pndng0C , pndng0D , pndng0E , pndng0F , pndng10 , pndng11 , pndng12 , pndng13 , pndng14 , pndng15 , pndng16 , pndng17 , pndng18 , pndng19 , pndng1A , pndng1B , pndng1C , pndng1D , pndng1E , pndng1F <] .
Lemma StakingContract_ι__acceptPendingRoundStake_А_pendingId_bs_id: StakingContract_ι__acceptPendingRoundStake_А_pendingId_bs_def = [> pndng00 , pndng01 , pndng02 , pndng03 , pndng04 , pndng05 , pndng06 , pndng07 , pndng08 , pndng09 , pndng0A , pndng0B , pndng0C , pndng0D , pndng0E , pndng0F , pndng10 , pndng11 , pndng12 , pndng13 , pndng14 , pndng15 , pndng16 , pndng17 , pndng18 , pndng19 , pndng1A , pndng1B , pndng1C , pndng1D , pndng1E , pndng1F <] .
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
Variables cmplt00 cmplt01 cmplt02 cmplt03 cmplt04 cmplt05 cmplt06 cmplt07  : TVMBit . 
Definition StakingContract_ι__completeRound2_А_completionStatus_bs_def := [> cmplt00 , cmplt01 , cmplt02 , cmplt03 , cmplt04 , cmplt05 , cmplt06 , cmplt07 <] .
Lemma StakingContract_ι__completeRound2_А_completionStatus_bs_id: StakingContract_ι__completeRound2_А_completionStatus_bs_def = [> cmplt00 , cmplt01 , cmplt02 , cmplt03 , cmplt04 , cmplt05 , cmplt06 , cmplt07 <] .
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
Variables stk00 stk01 stk02 stk03 stk04 stk05 stk06 stk07 stk08 stk09 stk0A stk0B stk0C stk0D stk0E stk0F stk10 stk11 stk12 stk13 stk14 stk15 stk16 stk17 stk18 stk19 stk1A stk1B stk1C stk1D stk1E stk1F stk20 stk21 stk22 stk23 stk24 stk25 stk26 stk27 stk28 stk29 stk2A stk2B stk2C stk2D stk2E stk2F stk30 stk31 stk32 stk33 stk34 stk35 stk36 stk37 stk38 stk39 stk3A stk3B stk3C stk3D stk3E stk3F  : TVMBit . 
Definition StakingContract_ι__recalcStakeAndFees_А_stake_bs_def := [> stk00 , stk01 , stk02 , stk03 , stk04 , stk05 , stk06 , stk07 , stk08 , stk09 , stk0A , stk0B , stk0C , stk0D , stk0E , stk0F , stk10 , stk11 , stk12 , stk13 , stk14 , stk15 , stk16 , stk17 , stk18 , stk19 , stk1A , stk1B , stk1C , stk1D , stk1E , stk1F , stk20 , stk21 , stk22 , stk23 , stk24 , stk25 , stk26 , stk27 , stk28 , stk29 , stk2A , stk2B , stk2C , stk2D , stk2E , stk2F , stk30 , stk31 , stk32 , stk33 , stk34 , stk35 , stk36 , stk37 , stk38 , stk39 , stk3A , stk3B , stk3C , stk3D , stk3E , stk3F <] .
Lemma StakingContract_ι__recalcStakeAndFees_А_stake_bs_id: StakingContract_ι__recalcStakeAndFees_А_stake_bs_def = [> stk00 , stk01 , stk02 , stk03 , stk04 , stk05 , stk06 , stk07 , stk08 , stk09 , stk0A , stk0B , stk0C , stk0D , stk0E , stk0F , stk10 , stk11 , stk12 , stk13 , stk14 , stk15 , stk16 , stk17 , stk18 , stk19 , stk1A , stk1B , stk1C , stk1D , stk1E , stk1F , stk20 , stk21 , stk22 , stk23 , stk24 , stk25 , stk26 , stk27 , stk28 , stk29 , stk2A , stk2B , stk2C , stk2D , stk2E , stk2F , stk30 , stk31 , stk32 , stk33 , stk34 , stk35 , stk36 , stk37 , stk38 , stk39 , stk3A , stk3B , stk3C , stk3D , stk3E , stk3F <] .
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
Qed. Variables StakingContract_ι__recalcStakeAndFees_А_reward : Z . 
Variables rwrd00 rwrd01 rwrd02 rwrd03 rwrd04 rwrd05 rwrd06 rwrd07 rwrd08 rwrd09 rwrd0A rwrd0B rwrd0C rwrd0D rwrd0E rwrd0F rwrd10 rwrd11 rwrd12 rwrd13 rwrd14 rwrd15 rwrd16 rwrd17 rwrd18 rwrd19 rwrd1A rwrd1B rwrd1C rwrd1D rwrd1E rwrd1F rwrd20 rwrd21 rwrd22 rwrd23 rwrd24 rwrd25 rwrd26 rwrd27 rwrd28 rwrd29 rwrd2A rwrd2B rwrd2C rwrd2D rwrd2E rwrd2F rwrd30 rwrd31 rwrd32 rwrd33 rwrd34 rwrd35 rwrd36 rwrd37 rwrd38 rwrd39 rwrd3A rwrd3B rwrd3C rwrd3D rwrd3E rwrd3F  : TVMBit . 
Definition StakingContract_ι__recalcStakeAndFees_А_reward_bs_def := [> rwrd00 , rwrd01 , rwrd02 , rwrd03 , rwrd04 , rwrd05 , rwrd06 , rwrd07 , rwrd08 , rwrd09 , rwrd0A , rwrd0B , rwrd0C , rwrd0D , rwrd0E , rwrd0F , rwrd10 , rwrd11 , rwrd12 , rwrd13 , rwrd14 , rwrd15 , rwrd16 , rwrd17 , rwrd18 , rwrd19 , rwrd1A , rwrd1B , rwrd1C , rwrd1D , rwrd1E , rwrd1F , rwrd20 , rwrd21 , rwrd22 , rwrd23 , rwrd24 , rwrd25 , rwrd26 , rwrd27 , rwrd28 , rwrd29 , rwrd2A , rwrd2B , rwrd2C , rwrd2D , rwrd2E , rwrd2F , rwrd30 , rwrd31 , rwrd32 , rwrd33 , rwrd34 , rwrd35 , rwrd36 , rwrd37 , rwrd38 , rwrd39 , rwrd3A , rwrd3B , rwrd3C , rwrd3D , rwrd3E , rwrd3F <] .
Lemma StakingContract_ι__recalcStakeAndFees_А_reward_bs_id: StakingContract_ι__recalcStakeAndFees_А_reward_bs_def = [> rwrd00 , rwrd01 , rwrd02 , rwrd03 , rwrd04 , rwrd05 , rwrd06 , rwrd07 , rwrd08 , rwrd09 , rwrd0A , rwrd0B , rwrd0C , rwrd0D , rwrd0E , rwrd0F , rwrd10 , rwrd11 , rwrd12 , rwrd13 , rwrd14 , rwrd15 , rwrd16 , rwrd17 , rwrd18 , rwrd19 , rwrd1A , rwrd1B , rwrd1C , rwrd1D , rwrd1E , rwrd1F , rwrd20 , rwrd21 , rwrd22 , rwrd23 , rwrd24 , rwrd25 , rwrd26 , rwrd27 , rwrd28 , rwrd29 , rwrd2A , rwrd2B , rwrd2C , rwrd2D , rwrd2E , rwrd2F , rwrd30 , rwrd31 , rwrd32 , rwrd33 , rwrd34 , rwrd35 , rwrd36 , rwrd37 , rwrd38 , rwrd39 , rwrd3A , rwrd3B , rwrd3C , rwrd3D , rwrd3E , rwrd3F <] .
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
Qed. Variables StakingContract_ι__recalcStakeAndFees_А_roundStake : Z . 
Variables rndSt00 rndSt01 rndSt02 rndSt03 rndSt04 rndSt05 rndSt06 rndSt07 rndSt08 rndSt09 rndSt0A rndSt0B rndSt0C rndSt0D rndSt0E rndSt0F rndSt10 rndSt11 rndSt12 rndSt13 rndSt14 rndSt15 rndSt16 rndSt17 rndSt18 rndSt19 rndSt1A rndSt1B rndSt1C rndSt1D rndSt1E rndSt1F rndSt20 rndSt21 rndSt22 rndSt23 rndSt24 rndSt25 rndSt26 rndSt27 rndSt28 rndSt29 rndSt2A rndSt2B rndSt2C rndSt2D rndSt2E rndSt2F rndSt30 rndSt31 rndSt32 rndSt33 rndSt34 rndSt35 rndSt36 rndSt37 rndSt38 rndSt39 rndSt3A rndSt3B rndSt3C rndSt3D rndSt3E rndSt3F  : TVMBit . 
Definition StakingContract_ι__recalcStakeAndFees_А_roundStake_bs_def := [> rndSt00 , rndSt01 , rndSt02 , rndSt03 , rndSt04 , rndSt05 , rndSt06 , rndSt07 , rndSt08 , rndSt09 , rndSt0A , rndSt0B , rndSt0C , rndSt0D , rndSt0E , rndSt0F , rndSt10 , rndSt11 , rndSt12 , rndSt13 , rndSt14 , rndSt15 , rndSt16 , rndSt17 , rndSt18 , rndSt19 , rndSt1A , rndSt1B , rndSt1C , rndSt1D , rndSt1E , rndSt1F , rndSt20 , rndSt21 , rndSt22 , rndSt23 , rndSt24 , rndSt25 , rndSt26 , rndSt27 , rndSt28 , rndSt29 , rndSt2A , rndSt2B , rndSt2C , rndSt2D , rndSt2E , rndSt2F , rndSt30 , rndSt31 , rndSt32 , rndSt33 , rndSt34 , rndSt35 , rndSt36 , rndSt37 , rndSt38 , rndSt39 , rndSt3A , rndSt3B , rndSt3C , rndSt3D , rndSt3E , rndSt3F <] .
Lemma StakingContract_ι__recalcStakeAndFees_А_roundStake_bs_id: StakingContract_ι__recalcStakeAndFees_А_roundStake_bs_def = [> rndSt00 , rndSt01 , rndSt02 , rndSt03 , rndSt04 , rndSt05 , rndSt06 , rndSt07 , rndSt08 , rndSt09 , rndSt0A , rndSt0B , rndSt0C , rndSt0D , rndSt0E , rndSt0F , rndSt10 , rndSt11 , rndSt12 , rndSt13 , rndSt14 , rndSt15 , rndSt16 , rndSt17 , rndSt18 , rndSt19 , rndSt1A , rndSt1B , rndSt1C , rndSt1D , rndSt1E , rndSt1F , rndSt20 , rndSt21 , rndSt22 , rndSt23 , rndSt24 , rndSt25 , rndSt26 , rndSt27 , rndSt28 , rndSt29 , rndSt2A , rndSt2B , rndSt2C , rndSt2D , rndSt2E , rndSt2F , rndSt30 , rndSt31 , rndSt32 , rndSt33 , rndSt34 , rndSt35 , rndSt36 , rndSt37 , rndSt38 , rndSt39 , rndSt3A , rndSt3B , rndSt3C , rndSt3D , rndSt3E , rndSt3F <] .
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
Qed. Variables StakingContract_ι__recalcStakeAndFees_А_roundRewards : Z . 
Variables rndRw00 rndRw01 rndRw02 rndRw03 rndRw04 rndRw05 rndRw06 rndRw07 rndRw08 rndRw09 rndRw0A rndRw0B rndRw0C rndRw0D rndRw0E rndRw0F rndRw10 rndRw11 rndRw12 rndRw13 rndRw14 rndRw15 rndRw16 rndRw17 rndRw18 rndRw19 rndRw1A rndRw1B rndRw1C rndRw1D rndRw1E rndRw1F rndRw20 rndRw21 rndRw22 rndRw23 rndRw24 rndRw25 rndRw26 rndRw27 rndRw28 rndRw29 rndRw2A rndRw2B rndRw2C rndRw2D rndRw2E rndRw2F rndRw30 rndRw31 rndRw32 rndRw33 rndRw34 rndRw35 rndRw36 rndRw37 rndRw38 rndRw39 rndRw3A rndRw3B rndRw3C rndRw3D rndRw3E rndRw3F  : TVMBit . 
Definition StakingContract_ι__recalcStakeAndFees_А_roundRewards_bs_def := [> rndRw00 , rndRw01 , rndRw02 , rndRw03 , rndRw04 , rndRw05 , rndRw06 , rndRw07 , rndRw08 , rndRw09 , rndRw0A , rndRw0B , rndRw0C , rndRw0D , rndRw0E , rndRw0F , rndRw10 , rndRw11 , rndRw12 , rndRw13 , rndRw14 , rndRw15 , rndRw16 , rndRw17 , rndRw18 , rndRw19 , rndRw1A , rndRw1B , rndRw1C , rndRw1D , rndRw1E , rndRw1F , rndRw20 , rndRw21 , rndRw22 , rndRw23 , rndRw24 , rndRw25 , rndRw26 , rndRw27 , rndRw28 , rndRw29 , rndRw2A , rndRw2B , rndRw2C , rndRw2D , rndRw2E , rndRw2F , rndRw30 , rndRw31 , rndRw32 , rndRw33 , rndRw34 , rndRw35 , rndRw36 , rndRw37 , rndRw38 , rndRw39 , rndRw3A , rndRw3B , rndRw3C , rndRw3D , rndRw3E , rndRw3F <] .
Lemma StakingContract_ι__recalcStakeAndFees_А_roundRewards_bs_id: StakingContract_ι__recalcStakeAndFees_А_roundRewards_bs_def = [> rndRw00 , rndRw01 , rndRw02 , rndRw03 , rndRw04 , rndRw05 , rndRw06 , rndRw07 , rndRw08 , rndRw09 , rndRw0A , rndRw0B , rndRw0C , rndRw0D , rndRw0E , rndRw0F , rndRw10 , rndRw11 , rndRw12 , rndRw13 , rndRw14 , rndRw15 , rndRw16 , rndRw17 , rndRw18 , rndRw19 , rndRw1A , rndRw1B , rndRw1C , rndRw1D , rndRw1E , rndRw1F , rndRw20 , rndRw21 , rndRw22 , rndRw23 , rndRw24 , rndRw25 , rndRw26 , rndRw27 , rndRw28 , rndRw29 , rndRw2A , rndRw2B , rndRw2C , rndRw2D , rndRw2E , rndRw2F , rndRw30 , rndRw31 , rndRw32 , rndRw33 , rndRw34 , rndRw35 , rndRw36 , rndRw37 , rndRw38 , rndRw39 , rndRw3A , rndRw3B , rndRw3C , rndRw3D , rndRw3E , rndRw3F <] .
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
Variables stk00 stk01 stk02 stk03 stk04 stk05 stk06 stk07 stk08 stk09 stk0A stk0B stk0C stk0D stk0E stk0F stk10 stk11 stk12 stk13 stk14 stk15 stk16 stk17 stk18 stk19 stk1A stk1B stk1C stk1D stk1E stk1F stk20 stk21 stk22 stk23 stk24 stk25 stk26 stk27 stk28 stk29 stk2A stk2B stk2C stk2D stk2E stk2F stk30 stk31 stk32 stk33 stk34 stk35 stk36 stk37 stk38 stk39 stk3A stk3B stk3C stk3D stk3E stk3F  : TVMBit . 
Definition StakingContract_ι__returnOrReinvest2_А_stake_bs_def := [> stk00 , stk01 , stk02 , stk03 , stk04 , stk05 , stk06 , stk07 , stk08 , stk09 , stk0A , stk0B , stk0C , stk0D , stk0E , stk0F , stk10 , stk11 , stk12 , stk13 , stk14 , stk15 , stk16 , stk17 , stk18 , stk19 , stk1A , stk1B , stk1C , stk1D , stk1E , stk1F , stk20 , stk21 , stk22 , stk23 , stk24 , stk25 , stk26 , stk27 , stk28 , stk29 , stk2A , stk2B , stk2C , stk2D , stk2E , stk2F , stk30 , stk31 , stk32 , stk33 , stk34 , stk35 , stk36 , stk37 , stk38 , stk39 , stk3A , stk3B , stk3C , stk3D , stk3E , stk3F <] .
Lemma StakingContract_ι__returnOrReinvest2_А_stake_bs_id: StakingContract_ι__returnOrReinvest2_А_stake_bs_def = [> stk00 , stk01 , stk02 , stk03 , stk04 , stk05 , stk06 , stk07 , stk08 , stk09 , stk0A , stk0B , stk0C , stk0D , stk0E , stk0F , stk10 , stk11 , stk12 , stk13 , stk14 , stk15 , stk16 , stk17 , stk18 , stk19 , stk1A , stk1B , stk1C , stk1D , stk1E , stk1F , stk20 , stk21 , stk22 , stk23 , stk24 , stk25 , stk26 , stk27 , stk28 , stk29 , stk2A , stk2B , stk2C , stk2D , stk2E , stk2F , stk30 , stk31 , stk32 , stk33 , stk34 , stk35 , stk36 , stk37 , stk38 , stk39 , stk3A , stk3B , stk3C , stk3D , stk3E , stk3F <] .
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
Variables stk00 stk01 stk02 stk03 stk04 stk05 stk06 stk07 stk08 stk09 stk0A stk0B stk0C stk0D stk0E stk0F stk10 stk11 stk12 stk13 stk14 stk15 stk16 stk17 stk18 stk19 stk1A stk1B stk1C stk1D stk1E stk1F stk20 stk21 stk22 stk23 stk24 stk25 stk26 stk27 stk28 stk29 stk2A stk2B stk2C stk2D stk2E stk2F stk30 stk31 stk32 stk33 stk34 stk35 stk36 stk37 stk38 stk39 stk3A stk3B stk3C stk3D stk3E stk3F  : TVMBit . 
Definition StakingContract_ι_removeStake_А_stake_bs_def := [> stk00 , stk01 , stk02 , stk03 , stk04 , stk05 , stk06 , stk07 , stk08 , stk09 , stk0A , stk0B , stk0C , stk0D , stk0E , stk0F , stk10 , stk11 , stk12 , stk13 , stk14 , stk15 , stk16 , stk17 , stk18 , stk19 , stk1A , stk1B , stk1C , stk1D , stk1E , stk1F , stk20 , stk21 , stk22 , stk23 , stk24 , stk25 , stk26 , stk27 , stk28 , stk29 , stk2A , stk2B , stk2C , stk2D , stk2E , stk2F , stk30 , stk31 , stk32 , stk33 , stk34 , stk35 , stk36 , stk37 , stk38 , stk39 , stk3A , stk3B , stk3C , stk3D , stk3E , stk3F <] .
Lemma StakingContract_ι_removeStake_А_stake_bs_id: StakingContract_ι_removeStake_А_stake_bs_def = [> stk00 , stk01 , stk02 , stk03 , stk04 , stk05 , stk06 , stk07 , stk08 , stk09 , stk0A , stk0B , stk0C , stk0D , stk0E , stk0F , stk10 , stk11 , stk12 , stk13 , stk14 , stk15 , stk16 , stk17 , stk18 , stk19 , stk1A , stk1B , stk1C , stk1D , stk1E , stk1F , stk20 , stk21 , stk22 , stk23 , stk24 , stk25 , stk26 , stk27 , stk28 , stk29 , stk2A , stk2B , stk2C , stk2D , stk2E , stk2F , stk30 , stk31 , stk32 , stk33 , stk34 , stk35 , stk36 , stk37 , stk38 , stk39 , stk3A , stk3B , stk3C , stk3D , stk3E , stk3F <] .
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
Variables mnt00 mnt01 mnt02 mnt03 mnt04 mnt05 mnt06 mnt07 mnt08 mnt09 mnt0A mnt0B mnt0C mnt0D mnt0E mnt0F mnt10 mnt11 mnt12 mnt13 mnt14 mnt15 mnt16 mnt17 mnt18 mnt19 mnt1A mnt1B mnt1C mnt1D mnt1E mnt1F mnt20 mnt21 mnt22 mnt23 mnt24 mnt25 mnt26 mnt27 mnt28 mnt29 mnt2A mnt2B mnt2C mnt2D mnt2E mnt2F mnt30 mnt31 mnt32 mnt33 mnt34 mnt35 mnt36 mnt37 mnt38 mnt39 mnt3A mnt3B mnt3C mnt3D mnt3E mnt3F  : TVMBit . 
Definition StakingContract_ι_continueStake_А_amount_bs_def := [> mnt00 , mnt01 , mnt02 , mnt03 , mnt04 , mnt05 , mnt06 , mnt07 , mnt08 , mnt09 , mnt0A , mnt0B , mnt0C , mnt0D , mnt0E , mnt0F , mnt10 , mnt11 , mnt12 , mnt13 , mnt14 , mnt15 , mnt16 , mnt17 , mnt18 , mnt19 , mnt1A , mnt1B , mnt1C , mnt1D , mnt1E , mnt1F , mnt20 , mnt21 , mnt22 , mnt23 , mnt24 , mnt25 , mnt26 , mnt27 , mnt28 , mnt29 , mnt2A , mnt2B , mnt2C , mnt2D , mnt2E , mnt2F , mnt30 , mnt31 , mnt32 , mnt33 , mnt34 , mnt35 , mnt36 , mnt37 , mnt38 , mnt39 , mnt3A , mnt3B , mnt3C , mnt3D , mnt3E , mnt3F <] .
Lemma StakingContract_ι_continueStake_А_amount_bs_id: StakingContract_ι_continueStake_А_amount_bs_def = [> mnt00 , mnt01 , mnt02 , mnt03 , mnt04 , mnt05 , mnt06 , mnt07 , mnt08 , mnt09 , mnt0A , mnt0B , mnt0C , mnt0D , mnt0E , mnt0F , mnt10 , mnt11 , mnt12 , mnt13 , mnt14 , mnt15 , mnt16 , mnt17 , mnt18 , mnt19 , mnt1A , mnt1B , mnt1C , mnt1D , mnt1E , mnt1F , mnt20 , mnt21 , mnt22 , mnt23 , mnt24 , mnt25 , mnt26 , mnt27 , mnt28 , mnt29 , mnt2A , mnt2B , mnt2C , mnt2D , mnt2E , mnt2F , mnt30 , mnt31 , mnt32 , mnt33 , mnt34 , mnt35 , mnt36 , mnt37 , mnt38 , mnt39 , mnt3A , mnt3B , mnt3C , mnt3D , mnt3E , mnt3F <] .
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
Variables qrd00 qrd01 qrd02 qrd03 qrd04 qrd05 qrd06 qrd07 qrd08 qrd09 qrd0A qrd0B qrd0C qrd0D qrd0E qrd0F qrd10 qrd11 qrd12 qrd13 qrd14 qrd15 qrd16 qrd17 qrd18 qrd19 qrd1A qrd1B qrd1C qrd1D qrd1E qrd1F qrd20 qrd21 qrd22 qrd23 qrd24 qrd25 qrd26 qrd27 qrd28 qrd29 qrd2A qrd2B qrd2C qrd2D qrd2E qrd2F qrd30 qrd31 qrd32 qrd33 qrd34 qrd35 qrd36 qrd37 qrd38 qrd39 qrd3A qrd3B qrd3C qrd3D qrd3E qrd3F  : TVMBit . 
Definition StakingContract_ι_processNewStake_А_queryId_bs_def := [> qrd00 , qrd01 , qrd02 , qrd03 , qrd04 , qrd05 , qrd06 , qrd07 , qrd08 , qrd09 , qrd0A , qrd0B , qrd0C , qrd0D , qrd0E , qrd0F , qrd10 , qrd11 , qrd12 , qrd13 , qrd14 , qrd15 , qrd16 , qrd17 , qrd18 , qrd19 , qrd1A , qrd1B , qrd1C , qrd1D , qrd1E , qrd1F , qrd20 , qrd21 , qrd22 , qrd23 , qrd24 , qrd25 , qrd26 , qrd27 , qrd28 , qrd29 , qrd2A , qrd2B , qrd2C , qrd2D , qrd2E , qrd2F , qrd30 , qrd31 , qrd32 , qrd33 , qrd34 , qrd35 , qrd36 , qrd37 , qrd38 , qrd39 , qrd3A , qrd3B , qrd3C , qrd3D , qrd3E , qrd3F <] .
Lemma StakingContract_ι_processNewStake_А_queryId_bs_id: StakingContract_ι_processNewStake_А_queryId_bs_def = [> qrd00 , qrd01 , qrd02 , qrd03 , qrd04 , qrd05 , qrd06 , qrd07 , qrd08 , qrd09 , qrd0A , qrd0B , qrd0C , qrd0D , qrd0E , qrd0F , qrd10 , qrd11 , qrd12 , qrd13 , qrd14 , qrd15 , qrd16 , qrd17 , qrd18 , qrd19 , qrd1A , qrd1B , qrd1C , qrd1D , qrd1E , qrd1F , qrd20 , qrd21 , qrd22 , qrd23 , qrd24 , qrd25 , qrd26 , qrd27 , qrd28 , qrd29 , qrd2A , qrd2B , qrd2C , qrd2D , qrd2E , qrd2F , qrd30 , qrd31 , qrd32 , qrd33 , qrd34 , qrd35 , qrd36 , qrd37 , qrd38 , qrd39 , qrd3A , qrd3B , qrd3C , qrd3D , qrd3E , qrd3F <] .
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
Qed. Variables StakingContract_ι_processNewStake_А_validatorKey : Z . 
Variables vldtr00 vldtr01 vldtr02 vldtr03 vldtr04 vldtr05 vldtr06 vldtr07 vldtr08 vldtr09 vldtr0A vldtr0B vldtr0C vldtr0D vldtr0E vldtr0F vldtr10 vldtr11 vldtr12 vldtr13 vldtr14 vldtr15 vldtr16 vldtr17 vldtr18 vldtr19 vldtr1A vldtr1B vldtr1C vldtr1D vldtr1E vldtr1F vldtr20 vldtr21 vldtr22 vldtr23 vldtr24 vldtr25 vldtr26 vldtr27 vldtr28 vldtr29 vldtr2A vldtr2B vldtr2C vldtr2D vldtr2E vldtr2F vldtr30 vldtr31 vldtr32 vldtr33 vldtr34 vldtr35 vldtr36 vldtr37 vldtr38 vldtr39 vldtr3A vldtr3B vldtr3C vldtr3D vldtr3E vldtr3F vldtr40 vldtr41 vldtr42 vldtr43 vldtr44 vldtr45 vldtr46 vldtr47 vldtr48 vldtr49 vldtr4A vldtr4B vldtr4C vldtr4D vldtr4E vldtr4F vldtr50 vldtr51 vldtr52 vldtr53 vldtr54 vldtr55 vldtr56 vldtr57 vldtr58 vldtr59 vldtr5A vldtr5B vldtr5C vldtr5D vldtr5E vldtr5F vldtr60 vldtr61 vldtr62 vldtr63 vldtr64 vldtr65 vldtr66 vldtr67 vldtr68 vldtr69 vldtr6A vldtr6B vldtr6C vldtr6D vldtr6E vldtr6F vldtr70 vldtr71 vldtr72 vldtr73 vldtr74 vldtr75 vldtr76 vldtr77 vldtr78 vldtr79 vldtr7A vldtr7B vldtr7C vldtr7D vldtr7E vldtr7F vldtr80 vldtr81 vldtr82 vldtr83 vldtr84 vldtr85 vldtr86 vldtr87 vldtr88 vldtr89 vldtr8A vldtr8B vldtr8C vldtr8D vldtr8E vldtr8F vldtr90 vldtr91 vldtr92 vldtr93 vldtr94 vldtr95 vldtr96 vldtr97 vldtr98 vldtr99 vldtr9A vldtr9B vldtr9C vldtr9D vldtr9E vldtr9F vldtrA0 vldtrA1 vldtrA2 vldtrA3 vldtrA4 vldtrA5 vldtrA6 vldtrA7 vldtrA8 vldtrA9 vldtrAA vldtrAB vldtrAC vldtrAD vldtrAE vldtrAF vldtrB0 vldtrB1 vldtrB2 vldtrB3 vldtrB4 vldtrB5 vldtrB6 vldtrB7 vldtrB8 vldtrB9 vldtrBA vldtrBB vldtrBC vldtrBD vldtrBE vldtrBF vldtrC0 vldtrC1 vldtrC2 vldtrC3 vldtrC4 vldtrC5 vldtrC6 vldtrC7 vldtrC8 vldtrC9 vldtrCA vldtrCB vldtrCC vldtrCD vldtrCE vldtrCF vldtrD0 vldtrD1 vldtrD2 vldtrD3 vldtrD4 vldtrD5 vldtrD6 vldtrD7 vldtrD8 vldtrD9 vldtrDA vldtrDB vldtrDC vldtrDD vldtrDE vldtrDF vldtrE0 vldtrE1 vldtrE2 vldtrE3 vldtrE4 vldtrE5 vldtrE6 vldtrE7 vldtrE8 vldtrE9 vldtrEA vldtrEB vldtrEC vldtrED vldtrEE vldtrEF vldtrF0 vldtrF1 vldtrF2 vldtrF3 vldtrF4 vldtrF5 vldtrF6 vldtrF7 vldtrF8 vldtrF9 vldtrFA vldtrFB vldtrFC vldtrFD vldtrFE vldtrFF  : TVMBit . 
Definition StakingContract_ι_processNewStake_А_validatorKey_bs_def := [> vldtr00 , vldtr01 , vldtr02 , vldtr03 , vldtr04 , vldtr05 , vldtr06 , vldtr07 , vldtr08 , vldtr09 , vldtr0A , vldtr0B , vldtr0C , vldtr0D , vldtr0E , vldtr0F , vldtr10 , vldtr11 , vldtr12 , vldtr13 , vldtr14 , vldtr15 , vldtr16 , vldtr17 , vldtr18 , vldtr19 , vldtr1A , vldtr1B , vldtr1C , vldtr1D , vldtr1E , vldtr1F , vldtr20 , vldtr21 , vldtr22 , vldtr23 , vldtr24 , vldtr25 , vldtr26 , vldtr27 , vldtr28 , vldtr29 , vldtr2A , vldtr2B , vldtr2C , vldtr2D , vldtr2E , vldtr2F , vldtr30 , vldtr31 , vldtr32 , vldtr33 , vldtr34 , vldtr35 , vldtr36 , vldtr37 , vldtr38 , vldtr39 , vldtr3A , vldtr3B , vldtr3C , vldtr3D , vldtr3E , vldtr3F , vldtr40 , vldtr41 , vldtr42 , vldtr43 , vldtr44 , vldtr45 , vldtr46 , vldtr47 , vldtr48 , vldtr49 , vldtr4A , vldtr4B , vldtr4C , vldtr4D , vldtr4E , vldtr4F , vldtr50 , vldtr51 , vldtr52 , vldtr53 , vldtr54 , vldtr55 , vldtr56 , vldtr57 , vldtr58 , vldtr59 , vldtr5A , vldtr5B , vldtr5C , vldtr5D , vldtr5E , vldtr5F , vldtr60 , vldtr61 , vldtr62 , vldtr63 , vldtr64 , vldtr65 , vldtr66 , vldtr67 , vldtr68 , vldtr69 , vldtr6A , vldtr6B , vldtr6C , vldtr6D , vldtr6E , vldtr6F , vldtr70 , vldtr71 , vldtr72 , vldtr73 , vldtr74 , vldtr75 , vldtr76 , vldtr77 , vldtr78 , vldtr79 , vldtr7A , vldtr7B , vldtr7C , vldtr7D , vldtr7E , vldtr7F , vldtr80 , vldtr81 , vldtr82 , vldtr83 , vldtr84 , vldtr85 , vldtr86 , vldtr87 , vldtr88 , vldtr89 , vldtr8A , vldtr8B , vldtr8C , vldtr8D , vldtr8E , vldtr8F , vldtr90 , vldtr91 , vldtr92 , vldtr93 , vldtr94 , vldtr95 , vldtr96 , vldtr97 , vldtr98 , vldtr99 , vldtr9A , vldtr9B , vldtr9C , vldtr9D , vldtr9E , vldtr9F , vldtrA0 , vldtrA1 , vldtrA2 , vldtrA3 , vldtrA4 , vldtrA5 , vldtrA6 , vldtrA7 , vldtrA8 , vldtrA9 , vldtrAA , vldtrAB , vldtrAC , vldtrAD , vldtrAE , vldtrAF , vldtrB0 , vldtrB1 , vldtrB2 , vldtrB3 , vldtrB4 , vldtrB5 , vldtrB6 , vldtrB7 , vldtrB8 , vldtrB9 , vldtrBA , vldtrBB , vldtrBC , vldtrBD , vldtrBE , vldtrBF , vldtrC0 , vldtrC1 , vldtrC2 , vldtrC3 , vldtrC4 , vldtrC5 , vldtrC6 , vldtrC7 , vldtrC8 , vldtrC9 , vldtrCA , vldtrCB , vldtrCC , vldtrCD , vldtrCE , vldtrCF , vldtrD0 , vldtrD1 , vldtrD2 , vldtrD3 , vldtrD4 , vldtrD5 , vldtrD6 , vldtrD7 , vldtrD8 , vldtrD9 , vldtrDA , vldtrDB , vldtrDC , vldtrDD , vldtrDE , vldtrDF , vldtrE0 , vldtrE1 , vldtrE2 , vldtrE3 , vldtrE4 , vldtrE5 , vldtrE6 , vldtrE7 , vldtrE8 , vldtrE9 , vldtrEA , vldtrEB , vldtrEC , vldtrED , vldtrEE , vldtrEF , vldtrF0 , vldtrF1 , vldtrF2 , vldtrF3 , vldtrF4 , vldtrF5 , vldtrF6 , vldtrF7 , vldtrF8 , vldtrF9 , vldtrFA , vldtrFB , vldtrFC , vldtrFD , vldtrFE , vldtrFF <] .
Lemma StakingContract_ι_processNewStake_А_validatorKey_bs_id: StakingContract_ι_processNewStake_А_validatorKey_bs_def = [> vldtr00 , vldtr01 , vldtr02 , vldtr03 , vldtr04 , vldtr05 , vldtr06 , vldtr07 , vldtr08 , vldtr09 , vldtr0A , vldtr0B , vldtr0C , vldtr0D , vldtr0E , vldtr0F , vldtr10 , vldtr11 , vldtr12 , vldtr13 , vldtr14 , vldtr15 , vldtr16 , vldtr17 , vldtr18 , vldtr19 , vldtr1A , vldtr1B , vldtr1C , vldtr1D , vldtr1E , vldtr1F , vldtr20 , vldtr21 , vldtr22 , vldtr23 , vldtr24 , vldtr25 , vldtr26 , vldtr27 , vldtr28 , vldtr29 , vldtr2A , vldtr2B , vldtr2C , vldtr2D , vldtr2E , vldtr2F , vldtr30 , vldtr31 , vldtr32 , vldtr33 , vldtr34 , vldtr35 , vldtr36 , vldtr37 , vldtr38 , vldtr39 , vldtr3A , vldtr3B , vldtr3C , vldtr3D , vldtr3E , vldtr3F , vldtr40 , vldtr41 , vldtr42 , vldtr43 , vldtr44 , vldtr45 , vldtr46 , vldtr47 , vldtr48 , vldtr49 , vldtr4A , vldtr4B , vldtr4C , vldtr4D , vldtr4E , vldtr4F , vldtr50 , vldtr51 , vldtr52 , vldtr53 , vldtr54 , vldtr55 , vldtr56 , vldtr57 , vldtr58 , vldtr59 , vldtr5A , vldtr5B , vldtr5C , vldtr5D , vldtr5E , vldtr5F , vldtr60 , vldtr61 , vldtr62 , vldtr63 , vldtr64 , vldtr65 , vldtr66 , vldtr67 , vldtr68 , vldtr69 , vldtr6A , vldtr6B , vldtr6C , vldtr6D , vldtr6E , vldtr6F , vldtr70 , vldtr71 , vldtr72 , vldtr73 , vldtr74 , vldtr75 , vldtr76 , vldtr77 , vldtr78 , vldtr79 , vldtr7A , vldtr7B , vldtr7C , vldtr7D , vldtr7E , vldtr7F , vldtr80 , vldtr81 , vldtr82 , vldtr83 , vldtr84 , vldtr85 , vldtr86 , vldtr87 , vldtr88 , vldtr89 , vldtr8A , vldtr8B , vldtr8C , vldtr8D , vldtr8E , vldtr8F , vldtr90 , vldtr91 , vldtr92 , vldtr93 , vldtr94 , vldtr95 , vldtr96 , vldtr97 , vldtr98 , vldtr99 , vldtr9A , vldtr9B , vldtr9C , vldtr9D , vldtr9E , vldtr9F , vldtrA0 , vldtrA1 , vldtrA2 , vldtrA3 , vldtrA4 , vldtrA5 , vldtrA6 , vldtrA7 , vldtrA8 , vldtrA9 , vldtrAA , vldtrAB , vldtrAC , vldtrAD , vldtrAE , vldtrAF , vldtrB0 , vldtrB1 , vldtrB2 , vldtrB3 , vldtrB4 , vldtrB5 , vldtrB6 , vldtrB7 , vldtrB8 , vldtrB9 , vldtrBA , vldtrBB , vldtrBC , vldtrBD , vldtrBE , vldtrBF , vldtrC0 , vldtrC1 , vldtrC2 , vldtrC3 , vldtrC4 , vldtrC5 , vldtrC6 , vldtrC7 , vldtrC8 , vldtrC9 , vldtrCA , vldtrCB , vldtrCC , vldtrCD , vldtrCE , vldtrCF , vldtrD0 , vldtrD1 , vldtrD2 , vldtrD3 , vldtrD4 , vldtrD5 , vldtrD6 , vldtrD7 , vldtrD8 , vldtrD9 , vldtrDA , vldtrDB , vldtrDC , vldtrDD , vldtrDE , vldtrDF , vldtrE0 , vldtrE1 , vldtrE2 , vldtrE3 , vldtrE4 , vldtrE5 , vldtrE6 , vldtrE7 , vldtrE8 , vldtrE9 , vldtrEA , vldtrEB , vldtrEC , vldtrED , vldtrEE , vldtrEF , vldtrF0 , vldtrF1 , vldtrF2 , vldtrF3 , vldtrF4 , vldtrF5 , vldtrF6 , vldtrF7 , vldtrF8 , vldtrF9 , vldtrFA , vldtrFB , vldtrFC , vldtrFD , vldtrFE , vldtrFF <] .
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
Qed. Variables StakingContract_ι_processNewStake_А_stakeAt : Z . 
Variables stkt00 stkt01 stkt02 stkt03 stkt04 stkt05 stkt06 stkt07 stkt08 stkt09 stkt0A stkt0B stkt0C stkt0D stkt0E stkt0F stkt10 stkt11 stkt12 stkt13 stkt14 stkt15 stkt16 stkt17 stkt18 stkt19 stkt1A stkt1B stkt1C stkt1D stkt1E stkt1F  : TVMBit . 
Definition StakingContract_ι_processNewStake_А_stakeAt_bs_def := [> stkt00 , stkt01 , stkt02 , stkt03 , stkt04 , stkt05 , stkt06 , stkt07 , stkt08 , stkt09 , stkt0A , stkt0B , stkt0C , stkt0D , stkt0E , stkt0F , stkt10 , stkt11 , stkt12 , stkt13 , stkt14 , stkt15 , stkt16 , stkt17 , stkt18 , stkt19 , stkt1A , stkt1B , stkt1C , stkt1D , stkt1E , stkt1F <] .
Lemma StakingContract_ι_processNewStake_А_stakeAt_bs_id: StakingContract_ι_processNewStake_А_stakeAt_bs_def = [> stkt00 , stkt01 , stkt02 , stkt03 , stkt04 , stkt05 , stkt06 , stkt07 , stkt08 , stkt09 , stkt0A , stkt0B , stkt0C , stkt0D , stkt0E , stkt0F , stkt10 , stkt11 , stkt12 , stkt13 , stkt14 , stkt15 , stkt16 , stkt17 , stkt18 , stkt19 , stkt1A , stkt1B , stkt1C , stkt1D , stkt1E , stkt1F <] .
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
Qed. Variables StakingContract_ι_processNewStake_А_maxFactor : Z . 
Variables mxFct00 mxFct01 mxFct02 mxFct03 mxFct04 mxFct05 mxFct06 mxFct07 mxFct08 mxFct09 mxFct0A mxFct0B mxFct0C mxFct0D mxFct0E mxFct0F mxFct10 mxFct11 mxFct12 mxFct13 mxFct14 mxFct15 mxFct16 mxFct17 mxFct18 mxFct19 mxFct1A mxFct1B mxFct1C mxFct1D mxFct1E mxFct1F  : TVMBit . 
Definition StakingContract_ι_processNewStake_А_maxFactor_bs_def := [> mxFct00 , mxFct01 , mxFct02 , mxFct03 , mxFct04 , mxFct05 , mxFct06 , mxFct07 , mxFct08 , mxFct09 , mxFct0A , mxFct0B , mxFct0C , mxFct0D , mxFct0E , mxFct0F , mxFct10 , mxFct11 , mxFct12 , mxFct13 , mxFct14 , mxFct15 , mxFct16 , mxFct17 , mxFct18 , mxFct19 , mxFct1A , mxFct1B , mxFct1C , mxFct1D , mxFct1E , mxFct1F <] .
Lemma StakingContract_ι_processNewStake_А_maxFactor_bs_id: StakingContract_ι_processNewStake_А_maxFactor_bs_def = [> mxFct00 , mxFct01 , mxFct02 , mxFct03 , mxFct04 , mxFct05 , mxFct06 , mxFct07 , mxFct08 , mxFct09 , mxFct0A , mxFct0B , mxFct0C , mxFct0D , mxFct0E , mxFct0F , mxFct10 , mxFct11 , mxFct12 , mxFct13 , mxFct14 , mxFct15 , mxFct16 , mxFct17 , mxFct18 , mxFct19 , mxFct1A , mxFct1B , mxFct1C , mxFct1D , mxFct1E , mxFct1F <] .
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
Qed. Variables StakingContract_ι_processNewStake_А_adnlAddr : Z . 
Variables dnldd00 dnldd01 dnldd02 dnldd03 dnldd04 dnldd05 dnldd06 dnldd07 dnldd08 dnldd09 dnldd0A dnldd0B dnldd0C dnldd0D dnldd0E dnldd0F dnldd10 dnldd11 dnldd12 dnldd13 dnldd14 dnldd15 dnldd16 dnldd17 dnldd18 dnldd19 dnldd1A dnldd1B dnldd1C dnldd1D dnldd1E dnldd1F dnldd20 dnldd21 dnldd22 dnldd23 dnldd24 dnldd25 dnldd26 dnldd27 dnldd28 dnldd29 dnldd2A dnldd2B dnldd2C dnldd2D dnldd2E dnldd2F dnldd30 dnldd31 dnldd32 dnldd33 dnldd34 dnldd35 dnldd36 dnldd37 dnldd38 dnldd39 dnldd3A dnldd3B dnldd3C dnldd3D dnldd3E dnldd3F dnldd40 dnldd41 dnldd42 dnldd43 dnldd44 dnldd45 dnldd46 dnldd47 dnldd48 dnldd49 dnldd4A dnldd4B dnldd4C dnldd4D dnldd4E dnldd4F dnldd50 dnldd51 dnldd52 dnldd53 dnldd54 dnldd55 dnldd56 dnldd57 dnldd58 dnldd59 dnldd5A dnldd5B dnldd5C dnldd5D dnldd5E dnldd5F dnldd60 dnldd61 dnldd62 dnldd63 dnldd64 dnldd65 dnldd66 dnldd67 dnldd68 dnldd69 dnldd6A dnldd6B dnldd6C dnldd6D dnldd6E dnldd6F dnldd70 dnldd71 dnldd72 dnldd73 dnldd74 dnldd75 dnldd76 dnldd77 dnldd78 dnldd79 dnldd7A dnldd7B dnldd7C dnldd7D dnldd7E dnldd7F dnldd80 dnldd81 dnldd82 dnldd83 dnldd84 dnldd85 dnldd86 dnldd87 dnldd88 dnldd89 dnldd8A dnldd8B dnldd8C dnldd8D dnldd8E dnldd8F dnldd90 dnldd91 dnldd92 dnldd93 dnldd94 dnldd95 dnldd96 dnldd97 dnldd98 dnldd99 dnldd9A dnldd9B dnldd9C dnldd9D dnldd9E dnldd9F dnlddA0 dnlddA1 dnlddA2 dnlddA3 dnlddA4 dnlddA5 dnlddA6 dnlddA7 dnlddA8 dnlddA9 dnlddAA dnlddAB dnlddAC dnlddAD dnlddAE dnlddAF dnlddB0 dnlddB1 dnlddB2 dnlddB3 dnlddB4 dnlddB5 dnlddB6 dnlddB7 dnlddB8 dnlddB9 dnlddBA dnlddBB dnlddBC dnlddBD dnlddBE dnlddBF dnlddC0 dnlddC1 dnlddC2 dnlddC3 dnlddC4 dnlddC5 dnlddC6 dnlddC7 dnlddC8 dnlddC9 dnlddCA dnlddCB dnlddCC dnlddCD dnlddCE dnlddCF dnlddD0 dnlddD1 dnlddD2 dnlddD3 dnlddD4 dnlddD5 dnlddD6 dnlddD7 dnlddD8 dnlddD9 dnlddDA dnlddDB dnlddDC dnlddDD dnlddDE dnlddDF dnlddE0 dnlddE1 dnlddE2 dnlddE3 dnlddE4 dnlddE5 dnlddE6 dnlddE7 dnlddE8 dnlddE9 dnlddEA dnlddEB dnlddEC dnlddED dnlddEE dnlddEF dnlddF0 dnlddF1 dnlddF2 dnlddF3 dnlddF4 dnlddF5 dnlddF6 dnlddF7 dnlddF8 dnlddF9 dnlddFA dnlddFB dnlddFC dnlddFD dnlddFE dnlddFF  : TVMBit . 
Definition StakingContract_ι_processNewStake_А_adnlAddr_bs_def := [> dnldd00 , dnldd01 , dnldd02 , dnldd03 , dnldd04 , dnldd05 , dnldd06 , dnldd07 , dnldd08 , dnldd09 , dnldd0A , dnldd0B , dnldd0C , dnldd0D , dnldd0E , dnldd0F , dnldd10 , dnldd11 , dnldd12 , dnldd13 , dnldd14 , dnldd15 , dnldd16 , dnldd17 , dnldd18 , dnldd19 , dnldd1A , dnldd1B , dnldd1C , dnldd1D , dnldd1E , dnldd1F , dnldd20 , dnldd21 , dnldd22 , dnldd23 , dnldd24 , dnldd25 , dnldd26 , dnldd27 , dnldd28 , dnldd29 , dnldd2A , dnldd2B , dnldd2C , dnldd2D , dnldd2E , dnldd2F , dnldd30 , dnldd31 , dnldd32 , dnldd33 , dnldd34 , dnldd35 , dnldd36 , dnldd37 , dnldd38 , dnldd39 , dnldd3A , dnldd3B , dnldd3C , dnldd3D , dnldd3E , dnldd3F , dnldd40 , dnldd41 , dnldd42 , dnldd43 , dnldd44 , dnldd45 , dnldd46 , dnldd47 , dnldd48 , dnldd49 , dnldd4A , dnldd4B , dnldd4C , dnldd4D , dnldd4E , dnldd4F , dnldd50 , dnldd51 , dnldd52 , dnldd53 , dnldd54 , dnldd55 , dnldd56 , dnldd57 , dnldd58 , dnldd59 , dnldd5A , dnldd5B , dnldd5C , dnldd5D , dnldd5E , dnldd5F , dnldd60 , dnldd61 , dnldd62 , dnldd63 , dnldd64 , dnldd65 , dnldd66 , dnldd67 , dnldd68 , dnldd69 , dnldd6A , dnldd6B , dnldd6C , dnldd6D , dnldd6E , dnldd6F , dnldd70 , dnldd71 , dnldd72 , dnldd73 , dnldd74 , dnldd75 , dnldd76 , dnldd77 , dnldd78 , dnldd79 , dnldd7A , dnldd7B , dnldd7C , dnldd7D , dnldd7E , dnldd7F , dnldd80 , dnldd81 , dnldd82 , dnldd83 , dnldd84 , dnldd85 , dnldd86 , dnldd87 , dnldd88 , dnldd89 , dnldd8A , dnldd8B , dnldd8C , dnldd8D , dnldd8E , dnldd8F , dnldd90 , dnldd91 , dnldd92 , dnldd93 , dnldd94 , dnldd95 , dnldd96 , dnldd97 , dnldd98 , dnldd99 , dnldd9A , dnldd9B , dnldd9C , dnldd9D , dnldd9E , dnldd9F , dnlddA0 , dnlddA1 , dnlddA2 , dnlddA3 , dnlddA4 , dnlddA5 , dnlddA6 , dnlddA7 , dnlddA8 , dnlddA9 , dnlddAA , dnlddAB , dnlddAC , dnlddAD , dnlddAE , dnlddAF , dnlddB0 , dnlddB1 , dnlddB2 , dnlddB3 , dnlddB4 , dnlddB5 , dnlddB6 , dnlddB7 , dnlddB8 , dnlddB9 , dnlddBA , dnlddBB , dnlddBC , dnlddBD , dnlddBE , dnlddBF , dnlddC0 , dnlddC1 , dnlddC2 , dnlddC3 , dnlddC4 , dnlddC5 , dnlddC6 , dnlddC7 , dnlddC8 , dnlddC9 , dnlddCA , dnlddCB , dnlddCC , dnlddCD , dnlddCE , dnlddCF , dnlddD0 , dnlddD1 , dnlddD2 , dnlddD3 , dnlddD4 , dnlddD5 , dnlddD6 , dnlddD7 , dnlddD8 , dnlddD9 , dnlddDA , dnlddDB , dnlddDC , dnlddDD , dnlddDE , dnlddDF , dnlddE0 , dnlddE1 , dnlddE2 , dnlddE3 , dnlddE4 , dnlddE5 , dnlddE6 , dnlddE7 , dnlddE8 , dnlddE9 , dnlddEA , dnlddEB , dnlddEC , dnlddED , dnlddEE , dnlddEF , dnlddF0 , dnlddF1 , dnlddF2 , dnlddF3 , dnlddF4 , dnlddF5 , dnlddF6 , dnlddF7 , dnlddF8 , dnlddF9 , dnlddFA , dnlddFB , dnlddFC , dnlddFD , dnlddFE , dnlddFF <] .
Lemma StakingContract_ι_processNewStake_А_adnlAddr_bs_id: StakingContract_ι_processNewStake_А_adnlAddr_bs_def = [> dnldd00 , dnldd01 , dnldd02 , dnldd03 , dnldd04 , dnldd05 , dnldd06 , dnldd07 , dnldd08 , dnldd09 , dnldd0A , dnldd0B , dnldd0C , dnldd0D , dnldd0E , dnldd0F , dnldd10 , dnldd11 , dnldd12 , dnldd13 , dnldd14 , dnldd15 , dnldd16 , dnldd17 , dnldd18 , dnldd19 , dnldd1A , dnldd1B , dnldd1C , dnldd1D , dnldd1E , dnldd1F , dnldd20 , dnldd21 , dnldd22 , dnldd23 , dnldd24 , dnldd25 , dnldd26 , dnldd27 , dnldd28 , dnldd29 , dnldd2A , dnldd2B , dnldd2C , dnldd2D , dnldd2E , dnldd2F , dnldd30 , dnldd31 , dnldd32 , dnldd33 , dnldd34 , dnldd35 , dnldd36 , dnldd37 , dnldd38 , dnldd39 , dnldd3A , dnldd3B , dnldd3C , dnldd3D , dnldd3E , dnldd3F , dnldd40 , dnldd41 , dnldd42 , dnldd43 , dnldd44 , dnldd45 , dnldd46 , dnldd47 , dnldd48 , dnldd49 , dnldd4A , dnldd4B , dnldd4C , dnldd4D , dnldd4E , dnldd4F , dnldd50 , dnldd51 , dnldd52 , dnldd53 , dnldd54 , dnldd55 , dnldd56 , dnldd57 , dnldd58 , dnldd59 , dnldd5A , dnldd5B , dnldd5C , dnldd5D , dnldd5E , dnldd5F , dnldd60 , dnldd61 , dnldd62 , dnldd63 , dnldd64 , dnldd65 , dnldd66 , dnldd67 , dnldd68 , dnldd69 , dnldd6A , dnldd6B , dnldd6C , dnldd6D , dnldd6E , dnldd6F , dnldd70 , dnldd71 , dnldd72 , dnldd73 , dnldd74 , dnldd75 , dnldd76 , dnldd77 , dnldd78 , dnldd79 , dnldd7A , dnldd7B , dnldd7C , dnldd7D , dnldd7E , dnldd7F , dnldd80 , dnldd81 , dnldd82 , dnldd83 , dnldd84 , dnldd85 , dnldd86 , dnldd87 , dnldd88 , dnldd89 , dnldd8A , dnldd8B , dnldd8C , dnldd8D , dnldd8E , dnldd8F , dnldd90 , dnldd91 , dnldd92 , dnldd93 , dnldd94 , dnldd95 , dnldd96 , dnldd97 , dnldd98 , dnldd99 , dnldd9A , dnldd9B , dnldd9C , dnldd9D , dnldd9E , dnldd9F , dnlddA0 , dnlddA1 , dnlddA2 , dnlddA3 , dnlddA4 , dnlddA5 , dnlddA6 , dnlddA7 , dnlddA8 , dnlddA9 , dnlddAA , dnlddAB , dnlddAC , dnlddAD , dnlddAE , dnlddAF , dnlddB0 , dnlddB1 , dnlddB2 , dnlddB3 , dnlddB4 , dnlddB5 , dnlddB6 , dnlddB7 , dnlddB8 , dnlddB9 , dnlddBA , dnlddBB , dnlddBC , dnlddBD , dnlddBE , dnlddBF , dnlddC0 , dnlddC1 , dnlddC2 , dnlddC3 , dnlddC4 , dnlddC5 , dnlddC6 , dnlddC7 , dnlddC8 , dnlddC9 , dnlddCA , dnlddCB , dnlddCC , dnlddCD , dnlddCE , dnlddCF , dnlddD0 , dnlddD1 , dnlddD2 , dnlddD3 , dnlddD4 , dnlddD5 , dnlddD6 , dnlddD7 , dnlddD8 , dnlddD9 , dnlddDA , dnlddDB , dnlddDC , dnlddDD , dnlddDE , dnlddDF , dnlddE0 , dnlddE1 , dnlddE2 , dnlddE3 , dnlddE4 , dnlddE5 , dnlddE6 , dnlddE7 , dnlddE8 , dnlddE9 , dnlddEA , dnlddEB , dnlddEC , dnlddED , dnlddEE , dnlddEF , dnlddF0 , dnlddF1 , dnlddF2 , dnlddF3 , dnlddF4 , dnlddF5 , dnlddF6 , dnlddF7 , dnlddF8 , dnlddF9 , dnlddFA , dnlddFB , dnlddFC , dnlddFD , dnlddFE , dnlddFF <] .
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
Qed. Variables StakingContract_ι_processNewStake_А_signature : Z . 
Variables sgntr00 sgntr01 sgntr02 sgntr03 sgntr04 sgntr05 sgntr06 sgntr07  : TVMBit . 
Definition StakingContract_ι_processNewStake_А_signature_bs_def := [> sgntr00 , sgntr01 , sgntr02 , sgntr03 , sgntr04 , sgntr05 , sgntr06 , sgntr07 <] .
Lemma StakingContract_ι_processNewStake_А_signature_bs_id: StakingContract_ι_processNewStake_А_signature_bs_def = [> sgntr00 , sgntr01 , sgntr02 , sgntr03 , sgntr04 , sgntr05 , sgntr06 , sgntr07 <] .
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
Variables rndd00 rndd01 rndd02 rndd03 rndd04 rndd05 rndd06 rndd07 rndd08 rndd09 rndd0A rndd0B rndd0C rndd0D rndd0E rndd0F rndd10 rndd11 rndd12 rndd13 rndd14 rndd15 rndd16 rndd17 rndd18 rndd19 rndd1A rndd1B rndd1C rndd1D rndd1E rndd1F  : TVMBit . 
Definition StakingContract_ι_completePendingRound_А_roundId_bs_def := [> rndd00 , rndd01 , rndd02 , rndd03 , rndd04 , rndd05 , rndd06 , rndd07 , rndd08 , rndd09 , rndd0A , rndd0B , rndd0C , rndd0D , rndd0E , rndd0F , rndd10 , rndd11 , rndd12 , rndd13 , rndd14 , rndd15 , rndd16 , rndd17 , rndd18 , rndd19 , rndd1A , rndd1B , rndd1C , rndd1D , rndd1E , rndd1F <] .
Lemma StakingContract_ι_completePendingRound_А_roundId_bs_id: StakingContract_ι_completePendingRound_А_roundId_bs_def = [> rndd00 , rndd01 , rndd02 , rndd03 , rndd04 , rndd05 , rndd06 , rndd07 , rndd08 , rndd09 , rndd0A , rndd0B , rndd0C , rndd0D , rndd0E , rndd0F , rndd10 , rndd11 , rndd12 , rndd13 , rndd14 , rndd15 , rndd16 , rndd17 , rndd18 , rndd19 , rndd1A , rndd1B , rndd1C , rndd1D , rndd1E , rndd1F <] .
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
Variables qrd00 qrd01 qrd02 qrd03 qrd04 qrd05 qrd06 qrd07 qrd08 qrd09 qrd0A qrd0B qrd0C qrd0D qrd0E qrd0F qrd10 qrd11 qrd12 qrd13 qrd14 qrd15 qrd16 qrd17 qrd18 qrd19 qrd1A qrd1B qrd1C qrd1D qrd1E qrd1F qrd20 qrd21 qrd22 qrd23 qrd24 qrd25 qrd26 qrd27 qrd28 qrd29 qrd2A qrd2B qrd2C qrd2D qrd2E qrd2F qrd30 qrd31 qrd32 qrd33 qrd34 qrd35 qrd36 qrd37 qrd38 qrd39 qrd3A qrd3B qrd3C qrd3D qrd3E qrd3F  : TVMBit . 
Definition StakingContract_ι_receiveConfirmation_А_queryId_bs_def := [> qrd00 , qrd01 , qrd02 , qrd03 , qrd04 , qrd05 , qrd06 , qrd07 , qrd08 , qrd09 , qrd0A , qrd0B , qrd0C , qrd0D , qrd0E , qrd0F , qrd10 , qrd11 , qrd12 , qrd13 , qrd14 , qrd15 , qrd16 , qrd17 , qrd18 , qrd19 , qrd1A , qrd1B , qrd1C , qrd1D , qrd1E , qrd1F , qrd20 , qrd21 , qrd22 , qrd23 , qrd24 , qrd25 , qrd26 , qrd27 , qrd28 , qrd29 , qrd2A , qrd2B , qrd2C , qrd2D , qrd2E , qrd2F , qrd30 , qrd31 , qrd32 , qrd33 , qrd34 , qrd35 , qrd36 , qrd37 , qrd38 , qrd39 , qrd3A , qrd3B , qrd3C , qrd3D , qrd3E , qrd3F <] .
Lemma StakingContract_ι_receiveConfirmation_А_queryId_bs_id: StakingContract_ι_receiveConfirmation_А_queryId_bs_def = [> qrd00 , qrd01 , qrd02 , qrd03 , qrd04 , qrd05 , qrd06 , qrd07 , qrd08 , qrd09 , qrd0A , qrd0B , qrd0C , qrd0D , qrd0E , qrd0F , qrd10 , qrd11 , qrd12 , qrd13 , qrd14 , qrd15 , qrd16 , qrd17 , qrd18 , qrd19 , qrd1A , qrd1B , qrd1C , qrd1D , qrd1E , qrd1F , qrd20 , qrd21 , qrd22 , qrd23 , qrd24 , qrd25 , qrd26 , qrd27 , qrd28 , qrd29 , qrd2A , qrd2B , qrd2C , qrd2D , qrd2E , qrd2F , qrd30 , qrd31 , qrd32 , qrd33 , qrd34 , qrd35 , qrd36 , qrd37 , qrd38 , qrd39 , qrd3A , qrd3B , qrd3C , qrd3D , qrd3E , qrd3F <] .
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
Qed. Variables StakingContract_ι_receiveConfirmation_А_comment : Z . 
Variables cmmnt00 cmmnt01 cmmnt02 cmmnt03 cmmnt04 cmmnt05 cmmnt06 cmmnt07 cmmnt08 cmmnt09 cmmnt0A cmmnt0B cmmnt0C cmmnt0D cmmnt0E cmmnt0F cmmnt10 cmmnt11 cmmnt12 cmmnt13 cmmnt14 cmmnt15 cmmnt16 cmmnt17 cmmnt18 cmmnt19 cmmnt1A cmmnt1B cmmnt1C cmmnt1D cmmnt1E cmmnt1F  : TVMBit . 
Definition StakingContract_ι_receiveConfirmation_А_comment_bs_def := [> cmmnt00 , cmmnt01 , cmmnt02 , cmmnt03 , cmmnt04 , cmmnt05 , cmmnt06 , cmmnt07 , cmmnt08 , cmmnt09 , cmmnt0A , cmmnt0B , cmmnt0C , cmmnt0D , cmmnt0E , cmmnt0F , cmmnt10 , cmmnt11 , cmmnt12 , cmmnt13 , cmmnt14 , cmmnt15 , cmmnt16 , cmmnt17 , cmmnt18 , cmmnt19 , cmmnt1A , cmmnt1B , cmmnt1C , cmmnt1D , cmmnt1E , cmmnt1F <] .
Lemma StakingContract_ι_receiveConfirmation_А_comment_bs_id: StakingContract_ι_receiveConfirmation_А_comment_bs_def = [> cmmnt00 , cmmnt01 , cmmnt02 , cmmnt03 , cmmnt04 , cmmnt05 , cmmnt06 , cmmnt07 , cmmnt08 , cmmnt09 , cmmnt0A , cmmnt0B , cmmnt0C , cmmnt0D , cmmnt0E , cmmnt0F , cmmnt10 , cmmnt11 , cmmnt12 , cmmnt13 , cmmnt14 , cmmnt15 , cmmnt16 , cmmnt17 , cmmnt18 , cmmnt19 , cmmnt1A , cmmnt1B , cmmnt1C , cmmnt1D , cmmnt1E , cmmnt1F <] .
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
Variables qrd00 qrd01 qrd02 qrd03 qrd04 qrd05 qrd06 qrd07 qrd08 qrd09 qrd0A qrd0B qrd0C qrd0D qrd0E qrd0F qrd10 qrd11 qrd12 qrd13 qrd14 qrd15 qrd16 qrd17 qrd18 qrd19 qrd1A qrd1B qrd1C qrd1D qrd1E qrd1F qrd20 qrd21 qrd22 qrd23 qrd24 qrd25 qrd26 qrd27 qrd28 qrd29 qrd2A qrd2B qrd2C qrd2D qrd2E qrd2F qrd30 qrd31 qrd32 qrd33 qrd34 qrd35 qrd36 qrd37 qrd38 qrd39 qrd3A qrd3B qrd3C qrd3D qrd3E qrd3F  : TVMBit . 
Definition StakingContract_ι_receiveReturnedStake_А_queryId_bs_def := [> qrd00 , qrd01 , qrd02 , qrd03 , qrd04 , qrd05 , qrd06 , qrd07 , qrd08 , qrd09 , qrd0A , qrd0B , qrd0C , qrd0D , qrd0E , qrd0F , qrd10 , qrd11 , qrd12 , qrd13 , qrd14 , qrd15 , qrd16 , qrd17 , qrd18 , qrd19 , qrd1A , qrd1B , qrd1C , qrd1D , qrd1E , qrd1F , qrd20 , qrd21 , qrd22 , qrd23 , qrd24 , qrd25 , qrd26 , qrd27 , qrd28 , qrd29 , qrd2A , qrd2B , qrd2C , qrd2D , qrd2E , qrd2F , qrd30 , qrd31 , qrd32 , qrd33 , qrd34 , qrd35 , qrd36 , qrd37 , qrd38 , qrd39 , qrd3A , qrd3B , qrd3C , qrd3D , qrd3E , qrd3F <] .
Lemma StakingContract_ι_receiveReturnedStake_А_queryId_bs_id: StakingContract_ι_receiveReturnedStake_А_queryId_bs_def = [> qrd00 , qrd01 , qrd02 , qrd03 , qrd04 , qrd05 , qrd06 , qrd07 , qrd08 , qrd09 , qrd0A , qrd0B , qrd0C , qrd0D , qrd0E , qrd0F , qrd10 , qrd11 , qrd12 , qrd13 , qrd14 , qrd15 , qrd16 , qrd17 , qrd18 , qrd19 , qrd1A , qrd1B , qrd1C , qrd1D , qrd1E , qrd1F , qrd20 , qrd21 , qrd22 , qrd23 , qrd24 , qrd25 , qrd26 , qrd27 , qrd28 , qrd29 , qrd2A , qrd2B , qrd2C , qrd2D , qrd2E , qrd2F , qrd30 , qrd31 , qrd32 , qrd33 , qrd34 , qrd35 , qrd36 , qrd37 , qrd38 , qrd39 , qrd3A , qrd3B , qrd3C , qrd3D , qrd3E , qrd3F <] .
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
Qed. Variables StakingContract_ι_receiveReturnedStake_А_comment : Z . 
Variables cmmnt00 cmmnt01 cmmnt02 cmmnt03 cmmnt04 cmmnt05 cmmnt06 cmmnt07 cmmnt08 cmmnt09 cmmnt0A cmmnt0B cmmnt0C cmmnt0D cmmnt0E cmmnt0F cmmnt10 cmmnt11 cmmnt12 cmmnt13 cmmnt14 cmmnt15 cmmnt16 cmmnt17 cmmnt18 cmmnt19 cmmnt1A cmmnt1B cmmnt1C cmmnt1D cmmnt1E cmmnt1F  : TVMBit . 
Definition StakingContract_ι_receiveReturnedStake_А_comment_bs_def := [> cmmnt00 , cmmnt01 , cmmnt02 , cmmnt03 , cmmnt04 , cmmnt05 , cmmnt06 , cmmnt07 , cmmnt08 , cmmnt09 , cmmnt0A , cmmnt0B , cmmnt0C , cmmnt0D , cmmnt0E , cmmnt0F , cmmnt10 , cmmnt11 , cmmnt12 , cmmnt13 , cmmnt14 , cmmnt15 , cmmnt16 , cmmnt17 , cmmnt18 , cmmnt19 , cmmnt1A , cmmnt1B , cmmnt1C , cmmnt1D , cmmnt1E , cmmnt1F <] .
Lemma StakingContract_ι_receiveReturnedStake_А_comment_bs_id: StakingContract_ι_receiveReturnedStake_А_comment_bs_def = [> cmmnt00 , cmmnt01 , cmmnt02 , cmmnt03 , cmmnt04 , cmmnt05 , cmmnt06 , cmmnt07 , cmmnt08 , cmmnt09 , cmmnt0A , cmmnt0B , cmmnt0C , cmmnt0D , cmmnt0E , cmmnt0F , cmmnt10 , cmmnt11 , cmmnt12 , cmmnt13 , cmmnt14 , cmmnt15 , cmmnt16 , cmmnt17 , cmmnt18 , cmmnt19 , cmmnt1A , cmmnt1B , cmmnt1C , cmmnt1D , cmmnt1E , cmmnt1F <] .
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
Variables qrd00 qrd01 qrd02 qrd03 qrd04 qrd05 qrd06 qrd07 qrd08 qrd09 qrd0A qrd0B qrd0C qrd0D qrd0E qrd0F qrd10 qrd11 qrd12 qrd13 qrd14 qrd15 qrd16 qrd17 qrd18 qrd19 qrd1A qrd1B qrd1C qrd1D qrd1E qrd1F qrd20 qrd21 qrd22 qrd23 qrd24 qrd25 qrd26 qrd27 qrd28 qrd29 qrd2A qrd2B qrd2C qrd2D qrd2E qrd2F qrd30 qrd31 qrd32 qrd33 qrd34 qrd35 qrd36 qrd37 qrd38 qrd39 qrd3A qrd3B qrd3C qrd3D qrd3E qrd3F  : TVMBit . 
Definition StakingContract_ι_acceptRecoveredStake_А_queryId_bs_def := [> qrd00 , qrd01 , qrd02 , qrd03 , qrd04 , qrd05 , qrd06 , qrd07 , qrd08 , qrd09 , qrd0A , qrd0B , qrd0C , qrd0D , qrd0E , qrd0F , qrd10 , qrd11 , qrd12 , qrd13 , qrd14 , qrd15 , qrd16 , qrd17 , qrd18 , qrd19 , qrd1A , qrd1B , qrd1C , qrd1D , qrd1E , qrd1F , qrd20 , qrd21 , qrd22 , qrd23 , qrd24 , qrd25 , qrd26 , qrd27 , qrd28 , qrd29 , qrd2A , qrd2B , qrd2C , qrd2D , qrd2E , qrd2F , qrd30 , qrd31 , qrd32 , qrd33 , qrd34 , qrd35 , qrd36 , qrd37 , qrd38 , qrd39 , qrd3A , qrd3B , qrd3C , qrd3D , qrd3E , qrd3F <] .
Lemma StakingContract_ι_acceptRecoveredStake_А_queryId_bs_id: StakingContract_ι_acceptRecoveredStake_А_queryId_bs_def = [> qrd00 , qrd01 , qrd02 , qrd03 , qrd04 , qrd05 , qrd06 , qrd07 , qrd08 , qrd09 , qrd0A , qrd0B , qrd0C , qrd0D , qrd0E , qrd0F , qrd10 , qrd11 , qrd12 , qrd13 , qrd14 , qrd15 , qrd16 , qrd17 , qrd18 , qrd19 , qrd1A , qrd1B , qrd1C , qrd1D , qrd1E , qrd1F , qrd20 , qrd21 , qrd22 , qrd23 , qrd24 , qrd25 , qrd26 , qrd27 , qrd28 , qrd29 , qrd2A , qrd2B , qrd2C , qrd2D , qrd2E , qrd2F , qrd30 , qrd31 , qrd32 , qrd33 , qrd34 , qrd35 , qrd36 , qrd37 , qrd38 , qrd39 , qrd3A , qrd3B , qrd3C , qrd3D , qrd3E , qrd3F <] .
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
Variables rwrd00 rwrd01 rwrd02 rwrd03 rwrd04 rwrd05 rwrd06 rwrd07 rwrd08 rwrd09 rwrd0A rwrd0B rwrd0C rwrd0D rwrd0E rwrd0F rwrd10 rwrd11 rwrd12 rwrd13 rwrd14 rwrd15 rwrd16 rwrd17 rwrd18 rwrd19 rwrd1A rwrd1B rwrd1C rwrd1D rwrd1E rwrd1F rwrd20 rwrd21 rwrd22 rwrd23 rwrd24 rwrd25 rwrd26 rwrd27 rwrd28 rwrd29 rwrd2A rwrd2B rwrd2C rwrd2D rwrd2E rwrd2F rwrd30 rwrd31 rwrd32 rwrd33 rwrd34 rwrd35 rwrd36 rwrd37 rwrd38 rwrd39 rwrd3A rwrd3B rwrd3C rwrd3D rwrd3E rwrd3F  : TVMBit . 
Definition OwnerBase_ι_Owner_ι_reward_bs_def := [> rwrd00 , rwrd01 , rwrd02 , rwrd03 , rwrd04 , rwrd05 , rwrd06 , rwrd07 , rwrd08 , rwrd09 , rwrd0A , rwrd0B , rwrd0C , rwrd0D , rwrd0E , rwrd0F , rwrd10 , rwrd11 , rwrd12 , rwrd13 , rwrd14 , rwrd15 , rwrd16 , rwrd17 , rwrd18 , rwrd19 , rwrd1A , rwrd1B , rwrd1C , rwrd1D , rwrd1E , rwrd1F , rwrd20 , rwrd21 , rwrd22 , rwrd23 , rwrd24 , rwrd25 , rwrd26 , rwrd27 , rwrd28 , rwrd29 , rwrd2A , rwrd2B , rwrd2C , rwrd2D , rwrd2E , rwrd2F , rwrd30 , rwrd31 , rwrd32 , rwrd33 , rwrd34 , rwrd35 , rwrd36 , rwrd37 , rwrd38 , rwrd39 , rwrd3A , rwrd3B , rwrd3C , rwrd3D , rwrd3E , rwrd3F <] .
Lemma OwnerBase_ι_Owner_ι_reward_bs_id: OwnerBase_ι_Owner_ι_reward_bs_def = [> rwrd00 , rwrd01 , rwrd02 , rwrd03 , rwrd04 , rwrd05 , rwrd06 , rwrd07 , rwrd08 , rwrd09 , rwrd0A , rwrd0B , rwrd0C , rwrd0D , rwrd0E , rwrd0F , rwrd10 , rwrd11 , rwrd12 , rwrd13 , rwrd14 , rwrd15 , rwrd16 , rwrd17 , rwrd18 , rwrd19 , rwrd1A , rwrd1B , rwrd1C , rwrd1D , rwrd1E , rwrd1F , rwrd20 , rwrd21 , rwrd22 , rwrd23 , rwrd24 , rwrd25 , rwrd26 , rwrd27 , rwrd28 , rwrd29 , rwrd2A , rwrd2B , rwrd2C , rwrd2D , rwrd2E , rwrd2F , rwrd30 , rwrd31 , rwrd32 , rwrd33 , rwrd34 , rwrd35 , rwrd36 , rwrd37 , rwrd38 , rwrd39 , rwrd3A , rwrd3B , rwrd3C , rwrd3D , rwrd3E , rwrd3F <] .
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
Variables qrd00 qrd01 qrd02 qrd03 qrd04 qrd05 qrd06 qrd07 qrd08 qrd09 qrd0A qrd0B qrd0C qrd0D qrd0E qrd0F qrd10 qrd11 qrd12 qrd13 qrd14 qrd15 qrd16 qrd17 qrd18 qrd19 qrd1A qrd1B qrd1C qrd1D qrd1E qrd1F qrd20 qrd21 qrd22 qrd23 qrd24 qrd25 qrd26 qrd27 qrd28 qrd29 qrd2A qrd2B qrd2C qrd2D qrd2E qrd2F qrd30 qrd31 qrd32 qrd33 qrd34 qrd35 qrd36 qrd37 qrd38 qrd39 qrd3A qrd3B qrd3C qrd3D qrd3E qrd3F  : TVMBit . 
Definition ElectorBase_ι_Request_ι_queryId_bs_def := [> qrd00 , qrd01 , qrd02 , qrd03 , qrd04 , qrd05 , qrd06 , qrd07 , qrd08 , qrd09 , qrd0A , qrd0B , qrd0C , qrd0D , qrd0E , qrd0F , qrd10 , qrd11 , qrd12 , qrd13 , qrd14 , qrd15 , qrd16 , qrd17 , qrd18 , qrd19 , qrd1A , qrd1B , qrd1C , qrd1D , qrd1E , qrd1F , qrd20 , qrd21 , qrd22 , qrd23 , qrd24 , qrd25 , qrd26 , qrd27 , qrd28 , qrd29 , qrd2A , qrd2B , qrd2C , qrd2D , qrd2E , qrd2F , qrd30 , qrd31 , qrd32 , qrd33 , qrd34 , qrd35 , qrd36 , qrd37 , qrd38 , qrd39 , qrd3A , qrd3B , qrd3C , qrd3D , qrd3E , qrd3F <] .
Lemma ElectorBase_ι_Request_ι_queryId_bs_id: ElectorBase_ι_Request_ι_queryId_bs_def = [> qrd00 , qrd01 , qrd02 , qrd03 , qrd04 , qrd05 , qrd06 , qrd07 , qrd08 , qrd09 , qrd0A , qrd0B , qrd0C , qrd0D , qrd0E , qrd0F , qrd10 , qrd11 , qrd12 , qrd13 , qrd14 , qrd15 , qrd16 , qrd17 , qrd18 , qrd19 , qrd1A , qrd1B , qrd1C , qrd1D , qrd1E , qrd1F , qrd20 , qrd21 , qrd22 , qrd23 , qrd24 , qrd25 , qrd26 , qrd27 , qrd28 , qrd29 , qrd2A , qrd2B , qrd2C , qrd2D , qrd2E , qrd2F , qrd30 , qrd31 , qrd32 , qrd33 , qrd34 , qrd35 , qrd36 , qrd37 , qrd38 , qrd39 , qrd3A , qrd3B , qrd3C , qrd3D , qrd3E , qrd3F <] .
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
Qed. Variables ElectorBase_ι_Request_ι_validatorKey : Z . 
Variables vldtr00 vldtr01 vldtr02 vldtr03 vldtr04 vldtr05 vldtr06 vldtr07 vldtr08 vldtr09 vldtr0A vldtr0B vldtr0C vldtr0D vldtr0E vldtr0F vldtr10 vldtr11 vldtr12 vldtr13 vldtr14 vldtr15 vldtr16 vldtr17 vldtr18 vldtr19 vldtr1A vldtr1B vldtr1C vldtr1D vldtr1E vldtr1F vldtr20 vldtr21 vldtr22 vldtr23 vldtr24 vldtr25 vldtr26 vldtr27 vldtr28 vldtr29 vldtr2A vldtr2B vldtr2C vldtr2D vldtr2E vldtr2F vldtr30 vldtr31 vldtr32 vldtr33 vldtr34 vldtr35 vldtr36 vldtr37 vldtr38 vldtr39 vldtr3A vldtr3B vldtr3C vldtr3D vldtr3E vldtr3F vldtr40 vldtr41 vldtr42 vldtr43 vldtr44 vldtr45 vldtr46 vldtr47 vldtr48 vldtr49 vldtr4A vldtr4B vldtr4C vldtr4D vldtr4E vldtr4F vldtr50 vldtr51 vldtr52 vldtr53 vldtr54 vldtr55 vldtr56 vldtr57 vldtr58 vldtr59 vldtr5A vldtr5B vldtr5C vldtr5D vldtr5E vldtr5F vldtr60 vldtr61 vldtr62 vldtr63 vldtr64 vldtr65 vldtr66 vldtr67 vldtr68 vldtr69 vldtr6A vldtr6B vldtr6C vldtr6D vldtr6E vldtr6F vldtr70 vldtr71 vldtr72 vldtr73 vldtr74 vldtr75 vldtr76 vldtr77 vldtr78 vldtr79 vldtr7A vldtr7B vldtr7C vldtr7D vldtr7E vldtr7F vldtr80 vldtr81 vldtr82 vldtr83 vldtr84 vldtr85 vldtr86 vldtr87 vldtr88 vldtr89 vldtr8A vldtr8B vldtr8C vldtr8D vldtr8E vldtr8F vldtr90 vldtr91 vldtr92 vldtr93 vldtr94 vldtr95 vldtr96 vldtr97 vldtr98 vldtr99 vldtr9A vldtr9B vldtr9C vldtr9D vldtr9E vldtr9F vldtrA0 vldtrA1 vldtrA2 vldtrA3 vldtrA4 vldtrA5 vldtrA6 vldtrA7 vldtrA8 vldtrA9 vldtrAA vldtrAB vldtrAC vldtrAD vldtrAE vldtrAF vldtrB0 vldtrB1 vldtrB2 vldtrB3 vldtrB4 vldtrB5 vldtrB6 vldtrB7 vldtrB8 vldtrB9 vldtrBA vldtrBB vldtrBC vldtrBD vldtrBE vldtrBF vldtrC0 vldtrC1 vldtrC2 vldtrC3 vldtrC4 vldtrC5 vldtrC6 vldtrC7 vldtrC8 vldtrC9 vldtrCA vldtrCB vldtrCC vldtrCD vldtrCE vldtrCF vldtrD0 vldtrD1 vldtrD2 vldtrD3 vldtrD4 vldtrD5 vldtrD6 vldtrD7 vldtrD8 vldtrD9 vldtrDA vldtrDB vldtrDC vldtrDD vldtrDE vldtrDF vldtrE0 vldtrE1 vldtrE2 vldtrE3 vldtrE4 vldtrE5 vldtrE6 vldtrE7 vldtrE8 vldtrE9 vldtrEA vldtrEB vldtrEC vldtrED vldtrEE vldtrEF vldtrF0 vldtrF1 vldtrF2 vldtrF3 vldtrF4 vldtrF5 vldtrF6 vldtrF7 vldtrF8 vldtrF9 vldtrFA vldtrFB vldtrFC vldtrFD vldtrFE vldtrFF  : TVMBit . 
Definition ElectorBase_ι_Request_ι_validatorKey_bs_def := [> vldtr00 , vldtr01 , vldtr02 , vldtr03 , vldtr04 , vldtr05 , vldtr06 , vldtr07 , vldtr08 , vldtr09 , vldtr0A , vldtr0B , vldtr0C , vldtr0D , vldtr0E , vldtr0F , vldtr10 , vldtr11 , vldtr12 , vldtr13 , vldtr14 , vldtr15 , vldtr16 , vldtr17 , vldtr18 , vldtr19 , vldtr1A , vldtr1B , vldtr1C , vldtr1D , vldtr1E , vldtr1F , vldtr20 , vldtr21 , vldtr22 , vldtr23 , vldtr24 , vldtr25 , vldtr26 , vldtr27 , vldtr28 , vldtr29 , vldtr2A , vldtr2B , vldtr2C , vldtr2D , vldtr2E , vldtr2F , vldtr30 , vldtr31 , vldtr32 , vldtr33 , vldtr34 , vldtr35 , vldtr36 , vldtr37 , vldtr38 , vldtr39 , vldtr3A , vldtr3B , vldtr3C , vldtr3D , vldtr3E , vldtr3F , vldtr40 , vldtr41 , vldtr42 , vldtr43 , vldtr44 , vldtr45 , vldtr46 , vldtr47 , vldtr48 , vldtr49 , vldtr4A , vldtr4B , vldtr4C , vldtr4D , vldtr4E , vldtr4F , vldtr50 , vldtr51 , vldtr52 , vldtr53 , vldtr54 , vldtr55 , vldtr56 , vldtr57 , vldtr58 , vldtr59 , vldtr5A , vldtr5B , vldtr5C , vldtr5D , vldtr5E , vldtr5F , vldtr60 , vldtr61 , vldtr62 , vldtr63 , vldtr64 , vldtr65 , vldtr66 , vldtr67 , vldtr68 , vldtr69 , vldtr6A , vldtr6B , vldtr6C , vldtr6D , vldtr6E , vldtr6F , vldtr70 , vldtr71 , vldtr72 , vldtr73 , vldtr74 , vldtr75 , vldtr76 , vldtr77 , vldtr78 , vldtr79 , vldtr7A , vldtr7B , vldtr7C , vldtr7D , vldtr7E , vldtr7F , vldtr80 , vldtr81 , vldtr82 , vldtr83 , vldtr84 , vldtr85 , vldtr86 , vldtr87 , vldtr88 , vldtr89 , vldtr8A , vldtr8B , vldtr8C , vldtr8D , vldtr8E , vldtr8F , vldtr90 , vldtr91 , vldtr92 , vldtr93 , vldtr94 , vldtr95 , vldtr96 , vldtr97 , vldtr98 , vldtr99 , vldtr9A , vldtr9B , vldtr9C , vldtr9D , vldtr9E , vldtr9F , vldtrA0 , vldtrA1 , vldtrA2 , vldtrA3 , vldtrA4 , vldtrA5 , vldtrA6 , vldtrA7 , vldtrA8 , vldtrA9 , vldtrAA , vldtrAB , vldtrAC , vldtrAD , vldtrAE , vldtrAF , vldtrB0 , vldtrB1 , vldtrB2 , vldtrB3 , vldtrB4 , vldtrB5 , vldtrB6 , vldtrB7 , vldtrB8 , vldtrB9 , vldtrBA , vldtrBB , vldtrBC , vldtrBD , vldtrBE , vldtrBF , vldtrC0 , vldtrC1 , vldtrC2 , vldtrC3 , vldtrC4 , vldtrC5 , vldtrC6 , vldtrC7 , vldtrC8 , vldtrC9 , vldtrCA , vldtrCB , vldtrCC , vldtrCD , vldtrCE , vldtrCF , vldtrD0 , vldtrD1 , vldtrD2 , vldtrD3 , vldtrD4 , vldtrD5 , vldtrD6 , vldtrD7 , vldtrD8 , vldtrD9 , vldtrDA , vldtrDB , vldtrDC , vldtrDD , vldtrDE , vldtrDF , vldtrE0 , vldtrE1 , vldtrE2 , vldtrE3 , vldtrE4 , vldtrE5 , vldtrE6 , vldtrE7 , vldtrE8 , vldtrE9 , vldtrEA , vldtrEB , vldtrEC , vldtrED , vldtrEE , vldtrEF , vldtrF0 , vldtrF1 , vldtrF2 , vldtrF3 , vldtrF4 , vldtrF5 , vldtrF6 , vldtrF7 , vldtrF8 , vldtrF9 , vldtrFA , vldtrFB , vldtrFC , vldtrFD , vldtrFE , vldtrFF <] .
Lemma ElectorBase_ι_Request_ι_validatorKey_bs_id: ElectorBase_ι_Request_ι_validatorKey_bs_def = [> vldtr00 , vldtr01 , vldtr02 , vldtr03 , vldtr04 , vldtr05 , vldtr06 , vldtr07 , vldtr08 , vldtr09 , vldtr0A , vldtr0B , vldtr0C , vldtr0D , vldtr0E , vldtr0F , vldtr10 , vldtr11 , vldtr12 , vldtr13 , vldtr14 , vldtr15 , vldtr16 , vldtr17 , vldtr18 , vldtr19 , vldtr1A , vldtr1B , vldtr1C , vldtr1D , vldtr1E , vldtr1F , vldtr20 , vldtr21 , vldtr22 , vldtr23 , vldtr24 , vldtr25 , vldtr26 , vldtr27 , vldtr28 , vldtr29 , vldtr2A , vldtr2B , vldtr2C , vldtr2D , vldtr2E , vldtr2F , vldtr30 , vldtr31 , vldtr32 , vldtr33 , vldtr34 , vldtr35 , vldtr36 , vldtr37 , vldtr38 , vldtr39 , vldtr3A , vldtr3B , vldtr3C , vldtr3D , vldtr3E , vldtr3F , vldtr40 , vldtr41 , vldtr42 , vldtr43 , vldtr44 , vldtr45 , vldtr46 , vldtr47 , vldtr48 , vldtr49 , vldtr4A , vldtr4B , vldtr4C , vldtr4D , vldtr4E , vldtr4F , vldtr50 , vldtr51 , vldtr52 , vldtr53 , vldtr54 , vldtr55 , vldtr56 , vldtr57 , vldtr58 , vldtr59 , vldtr5A , vldtr5B , vldtr5C , vldtr5D , vldtr5E , vldtr5F , vldtr60 , vldtr61 , vldtr62 , vldtr63 , vldtr64 , vldtr65 , vldtr66 , vldtr67 , vldtr68 , vldtr69 , vldtr6A , vldtr6B , vldtr6C , vldtr6D , vldtr6E , vldtr6F , vldtr70 , vldtr71 , vldtr72 , vldtr73 , vldtr74 , vldtr75 , vldtr76 , vldtr77 , vldtr78 , vldtr79 , vldtr7A , vldtr7B , vldtr7C , vldtr7D , vldtr7E , vldtr7F , vldtr80 , vldtr81 , vldtr82 , vldtr83 , vldtr84 , vldtr85 , vldtr86 , vldtr87 , vldtr88 , vldtr89 , vldtr8A , vldtr8B , vldtr8C , vldtr8D , vldtr8E , vldtr8F , vldtr90 , vldtr91 , vldtr92 , vldtr93 , vldtr94 , vldtr95 , vldtr96 , vldtr97 , vldtr98 , vldtr99 , vldtr9A , vldtr9B , vldtr9C , vldtr9D , vldtr9E , vldtr9F , vldtrA0 , vldtrA1 , vldtrA2 , vldtrA3 , vldtrA4 , vldtrA5 , vldtrA6 , vldtrA7 , vldtrA8 , vldtrA9 , vldtrAA , vldtrAB , vldtrAC , vldtrAD , vldtrAE , vldtrAF , vldtrB0 , vldtrB1 , vldtrB2 , vldtrB3 , vldtrB4 , vldtrB5 , vldtrB6 , vldtrB7 , vldtrB8 , vldtrB9 , vldtrBA , vldtrBB , vldtrBC , vldtrBD , vldtrBE , vldtrBF , vldtrC0 , vldtrC1 , vldtrC2 , vldtrC3 , vldtrC4 , vldtrC5 , vldtrC6 , vldtrC7 , vldtrC8 , vldtrC9 , vldtrCA , vldtrCB , vldtrCC , vldtrCD , vldtrCE , vldtrCF , vldtrD0 , vldtrD1 , vldtrD2 , vldtrD3 , vldtrD4 , vldtrD5 , vldtrD6 , vldtrD7 , vldtrD8 , vldtrD9 , vldtrDA , vldtrDB , vldtrDC , vldtrDD , vldtrDE , vldtrDF , vldtrE0 , vldtrE1 , vldtrE2 , vldtrE3 , vldtrE4 , vldtrE5 , vldtrE6 , vldtrE7 , vldtrE8 , vldtrE9 , vldtrEA , vldtrEB , vldtrEC , vldtrED , vldtrEE , vldtrEF , vldtrF0 , vldtrF1 , vldtrF2 , vldtrF3 , vldtrF4 , vldtrF5 , vldtrF6 , vldtrF7 , vldtrF8 , vldtrF9 , vldtrFA , vldtrFB , vldtrFC , vldtrFD , vldtrFE , vldtrFF <] .
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
Qed. Variables ElectorBase_ι_Request_ι_stakeAt : Z . 
Variables stkt00 stkt01 stkt02 stkt03 stkt04 stkt05 stkt06 stkt07 stkt08 stkt09 stkt0A stkt0B stkt0C stkt0D stkt0E stkt0F stkt10 stkt11 stkt12 stkt13 stkt14 stkt15 stkt16 stkt17 stkt18 stkt19 stkt1A stkt1B stkt1C stkt1D stkt1E stkt1F  : TVMBit . 
Definition ElectorBase_ι_Request_ι_stakeAt_bs_def := [> stkt00 , stkt01 , stkt02 , stkt03 , stkt04 , stkt05 , stkt06 , stkt07 , stkt08 , stkt09 , stkt0A , stkt0B , stkt0C , stkt0D , stkt0E , stkt0F , stkt10 , stkt11 , stkt12 , stkt13 , stkt14 , stkt15 , stkt16 , stkt17 , stkt18 , stkt19 , stkt1A , stkt1B , stkt1C , stkt1D , stkt1E , stkt1F <] .
Lemma ElectorBase_ι_Request_ι_stakeAt_bs_id: ElectorBase_ι_Request_ι_stakeAt_bs_def = [> stkt00 , stkt01 , stkt02 , stkt03 , stkt04 , stkt05 , stkt06 , stkt07 , stkt08 , stkt09 , stkt0A , stkt0B , stkt0C , stkt0D , stkt0E , stkt0F , stkt10 , stkt11 , stkt12 , stkt13 , stkt14 , stkt15 , stkt16 , stkt17 , stkt18 , stkt19 , stkt1A , stkt1B , stkt1C , stkt1D , stkt1E , stkt1F <] .
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
Qed. Variables ElectorBase_ι_Request_ι_maxFactor : Z . 
Variables mxFct00 mxFct01 mxFct02 mxFct03 mxFct04 mxFct05 mxFct06 mxFct07 mxFct08 mxFct09 mxFct0A mxFct0B mxFct0C mxFct0D mxFct0E mxFct0F mxFct10 mxFct11 mxFct12 mxFct13 mxFct14 mxFct15 mxFct16 mxFct17 mxFct18 mxFct19 mxFct1A mxFct1B mxFct1C mxFct1D mxFct1E mxFct1F  : TVMBit . 
Definition ElectorBase_ι_Request_ι_maxFactor_bs_def := [> mxFct00 , mxFct01 , mxFct02 , mxFct03 , mxFct04 , mxFct05 , mxFct06 , mxFct07 , mxFct08 , mxFct09 , mxFct0A , mxFct0B , mxFct0C , mxFct0D , mxFct0E , mxFct0F , mxFct10 , mxFct11 , mxFct12 , mxFct13 , mxFct14 , mxFct15 , mxFct16 , mxFct17 , mxFct18 , mxFct19 , mxFct1A , mxFct1B , mxFct1C , mxFct1D , mxFct1E , mxFct1F <] .
Lemma ElectorBase_ι_Request_ι_maxFactor_bs_id: ElectorBase_ι_Request_ι_maxFactor_bs_def = [> mxFct00 , mxFct01 , mxFct02 , mxFct03 , mxFct04 , mxFct05 , mxFct06 , mxFct07 , mxFct08 , mxFct09 , mxFct0A , mxFct0B , mxFct0C , mxFct0D , mxFct0E , mxFct0F , mxFct10 , mxFct11 , mxFct12 , mxFct13 , mxFct14 , mxFct15 , mxFct16 , mxFct17 , mxFct18 , mxFct19 , mxFct1A , mxFct1B , mxFct1C , mxFct1D , mxFct1E , mxFct1F <] .
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
Qed. Variables ElectorBase_ι_Request_ι_adnlAddr : Z . 
Variables dnldd00 dnldd01 dnldd02 dnldd03 dnldd04 dnldd05 dnldd06 dnldd07 dnldd08 dnldd09 dnldd0A dnldd0B dnldd0C dnldd0D dnldd0E dnldd0F dnldd10 dnldd11 dnldd12 dnldd13 dnldd14 dnldd15 dnldd16 dnldd17 dnldd18 dnldd19 dnldd1A dnldd1B dnldd1C dnldd1D dnldd1E dnldd1F dnldd20 dnldd21 dnldd22 dnldd23 dnldd24 dnldd25 dnldd26 dnldd27 dnldd28 dnldd29 dnldd2A dnldd2B dnldd2C dnldd2D dnldd2E dnldd2F dnldd30 dnldd31 dnldd32 dnldd33 dnldd34 dnldd35 dnldd36 dnldd37 dnldd38 dnldd39 dnldd3A dnldd3B dnldd3C dnldd3D dnldd3E dnldd3F dnldd40 dnldd41 dnldd42 dnldd43 dnldd44 dnldd45 dnldd46 dnldd47 dnldd48 dnldd49 dnldd4A dnldd4B dnldd4C dnldd4D dnldd4E dnldd4F dnldd50 dnldd51 dnldd52 dnldd53 dnldd54 dnldd55 dnldd56 dnldd57 dnldd58 dnldd59 dnldd5A dnldd5B dnldd5C dnldd5D dnldd5E dnldd5F dnldd60 dnldd61 dnldd62 dnldd63 dnldd64 dnldd65 dnldd66 dnldd67 dnldd68 dnldd69 dnldd6A dnldd6B dnldd6C dnldd6D dnldd6E dnldd6F dnldd70 dnldd71 dnldd72 dnldd73 dnldd74 dnldd75 dnldd76 dnldd77 dnldd78 dnldd79 dnldd7A dnldd7B dnldd7C dnldd7D dnldd7E dnldd7F dnldd80 dnldd81 dnldd82 dnldd83 dnldd84 dnldd85 dnldd86 dnldd87 dnldd88 dnldd89 dnldd8A dnldd8B dnldd8C dnldd8D dnldd8E dnldd8F dnldd90 dnldd91 dnldd92 dnldd93 dnldd94 dnldd95 dnldd96 dnldd97 dnldd98 dnldd99 dnldd9A dnldd9B dnldd9C dnldd9D dnldd9E dnldd9F dnlddA0 dnlddA1 dnlddA2 dnlddA3 dnlddA4 dnlddA5 dnlddA6 dnlddA7 dnlddA8 dnlddA9 dnlddAA dnlddAB dnlddAC dnlddAD dnlddAE dnlddAF dnlddB0 dnlddB1 dnlddB2 dnlddB3 dnlddB4 dnlddB5 dnlddB6 dnlddB7 dnlddB8 dnlddB9 dnlddBA dnlddBB dnlddBC dnlddBD dnlddBE dnlddBF dnlddC0 dnlddC1 dnlddC2 dnlddC3 dnlddC4 dnlddC5 dnlddC6 dnlddC7 dnlddC8 dnlddC9 dnlddCA dnlddCB dnlddCC dnlddCD dnlddCE dnlddCF dnlddD0 dnlddD1 dnlddD2 dnlddD3 dnlddD4 dnlddD5 dnlddD6 dnlddD7 dnlddD8 dnlddD9 dnlddDA dnlddDB dnlddDC dnlddDD dnlddDE dnlddDF dnlddE0 dnlddE1 dnlddE2 dnlddE3 dnlddE4 dnlddE5 dnlddE6 dnlddE7 dnlddE8 dnlddE9 dnlddEA dnlddEB dnlddEC dnlddED dnlddEE dnlddEF dnlddF0 dnlddF1 dnlddF2 dnlddF3 dnlddF4 dnlddF5 dnlddF6 dnlddF7 dnlddF8 dnlddF9 dnlddFA dnlddFB dnlddFC dnlddFD dnlddFE dnlddFF  : TVMBit . 
Definition ElectorBase_ι_Request_ι_adnlAddr_bs_def := [> dnldd00 , dnldd01 , dnldd02 , dnldd03 , dnldd04 , dnldd05 , dnldd06 , dnldd07 , dnldd08 , dnldd09 , dnldd0A , dnldd0B , dnldd0C , dnldd0D , dnldd0E , dnldd0F , dnldd10 , dnldd11 , dnldd12 , dnldd13 , dnldd14 , dnldd15 , dnldd16 , dnldd17 , dnldd18 , dnldd19 , dnldd1A , dnldd1B , dnldd1C , dnldd1D , dnldd1E , dnldd1F , dnldd20 , dnldd21 , dnldd22 , dnldd23 , dnldd24 , dnldd25 , dnldd26 , dnldd27 , dnldd28 , dnldd29 , dnldd2A , dnldd2B , dnldd2C , dnldd2D , dnldd2E , dnldd2F , dnldd30 , dnldd31 , dnldd32 , dnldd33 , dnldd34 , dnldd35 , dnldd36 , dnldd37 , dnldd38 , dnldd39 , dnldd3A , dnldd3B , dnldd3C , dnldd3D , dnldd3E , dnldd3F , dnldd40 , dnldd41 , dnldd42 , dnldd43 , dnldd44 , dnldd45 , dnldd46 , dnldd47 , dnldd48 , dnldd49 , dnldd4A , dnldd4B , dnldd4C , dnldd4D , dnldd4E , dnldd4F , dnldd50 , dnldd51 , dnldd52 , dnldd53 , dnldd54 , dnldd55 , dnldd56 , dnldd57 , dnldd58 , dnldd59 , dnldd5A , dnldd5B , dnldd5C , dnldd5D , dnldd5E , dnldd5F , dnldd60 , dnldd61 , dnldd62 , dnldd63 , dnldd64 , dnldd65 , dnldd66 , dnldd67 , dnldd68 , dnldd69 , dnldd6A , dnldd6B , dnldd6C , dnldd6D , dnldd6E , dnldd6F , dnldd70 , dnldd71 , dnldd72 , dnldd73 , dnldd74 , dnldd75 , dnldd76 , dnldd77 , dnldd78 , dnldd79 , dnldd7A , dnldd7B , dnldd7C , dnldd7D , dnldd7E , dnldd7F , dnldd80 , dnldd81 , dnldd82 , dnldd83 , dnldd84 , dnldd85 , dnldd86 , dnldd87 , dnldd88 , dnldd89 , dnldd8A , dnldd8B , dnldd8C , dnldd8D , dnldd8E , dnldd8F , dnldd90 , dnldd91 , dnldd92 , dnldd93 , dnldd94 , dnldd95 , dnldd96 , dnldd97 , dnldd98 , dnldd99 , dnldd9A , dnldd9B , dnldd9C , dnldd9D , dnldd9E , dnldd9F , dnlddA0 , dnlddA1 , dnlddA2 , dnlddA3 , dnlddA4 , dnlddA5 , dnlddA6 , dnlddA7 , dnlddA8 , dnlddA9 , dnlddAA , dnlddAB , dnlddAC , dnlddAD , dnlddAE , dnlddAF , dnlddB0 , dnlddB1 , dnlddB2 , dnlddB3 , dnlddB4 , dnlddB5 , dnlddB6 , dnlddB7 , dnlddB8 , dnlddB9 , dnlddBA , dnlddBB , dnlddBC , dnlddBD , dnlddBE , dnlddBF , dnlddC0 , dnlddC1 , dnlddC2 , dnlddC3 , dnlddC4 , dnlddC5 , dnlddC6 , dnlddC7 , dnlddC8 , dnlddC9 , dnlddCA , dnlddCB , dnlddCC , dnlddCD , dnlddCE , dnlddCF , dnlddD0 , dnlddD1 , dnlddD2 , dnlddD3 , dnlddD4 , dnlddD5 , dnlddD6 , dnlddD7 , dnlddD8 , dnlddD9 , dnlddDA , dnlddDB , dnlddDC , dnlddDD , dnlddDE , dnlddDF , dnlddE0 , dnlddE1 , dnlddE2 , dnlddE3 , dnlddE4 , dnlddE5 , dnlddE6 , dnlddE7 , dnlddE8 , dnlddE9 , dnlddEA , dnlddEB , dnlddEC , dnlddED , dnlddEE , dnlddEF , dnlddF0 , dnlddF1 , dnlddF2 , dnlddF3 , dnlddF4 , dnlddF5 , dnlddF6 , dnlddF7 , dnlddF8 , dnlddF9 , dnlddFA , dnlddFB , dnlddFC , dnlddFD , dnlddFE , dnlddFF <] .
Lemma ElectorBase_ι_Request_ι_adnlAddr_bs_id: ElectorBase_ι_Request_ι_adnlAddr_bs_def = [> dnldd00 , dnldd01 , dnldd02 , dnldd03 , dnldd04 , dnldd05 , dnldd06 , dnldd07 , dnldd08 , dnldd09 , dnldd0A , dnldd0B , dnldd0C , dnldd0D , dnldd0E , dnldd0F , dnldd10 , dnldd11 , dnldd12 , dnldd13 , dnldd14 , dnldd15 , dnldd16 , dnldd17 , dnldd18 , dnldd19 , dnldd1A , dnldd1B , dnldd1C , dnldd1D , dnldd1E , dnldd1F , dnldd20 , dnldd21 , dnldd22 , dnldd23 , dnldd24 , dnldd25 , dnldd26 , dnldd27 , dnldd28 , dnldd29 , dnldd2A , dnldd2B , dnldd2C , dnldd2D , dnldd2E , dnldd2F , dnldd30 , dnldd31 , dnldd32 , dnldd33 , dnldd34 , dnldd35 , dnldd36 , dnldd37 , dnldd38 , dnldd39 , dnldd3A , dnldd3B , dnldd3C , dnldd3D , dnldd3E , dnldd3F , dnldd40 , dnldd41 , dnldd42 , dnldd43 , dnldd44 , dnldd45 , dnldd46 , dnldd47 , dnldd48 , dnldd49 , dnldd4A , dnldd4B , dnldd4C , dnldd4D , dnldd4E , dnldd4F , dnldd50 , dnldd51 , dnldd52 , dnldd53 , dnldd54 , dnldd55 , dnldd56 , dnldd57 , dnldd58 , dnldd59 , dnldd5A , dnldd5B , dnldd5C , dnldd5D , dnldd5E , dnldd5F , dnldd60 , dnldd61 , dnldd62 , dnldd63 , dnldd64 , dnldd65 , dnldd66 , dnldd67 , dnldd68 , dnldd69 , dnldd6A , dnldd6B , dnldd6C , dnldd6D , dnldd6E , dnldd6F , dnldd70 , dnldd71 , dnldd72 , dnldd73 , dnldd74 , dnldd75 , dnldd76 , dnldd77 , dnldd78 , dnldd79 , dnldd7A , dnldd7B , dnldd7C , dnldd7D , dnldd7E , dnldd7F , dnldd80 , dnldd81 , dnldd82 , dnldd83 , dnldd84 , dnldd85 , dnldd86 , dnldd87 , dnldd88 , dnldd89 , dnldd8A , dnldd8B , dnldd8C , dnldd8D , dnldd8E , dnldd8F , dnldd90 , dnldd91 , dnldd92 , dnldd93 , dnldd94 , dnldd95 , dnldd96 , dnldd97 , dnldd98 , dnldd99 , dnldd9A , dnldd9B , dnldd9C , dnldd9D , dnldd9E , dnldd9F , dnlddA0 , dnlddA1 , dnlddA2 , dnlddA3 , dnlddA4 , dnlddA5 , dnlddA6 , dnlddA7 , dnlddA8 , dnlddA9 , dnlddAA , dnlddAB , dnlddAC , dnlddAD , dnlddAE , dnlddAF , dnlddB0 , dnlddB1 , dnlddB2 , dnlddB3 , dnlddB4 , dnlddB5 , dnlddB6 , dnlddB7 , dnlddB8 , dnlddB9 , dnlddBA , dnlddBB , dnlddBC , dnlddBD , dnlddBE , dnlddBF , dnlddC0 , dnlddC1 , dnlddC2 , dnlddC3 , dnlddC4 , dnlddC5 , dnlddC6 , dnlddC7 , dnlddC8 , dnlddC9 , dnlddCA , dnlddCB , dnlddCC , dnlddCD , dnlddCE , dnlddCF , dnlddD0 , dnlddD1 , dnlddD2 , dnlddD3 , dnlddD4 , dnlddD5 , dnlddD6 , dnlddD7 , dnlddD8 , dnlddD9 , dnlddDA , dnlddDB , dnlddDC , dnlddDD , dnlddDE , dnlddDF , dnlddE0 , dnlddE1 , dnlddE2 , dnlddE3 , dnlddE4 , dnlddE5 , dnlddE6 , dnlddE7 , dnlddE8 , dnlddE9 , dnlddEA , dnlddEB , dnlddEC , dnlddED , dnlddEE , dnlddEF , dnlddF0 , dnlddF1 , dnlddF2 , dnlddF3 , dnlddF4 , dnlddF5 , dnlddF6 , dnlddF7 , dnlddF8 , dnlddF9 , dnlddFA , dnlddFB , dnlddFC , dnlddFD , dnlddFE , dnlddFF <] .
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
Qed. Variables ElectorBase_ι_Request_ι_signature : Z . 
Variables sgntr00 sgntr01 sgntr02 sgntr03 sgntr04 sgntr05 sgntr06 sgntr07  : TVMBit . 
Definition ElectorBase_ι_Request_ι_signature_bs_def := [> sgntr00 , sgntr01 , sgntr02 , sgntr03 , sgntr04 , sgntr05 , sgntr06 , sgntr07 <] .
Lemma ElectorBase_ι_Request_ι_signature_bs_id: ElectorBase_ι_Request_ι_signature_bs_def = [> sgntr00 , sgntr01 , sgntr02 , sgntr03 , sgntr04 , sgntr05 , sgntr06 , sgntr07 <] .
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
Variables ddr7300 ddr7301 ddr7302 ddr7303 ddr7304 ddr7305 ddr7306 ddr7307  : TVMBit . 
Definition ElectionParams_ι_ValidatorDescr73_ι_validator_addr73_bs_def := [> ddr7300 , ddr7301 , ddr7302 , ddr7303 , ddr7304 , ddr7305 , ddr7306 , ddr7307 <] .
Lemma ElectionParams_ι_ValidatorDescr73_ι_validator_addr73_bs_id: ElectionParams_ι_ValidatorDescr73_ι_validator_addr73_bs_def = [> ddr7300 , ddr7301 , ddr7302 , ddr7303 , ddr7304 , ddr7305 , ddr7306 , ddr7307 <] .
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
Qed. Variables ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey : Z . 
Variables pbk00 pbk01 pbk02 pbk03 pbk04 pbk05 pbk06 pbk07 pbk08 pbk09 pbk0A pbk0B pbk0C pbk0D pbk0E pbk0F pbk10 pbk11 pbk12 pbk13 pbk14 pbk15 pbk16 pbk17 pbk18 pbk19 pbk1A pbk1B pbk1C pbk1D pbk1E pbk1F  : TVMBit . 
Definition ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey_bs_def := [> pbk00 , pbk01 , pbk02 , pbk03 , pbk04 , pbk05 , pbk06 , pbk07 , pbk08 , pbk09 , pbk0A , pbk0B , pbk0C , pbk0D , pbk0E , pbk0F , pbk10 , pbk11 , pbk12 , pbk13 , pbk14 , pbk15 , pbk16 , pbk17 , pbk18 , pbk19 , pbk1A , pbk1B , pbk1C , pbk1D , pbk1E , pbk1F <] .
Lemma ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey_bs_id: ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey_bs_def = [> pbk00 , pbk01 , pbk02 , pbk03 , pbk04 , pbk05 , pbk06 , pbk07 , pbk08 , pbk09 , pbk0A , pbk0B , pbk0C , pbk0D , pbk0E , pbk0F , pbk10 , pbk11 , pbk12 , pbk13 , pbk14 , pbk15 , pbk16 , pbk17 , pbk18 , pbk19 , pbk1A , pbk1B , pbk1C , pbk1D , pbk1E , pbk1F <] .
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
Qed. Variables ElectionParams_ι_ValidatorDescr73_ι_pubkey : Z . 
Variables pbk00 pbk01 pbk02 pbk03 pbk04 pbk05 pbk06 pbk07 pbk08 pbk09 pbk0A pbk0B pbk0C pbk0D pbk0E pbk0F pbk10 pbk11 pbk12 pbk13 pbk14 pbk15 pbk16 pbk17 pbk18 pbk19 pbk1A pbk1B pbk1C pbk1D pbk1E pbk1F pbk20 pbk21 pbk22 pbk23 pbk24 pbk25 pbk26 pbk27 pbk28 pbk29 pbk2A pbk2B pbk2C pbk2D pbk2E pbk2F pbk30 pbk31 pbk32 pbk33 pbk34 pbk35 pbk36 pbk37 pbk38 pbk39 pbk3A pbk3B pbk3C pbk3D pbk3E pbk3F pbk40 pbk41 pbk42 pbk43 pbk44 pbk45 pbk46 pbk47 pbk48 pbk49 pbk4A pbk4B pbk4C pbk4D pbk4E pbk4F pbk50 pbk51 pbk52 pbk53 pbk54 pbk55 pbk56 pbk57 pbk58 pbk59 pbk5A pbk5B pbk5C pbk5D pbk5E pbk5F pbk60 pbk61 pbk62 pbk63 pbk64 pbk65 pbk66 pbk67 pbk68 pbk69 pbk6A pbk6B pbk6C pbk6D pbk6E pbk6F pbk70 pbk71 pbk72 pbk73 pbk74 pbk75 pbk76 pbk77 pbk78 pbk79 pbk7A pbk7B pbk7C pbk7D pbk7E pbk7F pbk80 pbk81 pbk82 pbk83 pbk84 pbk85 pbk86 pbk87 pbk88 pbk89 pbk8A pbk8B pbk8C pbk8D pbk8E pbk8F pbk90 pbk91 pbk92 pbk93 pbk94 pbk95 pbk96 pbk97 pbk98 pbk99 pbk9A pbk9B pbk9C pbk9D pbk9E pbk9F pbkA0 pbkA1 pbkA2 pbkA3 pbkA4 pbkA5 pbkA6 pbkA7 pbkA8 pbkA9 pbkAA pbkAB pbkAC pbkAD pbkAE pbkAF pbkB0 pbkB1 pbkB2 pbkB3 pbkB4 pbkB5 pbkB6 pbkB7 pbkB8 pbkB9 pbkBA pbkBB pbkBC pbkBD pbkBE pbkBF pbkC0 pbkC1 pbkC2 pbkC3 pbkC4 pbkC5 pbkC6 pbkC7 pbkC8 pbkC9 pbkCA pbkCB pbkCC pbkCD pbkCE pbkCF pbkD0 pbkD1 pbkD2 pbkD3 pbkD4 pbkD5 pbkD6 pbkD7 pbkD8 pbkD9 pbkDA pbkDB pbkDC pbkDD pbkDE pbkDF pbkE0 pbkE1 pbkE2 pbkE3 pbkE4 pbkE5 pbkE6 pbkE7 pbkE8 pbkE9 pbkEA pbkEB pbkEC pbkED pbkEE pbkEF pbkF0 pbkF1 pbkF2 pbkF3 pbkF4 pbkF5 pbkF6 pbkF7 pbkF8 pbkF9 pbkFA pbkFB pbkFC pbkFD pbkFE pbkFF  : TVMBit . 
Definition ElectionParams_ι_ValidatorDescr73_ι_pubkey_bs_def := [> pbk00 , pbk01 , pbk02 , pbk03 , pbk04 , pbk05 , pbk06 , pbk07 , pbk08 , pbk09 , pbk0A , pbk0B , pbk0C , pbk0D , pbk0E , pbk0F , pbk10 , pbk11 , pbk12 , pbk13 , pbk14 , pbk15 , pbk16 , pbk17 , pbk18 , pbk19 , pbk1A , pbk1B , pbk1C , pbk1D , pbk1E , pbk1F , pbk20 , pbk21 , pbk22 , pbk23 , pbk24 , pbk25 , pbk26 , pbk27 , pbk28 , pbk29 , pbk2A , pbk2B , pbk2C , pbk2D , pbk2E , pbk2F , pbk30 , pbk31 , pbk32 , pbk33 , pbk34 , pbk35 , pbk36 , pbk37 , pbk38 , pbk39 , pbk3A , pbk3B , pbk3C , pbk3D , pbk3E , pbk3F , pbk40 , pbk41 , pbk42 , pbk43 , pbk44 , pbk45 , pbk46 , pbk47 , pbk48 , pbk49 , pbk4A , pbk4B , pbk4C , pbk4D , pbk4E , pbk4F , pbk50 , pbk51 , pbk52 , pbk53 , pbk54 , pbk55 , pbk56 , pbk57 , pbk58 , pbk59 , pbk5A , pbk5B , pbk5C , pbk5D , pbk5E , pbk5F , pbk60 , pbk61 , pbk62 , pbk63 , pbk64 , pbk65 , pbk66 , pbk67 , pbk68 , pbk69 , pbk6A , pbk6B , pbk6C , pbk6D , pbk6E , pbk6F , pbk70 , pbk71 , pbk72 , pbk73 , pbk74 , pbk75 , pbk76 , pbk77 , pbk78 , pbk79 , pbk7A , pbk7B , pbk7C , pbk7D , pbk7E , pbk7F , pbk80 , pbk81 , pbk82 , pbk83 , pbk84 , pbk85 , pbk86 , pbk87 , pbk88 , pbk89 , pbk8A , pbk8B , pbk8C , pbk8D , pbk8E , pbk8F , pbk90 , pbk91 , pbk92 , pbk93 , pbk94 , pbk95 , pbk96 , pbk97 , pbk98 , pbk99 , pbk9A , pbk9B , pbk9C , pbk9D , pbk9E , pbk9F , pbkA0 , pbkA1 , pbkA2 , pbkA3 , pbkA4 , pbkA5 , pbkA6 , pbkA7 , pbkA8 , pbkA9 , pbkAA , pbkAB , pbkAC , pbkAD , pbkAE , pbkAF , pbkB0 , pbkB1 , pbkB2 , pbkB3 , pbkB4 , pbkB5 , pbkB6 , pbkB7 , pbkB8 , pbkB9 , pbkBA , pbkBB , pbkBC , pbkBD , pbkBE , pbkBF , pbkC0 , pbkC1 , pbkC2 , pbkC3 , pbkC4 , pbkC5 , pbkC6 , pbkC7 , pbkC8 , pbkC9 , pbkCA , pbkCB , pbkCC , pbkCD , pbkCE , pbkCF , pbkD0 , pbkD1 , pbkD2 , pbkD3 , pbkD4 , pbkD5 , pbkD6 , pbkD7 , pbkD8 , pbkD9 , pbkDA , pbkDB , pbkDC , pbkDD , pbkDE , pbkDF , pbkE0 , pbkE1 , pbkE2 , pbkE3 , pbkE4 , pbkE5 , pbkE6 , pbkE7 , pbkE8 , pbkE9 , pbkEA , pbkEB , pbkEC , pbkED , pbkEE , pbkEF , pbkF0 , pbkF1 , pbkF2 , pbkF3 , pbkF4 , pbkF5 , pbkF6 , pbkF7 , pbkF8 , pbkF9 , pbkFA , pbkFB , pbkFC , pbkFD , pbkFE , pbkFF <] .
Lemma ElectionParams_ι_ValidatorDescr73_ι_pubkey_bs_id: ElectionParams_ι_ValidatorDescr73_ι_pubkey_bs_def = [> pbk00 , pbk01 , pbk02 , pbk03 , pbk04 , pbk05 , pbk06 , pbk07 , pbk08 , pbk09 , pbk0A , pbk0B , pbk0C , pbk0D , pbk0E , pbk0F , pbk10 , pbk11 , pbk12 , pbk13 , pbk14 , pbk15 , pbk16 , pbk17 , pbk18 , pbk19 , pbk1A , pbk1B , pbk1C , pbk1D , pbk1E , pbk1F , pbk20 , pbk21 , pbk22 , pbk23 , pbk24 , pbk25 , pbk26 , pbk27 , pbk28 , pbk29 , pbk2A , pbk2B , pbk2C , pbk2D , pbk2E , pbk2F , pbk30 , pbk31 , pbk32 , pbk33 , pbk34 , pbk35 , pbk36 , pbk37 , pbk38 , pbk39 , pbk3A , pbk3B , pbk3C , pbk3D , pbk3E , pbk3F , pbk40 , pbk41 , pbk42 , pbk43 , pbk44 , pbk45 , pbk46 , pbk47 , pbk48 , pbk49 , pbk4A , pbk4B , pbk4C , pbk4D , pbk4E , pbk4F , pbk50 , pbk51 , pbk52 , pbk53 , pbk54 , pbk55 , pbk56 , pbk57 , pbk58 , pbk59 , pbk5A , pbk5B , pbk5C , pbk5D , pbk5E , pbk5F , pbk60 , pbk61 , pbk62 , pbk63 , pbk64 , pbk65 , pbk66 , pbk67 , pbk68 , pbk69 , pbk6A , pbk6B , pbk6C , pbk6D , pbk6E , pbk6F , pbk70 , pbk71 , pbk72 , pbk73 , pbk74 , pbk75 , pbk76 , pbk77 , pbk78 , pbk79 , pbk7A , pbk7B , pbk7C , pbk7D , pbk7E , pbk7F , pbk80 , pbk81 , pbk82 , pbk83 , pbk84 , pbk85 , pbk86 , pbk87 , pbk88 , pbk89 , pbk8A , pbk8B , pbk8C , pbk8D , pbk8E , pbk8F , pbk90 , pbk91 , pbk92 , pbk93 , pbk94 , pbk95 , pbk96 , pbk97 , pbk98 , pbk99 , pbk9A , pbk9B , pbk9C , pbk9D , pbk9E , pbk9F , pbkA0 , pbkA1 , pbkA2 , pbkA3 , pbkA4 , pbkA5 , pbkA6 , pbkA7 , pbkA8 , pbkA9 , pbkAA , pbkAB , pbkAC , pbkAD , pbkAE , pbkAF , pbkB0 , pbkB1 , pbkB2 , pbkB3 , pbkB4 , pbkB5 , pbkB6 , pbkB7 , pbkB8 , pbkB9 , pbkBA , pbkBB , pbkBC , pbkBD , pbkBE , pbkBF , pbkC0 , pbkC1 , pbkC2 , pbkC3 , pbkC4 , pbkC5 , pbkC6 , pbkC7 , pbkC8 , pbkC9 , pbkCA , pbkCB , pbkCC , pbkCD , pbkCE , pbkCF , pbkD0 , pbkD1 , pbkD2 , pbkD3 , pbkD4 , pbkD5 , pbkD6 , pbkD7 , pbkD8 , pbkD9 , pbkDA , pbkDB , pbkDC , pbkDD , pbkDE , pbkDF , pbkE0 , pbkE1 , pbkE2 , pbkE3 , pbkE4 , pbkE5 , pbkE6 , pbkE7 , pbkE8 , pbkE9 , pbkEA , pbkEB , pbkEC , pbkED , pbkEE , pbkEF , pbkF0 , pbkF1 , pbkF2 , pbkF3 , pbkF4 , pbkF5 , pbkF6 , pbkF7 , pbkF8 , pbkF9 , pbkFA , pbkFB , pbkFC , pbkFD , pbkFE , pbkFF <] .
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
Qed. Variables ElectionParams_ι_ValidatorDescr73_ι_weight : Z . 
Variables wght00 wght01 wght02 wght03 wght04 wght05 wght06 wght07 wght08 wght09 wght0A wght0B wght0C wght0D wght0E wght0F wght10 wght11 wght12 wght13 wght14 wght15 wght16 wght17 wght18 wght19 wght1A wght1B wght1C wght1D wght1E wght1F wght20 wght21 wght22 wght23 wght24 wght25 wght26 wght27 wght28 wght29 wght2A wght2B wght2C wght2D wght2E wght2F wght30 wght31 wght32 wght33 wght34 wght35 wght36 wght37 wght38 wght39 wght3A wght3B wght3C wght3D wght3E wght3F  : TVMBit . 
Definition ElectionParams_ι_ValidatorDescr73_ι_weight_bs_def := [> wght00 , wght01 , wght02 , wght03 , wght04 , wght05 , wght06 , wght07 , wght08 , wght09 , wght0A , wght0B , wght0C , wght0D , wght0E , wght0F , wght10 , wght11 , wght12 , wght13 , wght14 , wght15 , wght16 , wght17 , wght18 , wght19 , wght1A , wght1B , wght1C , wght1D , wght1E , wght1F , wght20 , wght21 , wght22 , wght23 , wght24 , wght25 , wght26 , wght27 , wght28 , wght29 , wght2A , wght2B , wght2C , wght2D , wght2E , wght2F , wght30 , wght31 , wght32 , wght33 , wght34 , wght35 , wght36 , wght37 , wght38 , wght39 , wght3A , wght3B , wght3C , wght3D , wght3E , wght3F <] .
Lemma ElectionParams_ι_ValidatorDescr73_ι_weight_bs_id: ElectionParams_ι_ValidatorDescr73_ι_weight_bs_def = [> wght00 , wght01 , wght02 , wght03 , wght04 , wght05 , wght06 , wght07 , wght08 , wght09 , wght0A , wght0B , wght0C , wght0D , wght0E , wght0F , wght10 , wght11 , wght12 , wght13 , wght14 , wght15 , wght16 , wght17 , wght18 , wght19 , wght1A , wght1B , wght1C , wght1D , wght1E , wght1F , wght20 , wght21 , wght22 , wght23 , wght24 , wght25 , wght26 , wght27 , wght28 , wght29 , wght2A , wght2B , wght2C , wght2D , wght2E , wght2F , wght30 , wght31 , wght32 , wght33 , wght34 , wght35 , wght36 , wght37 , wght38 , wght39 , wght3A , wght3B , wght3C , wght3D , wght3E , wght3F <] .
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
Qed. Variables ElectionParams_ι_ValidatorDescr73_ι_adnl_addr : Z . 
Variables ddr00 ddr01 ddr02 ddr03 ddr04 ddr05 ddr06 ddr07 ddr08 ddr09 ddr0A ddr0B ddr0C ddr0D ddr0E ddr0F ddr10 ddr11 ddr12 ddr13 ddr14 ddr15 ddr16 ddr17 ddr18 ddr19 ddr1A ddr1B ddr1C ddr1D ddr1E ddr1F ddr20 ddr21 ddr22 ddr23 ddr24 ddr25 ddr26 ddr27 ddr28 ddr29 ddr2A ddr2B ddr2C ddr2D ddr2E ddr2F ddr30 ddr31 ddr32 ddr33 ddr34 ddr35 ddr36 ddr37 ddr38 ddr39 ddr3A ddr3B ddr3C ddr3D ddr3E ddr3F ddr40 ddr41 ddr42 ddr43 ddr44 ddr45 ddr46 ddr47 ddr48 ddr49 ddr4A ddr4B ddr4C ddr4D ddr4E ddr4F ddr50 ddr51 ddr52 ddr53 ddr54 ddr55 ddr56 ddr57 ddr58 ddr59 ddr5A ddr5B ddr5C ddr5D ddr5E ddr5F ddr60 ddr61 ddr62 ddr63 ddr64 ddr65 ddr66 ddr67 ddr68 ddr69 ddr6A ddr6B ddr6C ddr6D ddr6E ddr6F ddr70 ddr71 ddr72 ddr73 ddr74 ddr75 ddr76 ddr77 ddr78 ddr79 ddr7A ddr7B ddr7C ddr7D ddr7E ddr7F ddr80 ddr81 ddr82 ddr83 ddr84 ddr85 ddr86 ddr87 ddr88 ddr89 ddr8A ddr8B ddr8C ddr8D ddr8E ddr8F ddr90 ddr91 ddr92 ddr93 ddr94 ddr95 ddr96 ddr97 ddr98 ddr99 ddr9A ddr9B ddr9C ddr9D ddr9E ddr9F ddrA0 ddrA1 ddrA2 ddrA3 ddrA4 ddrA5 ddrA6 ddrA7 ddrA8 ddrA9 ddrAA ddrAB ddrAC ddrAD ddrAE ddrAF ddrB0 ddrB1 ddrB2 ddrB3 ddrB4 ddrB5 ddrB6 ddrB7 ddrB8 ddrB9 ddrBA ddrBB ddrBC ddrBD ddrBE ddrBF ddrC0 ddrC1 ddrC2 ddrC3 ddrC4 ddrC5 ddrC6 ddrC7 ddrC8 ddrC9 ddrCA ddrCB ddrCC ddrCD ddrCE ddrCF ddrD0 ddrD1 ddrD2 ddrD3 ddrD4 ddrD5 ddrD6 ddrD7 ddrD8 ddrD9 ddrDA ddrDB ddrDC ddrDD ddrDE ddrDF ddrE0 ddrE1 ddrE2 ddrE3 ddrE4 ddrE5 ddrE6 ddrE7 ddrE8 ddrE9 ddrEA ddrEB ddrEC ddrED ddrEE ddrEF ddrF0 ddrF1 ddrF2 ddrF3 ddrF4 ddrF5 ddrF6 ddrF7 ddrF8 ddrF9 ddrFA ddrFB ddrFC ddrFD ddrFE ddrFF  : TVMBit . 
Definition ElectionParams_ι_ValidatorDescr73_ι_adnl_addr_bs_def := [> ddr00 , ddr01 , ddr02 , ddr03 , ddr04 , ddr05 , ddr06 , ddr07 , ddr08 , ddr09 , ddr0A , ddr0B , ddr0C , ddr0D , ddr0E , ddr0F , ddr10 , ddr11 , ddr12 , ddr13 , ddr14 , ddr15 , ddr16 , ddr17 , ddr18 , ddr19 , ddr1A , ddr1B , ddr1C , ddr1D , ddr1E , ddr1F , ddr20 , ddr21 , ddr22 , ddr23 , ddr24 , ddr25 , ddr26 , ddr27 , ddr28 , ddr29 , ddr2A , ddr2B , ddr2C , ddr2D , ddr2E , ddr2F , ddr30 , ddr31 , ddr32 , ddr33 , ddr34 , ddr35 , ddr36 , ddr37 , ddr38 , ddr39 , ddr3A , ddr3B , ddr3C , ddr3D , ddr3E , ddr3F , ddr40 , ddr41 , ddr42 , ddr43 , ddr44 , ddr45 , ddr46 , ddr47 , ddr48 , ddr49 , ddr4A , ddr4B , ddr4C , ddr4D , ddr4E , ddr4F , ddr50 , ddr51 , ddr52 , ddr53 , ddr54 , ddr55 , ddr56 , ddr57 , ddr58 , ddr59 , ddr5A , ddr5B , ddr5C , ddr5D , ddr5E , ddr5F , ddr60 , ddr61 , ddr62 , ddr63 , ddr64 , ddr65 , ddr66 , ddr67 , ddr68 , ddr69 , ddr6A , ddr6B , ddr6C , ddr6D , ddr6E , ddr6F , ddr70 , ddr71 , ddr72 , ddr73 , ddr74 , ddr75 , ddr76 , ddr77 , ddr78 , ddr79 , ddr7A , ddr7B , ddr7C , ddr7D , ddr7E , ddr7F , ddr80 , ddr81 , ddr82 , ddr83 , ddr84 , ddr85 , ddr86 , ddr87 , ddr88 , ddr89 , ddr8A , ddr8B , ddr8C , ddr8D , ddr8E , ddr8F , ddr90 , ddr91 , ddr92 , ddr93 , ddr94 , ddr95 , ddr96 , ddr97 , ddr98 , ddr99 , ddr9A , ddr9B , ddr9C , ddr9D , ddr9E , ddr9F , ddrA0 , ddrA1 , ddrA2 , ddrA3 , ddrA4 , ddrA5 , ddrA6 , ddrA7 , ddrA8 , ddrA9 , ddrAA , ddrAB , ddrAC , ddrAD , ddrAE , ddrAF , ddrB0 , ddrB1 , ddrB2 , ddrB3 , ddrB4 , ddrB5 , ddrB6 , ddrB7 , ddrB8 , ddrB9 , ddrBA , ddrBB , ddrBC , ddrBD , ddrBE , ddrBF , ddrC0 , ddrC1 , ddrC2 , ddrC3 , ddrC4 , ddrC5 , ddrC6 , ddrC7 , ddrC8 , ddrC9 , ddrCA , ddrCB , ddrCC , ddrCD , ddrCE , ddrCF , ddrD0 , ddrD1 , ddrD2 , ddrD3 , ddrD4 , ddrD5 , ddrD6 , ddrD7 , ddrD8 , ddrD9 , ddrDA , ddrDB , ddrDC , ddrDD , ddrDE , ddrDF , ddrE0 , ddrE1 , ddrE2 , ddrE3 , ddrE4 , ddrE5 , ddrE6 , ddrE7 , ddrE8 , ddrE9 , ddrEA , ddrEB , ddrEC , ddrED , ddrEE , ddrEF , ddrF0 , ddrF1 , ddrF2 , ddrF3 , ddrF4 , ddrF5 , ddrF6 , ddrF7 , ddrF8 , ddrF9 , ddrFA , ddrFB , ddrFC , ddrFD , ddrFE , ddrFF <] .
Lemma ElectionParams_ι_ValidatorDescr73_ι_adnl_addr_bs_id: ElectionParams_ι_ValidatorDescr73_ι_adnl_addr_bs_def = [> ddr00 , ddr01 , ddr02 , ddr03 , ddr04 , ddr05 , ddr06 , ddr07 , ddr08 , ddr09 , ddr0A , ddr0B , ddr0C , ddr0D , ddr0E , ddr0F , ddr10 , ddr11 , ddr12 , ddr13 , ddr14 , ddr15 , ddr16 , ddr17 , ddr18 , ddr19 , ddr1A , ddr1B , ddr1C , ddr1D , ddr1E , ddr1F , ddr20 , ddr21 , ddr22 , ddr23 , ddr24 , ddr25 , ddr26 , ddr27 , ddr28 , ddr29 , ddr2A , ddr2B , ddr2C , ddr2D , ddr2E , ddr2F , ddr30 , ddr31 , ddr32 , ddr33 , ddr34 , ddr35 , ddr36 , ddr37 , ddr38 , ddr39 , ddr3A , ddr3B , ddr3C , ddr3D , ddr3E , ddr3F , ddr40 , ddr41 , ddr42 , ddr43 , ddr44 , ddr45 , ddr46 , ddr47 , ddr48 , ddr49 , ddr4A , ddr4B , ddr4C , ddr4D , ddr4E , ddr4F , ddr50 , ddr51 , ddr52 , ddr53 , ddr54 , ddr55 , ddr56 , ddr57 , ddr58 , ddr59 , ddr5A , ddr5B , ddr5C , ddr5D , ddr5E , ddr5F , ddr60 , ddr61 , ddr62 , ddr63 , ddr64 , ddr65 , ddr66 , ddr67 , ddr68 , ddr69 , ddr6A , ddr6B , ddr6C , ddr6D , ddr6E , ddr6F , ddr70 , ddr71 , ddr72 , ddr73 , ddr74 , ddr75 , ddr76 , ddr77 , ddr78 , ddr79 , ddr7A , ddr7B , ddr7C , ddr7D , ddr7E , ddr7F , ddr80 , ddr81 , ddr82 , ddr83 , ddr84 , ddr85 , ddr86 , ddr87 , ddr88 , ddr89 , ddr8A , ddr8B , ddr8C , ddr8D , ddr8E , ddr8F , ddr90 , ddr91 , ddr92 , ddr93 , ddr94 , ddr95 , ddr96 , ddr97 , ddr98 , ddr99 , ddr9A , ddr9B , ddr9C , ddr9D , ddr9E , ddr9F , ddrA0 , ddrA1 , ddrA2 , ddrA3 , ddrA4 , ddrA5 , ddrA6 , ddrA7 , ddrA8 , ddrA9 , ddrAA , ddrAB , ddrAC , ddrAD , ddrAE , ddrAF , ddrB0 , ddrB1 , ddrB2 , ddrB3 , ddrB4 , ddrB5 , ddrB6 , ddrB7 , ddrB8 , ddrB9 , ddrBA , ddrBB , ddrBC , ddrBD , ddrBE , ddrBF , ddrC0 , ddrC1 , ddrC2 , ddrC3 , ddrC4 , ddrC5 , ddrC6 , ddrC7 , ddrC8 , ddrC9 , ddrCA , ddrCB , ddrCC , ddrCD , ddrCE , ddrCF , ddrD0 , ddrD1 , ddrD2 , ddrD3 , ddrD4 , ddrD5 , ddrD6 , ddrD7 , ddrD8 , ddrD9 , ddrDA , ddrDB , ddrDC , ddrDD , ddrDE , ddrDF , ddrE0 , ddrE1 , ddrE2 , ddrE3 , ddrE4 , ddrE5 , ddrE6 , ddrE7 , ddrE8 , ddrE9 , ddrEA , ddrEB , ddrEC , ddrED , ddrEE , ddrEF , ddrF0 , ddrF1 , ddrF2 , ddrF3 , ddrF4 , ddrF5 , ddrF6 , ddrF7 , ddrF8 , ddrF9 , ddrFA , ddrFB , ddrFC , ddrFD , ddrFE , ddrFF <] .
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
Variables ttlSt00 ttlSt01 ttlSt02 ttlSt03 ttlSt04 ttlSt05 ttlSt06 ttlSt07 ttlSt08 ttlSt09 ttlSt0A ttlSt0B ttlSt0C ttlSt0D ttlSt0E ttlSt0F ttlSt10 ttlSt11 ttlSt12 ttlSt13 ttlSt14 ttlSt15 ttlSt16 ttlSt17 ttlSt18 ttlSt19 ttlSt1A ttlSt1B ttlSt1C ttlSt1D ttlSt1E ttlSt1F ttlSt20 ttlSt21 ttlSt22 ttlSt23 ttlSt24 ttlSt25 ttlSt26 ttlSt27 ttlSt28 ttlSt29 ttlSt2A ttlSt2B ttlSt2C ttlSt2D ttlSt2E ttlSt2F ttlSt30 ttlSt31 ttlSt32 ttlSt33 ttlSt34 ttlSt35 ttlSt36 ttlSt37 ttlSt38 ttlSt39 ttlSt3A ttlSt3B ttlSt3C ttlSt3D ttlSt3E ttlSt3F  : TVMBit . 
Definition StakeholderBase_ι_Stakeholder_ι_totalStake_bs_def := [> ttlSt00 , ttlSt01 , ttlSt02 , ttlSt03 , ttlSt04 , ttlSt05 , ttlSt06 , ttlSt07 , ttlSt08 , ttlSt09 , ttlSt0A , ttlSt0B , ttlSt0C , ttlSt0D , ttlSt0E , ttlSt0F , ttlSt10 , ttlSt11 , ttlSt12 , ttlSt13 , ttlSt14 , ttlSt15 , ttlSt16 , ttlSt17 , ttlSt18 , ttlSt19 , ttlSt1A , ttlSt1B , ttlSt1C , ttlSt1D , ttlSt1E , ttlSt1F , ttlSt20 , ttlSt21 , ttlSt22 , ttlSt23 , ttlSt24 , ttlSt25 , ttlSt26 , ttlSt27 , ttlSt28 , ttlSt29 , ttlSt2A , ttlSt2B , ttlSt2C , ttlSt2D , ttlSt2E , ttlSt2F , ttlSt30 , ttlSt31 , ttlSt32 , ttlSt33 , ttlSt34 , ttlSt35 , ttlSt36 , ttlSt37 , ttlSt38 , ttlSt39 , ttlSt3A , ttlSt3B , ttlSt3C , ttlSt3D , ttlSt3E , ttlSt3F <] .
Lemma StakeholderBase_ι_Stakeholder_ι_totalStake_bs_id: StakeholderBase_ι_Stakeholder_ι_totalStake_bs_def = [> ttlSt00 , ttlSt01 , ttlSt02 , ttlSt03 , ttlSt04 , ttlSt05 , ttlSt06 , ttlSt07 , ttlSt08 , ttlSt09 , ttlSt0A , ttlSt0B , ttlSt0C , ttlSt0D , ttlSt0E , ttlSt0F , ttlSt10 , ttlSt11 , ttlSt12 , ttlSt13 , ttlSt14 , ttlSt15 , ttlSt16 , ttlSt17 , ttlSt18 , ttlSt19 , ttlSt1A , ttlSt1B , ttlSt1C , ttlSt1D , ttlSt1E , ttlSt1F , ttlSt20 , ttlSt21 , ttlSt22 , ttlSt23 , ttlSt24 , ttlSt25 , ttlSt26 , ttlSt27 , ttlSt28 , ttlSt29 , ttlSt2A , ttlSt2B , ttlSt2C , ttlSt2D , ttlSt2E , ttlSt2F , ttlSt30 , ttlSt31 , ttlSt32 , ttlSt33 , ttlSt34 , ttlSt35 , ttlSt36 , ttlSt37 , ttlSt38 , ttlSt39 , ttlSt3A , ttlSt3B , ttlSt3C , ttlSt3D , ttlSt3E , ttlSt3F <] .
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
Qed. Variables StakeholderBase_ι_Stakeholder_ι_unusedStake : Z . 
Variables nsdSt00 nsdSt01 nsdSt02 nsdSt03 nsdSt04 nsdSt05 nsdSt06 nsdSt07 nsdSt08 nsdSt09 nsdSt0A nsdSt0B nsdSt0C nsdSt0D nsdSt0E nsdSt0F nsdSt10 nsdSt11 nsdSt12 nsdSt13 nsdSt14 nsdSt15 nsdSt16 nsdSt17 nsdSt18 nsdSt19 nsdSt1A nsdSt1B nsdSt1C nsdSt1D nsdSt1E nsdSt1F nsdSt20 nsdSt21 nsdSt22 nsdSt23 nsdSt24 nsdSt25 nsdSt26 nsdSt27 nsdSt28 nsdSt29 nsdSt2A nsdSt2B nsdSt2C nsdSt2D nsdSt2E nsdSt2F nsdSt30 nsdSt31 nsdSt32 nsdSt33 nsdSt34 nsdSt35 nsdSt36 nsdSt37 nsdSt38 nsdSt39 nsdSt3A nsdSt3B nsdSt3C nsdSt3D nsdSt3E nsdSt3F  : TVMBit . 
Definition StakeholderBase_ι_Stakeholder_ι_unusedStake_bs_def := [> nsdSt00 , nsdSt01 , nsdSt02 , nsdSt03 , nsdSt04 , nsdSt05 , nsdSt06 , nsdSt07 , nsdSt08 , nsdSt09 , nsdSt0A , nsdSt0B , nsdSt0C , nsdSt0D , nsdSt0E , nsdSt0F , nsdSt10 , nsdSt11 , nsdSt12 , nsdSt13 , nsdSt14 , nsdSt15 , nsdSt16 , nsdSt17 , nsdSt18 , nsdSt19 , nsdSt1A , nsdSt1B , nsdSt1C , nsdSt1D , nsdSt1E , nsdSt1F , nsdSt20 , nsdSt21 , nsdSt22 , nsdSt23 , nsdSt24 , nsdSt25 , nsdSt26 , nsdSt27 , nsdSt28 , nsdSt29 , nsdSt2A , nsdSt2B , nsdSt2C , nsdSt2D , nsdSt2E , nsdSt2F , nsdSt30 , nsdSt31 , nsdSt32 , nsdSt33 , nsdSt34 , nsdSt35 , nsdSt36 , nsdSt37 , nsdSt38 , nsdSt39 , nsdSt3A , nsdSt3B , nsdSt3C , nsdSt3D , nsdSt3E , nsdSt3F <] .
Lemma StakeholderBase_ι_Stakeholder_ι_unusedStake_bs_id: StakeholderBase_ι_Stakeholder_ι_unusedStake_bs_def = [> nsdSt00 , nsdSt01 , nsdSt02 , nsdSt03 , nsdSt04 , nsdSt05 , nsdSt06 , nsdSt07 , nsdSt08 , nsdSt09 , nsdSt0A , nsdSt0B , nsdSt0C , nsdSt0D , nsdSt0E , nsdSt0F , nsdSt10 , nsdSt11 , nsdSt12 , nsdSt13 , nsdSt14 , nsdSt15 , nsdSt16 , nsdSt17 , nsdSt18 , nsdSt19 , nsdSt1A , nsdSt1B , nsdSt1C , nsdSt1D , nsdSt1E , nsdSt1F , nsdSt20 , nsdSt21 , nsdSt22 , nsdSt23 , nsdSt24 , nsdSt25 , nsdSt26 , nsdSt27 , nsdSt28 , nsdSt29 , nsdSt2A , nsdSt2B , nsdSt2C , nsdSt2D , nsdSt2E , nsdSt2F , nsdSt30 , nsdSt31 , nsdSt32 , nsdSt33 , nsdSt34 , nsdSt35 , nsdSt36 , nsdSt37 , nsdSt38 , nsdSt39 , nsdSt3A , nsdSt3B , nsdSt3C , nsdSt3D , nsdSt3E , nsdSt3F <] .
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
Qed.  Variables StakeholderBase_ι_Stakeholder_ι_reward : Z . 
Variables rwrd00 rwrd01 rwrd02 rwrd03 rwrd04 rwrd05 rwrd06 rwrd07 rwrd08 rwrd09 rwrd0A rwrd0B rwrd0C rwrd0D rwrd0E rwrd0F rwrd10 rwrd11 rwrd12 rwrd13 rwrd14 rwrd15 rwrd16 rwrd17 rwrd18 rwrd19 rwrd1A rwrd1B rwrd1C rwrd1D rwrd1E rwrd1F rwrd20 rwrd21 rwrd22 rwrd23 rwrd24 rwrd25 rwrd26 rwrd27 rwrd28 rwrd29 rwrd2A rwrd2B rwrd2C rwrd2D rwrd2E rwrd2F rwrd30 rwrd31 rwrd32 rwrd33 rwrd34 rwrd35 rwrd36 rwrd37 rwrd38 rwrd39 rwrd3A rwrd3B rwrd3C rwrd3D rwrd3E rwrd3F  : TVMBit . 
Definition StakeholderBase_ι_Stakeholder_ι_reward_bs_def := [> rwrd00 , rwrd01 , rwrd02 , rwrd03 , rwrd04 , rwrd05 , rwrd06 , rwrd07 , rwrd08 , rwrd09 , rwrd0A , rwrd0B , rwrd0C , rwrd0D , rwrd0E , rwrd0F , rwrd10 , rwrd11 , rwrd12 , rwrd13 , rwrd14 , rwrd15 , rwrd16 , rwrd17 , rwrd18 , rwrd19 , rwrd1A , rwrd1B , rwrd1C , rwrd1D , rwrd1E , rwrd1F , rwrd20 , rwrd21 , rwrd22 , rwrd23 , rwrd24 , rwrd25 , rwrd26 , rwrd27 , rwrd28 , rwrd29 , rwrd2A , rwrd2B , rwrd2C , rwrd2D , rwrd2E , rwrd2F , rwrd30 , rwrd31 , rwrd32 , rwrd33 , rwrd34 , rwrd35 , rwrd36 , rwrd37 , rwrd38 , rwrd39 , rwrd3A , rwrd3B , rwrd3C , rwrd3D , rwrd3E , rwrd3F <] .
Lemma StakeholderBase_ι_Stakeholder_ι_reward_bs_id: StakeholderBase_ι_Stakeholder_ι_reward_bs_def = [> rwrd00 , rwrd01 , rwrd02 , rwrd03 , rwrd04 , rwrd05 , rwrd06 , rwrd07 , rwrd08 , rwrd09 , rwrd0A , rwrd0B , rwrd0C , rwrd0D , rwrd0E , rwrd0F , rwrd10 , rwrd11 , rwrd12 , rwrd13 , rwrd14 , rwrd15 , rwrd16 , rwrd17 , rwrd18 , rwrd19 , rwrd1A , rwrd1B , rwrd1C , rwrd1D , rwrd1E , rwrd1F , rwrd20 , rwrd21 , rwrd22 , rwrd23 , rwrd24 , rwrd25 , rwrd26 , rwrd27 , rwrd28 , rwrd29 , rwrd2A , rwrd2B , rwrd2C , rwrd2D , rwrd2E , rwrd2F , rwrd30 , rwrd31 , rwrd32 , rwrd33 , rwrd34 , rwrd35 , rwrd36 , rwrd37 , rwrd38 , rwrd39 , rwrd3A , rwrd3B , rwrd3C , rwrd3D , rwrd3E , rwrd3F <] .
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
Variables d00 d01 d02 d03 d04 d05 d06 d07 d08 d09 d0A d0B d0C d0D d0E d0F d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d1A d1B d1C d1D d1E d1F  : TVMBit . 
Definition RoundsBase_ι_Round_ι_id_bs_def := [> d00 , d01 , d02 , d03 , d04 , d05 , d06 , d07 , d08 , d09 , d0A , d0B , d0C , d0D , d0E , d0F , d10 , d11 , d12 , d13 , d14 , d15 , d16 , d17 , d18 , d19 , d1A , d1B , d1C , d1D , d1E , d1F <] .
Lemma RoundsBase_ι_Round_ι_id_bs_id: RoundsBase_ι_Round_ι_id_bs_def = [> d00 , d01 , d02 , d03 , d04 , d05 , d06 , d07 , d08 , d09 , d0A , d0B , d0C , d0D , d0E , d0F , d10 , d11 , d12 , d13 , d14 , d15 , d16 , d17 , d18 , d19 , d1A , d1B , d1C , d1D , d1E , d1F <] .
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
Qed. Variables RoundsBase_ι_Round_ι_step : Z . 
Variables stp00 stp01 stp02 stp03 stp04 stp05 stp06 stp07  : TVMBit . 
Definition RoundsBase_ι_Round_ι_step_bs_def := [> stp00 , stp01 , stp02 , stp03 , stp04 , stp05 , stp06 , stp07 <] .
Lemma RoundsBase_ι_Round_ι_step_bs_id: RoundsBase_ι_Round_ι_step_bs_def = [> stp00 , stp01 , stp02 , stp03 , stp04 , stp05 , stp06 , stp07 <] .
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
Qed. Variables RoundsBase_ι_Round_ι_count : Z . 
Variables cnt00 cnt01 cnt02 cnt03 cnt04 cnt05 cnt06 cnt07 cnt08 cnt09 cnt0A cnt0B cnt0C cnt0D cnt0E cnt0F cnt10 cnt11 cnt12 cnt13 cnt14 cnt15 cnt16 cnt17 cnt18 cnt19 cnt1A cnt1B cnt1C cnt1D cnt1E cnt1F  : TVMBit . 
Definition RoundsBase_ι_Round_ι_count_bs_def := [> cnt00 , cnt01 , cnt02 , cnt03 , cnt04 , cnt05 , cnt06 , cnt07 , cnt08 , cnt09 , cnt0A , cnt0B , cnt0C , cnt0D , cnt0E , cnt0F , cnt10 , cnt11 , cnt12 , cnt13 , cnt14 , cnt15 , cnt16 , cnt17 , cnt18 , cnt19 , cnt1A , cnt1B , cnt1C , cnt1D , cnt1E , cnt1F <] .
Lemma RoundsBase_ι_Round_ι_count_bs_id: RoundsBase_ι_Round_ι_count_bs_def = [> cnt00 , cnt01 , cnt02 , cnt03 , cnt04 , cnt05 , cnt06 , cnt07 , cnt08 , cnt09 , cnt0A , cnt0B , cnt0C , cnt0D , cnt0E , cnt0F , cnt10 , cnt11 , cnt12 , cnt13 , cnt14 , cnt15 , cnt16 , cnt17 , cnt18 , cnt19 , cnt1A , cnt1B , cnt1C , cnt1D , cnt1E , cnt1F <] .
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
Qed. Variables RoundsBase_ι_Round_ι_totalStake : Z . 
Variables ttlSt00 ttlSt01 ttlSt02 ttlSt03 ttlSt04 ttlSt05 ttlSt06 ttlSt07 ttlSt08 ttlSt09 ttlSt0A ttlSt0B ttlSt0C ttlSt0D ttlSt0E ttlSt0F ttlSt10 ttlSt11 ttlSt12 ttlSt13 ttlSt14 ttlSt15 ttlSt16 ttlSt17 ttlSt18 ttlSt19 ttlSt1A ttlSt1B ttlSt1C ttlSt1D ttlSt1E ttlSt1F ttlSt20 ttlSt21 ttlSt22 ttlSt23 ttlSt24 ttlSt25 ttlSt26 ttlSt27 ttlSt28 ttlSt29 ttlSt2A ttlSt2B ttlSt2C ttlSt2D ttlSt2E ttlSt2F ttlSt30 ttlSt31 ttlSt32 ttlSt33 ttlSt34 ttlSt35 ttlSt36 ttlSt37 ttlSt38 ttlSt39 ttlSt3A ttlSt3B ttlSt3C ttlSt3D ttlSt3E ttlSt3F  : TVMBit . 
Definition RoundsBase_ι_Round_ι_totalStake_bs_def := [> ttlSt00 , ttlSt01 , ttlSt02 , ttlSt03 , ttlSt04 , ttlSt05 , ttlSt06 , ttlSt07 , ttlSt08 , ttlSt09 , ttlSt0A , ttlSt0B , ttlSt0C , ttlSt0D , ttlSt0E , ttlSt0F , ttlSt10 , ttlSt11 , ttlSt12 , ttlSt13 , ttlSt14 , ttlSt15 , ttlSt16 , ttlSt17 , ttlSt18 , ttlSt19 , ttlSt1A , ttlSt1B , ttlSt1C , ttlSt1D , ttlSt1E , ttlSt1F , ttlSt20 , ttlSt21 , ttlSt22 , ttlSt23 , ttlSt24 , ttlSt25 , ttlSt26 , ttlSt27 , ttlSt28 , ttlSt29 , ttlSt2A , ttlSt2B , ttlSt2C , ttlSt2D , ttlSt2E , ttlSt2F , ttlSt30 , ttlSt31 , ttlSt32 , ttlSt33 , ttlSt34 , ttlSt35 , ttlSt36 , ttlSt37 , ttlSt38 , ttlSt39 , ttlSt3A , ttlSt3B , ttlSt3C , ttlSt3D , ttlSt3E , ttlSt3F <] .
Lemma RoundsBase_ι_Round_ι_totalStake_bs_id: RoundsBase_ι_Round_ι_totalStake_bs_def = [> ttlSt00 , ttlSt01 , ttlSt02 , ttlSt03 , ttlSt04 , ttlSt05 , ttlSt06 , ttlSt07 , ttlSt08 , ttlSt09 , ttlSt0A , ttlSt0B , ttlSt0C , ttlSt0D , ttlSt0E , ttlSt0F , ttlSt10 , ttlSt11 , ttlSt12 , ttlSt13 , ttlSt14 , ttlSt15 , ttlSt16 , ttlSt17 , ttlSt18 , ttlSt19 , ttlSt1A , ttlSt1B , ttlSt1C , ttlSt1D , ttlSt1E , ttlSt1F , ttlSt20 , ttlSt21 , ttlSt22 , ttlSt23 , ttlSt24 , ttlSt25 , ttlSt26 , ttlSt27 , ttlSt28 , ttlSt29 , ttlSt2A , ttlSt2B , ttlSt2C , ttlSt2D , ttlSt2E , ttlSt2F , ttlSt30 , ttlSt31 , ttlSt32 , ttlSt33 , ttlSt34 , ttlSt35 , ttlSt36 , ttlSt37 , ttlSt38 , ttlSt39 , ttlSt3A , ttlSt3B , ttlSt3C , ttlSt3D , ttlSt3E , ttlSt3F <] .
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
Qed. Variables RoundsBase_ι_Round_ι_rewards : Z . 
Variables rwrds00 rwrds01 rwrds02 rwrds03 rwrds04 rwrds05 rwrds06 rwrds07 rwrds08 rwrds09 rwrds0A rwrds0B rwrds0C rwrds0D rwrds0E rwrds0F rwrds10 rwrds11 rwrds12 rwrds13 rwrds14 rwrds15 rwrds16 rwrds17 rwrds18 rwrds19 rwrds1A rwrds1B rwrds1C rwrds1D rwrds1E rwrds1F rwrds20 rwrds21 rwrds22 rwrds23 rwrds24 rwrds25 rwrds26 rwrds27 rwrds28 rwrds29 rwrds2A rwrds2B rwrds2C rwrds2D rwrds2E rwrds2F rwrds30 rwrds31 rwrds32 rwrds33 rwrds34 rwrds35 rwrds36 rwrds37 rwrds38 rwrds39 rwrds3A rwrds3B rwrds3C rwrds3D rwrds3E rwrds3F  : TVMBit . 
Definition RoundsBase_ι_Round_ι_rewards_bs_def := [> rwrds00 , rwrds01 , rwrds02 , rwrds03 , rwrds04 , rwrds05 , rwrds06 , rwrds07 , rwrds08 , rwrds09 , rwrds0A , rwrds0B , rwrds0C , rwrds0D , rwrds0E , rwrds0F , rwrds10 , rwrds11 , rwrds12 , rwrds13 , rwrds14 , rwrds15 , rwrds16 , rwrds17 , rwrds18 , rwrds19 , rwrds1A , rwrds1B , rwrds1C , rwrds1D , rwrds1E , rwrds1F , rwrds20 , rwrds21 , rwrds22 , rwrds23 , rwrds24 , rwrds25 , rwrds26 , rwrds27 , rwrds28 , rwrds29 , rwrds2A , rwrds2B , rwrds2C , rwrds2D , rwrds2E , rwrds2F , rwrds30 , rwrds31 , rwrds32 , rwrds33 , rwrds34 , rwrds35 , rwrds36 , rwrds37 , rwrds38 , rwrds39 , rwrds3A , rwrds3B , rwrds3C , rwrds3D , rwrds3E , rwrds3F <] .
Lemma RoundsBase_ι_Round_ι_rewards_bs_id: RoundsBase_ι_Round_ι_rewards_bs_def = [> rwrds00 , rwrds01 , rwrds02 , rwrds03 , rwrds04 , rwrds05 , rwrds06 , rwrds07 , rwrds08 , rwrds09 , rwrds0A , rwrds0B , rwrds0C , rwrds0D , rwrds0E , rwrds0F , rwrds10 , rwrds11 , rwrds12 , rwrds13 , rwrds14 , rwrds15 , rwrds16 , rwrds17 , rwrds18 , rwrds19 , rwrds1A , rwrds1B , rwrds1C , rwrds1D , rwrds1E , rwrds1F , rwrds20 , rwrds21 , rwrds22 , rwrds23 , rwrds24 , rwrds25 , rwrds26 , rwrds27 , rwrds28 , rwrds29 , rwrds2A , rwrds2B , rwrds2C , rwrds2D , rwrds2E , rwrds2F , rwrds30 , rwrds31 , rwrds32 , rwrds33 , rwrds34 , rwrds35 , rwrds36 , rwrds37 , rwrds38 , rwrds39 , rwrds3A , rwrds3B , rwrds3C , rwrds3D , rwrds3E , rwrds3F <] .
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
Qed. Variables RoundsBase_ι_Round_ι_unused : Z . 
Variables nsd00 nsd01 nsd02 nsd03 nsd04 nsd05 nsd06 nsd07 nsd08 nsd09 nsd0A nsd0B nsd0C nsd0D nsd0E nsd0F nsd10 nsd11 nsd12 nsd13 nsd14 nsd15 nsd16 nsd17 nsd18 nsd19 nsd1A nsd1B nsd1C nsd1D nsd1E nsd1F nsd20 nsd21 nsd22 nsd23 nsd24 nsd25 nsd26 nsd27 nsd28 nsd29 nsd2A nsd2B nsd2C nsd2D nsd2E nsd2F nsd30 nsd31 nsd32 nsd33 nsd34 nsd35 nsd36 nsd37 nsd38 nsd39 nsd3A nsd3B nsd3C nsd3D nsd3E nsd3F  : TVMBit . 
Definition RoundsBase_ι_Round_ι_unused_bs_def := [> nsd00 , nsd01 , nsd02 , nsd03 , nsd04 , nsd05 , nsd06 , nsd07 , nsd08 , nsd09 , nsd0A , nsd0B , nsd0C , nsd0D , nsd0E , nsd0F , nsd10 , nsd11 , nsd12 , nsd13 , nsd14 , nsd15 , nsd16 , nsd17 , nsd18 , nsd19 , nsd1A , nsd1B , nsd1C , nsd1D , nsd1E , nsd1F , nsd20 , nsd21 , nsd22 , nsd23 , nsd24 , nsd25 , nsd26 , nsd27 , nsd28 , nsd29 , nsd2A , nsd2B , nsd2C , nsd2D , nsd2E , nsd2F , nsd30 , nsd31 , nsd32 , nsd33 , nsd34 , nsd35 , nsd36 , nsd37 , nsd38 , nsd39 , nsd3A , nsd3B , nsd3C , nsd3D , nsd3E , nsd3F <] .
Lemma RoundsBase_ι_Round_ι_unused_bs_id: RoundsBase_ι_Round_ι_unused_bs_def = [> nsd00 , nsd01 , nsd02 , nsd03 , nsd04 , nsd05 , nsd06 , nsd07 , nsd08 , nsd09 , nsd0A , nsd0B , nsd0C , nsd0D , nsd0E , nsd0F , nsd10 , nsd11 , nsd12 , nsd13 , nsd14 , nsd15 , nsd16 , nsd17 , nsd18 , nsd19 , nsd1A , nsd1B , nsd1C , nsd1D , nsd1E , nsd1F , nsd20 , nsd21 , nsd22 , nsd23 , nsd24 , nsd25 , nsd26 , nsd27 , nsd28 , nsd29 , nsd2A , nsd2B , nsd2C , nsd2D , nsd2E , nsd2F , nsd30 , nsd31 , nsd32 , nsd33 , nsd34 , nsd35 , nsd36 , nsd37 , nsd38 , nsd39 , nsd3A , nsd3B , nsd3C , nsd3D , nsd3E , nsd3F <] .
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
Qed. Variables RoundsBase_ι_Round_ι_completionStatus : Z . 
Variables cmplt00 cmplt01 cmplt02 cmplt03 cmplt04 cmplt05 cmplt06 cmplt07  : TVMBit . 
Definition RoundsBase_ι_Round_ι_completionStatus_bs_def := [> cmplt00 , cmplt01 , cmplt02 , cmplt03 , cmplt04 , cmplt05 , cmplt06 , cmplt07 <] .
Lemma RoundsBase_ι_Round_ι_completionStatus_bs_id: RoundsBase_ι_Round_ι_completionStatus_bs_def = [> cmplt00 , cmplt01 , cmplt02 , cmplt03 , cmplt04 , cmplt05 , cmplt06 , cmplt07 <] .
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
Qed. Variables RoundsBase_ι_Round_ι_start : Z . 
Variables strt00 strt01 strt02 strt03 strt04 strt05 strt06 strt07 strt08 strt09 strt0A strt0B strt0C strt0D strt0E strt0F strt10 strt11 strt12 strt13 strt14 strt15 strt16 strt17 strt18 strt19 strt1A strt1B strt1C strt1D strt1E strt1F  : TVMBit . 
Definition RoundsBase_ι_Round_ι_start_bs_def := [> strt00 , strt01 , strt02 , strt03 , strt04 , strt05 , strt06 , strt07 , strt08 , strt09 , strt0A , strt0B , strt0C , strt0D , strt0E , strt0F , strt10 , strt11 , strt12 , strt13 , strt14 , strt15 , strt16 , strt17 , strt18 , strt19 , strt1A , strt1B , strt1C , strt1D , strt1E , strt1F <] .
Lemma RoundsBase_ι_Round_ι_start_bs_id: RoundsBase_ι_Round_ι_start_bs_def = [> strt00 , strt01 , strt02 , strt03 , strt04 , strt05 , strt06 , strt07 , strt08 , strt09 , strt0A , strt0B , strt0C , strt0D , strt0E , strt0F , strt10 , strt11 , strt12 , strt13 , strt14 , strt15 , strt16 , strt17 , strt18 , strt19 , strt1A , strt1B , strt1C , strt1D , strt1E , strt1F <] .
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
Qed. Variables RoundsBase_ι_Round_ι_end : Z . 
Variables nd00 nd01 nd02 nd03 nd04 nd05 nd06 nd07 nd08 nd09 nd0A nd0B nd0C nd0D nd0E nd0F nd10 nd11 nd12 nd13 nd14 nd15 nd16 nd17 nd18 nd19 nd1A nd1B nd1C nd1D nd1E nd1F  : TVMBit . 
Definition RoundsBase_ι_Round_ι_end_bs_def := [> nd00 , nd01 , nd02 , nd03 , nd04 , nd05 , nd06 , nd07 , nd08 , nd09 , nd0A , nd0B , nd0C , nd0D , nd0E , nd0F , nd10 , nd11 , nd12 , nd13 , nd14 , nd15 , nd16 , nd17 , nd18 , nd19 , nd1A , nd1B , nd1C , nd1D , nd1E , nd1F <] .
Lemma RoundsBase_ι_Round_ι_end_bs_id: RoundsBase_ι_Round_ι_end_bs_def = [> nd00 , nd01 , nd02 , nd03 , nd04 , nd05 , nd06 , nd07 , nd08 , nd09 , nd0A , nd0B , nd0C , nd0D , nd0E , nd0F , nd10 , nd11 , nd12 , nd13 , nd14 , nd15 , nd16 , nd17 , nd18 , nd19 , nd1A , nd1B , nd1C , nd1D , nd1E , nd1F <] .
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
Variables d00 d01 d02 d03 d04 d05 d06 d07 d08 d09 d0A d0B d0C d0D d0E d0F d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d1A d1B d1C d1D d1E d1F  : TVMBit . 
Definition RoundsBase_ι_RoundInfo_ι_id_bs_def := [> d00 , d01 , d02 , d03 , d04 , d05 , d06 , d07 , d08 , d09 , d0A , d0B , d0C , d0D , d0E , d0F , d10 , d11 , d12 , d13 , d14 , d15 , d16 , d17 , d18 , d19 , d1A , d1B , d1C , d1D , d1E , d1F <] .
Lemma RoundsBase_ι_RoundInfo_ι_id_bs_id: RoundsBase_ι_RoundInfo_ι_id_bs_def = [> d00 , d01 , d02 , d03 , d04 , d05 , d06 , d07 , d08 , d09 , d0A , d0B , d0C , d0D , d0E , d0F , d10 , d11 , d12 , d13 , d14 , d15 , d16 , d17 , d18 , d19 , d1A , d1B , d1C , d1D , d1E , d1F <] .
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
Qed. Variables RoundsBase_ι_RoundInfo_ι_start : Z . 
Variables strt00 strt01 strt02 strt03 strt04 strt05 strt06 strt07 strt08 strt09 strt0A strt0B strt0C strt0D strt0E strt0F strt10 strt11 strt12 strt13 strt14 strt15 strt16 strt17 strt18 strt19 strt1A strt1B strt1C strt1D strt1E strt1F  : TVMBit . 
Definition RoundsBase_ι_RoundInfo_ι_start_bs_def := [> strt00 , strt01 , strt02 , strt03 , strt04 , strt05 , strt06 , strt07 , strt08 , strt09 , strt0A , strt0B , strt0C , strt0D , strt0E , strt0F , strt10 , strt11 , strt12 , strt13 , strt14 , strt15 , strt16 , strt17 , strt18 , strt19 , strt1A , strt1B , strt1C , strt1D , strt1E , strt1F <] .
Lemma RoundsBase_ι_RoundInfo_ι_start_bs_id: RoundsBase_ι_RoundInfo_ι_start_bs_def = [> strt00 , strt01 , strt02 , strt03 , strt04 , strt05 , strt06 , strt07 , strt08 , strt09 , strt0A , strt0B , strt0C , strt0D , strt0E , strt0F , strt10 , strt11 , strt12 , strt13 , strt14 , strt15 , strt16 , strt17 , strt18 , strt19 , strt1A , strt1B , strt1C , strt1D , strt1E , strt1F <] .
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
Qed. Variables RoundsBase_ι_RoundInfo_ι_end : Z . 
Variables nd00 nd01 nd02 nd03 nd04 nd05 nd06 nd07 nd08 nd09 nd0A nd0B nd0C nd0D nd0E nd0F nd10 nd11 nd12 nd13 nd14 nd15 nd16 nd17 nd18 nd19 nd1A nd1B nd1C nd1D nd1E nd1F  : TVMBit . 
Definition RoundsBase_ι_RoundInfo_ι_end_bs_def := [> nd00 , nd01 , nd02 , nd03 , nd04 , nd05 , nd06 , nd07 , nd08 , nd09 , nd0A , nd0B , nd0C , nd0D , nd0E , nd0F , nd10 , nd11 , nd12 , nd13 , nd14 , nd15 , nd16 , nd17 , nd18 , nd19 , nd1A , nd1B , nd1C , nd1D , nd1E , nd1F <] .
Lemma RoundsBase_ι_RoundInfo_ι_end_bs_id: RoundsBase_ι_RoundInfo_ι_end_bs_def = [> nd00 , nd01 , nd02 , nd03 , nd04 , nd05 , nd06 , nd07 , nd08 , nd09 , nd0A , nd0B , nd0C , nd0D , nd0E , nd0F , nd10 , nd11 , nd12 , nd13 , nd14 , nd15 , nd16 , nd17 , nd18 , nd19 , nd1A , nd1B , nd1C , nd1D , nd1E , nd1F <] .
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
Qed. Variables RoundsBase_ι_RoundInfo_ι_step : Z . 
Variables stp00 stp01 stp02 stp03 stp04 stp05 stp06 stp07  : TVMBit . 
Definition RoundsBase_ι_RoundInfo_ι_step_bs_def := [> stp00 , stp01 , stp02 , stp03 , stp04 , stp05 , stp06 , stp07 <] .
Lemma RoundsBase_ι_RoundInfo_ι_step_bs_id: RoundsBase_ι_RoundInfo_ι_step_bs_def = [> stp00 , stp01 , stp02 , stp03 , stp04 , stp05 , stp06 , stp07 <] .
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
Qed. Variables RoundsBase_ι_RoundInfo_ι_completionStatus : Z . 
Variables cmplt00 cmplt01 cmplt02 cmplt03 cmplt04 cmplt05 cmplt06 cmplt07  : TVMBit . 
Definition RoundsBase_ι_RoundInfo_ι_completionStatus_bs_def := [> cmplt00 , cmplt01 , cmplt02 , cmplt03 , cmplt04 , cmplt05 , cmplt06 , cmplt07 <] .
Lemma RoundsBase_ι_RoundInfo_ι_completionStatus_bs_id: RoundsBase_ι_RoundInfo_ι_completionStatus_bs_def = [> cmplt00 , cmplt01 , cmplt02 , cmplt03 , cmplt04 , cmplt05 , cmplt06 , cmplt07 <] .
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
Qed. Variables RoundsBase_ι_RoundInfo_ι_stake : Z . 
Variables stk00 stk01 stk02 stk03 stk04 stk05 stk06 stk07 stk08 stk09 stk0A stk0B stk0C stk0D stk0E stk0F stk10 stk11 stk12 stk13 stk14 stk15 stk16 stk17 stk18 stk19 stk1A stk1B stk1C stk1D stk1E stk1F stk20 stk21 stk22 stk23 stk24 stk25 stk26 stk27 stk28 stk29 stk2A stk2B stk2C stk2D stk2E stk2F stk30 stk31 stk32 stk33 stk34 stk35 stk36 stk37 stk38 stk39 stk3A stk3B stk3C stk3D stk3E stk3F  : TVMBit . 
Definition RoundsBase_ι_RoundInfo_ι_stake_bs_def := [> stk00 , stk01 , stk02 , stk03 , stk04 , stk05 , stk06 , stk07 , stk08 , stk09 , stk0A , stk0B , stk0C , stk0D , stk0E , stk0F , stk10 , stk11 , stk12 , stk13 , stk14 , stk15 , stk16 , stk17 , stk18 , stk19 , stk1A , stk1B , stk1C , stk1D , stk1E , stk1F , stk20 , stk21 , stk22 , stk23 , stk24 , stk25 , stk26 , stk27 , stk28 , stk29 , stk2A , stk2B , stk2C , stk2D , stk2E , stk2F , stk30 , stk31 , stk32 , stk33 , stk34 , stk35 , stk36 , stk37 , stk38 , stk39 , stk3A , stk3B , stk3C , stk3D , stk3E , stk3F <] .
Lemma RoundsBase_ι_RoundInfo_ι_stake_bs_id: RoundsBase_ι_RoundInfo_ι_stake_bs_def = [> stk00 , stk01 , stk02 , stk03 , stk04 , stk05 , stk06 , stk07 , stk08 , stk09 , stk0A , stk0B , stk0C , stk0D , stk0E , stk0F , stk10 , stk11 , stk12 , stk13 , stk14 , stk15 , stk16 , stk17 , stk18 , stk19 , stk1A , stk1B , stk1C , stk1D , stk1E , stk1F , stk20 , stk21 , stk22 , stk23 , stk24 , stk25 , stk26 , stk27 , stk28 , stk29 , stk2A , stk2B , stk2C , stk2D , stk2E , stk2F , stk30 , stk31 , stk32 , stk33 , stk34 , stk35 , stk36 , stk37 , stk38 , stk39 , stk3A , stk3B , stk3C , stk3D , stk3E , stk3F <] .
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
Qed. Variables RoundsBase_ι_RoundInfo_ι_stakeholderCount : Z . 
Variables stkhl00 stkhl01 stkhl02 stkhl03 stkhl04 stkhl05 stkhl06 stkhl07 stkhl08 stkhl09 stkhl0A stkhl0B stkhl0C stkhl0D stkhl0E stkhl0F stkhl10 stkhl11 stkhl12 stkhl13 stkhl14 stkhl15 stkhl16 stkhl17 stkhl18 stkhl19 stkhl1A stkhl1B stkhl1C stkhl1D stkhl1E stkhl1F  : TVMBit . 
Definition RoundsBase_ι_RoundInfo_ι_stakeholderCount_bs_def := [> stkhl00 , stkhl01 , stkhl02 , stkhl03 , stkhl04 , stkhl05 , stkhl06 , stkhl07 , stkhl08 , stkhl09 , stkhl0A , stkhl0B , stkhl0C , stkhl0D , stkhl0E , stkhl0F , stkhl10 , stkhl11 , stkhl12 , stkhl13 , stkhl14 , stkhl15 , stkhl16 , stkhl17 , stkhl18 , stkhl19 , stkhl1A , stkhl1B , stkhl1C , stkhl1D , stkhl1E , stkhl1F <] .
Lemma RoundsBase_ι_RoundInfo_ι_stakeholderCount_bs_id: RoundsBase_ι_RoundInfo_ι_stakeholderCount_bs_def = [> stkhl00 , stkhl01 , stkhl02 , stkhl03 , stkhl04 , stkhl05 , stkhl06 , stkhl07 , stkhl08 , stkhl09 , stkhl0A , stkhl0B , stkhl0C , stkhl0D , stkhl0E , stkhl0F , stkhl10 , stkhl11 , stkhl12 , stkhl13 , stkhl14 , stkhl15 , stkhl16 , stkhl17 , stkhl18 , stkhl19 , stkhl1A , stkhl1B , stkhl1C , stkhl1D , stkhl1E , stkhl1F <] .
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
Qed. Variables RoundsBase_ι_RoundInfo_ι_rewards : Z . 
Variables rwrds00 rwrds01 rwrds02 rwrds03 rwrds04 rwrds05 rwrds06 rwrds07 rwrds08 rwrds09 rwrds0A rwrds0B rwrds0C rwrds0D rwrds0E rwrds0F rwrds10 rwrds11 rwrds12 rwrds13 rwrds14 rwrds15 rwrds16 rwrds17 rwrds18 rwrds19 rwrds1A rwrds1B rwrds1C rwrds1D rwrds1E rwrds1F rwrds20 rwrds21 rwrds22 rwrds23 rwrds24 rwrds25 rwrds26 rwrds27 rwrds28 rwrds29 rwrds2A rwrds2B rwrds2C rwrds2D rwrds2E rwrds2F rwrds30 rwrds31 rwrds32 rwrds33 rwrds34 rwrds35 rwrds36 rwrds37 rwrds38 rwrds39 rwrds3A rwrds3B rwrds3C rwrds3D rwrds3E rwrds3F  : TVMBit . 
Definition RoundsBase_ι_RoundInfo_ι_rewards_bs_def := [> rwrds00 , rwrds01 , rwrds02 , rwrds03 , rwrds04 , rwrds05 , rwrds06 , rwrds07 , rwrds08 , rwrds09 , rwrds0A , rwrds0B , rwrds0C , rwrds0D , rwrds0E , rwrds0F , rwrds10 , rwrds11 , rwrds12 , rwrds13 , rwrds14 , rwrds15 , rwrds16 , rwrds17 , rwrds18 , rwrds19 , rwrds1A , rwrds1B , rwrds1C , rwrds1D , rwrds1E , rwrds1F , rwrds20 , rwrds21 , rwrds22 , rwrds23 , rwrds24 , rwrds25 , rwrds26 , rwrds27 , rwrds28 , rwrds29 , rwrds2A , rwrds2B , rwrds2C , rwrds2D , rwrds2E , rwrds2F , rwrds30 , rwrds31 , rwrds32 , rwrds33 , rwrds34 , rwrds35 , rwrds36 , rwrds37 , rwrds38 , rwrds39 , rwrds3A , rwrds3B , rwrds3C , rwrds3D , rwrds3E , rwrds3F <] .
Lemma RoundsBase_ι_RoundInfo_ι_rewards_bs_id: RoundsBase_ι_RoundInfo_ι_rewards_bs_def = [> rwrds00 , rwrds01 , rwrds02 , rwrds03 , rwrds04 , rwrds05 , rwrds06 , rwrds07 , rwrds08 , rwrds09 , rwrds0A , rwrds0B , rwrds0C , rwrds0D , rwrds0E , rwrds0F , rwrds10 , rwrds11 , rwrds12 , rwrds13 , rwrds14 , rwrds15 , rwrds16 , rwrds17 , rwrds18 , rwrds19 , rwrds1A , rwrds1B , rwrds1C , rwrds1D , rwrds1E , rwrds1F , rwrds20 , rwrds21 , rwrds22 , rwrds23 , rwrds24 , rwrds25 , rwrds26 , rwrds27 , rwrds28 , rwrds29 , rwrds2A , rwrds2B , rwrds2C , rwrds2D , rwrds2E , rwrds2F , rwrds30 , rwrds31 , rwrds32 , rwrds33 , rwrds34 , rwrds35 , rwrds36 , rwrds37 , rwrds38 , rwrds39 , rwrds3A , rwrds3B , rwrds3C , rwrds3D , rwrds3E , rwrds3F <] .
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
Variables fctr00 fctr01 fctr02 fctr03 fctr04 fctr05 fctr06 fctr07 fctr08 fctr09 fctr0A fctr0B fctr0C fctr0D fctr0E fctr0F fctr10 fctr11 fctr12 fctr13 fctr14 fctr15 fctr16 fctr17 fctr18 fctr19 fctr1A fctr1B fctr1C fctr1D fctr1E fctr1F  : TVMBit . 
Definition StakingContract_ι_Node_ι_factor_bs_def := [> fctr00 , fctr01 , fctr02 , fctr03 , fctr04 , fctr05 , fctr06 , fctr07 , fctr08 , fctr09 , fctr0A , fctr0B , fctr0C , fctr0D , fctr0E , fctr0F , fctr10 , fctr11 , fctr12 , fctr13 , fctr14 , fctr15 , fctr16 , fctr17 , fctr18 , fctr19 , fctr1A , fctr1B , fctr1C , fctr1D , fctr1E , fctr1F <] .
Lemma StakingContract_ι_Node_ι_factor_bs_id: StakingContract_ι_Node_ι_factor_bs_def = [> fctr00 , fctr01 , fctr02 , fctr03 , fctr04 , fctr05 , fctr06 , fctr07 , fctr08 , fctr09 , fctr0A , fctr0B , fctr0C , fctr0D , fctr0E , fctr0F , fctr10 , fctr11 , fctr12 , fctr13 , fctr14 , fctr15 , fctr16 , fctr17 , fctr18 , fctr19 , fctr1A , fctr1B , fctr1C , fctr1D , fctr1E , fctr1F <] .
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
Variables rndd00 rndd01 rndd02 rndd03 rndd04 rndd05 rndd06 rndd07 rndd08 rndd09 rndd0A rndd0B rndd0C rndd0D rndd0E rndd0F rndd10 rndd11 rndd12 rndd13 rndd14 rndd15 rndd16 rndd17 rndd18 rndd19 rndd1A rndd1B rndd1C rndd1D rndd1E rndd1F  : TVMBit . 
Definition StakingContract_ι_StakeInfo_ι_roundId_bs_def := [> rndd00 , rndd01 , rndd02 , rndd03 , rndd04 , rndd05 , rndd06 , rndd07 , rndd08 , rndd09 , rndd0A , rndd0B , rndd0C , rndd0D , rndd0E , rndd0F , rndd10 , rndd11 , rndd12 , rndd13 , rndd14 , rndd15 , rndd16 , rndd17 , rndd18 , rndd19 , rndd1A , rndd1B , rndd1C , rndd1D , rndd1E , rndd1F <] .
Lemma StakingContract_ι_StakeInfo_ι_roundId_bs_id: StakingContract_ι_StakeInfo_ι_roundId_bs_def = [> rndd00 , rndd01 , rndd02 , rndd03 , rndd04 , rndd05 , rndd06 , rndd07 , rndd08 , rndd09 , rndd0A , rndd0B , rndd0C , rndd0D , rndd0E , rndd0F , rndd10 , rndd11 , rndd12 , rndd13 , rndd14 , rndd15 , rndd16 , rndd17 , rndd18 , rndd19 , rndd1A , rndd1B , rndd1C , rndd1D , rndd1E , rndd1F <] .
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
Qed. Variables StakingContract_ι_StakeInfo_ι_stake : Z . 
Variables stk00 stk01 stk02 stk03 stk04 stk05 stk06 stk07 stk08 stk09 stk0A stk0B stk0C stk0D stk0E stk0F stk10 stk11 stk12 stk13 stk14 stk15 stk16 stk17 stk18 stk19 stk1A stk1B stk1C stk1D stk1E stk1F stk20 stk21 stk22 stk23 stk24 stk25 stk26 stk27 stk28 stk29 stk2A stk2B stk2C stk2D stk2E stk2F stk30 stk31 stk32 stk33 stk34 stk35 stk36 stk37 stk38 stk39 stk3A stk3B stk3C stk3D stk3E stk3F  : TVMBit . 
Definition StakingContract_ι_StakeInfo_ι_stake_bs_def := [> stk00 , stk01 , stk02 , stk03 , stk04 , stk05 , stk06 , stk07 , stk08 , stk09 , stk0A , stk0B , stk0C , stk0D , stk0E , stk0F , stk10 , stk11 , stk12 , stk13 , stk14 , stk15 , stk16 , stk17 , stk18 , stk19 , stk1A , stk1B , stk1C , stk1D , stk1E , stk1F , stk20 , stk21 , stk22 , stk23 , stk24 , stk25 , stk26 , stk27 , stk28 , stk29 , stk2A , stk2B , stk2C , stk2D , stk2E , stk2F , stk30 , stk31 , stk32 , stk33 , stk34 , stk35 , stk36 , stk37 , stk38 , stk39 , stk3A , stk3B , stk3C , stk3D , stk3E , stk3F <] .
Lemma StakingContract_ι_StakeInfo_ι_stake_bs_id: StakingContract_ι_StakeInfo_ι_stake_bs_def = [> stk00 , stk01 , stk02 , stk03 , stk04 , stk05 , stk06 , stk07 , stk08 , stk09 , stk0A , stk0B , stk0C , stk0D , stk0E , stk0F , stk10 , stk11 , stk12 , stk13 , stk14 , stk15 , stk16 , stk17 , stk18 , stk19 , stk1A , stk1B , stk1C , stk1D , stk1E , stk1F , stk20 , stk21 , stk22 , stk23 , stk24 , stk25 , stk26 , stk27 , stk28 , stk29 , stk2A , stk2B , stk2C , stk2D , stk2E , stk2F , stk30 , stk31 , stk32 , stk33 , stk34 , stk35 , stk36 , stk37 , stk38 , stk39 , stk3A , stk3B , stk3C , stk3D , stk3E , stk3F <] .
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

