Require Import Lia.
Require Import RelationClasses.

From Paco Require Import paco.
From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
Require Import Time.
Require Import Event.
From PromisingLib Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import Cover.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.
Require Import APromiseConsistent.
From PromisingLib Require Import Loc.

Require Import APF.
Require Import Race.
Require Import Behavior.
Require Import SimMemory.
Require Import yjtac.
Require Import Program.
Require Import Cell.
Require Import Time.
Require Import PredStep.
Require Import ReorderPromises2.

Require Import Pred.
Require Import AMemory.
Require Import ALocal.
Require Import AThread.
Require Import APredStep.
Require Import ADRF_PF0.
Require Import ADRF_PF1.
Require Import ADRF_PF2.
Require Import ADRF_PF3.
Require Import ADRF_PF4.
Require Import ADRF_PF5.
Require Import AMapping.

Set Implicit Arguments.

Lemma forget_config_terminal c_src c_tgt
      (SIM: forget_config c_src c_tgt)
      (TERMINAL: Configuration.is_terminal c_tgt)
  :
    Configuration.is_terminal c_src.
Proof.
  inv SIM. ii. specialize (THS tid). rewrite FIND in *.
  unfold option_rel in THS. des_ifs. inv THS. split; auto.
  eapply TERMINAL; eauto.
Qed.

Lemma sim_pf_all_adequacy c_src c_tgt
      (SIM: sim_pf_all c_src c_tgt)
  :
    behaviors Configuration.step c_tgt <1=
    behaviors APFConfiguration.step c_src.
Proof.
  i. ginduction PR; i.
  - inv SIM. inv SIM0. econs 1. eapply forget_config_terminal; eauto.
  - exploit sim_pf_step; eauto. i. des; clarify.
    + inv STEP0. econs 2; eauto. econs 3; eauto.
    + inv STEP0. econs 2; eauto.
  - exploit sim_pf_step; eauto. i. des; clarify.
    + inv STEP0. econs 3; eauto.
    + inv STEP0. econs 3; eauto.
    + inv STEP0. econs 3; eauto.
  - exploit sim_pf_step; eauto. i. des; clarify.
    + inv STEP0.
      * econs 3; eauto.
      * econs 4; eauto. econs 3; eauto.
    + inv STEP0.
      * eauto.
      * econs 4; eauto.
Qed.

Theorem drf_apf s
        (RACEFREE: pf_racefree APFConfiguration.step (Configuration.init s))
  :
    behaviors Configuration.step (Configuration.init s) <1=
    behaviors APFConfiguration.step (Configuration.init s).
Proof.
  eapply sim_pf_all_adequacy.
  eapply sim_pf_init; auto.
Qed.
