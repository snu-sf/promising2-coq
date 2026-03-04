From Stdlib Require Import Lia.
From Stdlib Require Import RelationClasses.

From Paco Require Import paco.
From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
Require Import lang.Time.
Require Import lang.Event.
From PromisingLib Require Import Language.
Require Import lang.View.
Require Import lang.Cell.
Require Import lang.Memory.
Require Import prop.Cover.
Require Import lang.TView.
Require Import lang.Local.
Require Import lang.Thread.
Require Import lang.Configuration.
Require Import lang.Progress.
Require Import attachable.APromiseConsistent.
From PromisingLib Require Import Loc.

Require Import pf.APF.
Require Import drf.Race.
Require Import lang.Behavior.
Require Import opt.SimMemory.
Require Import drf.yjtac.
From Stdlib Require Import Program.
Require Import lang.Cell.
Require Import lang.Time.
Require Import drf.PredStep.
Require Import drf.ReorderPromises2.

Require Import drf.Pred.
Require Import attachable.AMemory.
Require Import attachable.ALocal.
Require Import attachable.AThread.
Require Import drf.APredStep.
Require Import drf.ADRF_PF0.
Require Import drf.ADRF_PF1.
Require Import drf.ADRF_PF2.
Require Import drf.ADRF_PF3.
Require Import drf.ADRF_PF4.
Require Import drf.ADRF_PF5.
Require Import drf.AMapping.

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
