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
Require Import lang.MemoryFacts.
Require Import lang.TView.
Require Import lang.Local.
Require Import lang.Thread.
Require Import lang.Configuration.
Require Import lang.Progress.
Require Import lang.Behavior.

Require Import attachable.AMemory.
Require Import attachable.ALocal.
Require Import attachable.AThread.
Require Import drf.Race.

Require Import pf.APF.
Require Import pf.APFSingle.
Require Import drf.ADRF_PF.

Lemma sim_apf_pf_racefree c
      (RACEFREE: pf_racefree APFSingle.step c)
  :
    pf_racefree APFConfiguration.step c.
Proof.
  ii. ginduction STEPS; i.
  - eapply RACEFREE; eauto.
  - inv H. exploit APFSingle.step_sim; eauto. i. des.
    eapply IHSTEPS; auto. ii. eapply RACEFREE; cycle 1; eauto. etrans.
    + eapply rtc_implies; try apply STEPS0. i. inv H. econs; eauto.
    + econs; eauto. econs; eauto.
Qed.

Theorem drf_single_apf s
        (RACEFREE: pf_racefree APFSingle.step (Configuration.init s))
  :
    behaviors Configuration.step (Configuration.init s) <1=
    behaviors APFSingle.step (Configuration.init s).
Proof.
  ii. eapply APFSingle.long_step_equiv; eauto.
  eapply drf_apf; eauto.
  eapply sim_apf_pf_racefree; eauto.
Qed.
