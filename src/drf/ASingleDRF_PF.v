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
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.
Require Import Behavior.

Require Import AMemory.
Require Import ALocal.
Require Import AThread.
Require Import Race.

Require Import APF.
Require Import APFSingle.
Require Import ADRF_PF.

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
