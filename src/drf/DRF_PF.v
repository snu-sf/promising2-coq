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
Require Import pf.PF.
Require Import drf.ADRF_PF.
Require Import attachable.APFPF.

Lemma sim_apf_pf_race c_src c_tgt
      (SIM: sim_apf_pf c_src c_tgt)
  :
    pf_race c_src <-> pf_race c_tgt.
Proof.
  inv SIM. split; i.
  - inv H. ss. econs; [eapply TID1|eapply TID2|..]; eauto.
  - inv H. ss. econs; [eapply TID1|eapply TID2|..]; eauto.
Qed.

Lemma sim_apf_pf_racefree c_src c_tgt
      (SIM: sim_apf_pf c_src c_tgt)
      (RACEFREE: pf_racefree PFConfiguration.step c_src)
  :
    pf_racefree APFConfiguration.step c_tgt.
Proof.
  ii. ginduction STEPS.
  - i. erewrite <- sim_apf_pf_race in RACE; eauto.
  - i. inv H. exploit sim_apf_pf_step; eauto.
    i. des. eapply IHSTEPS; eauto.
    eapply pf_racefree_step; eauto.
Qed.

Theorem drf_pf s
        (RACEFREE: pf_racefree PFConfiguration.step (Configuration.init s))
  :
    behaviors Configuration.step (Configuration.init s) <1=
    behaviors PFConfiguration.step (Configuration.init s).
Proof.
  ii. eapply drf_apf in PR.
  - eapply apf_pf_equiv; eauto.
  - eapply sim_apf_pf_racefree; eauto.
    eapply sim_apf_pf_init; eauto.
Qed.
