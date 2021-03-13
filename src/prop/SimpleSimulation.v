From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.

Require Import Event.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Thread.
Require Import Configuration.
Require Import Behavior.

Set Implicit Arguments.


Section Simulation.
  Definition SIM := forall (c1_src c1_tgt: Configuration.t), Prop.

  Definition _sim (sim: SIM) (c1_src c1_tgt:Configuration.t): Prop :=
    forall (WF_SRC: Configuration.wf c1_src)
      (WF_TGT: Configuration.wf c1_tgt),
      <<TERMINAL:
        forall (TERMINAL_TGT: Threads.is_terminal (Configuration.threads c1_tgt)),
        exists c2_src,
          <<STEPS_SRC: rtc Configuration.tau_step c1_src c2_src>> /\
          <<TERMINAL_SRC: Threads.is_terminal (Configuration.threads c2_src)>>>> /\
      <<STEP:
        forall e tid c2_tgt
          (STEP_TGT: Configuration.step e tid c1_tgt c2_tgt),
        exists c2_src,
          <<STEP_SRC: Configuration.opt_step e tid c1_src c2_src>> /\
          <<SIM: sim c2_src c2_tgt>>>>
  .

  Lemma _sim_mon: monotone2 _sim.
  Proof.
    ii. exploit IN; eauto. i. des.
    econs; eauto. ii.
    exploit STEP; eauto. i. des. eauto.
  Qed.
  Hint Resolve _sim_mon: paco.

  Definition sim: SIM := paco2 _sim bot2.
End Simulation.
Hint Resolve _sim_mon: paco.


Lemma sim_adequacy
      c_src c_tgt
      (WF_SRC: Configuration.wf c_src)
      (WF_TGT: Configuration.wf c_tgt)
      (SIM: sim c_src c_tgt):
  behaviors Configuration.step c_tgt <1= behaviors Configuration.step c_src.
Proof.
  i. revert c_src WF_SRC WF_TGT SIM.
  induction PR; i.
  - punfold SIM0. exploit SIM0; eauto. i. des.
    hexploit TERMINAL0; eauto. i. des.
    eapply rtc_tau_step_behavior; eauto.
    econs 1. eauto.
  - punfold SIM0. exploit SIM0; eauto. i. des.
    exploit STEP0; eauto. i. des.
    exploit Configuration.step_future; try exact STEP; eauto. i. des.
    exploit Configuration.opt_step_future; try exact STEP_SRC; eauto. i. des.
    inv SIM1; ss. inv STEP_SRC.
    econs 2; eauto.
  - punfold SIM0. exploit SIM0; eauto. i. des.
    exploit STEP0; eauto. i. des.
    exploit Configuration.step_future; try exact STEP; eauto. i. des.
    exploit Configuration.opt_step_future; try exact STEP_SRC; eauto. i. des.
    inv SIM1; ss. inv STEP_SRC.
    econs 3; eauto.
  - punfold SIM0. exploit SIM0; eauto. i. des.
    exploit STEP0; eauto. i. des.
    exploit Configuration.step_future; try exact STEP; eauto. i. des.
    exploit Configuration.opt_step_future; try exact STEP_SRC; eauto. i. des.
    inv SIM1; ss. inv STEP_SRC; eauto.
    econs 4; eauto.
Qed.
