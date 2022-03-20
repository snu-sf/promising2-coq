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

Set Implicit Arguments.

Module PFConfiguration.

  Inductive step: forall (e:MachineEvent.t) (tid:Ident.t) (c1 c2: Configuration.t), Prop :=
  | step_intro
      e tid c1 lang st1 lc1 e2 st3 lc3 sc3 memory3
      (TID: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st1, lc1))
      (STEPS: rtc (tau (@Thread.program_step _)) (Thread.mk _ st1 lc1 (Configuration.sc c1) (Configuration.memory c1)) e2)
      (STEP: Thread.program_step e e2 (Thread.mk _ st3 lc3 sc3 memory3)):
      step (ThreadEvent.get_machine_event e) tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st3, lc3) (Configuration.threads c1)) sc3 memory3)
  .
  #[export]
  Hint Constructors step: core.

  Definition step_all (c0 c1: Configuration.t) :=
    union (fun e => union (step e)) c0 c1.
  #[export]
  Hint Unfold step_all: core.

  Inductive opt_step: forall (e: MachineEvent.t) (tid: Ident.t) (c1 c2: Configuration.t), Prop :=
  | step_none
      tid c:
      opt_step MachineEvent.silent tid c c
  | step_some
      e tid c1 c2
      (STEP: step e tid c1 c2):
      opt_step e tid c1 c2
  .
  #[export]
  Hint Constructors opt_step: core.

  Lemma step_future
        e tid c1 c2
        (STEP: step e tid c1 c2)
        (WF1: Configuration.wf c1):
    Configuration.wf c2.
  Proof.
    inv WF1. inv WF. inv STEP; s.
    exploit THREADS; ss; eauto. i.
    exploit Thread.rtc_tau_step_future.
    { eapply rtc_implies; try apply STEPS. eapply tau_mon.
      i. econs. econs 2; eauto. } all: eauto. s. i. des.
    exploit Thread.step_future.
    { econs 2; eauto. } all: eauto. s. i. des.
    econs; ss. econs.
    i. Configuration.simplify.
    - exploit THREADS; try apply TH1; eauto. i. des.
      exploit Thread.rtc_tau_step_disjoint.
      { eapply rtc_implies; try apply STEPS. eapply tau_mon.
        i. econs. econs 2; eauto. } all: eauto. i. des.
      exploit Thread.step_disjoint.
      { econs 2; eauto. } all: eauto. i. des. ss.
      symmetry. auto.
    - exploit THREADS; try apply TH2; eauto. i. des.
      exploit Thread.rtc_tau_step_disjoint.
      { eapply rtc_implies; try apply STEPS. eapply tau_mon.
        i. econs. econs 2; eauto. } all: eauto. i. des.
      exploit Thread.step_disjoint.
      { econs 2; eauto. } all: eauto. i. des. ss.
    - eapply DISJOINT; [|eauto|eauto]. auto.
    - i. Configuration.simplify.
      exploit THREADS; try apply TH; eauto. i.
      exploit Thread.rtc_tau_step_disjoint.
      { eapply rtc_implies; try apply STEPS. eapply tau_mon.
        i. econs. econs 2; eauto. } all: eauto. i. des.
      exploit Thread.step_disjoint.
      { econs 2; eauto. } all: eauto. i. des. ss.
  Qed.

  Lemma write_no_promise mem0 loc from to val released prom1 mem1 kind
        (WRITE: Memory.write Memory.bot mem0 loc from to val released prom1 mem1 kind)
    :
      <<NOPROMISE: prom1 = Memory.bot>> /\ <<ADD: kind = Memory.op_kind_add>>.
  Proof.
    inv WRITE. inv PROMISE.
    - split; auto. eapply MemoryFacts.add_remove_eq; eauto.
    - eapply Memory.split_get0 in PROMISES. des.
      erewrite Memory.bot_get in GET0. clarify.
    - eapply Memory.lower_get0 in PROMISES. des.
      erewrite Memory.bot_get in GET. clarify.
    - eapply Memory.remove_get0 in PROMISES. des.
      erewrite Memory.bot_get in GET. clarify.
  Qed.

  Lemma program_step_no_promise lang (th0 th1: Thread.t lang) e
        (STEP: Thread.program_step e th0 th1)
        (NOPROMISE: (Local.promises (Thread.local th0)) = Memory.bot)
    :
      (Local.promises (Thread.local th1)) = Memory.bot.
  Proof.
    inv STEP. inv LOCAL; ss.
    - inv LOCAL0. ss.
    - inv LOCAL0. rewrite NOPROMISE in WRITE.
      eapply write_no_promise in WRITE. des. auto.
    - inv LOCAL1. inv LOCAL2. rewrite NOPROMISE in WRITE.
      eapply write_no_promise in WRITE. des. auto.
    - inv LOCAL0. ss.
    - inv LOCAL0. ss.
  Qed.

  Lemma program_steps_no_promise lang (th0 th1: Thread.t lang)
        (STEP: rtc (tau (@Thread.program_step lang)) th0 th1)
        (NOPROMISE: (Local.promises (Thread.local th0)) = Memory.bot)
    :
      (Local.promises (Thread.local th1)) = Memory.bot.
  Proof.
    ginduction STEP; ss. i. eapply IHSTEP. inv H.
    eapply program_step_no_promise; eauto.
  Qed.

  Lemma no_promise_spec c
        (NOPROMISE: ~ Configuration.has_promise c)
        tid st lc
        (FIND: IdentMap.find tid (Configuration.threads c) = Some (st, lc))
    :
      (Local.promises lc) = Memory.bot.
  Proof.
    eapply Memory.ext. i. rewrite Memory.bot_get.
    destruct (Memory.get loc ts (Local.promises lc)) as [[from msg]|] eqn:GET; auto.
    exfalso. eapply NOPROMISE. econs; eauto.
  Qed.

  Lemma configuration_step_no_promise c0 c1 tid e
        (NOPROMISE: ~ Configuration.has_promise c0)
        (STEP: step tid e c0 c1)
    :
      ~ Configuration.has_promise c1.
  Proof.
    inv STEP. ii. inv H. ss. rewrite IdentMap.gsspec in FIND. des_ifs.
    - eapply no_promise_spec in TID; eauto.
      eapply program_steps_no_promise in STEPS; eauto.
      eapply program_step_no_promise in STEP0; eauto.
      ss. rewrite STEP0 in *. rewrite Memory.bot_get in *. clarify.
    - eapply NOPROMISE. econs; eauto.
  Qed.

  Lemma step_no_promise_step c0 c1 e tid
        (NOPROMISE: ~ Configuration.has_promise c0)
        (STEP: step e tid c0 c1)
    :
      Configuration.step e tid c0 c1.
  Proof.
    inv STEP.
    exploit no_promise_spec; eauto. intros LCBOT0.
    exploit program_steps_no_promise; eauto. intros LCBOT1.
    exploit program_step_no_promise; eauto. intros LCBOT2. ss.
    destruct (classic (e0 <> ThreadEvent.failure)).
    - econs 2.
      + eauto.
      + eapply rtc_implies; cycle 1.
        * eapply STEPS.
        * eapply tau_mon. i. econs. econs 2; eauto.
      + econs 2; eauto.
      + auto.
      + ii. ss. right. esplits; eauto.
    - apply NNPP in H. subst. econs 1.
      + eauto.
      + eapply rtc_implies; cycle 1.
        * eapply STEPS.
        * eapply tau_mon. i. econs. econs 2; eauto.
      + econs 2; eauto.
  Qed.

  Lemma step_no_promise_adequacy c0 beh
        (NOPROMISE: ~ Configuration.has_promise c0)
        (BEH: behaviors step c0 beh)
    :
      behaviors Configuration.step c0 beh.
  Proof.
    ginduction BEH; i.
    - econs; ss.
    - exploit step_no_promise_step; eauto. i. econs 2; eauto.
      eapply IHBEH. eapply configuration_step_no_promise; eauto.
    - exploit step_no_promise_step; eauto. i. econs 3; eauto.
    - exploit step_no_promise_step; eauto. i. econs 4; eauto.
      eapply IHBEH. eapply configuration_step_no_promise; eauto.
  Qed.

  Lemma step_promise_behavior s
    :
      behaviors step (Configuration.init s) <1=
      behaviors Configuration.step (Configuration.init s).
  Proof.
    i. eapply step_no_promise_adequacy; auto.
    ii. inv H. ss. unfold Threads.init in FIND.
    erewrite IdentMap.Properties.F.map_o in *.
    unfold option_map in *. des_ifs. ss.
    rewrite Memory.bot_get in GET. clarify.
  Qed.

End PFConfiguration.
