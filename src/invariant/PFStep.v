Require Import Omega.
Require Import RelationClasses.

From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.

Require Import Time.
Require Import Event.
From PromisingLib Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.

Require Import PromiseConsistent.

Require Import AMemory.
Require Import ALocal.
Require Import ATView.
Require Import AThread.

Require Import PFCommon.

Set Implicit Arguments.


Module PFStep.
  Include PFCommon.

  Inductive sim_memory (promises mem_src mem_tgt: Memory.t): Prop :=
  | sim_memory_intro
      (SOUND: Memory.le mem_src mem_tgt)
      (COMPLETE1: forall loc to from msg
                   (GETP: Memory.get loc to promises = Some (from, msg))
                   (GET_TGT: Memory.get loc to mem_tgt = Some (from, msg)),
          <<GET_SRC: Memory.get loc to mem_src = None>>)
      (COMPLETE2: forall loc to from msg
                   (GETP: Memory.get loc to promises = None)
                   (GET_TGT: Memory.get loc to mem_tgt = Some (from, msg)),
          <<GET_SRC: Memory.get loc to mem_src = Some (from, msg)>>)
  .

  Inductive sim_thread (lang: language) (e_src e_tgt: @Thread.t lang): Prop :=
  | sim_thread_intro
      (STATE: (Thread.state e_src) = (Thread.state e_tgt))
      (LOCAL: sim_local (Thread.local e_src) (Thread.local e_tgt))
      (SC: (Thread.sc e_src) = (Thread.sc e_tgt))
      (MEMORY: sim_memory (Local.promises (Thread.local e_tgt))
                          (Thread.memory e_src) (Thread.memory e_tgt))
  .


  Lemma sim_memory_get
        promises mem_src mem_tgt
        loc from to msg
        (MEM: sim_memory promises mem_src mem_tgt)
        (LE_TGT: Memory.le promises mem_tgt)
        (GET_TGT: Memory.get loc to mem_tgt = Some (from, msg)):
    <<GETP: Memory.get loc to promises = Some (from, msg)>> /\
    <<GET_SRC: Memory.get loc to mem_src = None>> \/
    <<GETP: Memory.get loc to promises = None>> /\
    <<GET_SRC: Memory.get loc to mem_src = Some (from, msg)>>.
  Proof.
    inv MEM.
    destruct (Memory.get loc to promises) as [[f m]|] eqn:GETP; eauto.
    exploit LE_TGT; eauto. i.
    rewrite GET_TGT in x. inv x. eauto.
  Qed.


  (* lemmas on step *)

  Lemma promise
        mem1_src
        promises1 mem1_tgt loc from to msg promises2 mem2_tgt kind
        (MEM1: sim_memory promises1 mem1_src mem1_tgt)
        (LE1_TGT: Memory.le promises1 mem1_tgt)
        (PROMISE: Memory.promise promises1 mem1_tgt loc from to msg promises2 mem2_tgt kind):
    sim_memory promises2 mem1_src mem2_tgt.
  Proof.
    inv MEM1. inv PROMISE.
    - clear TS RESERVE.
      exploit Memory.add_get0; try exact PROMISES. i. des.
      exploit Memory.add_get0; try exact MEM. i. des.
      econs; ii.
      + erewrite Memory.add_o; eauto. condtac; ss; eauto.
        des. subst. exploit SOUND; eauto. congr.
      + revert GETP.
        erewrite Memory.add_o; eauto. condtac; ss; eauto. i.
        des. subst.
        destruct (Memory.get loc to mem1_src) as [[]|] eqn:GET_SRC; ss.
        exploit SOUND; eauto. congr.
      + revert GETP.
        erewrite Memory.add_o; eauto. condtac; ss; eauto. i.
        revert GET_TGT.
        erewrite Memory.add_o; eauto. condtac; ss; eauto.
    - clear TS RESERVE.
      exploit Memory.split_get0; try exact PROMISES. i. des.
      exploit Memory.split_get0; try exact MEM. i. des.
      econs; ii.
      + erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
        * des. subst. exploit SOUND; eauto. congr.
        * guardH o. des. subst.
          exploit COMPLETE1; try exact GET0; eauto. congr.
      + revert GETP.
        erewrite Memory.split_o; eauto. repeat condtac; ss; eauto; i.
        * des. subst.
          destruct (Memory.get loc to mem1_src) as [[]|] eqn:GET_SRC; ss.
          exploit SOUND; eauto. congr.
        * guardH o. des. subst. inv GETP. eauto.
      + revert GETP.
        erewrite Memory.split_o; eauto. repeat condtac; ss; eauto; i.
        revert GET_TGT.
        erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
    - clear TS.
      exploit Memory.lower_get0; try exact PROMISES. i. des.
      exploit Memory.lower_get0; try exact MEM. i. des.
      econs; ii.
      + erewrite Memory.lower_o; eauto. condtac; ss; eauto.
        des. subst. exploit COMPLETE1; eauto. congr.
      + revert GETP.
        erewrite Memory.lower_o; eauto. condtac; ss; eauto. i.
        des. subst. inv GETP.
        revert GET_TGT.
        erewrite Memory.lower_o; eauto.
      + revert GETP.
        erewrite Memory.lower_o; eauto. condtac; ss; eauto. i.
        revert GET_TGT.
        erewrite Memory.lower_o; eauto. condtac; ss; eauto.
    - exploit Memory.remove_get0; try exact PROMISES. i. des.
      exploit Memory.remove_get0; try exact MEM. i. des.
      econs; ii.
      + erewrite Memory.remove_o; eauto. condtac; ss; eauto.
        des. subst. exploit COMPLETE1; eauto. congr.
      + revert GETP.
        erewrite Memory.remove_o; eauto. condtac; ss; eauto.
      + revert GETP.
        erewrite Memory.remove_o; eauto. condtac; ss; i.
        * revert GET_TGT.
          erewrite Memory.remove_o; eauto. condtac; ss; eauto.
        * revert GET_TGT.
          erewrite Memory.remove_o; eauto. condtac; ss; eauto.
  Qed.

  Lemma read_step
        lc1_src mem1_src
        lc1_tgt mem1_tgt loc to val released ord lc2_tgt
        (LOCAL1: sim_local lc1_src lc1_tgt)
        (MEM1: sim_memory (Local.promises lc1_tgt) mem1_src mem1_tgt)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (STEP_TGT: Local.read_step lc1_tgt mem1_tgt loc to val released ord lc2_tgt)
        (CONS_TGT: Local.promise_consistent lc2_tgt):
    exists lc2_src,
      <<STEP_SRC: Local.read_step lc1_src mem1_src loc to val released ord lc2_src>> /\
      <<LOCAL2: sim_local lc2_src lc2_tgt>>.
  Proof.
    inv STEP_TGT.
    exploit sim_memory_get; eauto; try apply WF1_TGT. i. des.
    { exploit promise_consistent_promise_read; eauto. i. timetac. }
    inv MEM1. inv LOCAL1.
    destruct lc1_src, lc1_tgt. ss. subst.
    esplits; econs; eauto.
  Qed.

  Lemma write_aux
        mem1_src
        promises1 mem1_tgt loc from to msg promises2 mem2_tgt kind
        promises3
        (MEM1: sim_memory promises1 mem1_src mem1_tgt)
        (LE1_TGT: Memory.le promises1 mem1_tgt)
        (PROMISE_TGT: Memory.promise promises1 mem1_tgt loc from to msg promises2 mem2_tgt kind)
        (REMOVE_TGT: Memory.remove promises2 loc from to msg promises3):
    exists mem2_src,
      <<ADD_SRC: Memory.add mem1_src loc from to msg mem2_src>> /\
      <<MEM2: sim_memory promises3 mem2_src mem2_tgt>>.
  Proof.
    dup MEM1. inv MEM0. inv PROMISE_TGT.
    - (* add *)
      clear TS RESERVE.
      exploit (@Memory.add_exists mem1_src loc from to msg); eauto.
      { ii. exploit SOUND; eauto. i.
        inv MEM. inv ADD. eapply DISJOINT; eauto. }
      { inv MEM. inv ADD. ss. }
      { inv MEM. inv ADD. ss. }
      i. des. esplits; eauto.
      exploit Memory.add_get0; try exact MEM. i. des.
      exploit Memory.add_get0; try exact x0. i. des.
      econs; ii.
      + revert LHS.
        erewrite Memory.add_o; eauto. condtac; ss.
        * des. subst. i. inv LHS. auto.
        * i. erewrite Memory.add_o; eauto. condtac; ss. auto.
      + revert GETP.
        erewrite Memory.remove_o; eauto. condtac; ss.
        erewrite Memory.add_o; eauto. condtac; ss. i.
        revert GET_TGT.
        erewrite Memory.add_o; eauto. condtac; ss. i.
        erewrite Memory.add_o; eauto. condtac; ss. eauto.
      + revert GETP.
        erewrite Memory.remove_o; eauto. condtac; ss.
        * i. des. subst. rewrite GET0 in *. inv GET_TGT. ss.
        * erewrite Memory.add_o; eauto. condtac; ss; i.
          revert GET_TGT.
          erewrite Memory.add_o; eauto. condtac; ss. i.
          erewrite Memory.add_o; eauto. condtac; ss. eauto.
    - (* split *)
      clear TS RESERVE.
      exploit (@Memory.add_exists mem1_src loc from to msg); eauto.
      { ii. exploit SOUND; eauto. i.
        exploit Memory.split_get0; try exact MEM. i. des.
        exploit Memory.get_disjoint; [exact x0|exact GET0|..]. i. des.
        { subst. exploit Memory.split_get0; try exact PROMISES. i. des.
          exploit COMPLETE1; try exact GET0; eauto. congr. }
        inv LHS. inv RHS. apply (x2 x); ss. econs; ss.
        etrans; try exact TO. inv MEM. inv SPLIT. econs. ss. }
      { inv MEM. inv SPLIT. ss. }
      { inv MEM. inv SPLIT. ss. }
      i. des. esplits; eauto.
      exploit Memory.split_get0; try exact MEM. i. des.
      exploit Memory.add_get0; try exact x0. i. des.
      econs; ii.
      + revert LHS.
        erewrite Memory.add_o; eauto. condtac; ss; i.
        * des. subst. inv LHS. auto.
        * erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
          guardH o. guardH o0. des. subst.
          exploit Memory.split_get0; try exact PROMISES. i. des.
          exploit COMPLETE1; try exact GET6; eauto. congr.
      + revert GETP.
        erewrite Memory.remove_o; eauto. condtac; ss.
        guardH o.
        erewrite Memory.split_o; eauto. repeat condtac; ss; i.
        * guardH o0. des. subst.
          revert GET_TGT.
          erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          guardH o1. inv GETP. inv GET_TGT.
          erewrite Memory.add_o; eauto. condtac; ss.
          guardH o2.
          exploit Memory.split_get0; try exact PROMISES; eauto. i. des. eauto.
        * revert GET_TGT.
          erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          erewrite Memory.add_o; eauto. condtac; ss. eauto.
      + revert GETP.
        erewrite Memory.remove_o; eauto. condtac; ss.
        * des. subst. rewrite GET1 in *. inv GET_TGT. ss.
        * erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          revert GET_TGT.
          erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          erewrite Memory.add_o; eauto. condtac; ss. eauto.
    - clear TS.
      exploit (@Memory.add_exists mem1_src loc from to msg); eauto.
      { ii. exploit SOUND; eauto.
        exploit Memory.lower_get0; try exact MEM. i. des.
        exploit Memory.get_disjoint; [exact GET|exact x0|..]. i. des.
        { subst. exploit Memory.lower_get0; try exact PROMISES. i. des.
          exploit COMPLETE1; try exact GET1; eauto. congr. }
        apply (x2 x); ss. }
      { inv MEM. inv LOWER. ss. }
      { inv MEM. inv LOWER. ss. }
      i. des. esplits; eauto.
      exploit Memory.lower_get0; try exact MEM. i. des.
      exploit Memory.add_get0; try exact x0. i. des.
      econs; ii.
      + revert LHS. erewrite Memory.add_o; eauto. condtac; ss; i.
        * des. subst. inv LHS. auto.
        * erewrite Memory.lower_o; eauto. condtac; ss. eauto.
      + revert GETP.
        erewrite Memory.remove_o; eauto. condtac; ss.
        erewrite Memory.lower_o; eauto. condtac; ss; i.
        revert GET_TGT.
        erewrite Memory.lower_o; eauto. condtac; ss; i.
        erewrite Memory.add_o; eauto. condtac; ss. eauto.
      + revert GETP.
        erewrite Memory.remove_o; eauto. condtac; ss.
        * des. subst. rewrite GET0 in *. inv GET_TGT. ss.
        * erewrite Memory.lower_o; eauto. condtac; ss; i.
          revert GET_TGT.
          erewrite Memory.lower_o; eauto. condtac; ss; i.
          erewrite Memory.add_o; eauto. condtac; ss. eauto.
    - exploit Memory.remove_get0; try exact REMOVE_TGT. i. des.
      exploit Memory.remove_get0; try exact PROMISES. i. des. congr.
  Qed.

  Lemma write_step
        lc1_src mem1_src
        lc1_tgt sc1 mem1_tgt loc from to val releasedm released ord lc2_tgt sc2 mem2_tgt kind
        (LOCAL1: sim_local lc1_src lc1_tgt)
        (MEM1: sim_memory (Local.promises lc1_tgt) mem1_src mem1_tgt)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (RELEASEDM: View.opt_wf releasedm)
        (STEP_TGT: Local.write_step lc1_tgt sc1 mem1_tgt loc from to val
                                    releasedm released ord lc2_tgt sc2 mem2_tgt kind):
    exists lc2_src mem2_src,
      <<STEP_SRC: ALocal.write_step lc1_src sc1 mem1_src loc from to val
                                   releasedm released ord lc2_src sc2 mem2_src Memory.op_kind_add>> /\
      <<LOCAL2: sim_local lc2_src lc2_tgt>> /\
      <<MEM2: sim_memory (Local.promises lc2_tgt) mem2_src mem2_tgt>>.
  Proof.
    destruct lc1_src, lc1_tgt. ss.
    inv STEP_TGT. inv WRITE. inv LOCAL1. ss. subst.
    exploit write_aux; try apply WF1_TGT; ss; eauto. i. des.
    exploit Memory.add_exists_le; eauto.
    { eapply Memory.bot_le. }
    i. des.
    exploit Memory.add_get0; try exact x0. i. des.
    exploit Memory.remove_exists; try exact GET0. i. des.
    esplits; eauto.
    - econs; ss.
      + econs; eauto. econs; eauto; ss. inv PROMISE; ss.
      + ii. rewrite Memory.bot_get in *. ss.
    - econs; ss. apply Memory.ext. i.
      rewrite Memory.bot_get.
      erewrite Memory.remove_o; eauto. condtac; ss.
      erewrite Memory.add_o; eauto. condtac; ss.
      apply Memory.bot_get.
  Qed.

  Lemma program_step
        lc1_src mem1_src
        e lc1_tgt sc1 mem1_tgt lc2_tgt sc2 mem2_tgt
        (LOCAL1: sim_local lc1_src lc1_tgt)
        (MEM1: sim_memory (Local.promises lc1_tgt) mem1_src mem1_tgt)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (STEP_TGT: Local.program_step e lc1_tgt sc1 mem1_tgt lc2_tgt sc2 mem2_tgt)
        (CONS: Local.promise_consistent lc2_tgt):
    exists lc2_src mem2_src,
      <<STEP_SRC: ALocal.program_step e lc1_src sc1 mem1_src lc2_src sc2 mem2_src>> /\
      <<LOCAL2: sim_local lc2_src lc2_tgt>> /\
      <<MEM2: sim_memory (Local.promises lc2_tgt) mem2_src mem2_tgt>>.
  Proof.
    inv STEP_TGT.
    - esplits; eauto.
    - exploit read_step; eauto. i. des.
      esplits; try exact LOCAL2; eauto.
      inv LOCAL. ss.
    - exploit write_step; try exact LOCAL; eauto. i. des.
      esplits; try exact LOCAL2; eauto.
    - exploit read_step; eauto.
      { eapply write_step_promise_consistent; eauto. }
      i. des.
      exploit Local.read_step_future; try exact LOCAL0; eauto. i. des.
      exploit write_step; try exact LOCAL2; eauto.
      { inv LOCAL0. ss. eauto. }
      i. des.
      esplits; try exact LOCAL4; eauto.
    - exploit fence_step; eauto. i. des.
      esplits; try exact LOCAL2; eauto.
      inv LOCAL. ss.
    - exploit fence_step; eauto. i. des.
      esplits; try exact LOCAL2; eauto.
      inv LOCAL. ss.
    - exploit failure_step; eauto. i. des.
      esplits; eauto.
  Qed.

  Lemma thread_promise_step
        lang e1_src
        pf e_tgt e1_tgt e2_tgt
        (SIM1: @sim_thread lang e1_src e1_tgt)
        (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
        (MEM1_TGT: Memory.closed (Thread.memory e1_tgt))
        (STEP_TGT: Thread.promise_step pf e_tgt e1_tgt e2_tgt):
    sim_thread e1_src e2_tgt.
  Proof.
    destruct e1_src, e1_tgt, e2_tgt. ss.
    inv SIM1. inv LOCAL. inv STEP_TGT. ss. subst.
    destruct local, local0; ss. subst.
    inv LOCAL.
    econs; ss; eauto.
    eapply promise; eauto. apply WF1_TGT.
  Qed.

  Lemma thread_program_step
        lang e1_src
        e e1_tgt e2_tgt
        (SIM1: @sim_thread lang e1_src e1_tgt)
        (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
        (MEM1_TGT: Memory.closed (Thread.memory e1_tgt))
        (STEP_TGT: Thread.program_step e e1_tgt e2_tgt)
        (CONS: Local.promise_consistent (Thread.local e2_tgt)):
    exists e2_src,
      <<STEP_SRC: AThread.program_step e e1_src e2_src>> /\
      <<SIM2: sim_thread e2_src e2_tgt>>.
  Proof.
    destruct e1_src, e1_tgt, e2_tgt. ss.
    inv SIM1. inv STEP_TGT. ss. subst.
    exploit program_step; try exact LOCAL; try exact MEMORY; eauto. i. des.
    esplits.
    - econs; try exact STEP_SRC. eauto.
    - econs; eauto.
  Qed.

  Lemma thread_rtc_all_step
        lang e1_src
        e1_tgt e2_tgt
        (SIM1: @sim_thread lang e1_src e1_tgt)
        (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
        (SC1_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
        (MEM1_TGT: Memory.closed (Thread.memory e1_tgt))
        (STEPS_TGT: rtc (@Thread.all_step lang) e1_tgt e2_tgt)
        (CONS: Local.promise_consistent (Thread.local e2_tgt)):
    exists e2_src,
      <<STEPS_SRC: rtc (union (@AThread.program_step lang)) e1_src e2_src>> /\
      <<SIM2: sim_thread e2_src e2_tgt>>.
  Proof.
    revert e1_src SIM1.
    induction STEPS_TGT; eauto; i.
    inv H. inv USTEP.
    exploit Thread.step_future; eauto. i. des.
    inv STEP.
    - exploit thread_promise_step; eauto.
    - exploit thread_program_step; eauto.
      { eapply rtc_all_step_promise_consistent; eauto. }
      i. des.
      exploit IHSTEPS_TGT; try exact SIM2; eauto. i. des.
      esplits; try exact SIM0.
      econs 2; eauto.
  Qed.

  Lemma thread_rtc_tau_step
        lang e1_src
        e1_tgt e2_tgt
        (SIM1: @sim_thread lang e1_src e1_tgt)
        (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
        (SC1_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
        (MEM1_TGT: Memory.closed (Thread.memory e1_tgt))
        (STEPS_TGT: rtc (@Thread.tau_step lang) e1_tgt e2_tgt)
        (CONS: Local.promise_consistent (Thread.local e2_tgt)):
    exists e2_src,
      <<STEPS_SRC: rtc (tau (@AThread.program_step lang)) e1_src e2_src>> /\
      <<SIM2: sim_thread e2_src e2_tgt>>.
  Proof.
    revert e1_src SIM1.
    induction STEPS_TGT; eauto; i.
    inv H. inv TSTEP.
    exploit Thread.step_future; eauto. i. des.
    inv STEP.
    - exploit thread_promise_step; eauto.
    - exploit thread_program_step; eauto.
      { eapply rtc_tau_step_promise_consistent; eauto. }
      i. des.
      exploit IHSTEPS_TGT; try exact SIM2; eauto. i. des.
      esplits; try exact SIM0.
      econs 2; eauto.
  Qed.


  (* existence of sim *)

  Inductive sim_memory_aux (dom: list (Loc.t * Time.t)) (promises mem_src mem_tgt: Memory.t): Prop :=
  | sim_memory_aux_intro
      (SOUND: Memory.le mem_src mem_tgt)
      (COMPLETE1: forall loc from to msg
                    (IN: List.In (loc, to) dom)
                    (GETP: Memory.get loc to promises = Some (from, msg))
                    (GET_TGT: Memory.get loc to mem_tgt = Some (from, msg)),
          Memory.get loc to mem_src = None)
      (COMPLETE2: forall loc from to msg
                    (GETP: Memory.get loc to promises = None)
                    (GET_TGT: Memory.get loc to mem_tgt = Some (from, msg)),
          Memory.get loc to mem_src = Some (from, msg))
  .

  Lemma sim_memory_aux_exists
        dom promises mem_tgt
        (LE: Memory.le promises mem_tgt):
    exists mem_src, sim_memory_aux dom promises mem_src mem_tgt.
  Proof.
    induction dom.
    { exists mem_tgt. econs; i; eauto; try refl. inv IN. }
    des. destruct a as [loc to]. inv IHdom.
    destruct (Memory.get loc to promises) as [[from msg]|] eqn:GETT; cycle 1.
    { exists mem_src. econs; i; ss; eauto.
      inv IN; eauto. inv H. congr. }
    destruct (Memory.get loc to mem_src) as [[from_src msg_src]|] eqn:GETS; cycle 1.
    { exists mem_src. econs; i; ss; eauto.
      inv IN; eauto. inv H. ss. }
    exploit SOUND; eauto. i.
    exploit LE; eauto. i.
    rewrite x in *. inv x0.
    exploit Memory.remove_exists; try exact GETS. i. des.
    exists mem2. econs; ss; ii.
    - revert LHS.
      erewrite Memory.remove_o; eauto. condtac; ss; eauto.
    - erewrite Memory.remove_o; eauto. condtac; ss.
      inv IN; eauto. inv H. des; congr.
    - erewrite Memory.remove_o; eauto. condtac; ss; eauto.
      des. subst. congr.
  Qed.

  Lemma sim_memory_exists
        promises mem_tgt
        (LE: Memory.le promises mem_tgt)
        (FINITE: Memory.finite promises):
    exists mem_src, sim_memory promises mem_src mem_tgt.
  Proof.
    destruct FINITE.
    exploit (@sim_memory_aux_exists x promises mem_tgt); eauto. i. des.
    inv x1.
    exists mem_src. econs; eauto.
  Qed.

  Lemma sim_thread_exists
        lang e
        (WF: Local.wf (Thread.local e) (Thread.memory e))
        (SC: Memory.closed_timemap (Thread.sc e) (Thread.memory e))
        (MEM: Memory.closed (Thread.memory e)):
    exists e_src, <<SIM: @sim_thread lang e_src e>>.
  Proof.
    destruct e. destruct local. inv WF. ss.
    exploit sim_memory_exists; eauto. i. des.
    exists (Thread.mk lang state (Local.mk tview Memory.bot) sc mem_src).
    ss.
  Qed.

  Lemma sim_memory_inhabited
        promises mem_src mem_tgt
        (SIM: sim_memory promises mem_src mem_tgt)
        (BOT: Memory.bot_none promises)
        (INHABITED_TGT: Memory.inhabited mem_tgt):
    <<INHABITED_SRC: Memory.inhabited mem_src>>.
  Proof.
    inv SIM. ii.
    specialize (BOT loc). specialize (INHABITED_TGT loc).
    exploit COMPLETE2; eauto.
  Qed.

  Lemma sim_memory_vals_incl
        promises_tgt mem_src mem_tgt
        (MEM: sim_memory promises_tgt mem_src mem_tgt):
    vals_incl mem_src mem_tgt.
  Proof.
    inv MEM. ii. exploit SOUND; eauto.
  Qed.
End PFStep.
