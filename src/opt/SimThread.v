From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
Require Import Event.
From PromisingLib Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import PromiseConsistent.

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.

Set Implicit Arguments.


Section SimulationThread.
  Variable (lang_src lang_tgt:language).

  Definition SIM_TERMINAL :=
    forall (st_src:(Language.state lang_src)) (st_tgt:(Language.state lang_tgt)), Prop.

  Definition SIM_THREAD :=
    forall (sim_terminal: SIM_TERMINAL)
      (st1_src:(Language.state lang_src)) (lc1_src:Local.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
      (st1_tgt:(Language.state lang_tgt)) (lc1_tgt:Local.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t), Prop.

  Definition _sim_thread_step
             (sim_thread: forall (st1_src:(Language.state lang_src)) (lc1_src:Local.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
                            (st1_tgt:(Language.state lang_tgt)) (lc1_tgt:Local.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t), Prop)
             st1_src lc1_src sc1_src mem1_src
             st1_tgt lc1_tgt sc1_tgt mem1_tgt
    :=
    forall pf_tgt e_tgt st3_tgt lc3_tgt sc3_tgt mem3_tgt
      (STEP_TGT: Thread.step pf_tgt e_tgt
                             (Thread.mk _ st1_tgt lc1_tgt sc1_tgt mem1_tgt)
                             (Thread.mk _ st3_tgt lc3_tgt sc3_tgt mem3_tgt)),
      <<FAILURE: Thread.steps_failure (Thread.mk _ st1_src lc1_src sc1_src mem1_src)>> \/
      exists e_src st2_src lc2_src sc2_src mem2_src st3_src lc3_src sc3_src mem3_src,
        <<FAILURE: e_tgt <> ThreadEvent.failure>> /\
        <<STEPS: rtc (@Thread.tau_step _)
                     (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                     (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>> /\
        <<STEP_SRC: Thread.opt_step e_src
                                    (Thread.mk _ st2_src lc2_src sc2_src mem2_src)
                                    (Thread.mk _ st3_src lc3_src sc3_src mem3_src)>> /\
        <<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>> /\
        <<SC3: TimeMap.le sc3_src sc3_tgt>> /\
        <<MEMORY3: sim_memory mem3_src mem3_tgt>> /\
        <<SIM: sim_thread st3_src lc3_src sc3_src mem3_src st3_tgt lc3_tgt sc3_tgt mem3_tgt>>.

  Definition _sim_thread
             (sim_thread: SIM_THREAD)
             (sim_terminal: SIM_TERMINAL)
             (st1_src:(Language.state lang_src)) (lc1_src:Local.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
             (st1_tgt:(Language.state lang_tgt)) (lc1_tgt:Local.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t): Prop :=
    forall sc1_src mem1_src
      sc1_tgt mem1_tgt
      (SC: TimeMap.le sc1_src sc1_tgt)
      (MEMORY: sim_memory mem1_src mem1_tgt)
      (SC_FUTURE_SRC: TimeMap.le sc0_src sc1_src)
      (SC_FUTURE_TGT: TimeMap.le sc0_tgt sc1_tgt)
      (MEM_FUTURE_SRC: Memory.future_weak mem0_src mem1_src)
      (MEM_FUTURE_TGT: Memory.future_weak mem0_tgt mem1_tgt)
      (WF_SRC: Local.wf lc1_src mem1_src)
      (WF_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM_SRC: Memory.closed mem1_src)
      (MEM_TGT: Memory.closed mem1_tgt)
      (CONS_TGT: Local.promise_consistent lc1_tgt),
      <<TERMINAL:
        forall (TERMINAL_TGT: (Language.is_terminal lang_tgt) st1_tgt),
          <<FAILURE: Thread.steps_failure (Thread.mk _ st1_src lc1_src sc1_src mem1_src)>> \/
          exists st2_src lc2_src sc2_src mem2_src,
            <<STEPS: rtc (@Thread.tau_step _)
                         (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                         (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>> /\
            <<SC: TimeMap.le sc2_src sc1_tgt>> /\
            <<MEMORY: sim_memory mem2_src mem1_tgt>> /\
            <<TERMINAL_SRC: (Language.is_terminal lang_src) st2_src>> /\
            <<LOCAL: sim_local SimPromises.bot lc2_src lc1_tgt>> /\
            <<TERMINAL: sim_terminal st2_src st1_tgt>>>> /\
      <<CAP:
        forall mem2_src
          (CAP_SRC: Memory.cap (Local.promises lc1_src) mem1_src mem2_src),
        exists mem2_tgt,
          <<MEMORY: sim_memory mem2_src mem2_tgt>> /\
          <<CAP_TGT: Memory.cap (Local.promises lc1_tgt) mem1_tgt mem2_tgt>>>> /\
      <<PROMISES:
        forall (PROMISES_TGT: (Local.promises lc1_tgt) = Memory.bot)
          (NORESERVE: Memory.no_reserve mem1_tgt),
          <<FAILURE: Thread.steps_failure (Thread.mk _ st1_src lc1_src sc1_src mem1_src)>> \/
          exists st2_src lc2_src sc2_src mem2_src,
            <<STEPS: rtc (@Thread.tau_step _)
                         (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                         (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>> /\
            <<PROMISES_SRC: (Local.promises lc2_src) = Memory.bot>>>> /\
      <<STEP: _sim_thread_step (sim_thread sim_terminal)
                               st1_src lc1_src sc1_src mem1_src
                               st1_tgt lc1_tgt sc1_tgt mem1_tgt>>.

  Lemma _sim_thread_mon: monotone9 _sim_thread.
  Proof.
    ii. exploit IN; try apply SC; eauto. i. des.
    splits; eauto. ii.
    exploit STEP; eauto. i. des; eauto.
    right. esplits; eauto.
  Qed.
  #[local]
  Hint Resolve _sim_thread_mon: paco.

  Definition sim_thread: SIM_THREAD := paco9 _sim_thread bot9.

  Lemma sim_thread_mon
        sim_terminal1 sim_terminal2
        (SIM: sim_terminal1 <2= sim_terminal2):
    sim_thread sim_terminal1 <8= sim_thread sim_terminal2.
  Proof.
    pcofix CIH. i. punfold PR. pfold. ii.
    exploit PR; try apply SC; eauto. i. des.
    splits; auto.
    - i. exploit TERMINAL; eauto. i. des; eauto.
      right. esplits; eauto.
    - ii. exploit STEP; eauto. i. des; eauto.
      inv SIM0; [|done].
      right. esplits; eauto.
  Qed.
End SimulationThread.
#[export]
Hint Resolve _sim_thread_mon: paco.


Lemma sim_thread_step
      lang_src lang_tgt
      sim_terminal
      pf_tgt e_tgt
      st1_src lc1_src sc1_src mem1_src
      st1_tgt lc1_tgt sc1_tgt mem1_tgt
      st3_tgt lc3_tgt sc3_tgt mem3_tgt
      (STEP: @Thread.step lang_tgt pf_tgt e_tgt
                          (Thread.mk _ st1_tgt lc1_tgt sc1_tgt mem1_tgt)
                          (Thread.mk _ st3_tgt lc3_tgt sc3_tgt mem3_tgt))
      (SC: TimeMap.le sc1_src sc1_tgt)
      (MEMORY: sim_memory mem1_src mem1_tgt)
      (WF_SRC: Local.wf lc1_src mem1_src)
      (WF_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM_SRC: Memory.closed mem1_src)
      (MEM_TGT: Memory.closed mem1_tgt)
      (CONS_TGT: Local.promise_consistent lc3_tgt)
      (SIM: sim_thread sim_terminal st1_src lc1_src sc1_src mem1_src st1_tgt lc1_tgt sc1_tgt mem1_tgt):
  <<FAILURE: Thread.steps_failure (Thread.mk lang_src st1_src lc1_src sc1_src mem1_src)>> \/
  exists e_src st2_src lc2_src sc2_src mem2_src st3_src lc3_src sc3_src mem3_src,
    <<FAILURE: e_tgt <> ThreadEvent.failure>> /\
    <<STEPS: rtc (@Thread.tau_step lang_src)
                 (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                 (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>> /\
    <<STEP: Thread.opt_step e_src
                            (Thread.mk _ st2_src lc2_src sc2_src mem2_src)
                            (Thread.mk _ st3_src lc3_src sc3_src mem3_src)>> /\
    <<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>> /\
    <<SC: TimeMap.le sc3_src sc3_tgt>> /\
    <<MEMORY: sim_memory mem3_src mem3_tgt>> /\
    <<WF_SRC: Local.wf lc3_src mem3_src>> /\
    <<WF_TGT: Local.wf lc3_tgt mem3_tgt>> /\
    <<SC_SRC: Memory.closed_timemap sc3_src mem3_src>> /\
    <<SC_TGT: Memory.closed_timemap sc3_tgt mem3_tgt>> /\
    <<MEM_SRC: Memory.closed mem3_src>> /\
    <<MEM_TGT: Memory.closed mem3_tgt>> /\
    <<SIM: sim_thread sim_terminal st3_src lc3_src sc3_src mem3_src st3_tgt lc3_tgt sc3_tgt mem3_tgt>>.
Proof.
  hexploit step_promise_consistent; eauto. s. i.
  punfold SIM. exploit SIM; eauto; try refl. i. des.
  exploit Thread.step_future; eauto. s. i. des.
  exploit STEP0; eauto. i. des; eauto.
  inv SIM0; [|done]. right.
  exploit Thread.rtc_tau_step_future; eauto. s. i. des.
  exploit Thread.opt_step_future; eauto. s. i. des.
  esplits; eauto.
Qed.

Lemma sim_thread_opt_step
      lang_src lang_tgt
      sim_terminal
      e_tgt
      st1_src lc1_src sc1_src mem1_src
      st1_tgt lc1_tgt sc1_tgt mem1_tgt
      st3_tgt lc3_tgt sc3_tgt mem3_tgt
      (STEP: @Thread.opt_step lang_tgt e_tgt
                              (Thread.mk _ st1_tgt lc1_tgt sc1_tgt mem1_tgt)
                              (Thread.mk _ st3_tgt lc3_tgt sc3_tgt mem3_tgt))
      (SC: TimeMap.le sc1_src sc1_tgt)
      (MEMORY: sim_memory mem1_src mem1_tgt)
      (WF_SRC: Local.wf lc1_src mem1_src)
      (WF_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM_SRC: Memory.closed mem1_src)
      (MEM_TGT: Memory.closed mem1_tgt)
      (CONS_TGT: Local.promise_consistent lc3_tgt)
      (SIM: sim_thread sim_terminal st1_src lc1_src sc1_src mem1_src st1_tgt lc1_tgt sc1_tgt mem1_tgt):
  <<FAILURE: Thread.steps_failure (Thread.mk lang_src st1_src lc1_src sc1_src mem1_src)>> \/
  exists e_src st2_src lc2_src sc2_src mem2_src st3_src lc3_src sc3_src mem3_src,
    <<FAILURE: e_tgt <> ThreadEvent.failure>> /\
    <<STEPS: rtc (@Thread.tau_step lang_src)
                 (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                 (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>> /\
    <<STEP: Thread.opt_step e_src
                            (Thread.mk _ st2_src lc2_src sc2_src mem2_src)
                            (Thread.mk _ st3_src lc3_src sc3_src mem3_src)>> /\
    <<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>> /\
    <<SC: TimeMap.le sc3_src sc3_tgt>> /\
    <<MEMORY: sim_memory mem3_src mem3_tgt>> /\
    <<WF_SRC: Local.wf lc3_src mem3_src>> /\
    <<WF_TGT: Local.wf lc3_tgt mem3_tgt>> /\
    <<SC_SRC: Memory.closed_timemap sc3_src mem3_src>> /\
    <<SC_TGT: Memory.closed_timemap sc3_tgt mem3_tgt>> /\
    <<MEM_SRC: Memory.closed mem3_src>> /\
    <<MEM_TGT: Memory.closed mem3_tgt>> /\
    <<SIM: sim_thread sim_terminal st3_src lc3_src sc3_src mem3_src st3_tgt lc3_tgt sc3_tgt mem3_tgt>>.
Proof.
  inv STEP.
  - right. esplits; eauto; ss. econs 1.
  - eapply sim_thread_step; eauto.
Qed.

Lemma sim_thread_rtc_step
      lang_src lang_tgt
      sim_terminal
      st1_src lc1_src sc1_src mem1_src
      e1_tgt e2_tgt
      (STEPS: rtc (@Thread.tau_step lang_tgt) e1_tgt e2_tgt)
      (SC: TimeMap.le sc1_src (Thread.sc e1_tgt))
      (MEMORY: sim_memory mem1_src (Thread.memory e1_tgt))
      (WF_SRC: Local.wf lc1_src mem1_src)
      (WF_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
      (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
      (MEM_SRC: Memory.closed mem1_src)
      (MEM_TGT: Memory.closed (Thread.memory e1_tgt))
      (CONS_TGT: Local.promise_consistent (Thread.local e2_tgt))
      (SIM: sim_thread sim_terminal st1_src lc1_src sc1_src mem1_src (Thread.state e1_tgt) (Thread.local e1_tgt) (Thread.sc e1_tgt) (Thread.memory e1_tgt)):
  <<FAILURE: Thread.steps_failure (Thread.mk lang_src st1_src lc1_src sc1_src mem1_src)>> \/
  exists st2_src lc2_src sc2_src mem2_src,
    <<STEPS: rtc (@Thread.tau_step lang_src)
                 (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                 (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>> /\
    <<SC: TimeMap.le sc2_src (Thread.sc e2_tgt)>> /\
    <<MEMORY: sim_memory mem2_src (Thread.memory e2_tgt)>> /\
    <<WF_SRC: Local.wf lc2_src mem2_src>> /\
    <<WF_TGT: Local.wf (Thread.local e2_tgt) (Thread.memory e2_tgt)>> /\
    <<SC_SRC: Memory.closed_timemap sc2_src mem2_src>> /\
    <<SC_TGT: Memory.closed_timemap (Thread.sc e2_tgt) (Thread.memory e2_tgt)>> /\
    <<MEM_SRC: Memory.closed mem2_src>> /\
    <<MEM_TGT: Memory.closed (Thread.memory e2_tgt)>> /\
    <<SIM: sim_thread sim_terminal st2_src lc2_src sc2_src mem2_src (Thread.state e2_tgt) (Thread.local e2_tgt) (Thread.sc e2_tgt) (Thread.memory e2_tgt)>>.
Proof.
  revert SC MEMORY WF_SRC WF_TGT SC_SRC SC_TGT MEM_SRC MEM_TGT SIM.
  revert st1_src lc1_src sc1_src mem1_src.
  induction STEPS; i.
  { right. esplits; eauto. }
  inv H. inv TSTEP. destruct x, y. ss.
  exploit Thread.step_future; eauto. s. i. des.
  hexploit rtc_tau_step_promise_consistent; eauto. s. i.
  exploit sim_thread_step; eauto. i. des; eauto.
  exploit IHSTEPS; eauto. i. des.
  - left. inv FAILURE0. des.
    unfold Thread.steps_failure. esplits; [|eauto].
    etrans; eauto. etrans; eauto. inv STEP0; eauto.
    econs 2; eauto. econs.
    + econs. eauto.
    + destruct e, e_src; ss.
  - right. destruct z. ss.
    esplits; try apply MEMORY1; eauto.
    etrans; [eauto|]. etrans; [|eauto]. inv STEP0; eauto.
    econs 2; eauto. econs.
    + econs. eauto.
    + destruct e, e_src; ss.
Qed.

Lemma sim_thread_plus_step
      lang_src lang_tgt
      sim_terminal
      pf_tgt e_tgt
      st1_src lc1_src sc1_src mem1_src
      e1_tgt e2_tgt e3_tgt
      (STEPS: rtc (@Thread.tau_step lang_tgt) e1_tgt e2_tgt)
      (STEP: @Thread.step lang_tgt pf_tgt e_tgt e2_tgt e3_tgt)
      (SC: TimeMap.le sc1_src (Thread.sc e1_tgt))
      (MEMORY: sim_memory mem1_src (Thread.memory e1_tgt))
      (WF_SRC: Local.wf lc1_src mem1_src)
      (WF_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
      (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
      (MEM_SRC: Memory.closed mem1_src)
      (MEM_TGT: Memory.closed (Thread.memory e1_tgt))
      (CONS_TGT: Local.promise_consistent (Thread.local e3_tgt))
      (SIM: sim_thread sim_terminal st1_src lc1_src sc1_src mem1_src (Thread.state e1_tgt) (Thread.local e1_tgt) (Thread.sc e1_tgt) (Thread.memory e1_tgt)):
  <<FAILURE: Thread.steps_failure (Thread.mk lang_src st1_src lc1_src sc1_src mem1_src)>> \/
  exists e_src st2_src lc2_src sc2_src mem2_src st3_src lc3_src sc3_src mem3_src,
    <<FAILURE: e_tgt <> ThreadEvent.failure>> /\
    <<STEPS: rtc (@Thread.tau_step lang_src)
                 (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                 (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>> /\
    <<STEP: Thread.opt_step e_src
                            (Thread.mk _ st2_src lc2_src sc2_src mem2_src)
                            (Thread.mk _ st3_src lc3_src sc3_src mem3_src)>> /\
    <<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>> /\
    <<SC: TimeMap.le sc3_src (Thread.sc e3_tgt)>> /\
    <<MEMORY: sim_memory mem3_src (Thread.memory e3_tgt)>> /\
    <<WF_SRC: Local.wf lc3_src mem3_src>> /\
    <<WF_TGT: Local.wf (Thread.local e3_tgt) (Thread.memory e3_tgt)>> /\
    <<SC_SRC: Memory.closed_timemap sc3_src mem3_src>> /\
    <<SC_TGT: Memory.closed_timemap (Thread.sc e3_tgt) (Thread.memory e3_tgt)>> /\
    <<MEM_SRC: Memory.closed mem3_src>> /\
    <<MEM_TGT: Memory.closed (Thread.memory e3_tgt)>> /\
    <<SIM: sim_thread sim_terminal st3_src lc3_src sc3_src mem3_src (Thread.state e3_tgt) (Thread.local e3_tgt) (Thread.sc e3_tgt) (Thread.memory e3_tgt)>>.
Proof.
  destruct e1_tgt, e2_tgt, e3_tgt. ss.
  exploit Thread.rtc_tau_step_future; eauto. s. i. des.
  hexploit step_promise_consistent; eauto. s. i.
  exploit sim_thread_rtc_step; eauto. s. i. des; eauto.
  exploit Thread.rtc_tau_step_future; try exact STEPS0; eauto. s. i. des.
  exploit sim_thread_step; try exact STEP; try exact SIM0; eauto. s. i. des.
  - left. inv FAILURE. des.
    unfold Thread.steps_failure. esplits; [|eauto].
    etrans; eauto.
  - right. rewrite STEPS1 in STEPS0.
    esplits; try exact STEPS0; try exact STEP0; eauto.
Qed.

Lemma sim_thread_future
      lang_src lang_tgt
      sim_terminal
      st_src lc_src sc1_src sc2_src mem1_src mem2_src
      st_tgt lc_tgt sc1_tgt sc2_tgt mem1_tgt mem2_tgt
      (SIM: @sim_thread lang_src lang_tgt sim_terminal st_src lc_src sc1_src mem1_src st_tgt lc_tgt sc1_tgt mem1_tgt)
      (SC_FUTURE_SRC: TimeMap.le sc1_src sc2_src)
      (SC_FUTURE_TGT: TimeMap.le sc1_tgt sc2_tgt)
      (MEM_FUTURE_SRC: Memory.future_weak mem1_src mem2_src)
      (MEM_FUTURE_TGT: Memory.future_weak mem1_tgt mem2_tgt):
  sim_thread sim_terminal st_src lc_src sc2_src mem2_src st_tgt lc_tgt sc2_tgt mem2_tgt.
Proof.
  pfold. ii.
  punfold SIM. exploit SIM; (try by etrans; eauto); eauto.
Qed.


Lemma cap_property
      mem1 mem2 lc sc
      (CAP: Memory.cap (Local.promises lc) mem1 mem2)
      (WF: Local.wf lc mem1)
      (SC: Memory.closed_timemap sc mem1)
      (CLOSED: Memory.closed mem1):
  <<FUTURE: Memory.future_weak mem1 mem2>> /\
  <<WF: Local.wf lc mem2>> /\
  <<SC: Memory.closed_timemap sc mem2>> /\
  <<CLOSED: Memory.closed mem2>> /\
  <<NORESERVE: Memory.no_reserve_except (Local.promises lc) mem2>>.
Proof.
  splits.
  - eapply Memory.cap_future_weak; eauto.
  - eapply Local.cap_wf; eauto.
  - eapply Memory.cap_closed_timemap; eauto.
  - eapply Memory.cap_closed; eauto.
  - eapply Memory.cap_no_reserve_except; eauto. apply WF.
Qed.

Lemma sc_property
      sc1 sc2 mem
      (MAX: Memory.max_full_timemap mem sc2)
      (SC1: Memory.closed_timemap sc1 mem)
      (MEM: Memory.closed mem):
  <<SC2: Memory.closed_timemap sc2 mem>> /\
  <<LE: TimeMap.le sc1 sc2>>.
Proof.
  splits.
  - eapply Memory.max_full_timemap_closed; eauto.
  - eapply Memory.max_full_timemap_spec; eauto.
Qed.

Lemma sim_thread_consistent
      lang_src lang_tgt
      sim_terminal
      st_src lc_src sc_src mem_src
      st_tgt lc_tgt sc_tgt mem_tgt
      (SIM: sim_thread sim_terminal st_src lc_src sc_src mem_src st_tgt lc_tgt sc_tgt mem_tgt)
      (SC: TimeMap.le sc_src sc_tgt)
      (MEMORY: sim_memory mem_src mem_tgt)
      (WF_SRC: Local.wf lc_src mem_src)
      (WF_TGT: Local.wf lc_tgt mem_tgt)
      (SC_SRC: Memory.closed_timemap sc_src mem_src)
      (SC_TGT: Memory.closed_timemap sc_tgt mem_tgt)
      (MEM_SRC: Memory.closed mem_src)
      (MEM_TGT: Memory.closed mem_tgt)
      (CONSISTENT: Thread.consistent (Thread.mk lang_tgt st_tgt lc_tgt sc_tgt mem_tgt)):
  Thread.consistent (Thread.mk lang_src st_src lc_src sc_src mem_src).
Proof.
  hexploit consistent_promise_consistent; eauto. s. i.
  generalize SIM. intro X.
  punfold X. exploit X; eauto; try refl. i. des.
  ii. ss.
  exploit CAP; eauto. i. des.
  exploit cap_property; try exact CAP0; eauto. i. des.
  exploit cap_property; try exact CAP_TGT; eauto. i. des.
  exploit Memory.max_full_timemap_exists; try apply CLOSED0. i. des.
  exploit sim_memory_max_full_timemap; try exact MEMORY0; eauto. i. subst.
  exploit sc_property; try exact SC_MAX; eauto. i. des.
  exploit sc_property; try exact x0; eauto. i. des.
  exploit CONSISTENT; eauto. s. i. des.
  - left. inv FAILURE. des.
    exploit sim_thread_future; try exact SIM; try exact LE; try exact LE0; eauto. i.
    exploit sim_thread_plus_step; try exact STEPS; try exact FAILURE; try exact x2; eauto; try refl.
    { inv FAILURE; inv STEP0. inv LOCAL. inv LOCAL0. ss. }
    i. des; auto. ss.
  - hexploit Local.bot_promise_consistent; eauto. i.
    exploit sim_thread_future; try exact SIM; try exact LE; try exact LE0; eauto. i.
    exploit sim_thread_rtc_step; try apply STEPS; try exact x1; eauto; try refl. i. des; eauto.
    destruct e2. ss.
    punfold SIM0. exploit SIM0; eauto; try refl. i. des.
    hexploit Thread.rtc_tau_step_no_reserve_except; try exact STEPS; eauto. i.
    unfold Thread.no_reserve_except in *. ss.
    rewrite PROMISES0 in *.
    hexploit Memory.no_reserve_except_bot_no_reserve; try apply MEM_TGT0; eauto. i.
    exploit PROMISES1; eauto. i. des.
    + left. unfold Thread.steps_failure in *. des.
      esplits; [|eauto]. etrans; eauto.
    + right. eexists (Thread.mk _ _ _ _ _). splits; [|eauto].
      etrans; eauto.
Qed.
