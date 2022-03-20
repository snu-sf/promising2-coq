Require Import Omega.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.

Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import Syntax.
Require Import Semantics.

Require Import PromiseConsistent.

Require Import FulfillStep.

Require Import PromotionDef.
Require Import SimCommon.

Set Implicit Arguments.


Module SimThreadOther.
  Import SimCommon.

  Inductive sim_thread (l: Loc.t) (e_src e_tgt: Thread.t lang): Prop :=
  | sim_thread_intro
      (LOCFREE: loc_free_stmts l (State.stmts (Thread.state e_src)))
      (STATE: (Thread.state e_src) = (Thread.state e_tgt))
      (LOCAL: sim_local l (Thread.local e_src) (Thread.local e_tgt))
      (SC: sim_timemap l (Thread.sc e_src) (Thread.sc e_tgt))
      (MEMORY: sim_memory l (Thread.memory e_src) (Thread.memory e_tgt))
      (PROMISES: forall to, Memory.get l to (Local.promises (Thread.local e_src)) = None)
      (FULFILLABLE: fulfillable l (Local.tview (Thread.local e_src)) (Thread.memory e_src)
                                  (Local.promises (Thread.local e_src)))
  .
  #[export]
  Hint Constructors sim_thread: core.

  Lemma sim_thread_promise_step
        l e1_src
        pf e_tgt e1_tgt e2_tgt
        (SIM1: sim_thread l e1_src e1_tgt)
        (WF1_SRC: Local.wf (Thread.local e1_src) (Thread.memory e1_src))
        (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
        (CLOSED1_SRC: Memory.closed (Thread.memory e1_src))
        (STEP_TGT: Thread.promise_step pf e_tgt e1_tgt e2_tgt):
    exists e_src e2_src,
      <<STEP_SRC: Thread.opt_promise_step e_src e1_src e2_src>> /\
      <<SIM2: sim_thread l e2_src e2_tgt>> /\
      <<MEMLOC: forall to, Memory.get l to (Thread.memory e1_src) = Memory.get l to (Thread.memory e2_src)>>.
  Proof.
    inversion STEP_TGT. subst.
    destruct (Loc.eq_dec loc l).
    { subst. inv LOCAL; ss.
      esplits; [econs 1| |]; eauto.
      inv SIM1. ss.
      exploit promise_loc; try exact PROMISE; try apply LOCAL; eauto. i. des.
      econs; ss; eauto.
      econs; ss; eauto; try apply LOCAL.
    }
    exploit promise_step; try exact LOCAL; try apply SIM1;
      try apply WF1_SRC; try apply WF1_TGT; eauto.
    i. des.
    destruct e1_src. ss.
    esplits.
    - econs 2. econs; eauto.
    - inv SIM1. ss. econs; eauto; ss.
      i. inv STEP_SRC.
      erewrite <- promise_eq_promises; try exact PROMISE; eauto.
    - i. s. inv STEP_SRC.
      erewrite promise_eq_mem; try exact PROMISE; eauto.
  Qed.

  Lemma sim_thread_program_step
        l e1_src
        e_tgt e1_tgt e2_tgt
        (SIM1: sim_thread l e1_src e1_tgt)
        (WF1_SRC: Local.wf (Thread.local e1_src) (Thread.memory e1_src))
        (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
        (SC1_SRC: Memory.closed_timemap (Thread.sc e1_src) (Thread.memory e1_src))
        (SC1_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
        (CLOSED1_SRC: Memory.closed (Thread.memory e1_src))
        (CLOSED1_TGT: Memory.closed (Thread.memory e1_tgt))
        (STEP_TGT: Thread.program_step e_tgt e1_tgt e2_tgt):
    exists e_src e2_src,
      <<STEP_SRC: Thread.opt_program_step e_src e1_src e2_src>> /\
      <<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>> /\
      <<SIM2: sim_thread l e2_src e2_tgt>> /\
      <<MEMLOC: forall to, Memory.get l to (Thread.memory e1_src) = Memory.get l to (Thread.memory e2_src)>>.
  Proof.
    inv STEP_TGT; ss.
    hexploit loc_free_step_is_accessing_loc; eauto; i.
    { inv SIM1. ss. subst. eauto. }
    exploit program_step; try exact LOCAL; try eapply SIM1; eauto. i. des.
    destruct e1_src. ss.
    esplits.
    - econs 2. econs; try exact STEP_SRC.
      inv SIM1. inv STATE0. ss.
      rewrite H0. rewrite EVENT2. eauto.
    - ss.
    - econs; eauto.
      + s. eapply step_loc_free; eauto.
        inv SIM1. ss. subst. ss.
      + s. i. inv SIM1.
        erewrite <- program_step_eq_promises; eauto.
        erewrite ThreadEvent.eq_program_event_eq_loc; eauto.
    - s. i.
      eapply program_step_eq_mem; eauto.
      erewrite ThreadEvent.eq_program_event_eq_loc; eauto.
  Qed.

  Lemma sim_thread_step
        l e1_src
        pf e_tgt e1_tgt e2_tgt
        (SIM1: sim_thread l e1_src e1_tgt)
        (WF1_SRC: Local.wf (Thread.local e1_src) (Thread.memory e1_src))
        (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
        (SC1_SRC: Memory.closed_timemap (Thread.sc e1_src) (Thread.memory e1_src))
        (SC1_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
        (CLOSED1_SRC: Memory.closed (Thread.memory e1_src))
        (CLOSED1_TGT: Memory.closed (Thread.memory e1_tgt))
        (STEP_TGT: Thread.step pf e_tgt e1_tgt e2_tgt):
    exists e_src e2_src,
      <<STEP_SRC: Thread.opt_step e_src e1_src e2_src>> /\
      <<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>> /\
      <<SIM2: sim_thread l e2_src e2_tgt>> /\
      <<MEMLOC: forall to, Memory.get l to (Thread.memory e1_src) = Memory.get l to (Thread.memory e2_src)>>.
  Proof.
    inv STEP_TGT.
    - exploit sim_thread_promise_step; eauto. i. des.
      esplits.
      + inv STEP_SRC.
        * econs 1.
        * econs 2. econs 1; eauto.
      + inv STEP. ss. inv STEP_SRC; ss. inv STEP. ss.
      + ss.
      + ss.
    - exploit sim_thread_program_step; eauto. i. des.
      esplits.
      + inv STEP_SRC.
        * econs 1.
        * econs 2. econs 2; eauto.
      + ss.
      + ss.
      + ss.
  Qed.

  Lemma sim_thread_opt_step
        l e1_src
        e_tgt e1_tgt e2_tgt
        (SIM1: sim_thread l e1_src e1_tgt)
        (WF1_SRC: Local.wf (Thread.local e1_src) (Thread.memory e1_src))
        (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
        (SC1_SRC: Memory.closed_timemap (Thread.sc e1_src) (Thread.memory e1_src))
        (SC1_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
        (CLOSED1_SRC: Memory.closed (Thread.memory e1_src))
        (CLOSED1_TGT: Memory.closed (Thread.memory e1_tgt))
        (STEP_TGT: Thread.opt_step e_tgt e1_tgt e2_tgt):
    exists e_src e2_src,
      <<STEP_SRC: Thread.opt_step e_src e1_src e2_src>> /\
      <<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>> /\
      <<SIM2: sim_thread l e2_src e2_tgt>> /\
      <<MEMLOC: forall to, Memory.get l to (Thread.memory e1_src) = Memory.get l to (Thread.memory e2_src)>>.
  Proof.
    inv STEP_TGT.
    - esplits; eauto. econs 1.
    - exploit sim_thread_step; eauto.
  Qed.

  Lemma sim_thread_rtc_tau_step
        l e1_src
        e1_tgt e2_tgt
        (SIM1: sim_thread l e1_src e1_tgt)
        (WF1_SRC: Local.wf (Thread.local e1_src) (Thread.memory e1_src))
        (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
        (SC1_SRC: Memory.closed_timemap (Thread.sc e1_src) (Thread.memory e1_src))
        (SC1_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
        (CLOSED1_SRC: Memory.closed (Thread.memory e1_src))
        (CLOSED1_TGT: Memory.closed (Thread.memory e1_tgt))
        (STEPS_TGT: rtc (@Thread.tau_step lang) e1_tgt e2_tgt):
    exists e2_src,
      <<STEPS_SRC: rtc (@Thread.tau_step lang) e1_src e2_src>> /\
      <<SIM2: sim_thread l e2_src e2_tgt>> /\
      <<MEMLOC: forall to, Memory.get l to (Thread.memory e1_src) = Memory.get l to (Thread.memory e2_src)>>.
  Proof.
    revert e1_src SIM1 WF1_SRC SC1_SRC CLOSED1_SRC.
    induction STEPS_TGT; i.
    - esplits; eauto.
    - inv H. inv TSTEP.
      exploit sim_thread_step; eauto. i. des.
      exploit Thread.step_future; try exact STEP; eauto. i. des.
      exploit Thread.opt_step_future; try exact STEP_SRC; eauto. i. des.
      exploit IHSTEPS_TGT; eauto. i. des.
      inv STEP_SRC.
      + esplits; eauto.
      + esplits; [M|..]; eauto.
        * econs; [|eauto].
          econs; [econs; eauto|]. rewrite <- EVENT. ss.
        * i. rewrite MEMLOC. ss.
  Qed.

  Lemma sim_thread_plus_step
        l e1_src
        pf e_tgt e1_tgt e2_tgt e3_tgt
        (SIM1: sim_thread l e1_src e1_tgt)
        (WF1_SRC: Local.wf (Thread.local e1_src) (Thread.memory e1_src))
        (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
        (SC1_SRC: Memory.closed_timemap (Thread.sc e1_src) (Thread.memory e1_src))
        (SC1_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
        (CLOSED1_SRC: Memory.closed (Thread.memory e1_src))
        (CLOSED1_TGT: Memory.closed (Thread.memory e1_tgt))
        (STEPS_TGT: rtc (@Thread.tau_step lang) e1_tgt e2_tgt)
        (STEP_TGT: Thread.step pf e_tgt e2_tgt e3_tgt):
    exists e_src e2_src e3_src,
      <<STEPS_SRC: rtc (@Thread.tau_step lang) e1_src e2_src>> /\
      <<STEP_SRC: Thread.opt_step e_src e2_src e3_src>> /\
      <<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>> /\
      <<SIM3: sim_thread l e3_src e3_tgt>> /\
      <<MEMLOC: forall to, Memory.get l to (Thread.memory e1_src) = Memory.get l to (Thread.memory e3_src)>>.
  Proof.
    exploit sim_thread_rtc_tau_step; eauto. i. des.
    exploit Thread.rtc_tau_step_future; try exact STEPS_SRC; eauto. i. des.
    exploit Thread.rtc_tau_step_future; try exact STEPS_TGT; eauto. i. des.
    exploit sim_thread_step; eauto. i. des.
    esplits; eauto.
    i. rewrite MEMLOC. ss.
  Qed.


  (* future *)

  Lemma sim_thread_future
        l
        st_src lc_src sc1_src mem1_src sc2_src mem2_src
        st_tgt lc_tgt sc1_tgt mem1_tgt sc2_tgt mem2_tgt
        (SIM1: sim_thread l
                          (Thread.mk lang st_src lc_src sc1_src mem1_src)
                          (Thread.mk lang st_tgt lc_tgt sc1_tgt mem1_tgt))
        (WF1_SRC: Local.wf lc_src mem1_src)
        (MEM_SRC: Memory.future mem1_src mem2_src)
        (SC: sim_timemap l sc2_src sc2_tgt)
        (MEM: sim_memory l mem2_src mem2_tgt)
        (PREV: Memory.prev_None mem1_src mem2_src):
    sim_thread l
               (Thread.mk lang st_src lc_src sc2_src mem2_src)
               (Thread.mk lang st_tgt lc_tgt sc2_tgt mem2_tgt).
  Proof.
    inv SIM1. ss. econs; s; eauto. ii.
    exploit FULFILLABLE; eauto. i. des. split; ss.
    unfold prev_released_le_loc in *. des_ifs; ss.
    - exploit Memory.future_get1; try exact Heq0; eauto. i. des.
      inv MSG_LE. inv RELEASED; try congr.
      rewrite Heq in *. inv GET.
      unnw. etrans; eauto. split; apply LE.
    - exploit Memory.future_get1; try exact Heq0; eauto. i. des.
      inv MSG_LE. inv RELEASED; try congr.
    - inv WF1_SRC. exploit PROMISES0; eauto. i.
      exploit PREV; eauto; ss. ii. congr.
    - inv WF1_SRC. exploit PROMISES0; eauto. i.
      exploit PREV; eauto; ss. ii. congr.
  Qed.


  (* terminal *)

  Lemma sim_thread_promises_bot
        l e_src e_tgt
        (SIM: sim_thread l e_src e_tgt)
        (PROMISES_TGT: (Local.promises (Thread.local e_tgt)) = Memory.bot):
    <<PROMISES_SRC: (Local.promises (Thread.local e_src)) = Memory.bot>>.
  Proof.
    inv SIM. inv LOCAL. apply Memory.ext. i.
    rewrite Memory.bot_get.
    destruct (Loc.eq_dec loc l); subst; ss.
    symmetry in PROMISES1.
    exploit sim_memory_get_None_src; eauto.
    rewrite PROMISES_TGT. rewrite Memory.bot_get. ss.
  Qed.

  Lemma sim_thread_terminal
        l e_src e_tgt
        (SIM: sim_thread l e_src e_tgt)
        (TERMINAL_TGT: (Language.is_terminal lang) (Thread.state e_tgt)):
    <<TERMINAL_SRC: (Language.is_terminal lang) (Thread.state e_src)>>.
  Proof.
    inv SIM. rewrite STATE. ss.
  Qed.


  (* certification *)

  Lemma sim_thread_cap
        l e_src e_tgt
        sc_src sc_tgt
        cap_src cap_tgt
        (SIM: sim_thread l e_src e_tgt)
        (WF_SRC: Local.wf (Thread.local e_src) (Thread.memory e_src))
        (WF_TGT: Local.wf (Thread.local e_tgt) (Thread.memory e_tgt))
        (CLOSED_SRC: Memory.closed (Thread.memory e_src))
        (CLOSED_TGT: Memory.closed (Thread.memory e_tgt))
        (SC_SRC: Memory.max_full_timemap cap_src sc_src)
        (SC_TGT: Memory.max_full_timemap cap_tgt sc_tgt)
        (CAP_SRC: Memory.cap (Local.promises (Thread.local e_src)) (Thread.memory e_src) cap_src)
        (CAP_TGT: Memory.cap (Local.promises (Thread.local e_tgt)) (Thread.memory e_tgt) cap_tgt):
    sim_thread l
               (Thread.mk lang (Thread.state e_src) (Thread.local e_src) sc_src cap_src)
               (Thread.mk lang (Thread.state e_tgt) (Thread.local e_tgt) sc_tgt cap_tgt).
  Proof.
    inv SIM. inv LOCAL.
    exploit sim_memory_cap; [apply PROMISES1|exact MEMORY|..]; eauto. i. des.
    hexploit sim_memory_max_full_timemap; try exact x0; eauto. i. des.
    econs; eauto.
    s. eapply cap_fulfillable; eauto. apply WF_SRC.
  Qed.

  Lemma sim_thread_consistent
        l e_src e_tgt
        (SIM: sim_thread l e_src e_tgt)
        (WF_SRC: Local.wf (Thread.local e_src) (Thread.memory e_src))
        (WF_TGT: Local.wf (Thread.local e_tgt) (Thread.memory e_tgt))
        (SC_SRC: Memory.closed_timemap (Thread.sc e_src) (Thread.memory e_src))
        (SC_TGT: Memory.closed_timemap (Thread.sc e_tgt) (Thread.memory e_tgt))
        (CLOSED_SRC: Memory.closed (Thread.memory e_src))
        (CLOSED_TGT: Memory.closed (Thread.memory e_tgt))
        (CONSISTENT_TGT: Thread.consistent e_tgt):
    <<CONSISTENT_SRC: Thread.consistent e_src>>.
  Proof.
    exploit Memory.cap_exists; try exact CLOSED_TGT. i. des.
    exploit Memory.cap_closed; eauto. i.
    exploit Memory.max_full_timemap_exists; try apply x0. i. des.
    ii.
    exploit sim_thread_cap; try exact SIM; try exact CAP0; try exact CAP; eauto. i.
    exploit Local.cap_wf; try exact WF_SRC; eauto. intro WF_CAP_SRC.
    exploit Local.cap_wf; try exact WF_TGT; eauto. intro WF_CAP_TGT.
    hexploit Memory.max_full_timemap_closed; try exact SC_MAX. intro SC_MAX_SRC.
    hexploit Memory.max_full_timemap_closed; try exact x1. intro SC_MAX_TGT.
    exploit Memory.cap_closed; try exact CLOSED_SRC; eauto. intro CLOSED_CAP_SRC.
    exploit Memory.cap_closed; try exact CLOSED_TGT; eauto. intro CLOSED_CAP_TGT.
    exploit CONSISTENT_TGT; eauto. i. des.
    - left. unfold Thread.steps_failure in *. des.
      exploit sim_thread_plus_step; eauto. s. i. des.
      destruct e_src0; ss. inv STEP_SRC.
      destruct pf; try by (inv STEP; inv STEP0).
      esplits; eauto.
    - right.
      exploit sim_thread_rtc_tau_step; try exact STEPS; eauto. i. des.
      esplits; eauto.
      eapply sim_thread_promises_bot; eauto.
  Qed.
End SimThreadOther.
