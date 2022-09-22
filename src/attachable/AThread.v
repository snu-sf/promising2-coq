Require Import Lia.
Require Import Bool.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
Require Import Event.
Require Import Time.
From PromisingLib Require Import Language.

Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.

Require Import AMemory.
Require Import ATView.
Require Import ALocal.

Set Implicit Arguments.


Module AThread.
  Section AThread.
    Variable (lang:language).

    Inductive promise_step (pf:bool): forall (e:ThreadEvent.t) (e1 e2:Thread.t lang), Prop :=
    | promise_step_intro
        st lc1 sc1 mem1
        loc from to msg kind
        lc2 mem2
        (LOCAL: ALocal.promise_step lc1 mem1 loc from to msg lc2 mem2 kind)
        (PF: pf = orb (andb (Memory.op_kind_is_lower_full kind) (Message.is_released_none msg))
                      (Memory.op_kind_is_cancel kind)):
        promise_step pf (ThreadEvent.promise loc from to msg kind) (Thread.mk lang st lc1 sc1 mem1) (Thread.mk lang st lc2 sc1 mem2)
    .

    (* NOTE: Syscalls act like a SC fence. *)
    Inductive program_step (e:ThreadEvent.t): forall (e1 e2:Thread.t lang), Prop :=
    | program_step_intro
        st1 lc1 sc1 mem1
        st2 lc2 sc2 mem2
        (STATE: (Language.step lang) (ThreadEvent.get_program_event e) st1 st2)
        (LOCAL: ALocal.program_step e lc1 sc1 mem1 lc2 sc2 mem2):
        program_step e (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2)
    .
    #[local]
    Hint Constructors program_step: core.

    Inductive step: forall (pf:bool) (e:ThreadEvent.t) (e1 e2:Thread.t lang), Prop :=
    | step_promise
        pf e e1 e2
        (STEP: promise_step pf e e1 e2):
        step pf e e1 e2
    | step_program
        e e1 e2
        (STEP: program_step e e1 e2):
        step true e e1 e2
    .
    #[local]
    Hint Constructors step: core.

    Inductive step_allpf (e:ThreadEvent.t) (e1 e2:Thread.t lang): Prop :=
    | step_nopf_intro
        pf
        (STEP: step pf e e1 e2)
    .
    #[local]
    Hint Constructors step_allpf: core.

    Lemma allpf pf: step pf <3= step_allpf.
    Proof.
      i. econs. eauto.
    Qed.

    Definition pf_tau_step := tau (step true).
    #[local]
    Hint Unfold pf_tau_step: core.

    Definition tau_step := tau step_allpf.
    #[local]
    Hint Unfold tau_step: core.

    Definition all_step := union step_allpf.
    #[local]
    Hint Unfold all_step: core.

    Inductive opt_step: forall (e:ThreadEvent.t) (e1 e2:Thread.t lang), Prop :=
    | step_none
        e:
        opt_step ThreadEvent.silent e e
    | step_some
        pf e e1 e2
        (STEP: step pf e e1 e2):
        opt_step e e1 e2
    .
    #[local]
    Hint Constructors opt_step: core.

    Definition steps_failure (e1: Thread.t lang): Prop :=
      exists e2 e3,
        <<STEPS: rtc tau_step e1 e2>> /\
        <<FAILURE: step true ThreadEvent.failure e2 e3>>.
    #[local]
    Hint Unfold steps_failure: core.

    Definition consistent (e:Thread.t lang): Prop :=
      forall mem1 sc1
        (CAP: Memory.cap (Local.promises (Thread.local e)) (Thread.memory e) mem1)
        (SC_MAX: Memory.max_full_timemap mem1 sc1),
        <<FAILURE: steps_failure (Thread.mk lang (Thread.state e) (Thread.local e) sc1 mem1)>> \/
        exists e2,
          <<STEPS: rtc tau_step (Thread.mk lang (Thread.state e) (Thread.local e) sc1 mem1) e2>> /\
          <<PROMISES: (Local.promises (Thread.local e2)) = Memory.bot>>.


    (* step_future *)

    Lemma promise_step_future
          pf e e1 e2
          (STEP: promise_step pf e e1 e2)
          (WF1: Local.wf (Thread.local e1) (Thread.memory e1))
          (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1))
          (CLOSED1: Memory.closed (Thread.memory e1)):
      <<WF2: Local.wf (Thread.local e2) (Thread.memory e2)>> /\
      <<SC2: Memory.closed_timemap (Thread.sc e2) (Thread.memory e2)>> /\
      <<CLOSED2: Memory.closed (Thread.memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (Thread.local e1)) (Local.tview (Thread.local e2))>> /\
      <<SC_FUTURE: TimeMap.le (Thread.sc e1) (Thread.sc e2)>> /\
      <<MEM_FUTURE: Memory.future (Thread.memory e1) (Thread.memory e2)>>.
    Proof.
      inv STEP. ss.
      exploit ALocal.promise_step_future; eauto. i. des.
      splits; eauto. refl.
    Qed.

    Lemma program_step_future
          e e1 e2
          (STEP: program_step e e1 e2)
          (WF1: Local.wf (Thread.local e1) (Thread.memory e1))
          (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1))
          (CLOSED1: Memory.closed (Thread.memory e1)):
      <<WF2: Local.wf (Thread.local e2) (Thread.memory e2)>> /\
      <<SC2: Memory.closed_timemap (Thread.sc e2) (Thread.memory e2)>> /\
      <<CLOSED2: Memory.closed (Thread.memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (Thread.local e1)) (Local.tview (Thread.local e2))>> /\
      <<SC_FUTURE: TimeMap.le (Thread.sc e1) (Thread.sc e2)>> /\
      <<MEM_FUTURE: Memory.future (Thread.memory e1) (Thread.memory e2)>>.
    Proof.
      inv STEP. ss. eapply ALocal.program_step_future; eauto.
    Qed.

    Lemma step_future
          pf e e1 e2
          (STEP: step pf e e1 e2)
          (WF1: Local.wf (Thread.local e1) (Thread.memory e1))
          (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1))
          (CLOSED1: Memory.closed (Thread.memory e1)):
      <<WF2: Local.wf (Thread.local e2) (Thread.memory e2)>> /\
      <<SC2: Memory.closed_timemap (Thread.sc e2) (Thread.memory e2)>> /\
      <<CLOSED2: Memory.closed (Thread.memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (Thread.local e1)) (Local.tview (Thread.local e2))>> /\
      <<SC_FUTURE: TimeMap.le (Thread.sc e1) (Thread.sc e2)>> /\
      <<MEM_FUTURE: Memory.future (Thread.memory e1) (Thread.memory e2)>>.
    Proof.
      inv STEP.
      - eapply promise_step_future; eauto.
      - eapply program_step_future; eauto.
    Qed.

    Lemma opt_step_future
          e e1 e2
          (STEP: opt_step e e1 e2)
          (WF1: Local.wf (Thread.local e1) (Thread.memory e1))
          (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1))
          (CLOSED1: Memory.closed (Thread.memory e1)):
      <<WF2: Local.wf (Thread.local e2) (Thread.memory e2)>> /\
      <<SC2: Memory.closed_timemap (Thread.sc e2) (Thread.memory e2)>> /\
      <<CLOSED2: Memory.closed (Thread.memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (Thread.local e1)) (Local.tview (Thread.local e2))>> /\
      <<SC_FUTURE: TimeMap.le (Thread.sc e1) (Thread.sc e2)>> /\
      <<MEM_FUTURE: Memory.future (Thread.memory e1) (Thread.memory e2)>>.
    Proof.
      inv STEP.
      - esplits; eauto; refl.
      - eapply step_future; eauto.
    Qed.

    Lemma rtc_all_step_future
          e1 e2
          (STEP: rtc all_step e1 e2)
          (WF1: Local.wf (Thread.local e1) (Thread.memory e1))
          (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1))
          (CLOSED1: Memory.closed (Thread.memory e1)):
      <<WF2: Local.wf (Thread.local e2) (Thread.memory e2)>> /\
      <<SC2: Memory.closed_timemap (Thread.sc e2) (Thread.memory e2)>> /\
      <<CLOSED2: Memory.closed (Thread.memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (Thread.local e1)) (Local.tview (Thread.local e2))>> /\
      <<SC_FUTURE: TimeMap.le (Thread.sc e1) (Thread.sc e2)>> /\
      <<MEM_FUTURE: Memory.future (Thread.memory e1) (Thread.memory e2)>>.
    Proof.
      revert WF1. induction STEP.
      - i. splits; ss; refl.
      - i. inv H. inv USTEP.
        exploit step_future; eauto. i. des.
        exploit IHSTEP; eauto. i. des.
        splits; ss; etrans; eauto.
    Qed.

    Lemma rtc_tau_step_future
          e1 e2
          (STEP: rtc tau_step e1 e2)
          (WF1: Local.wf (Thread.local e1) (Thread.memory e1))
          (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1))
          (CLOSED1: Memory.closed (Thread.memory e1)):
      <<WF2: Local.wf (Thread.local e2) (Thread.memory e2)>> /\
      <<SC2: Memory.closed_timemap (Thread.sc e2) (Thread.memory e2)>> /\
      <<CLOSED2: Memory.closed (Thread.memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (Thread.local e1)) (Local.tview (Thread.local e2))>> /\
      <<SC_FUTURE: TimeMap.le (Thread.sc e1) (Thread.sc e2)>> /\
      <<MEM_FUTURE: Memory.future (Thread.memory e1) (Thread.memory e2)>>.
    Proof.
      apply rtc_all_step_future; auto.
      eapply rtc_implies; [|eauto].
      apply tau_union.
    Qed.

    Lemma promise_step_inhabited
          pf e e1 e2
          (STEP: promise_step pf e e1 e2)
          (INHABITED1: Memory.inhabited (Thread.memory e1)):
      <<INHABITED2: Memory.inhabited (Thread.memory e2)>>.
    Proof.
      inv STEP. ss.
      eapply ALocal.promise_step_inhabited; eauto.
    Qed.

    Lemma program_step_inhabited
          e e1 e2
          (STEP: program_step e e1 e2)
          (INHABITED1: Memory.inhabited (Thread.memory e1)):
      <<INHABITED2: Memory.inhabited (Thread.memory e2)>>.
    Proof.
      inv STEP. ss.
      eapply ALocal.program_step_inhabited; eauto.
    Qed.

    Lemma step_inhabited
          pf e e1 e2
          (STEP: step pf e e1 e2)
          (INHABITED1: Memory.inhabited (Thread.memory e1)):
      <<INHABITED2: Memory.inhabited (Thread.memory e2)>>.
    Proof.
      inv STEP.
      - eapply promise_step_inhabited; eauto.
      - eapply program_step_inhabited; eauto.
    Qed.


    (* step_disjoint *)

    Lemma promise_step_disjoint
          pf e e1 e2 lc
          (STEP: promise_step pf e e1 e2)
          (WF1: Local.wf (Thread.local e1) (Thread.memory e1))
          (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1))
          (CLOSED1: Memory.closed (Thread.memory e1))
          (DISJOINT1: Local.disjoint (Thread.local e1) lc)
          (WF: Local.wf lc (Thread.memory e1)):
      <<DISJOINT2: Local.disjoint (Thread.local e2) lc>> /\
      <<WF: Local.wf lc (Thread.memory e2)>>.
    Proof.
      inv STEP.
      exploit ALocal.promise_step_future; eauto. i. des.
      exploit ALocal.promise_step_disjoint; eauto.
    Qed.

    Lemma program_step_disjoint
          e e1 e2 lc
          (STEP: program_step e e1 e2)
          (WF1: Local.wf (Thread.local e1) (Thread.memory e1))
          (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1))
          (CLOSED1: Memory.closed (Thread.memory e1))
          (DISJOINT1: Local.disjoint (Thread.local e1) lc)
          (WF: Local.wf lc (Thread.memory e1)):
      <<DISJOINT2: Local.disjoint (Thread.local e2) lc>> /\
      <<WF: Local.wf lc (Thread.memory e2)>>.
    Proof.
      inv STEP. ss. eapply ALocal.program_step_disjoint; eauto.
    Qed.

    Lemma step_disjoint
          pf e e1 e2 lc
          (STEP: step pf e e1 e2)
          (WF1: Local.wf (Thread.local e1) (Thread.memory e1))
          (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1))
          (CLOSED1: Memory.closed (Thread.memory e1))
          (DISJOINT1: Local.disjoint (Thread.local e1) lc)
          (WF: Local.wf lc (Thread.memory e1)):
      <<DISJOINT2: Local.disjoint (Thread.local e2) lc>> /\
      <<WF: Local.wf lc (Thread.memory e2)>>.
    Proof.
      inv STEP.
      - eapply promise_step_disjoint; eauto.
      - eapply program_step_disjoint; eauto.
    Qed.

    Lemma opt_step_disjoint
          e e1 e2 lc
          (STEP: opt_step e e1 e2)
          (WF1: Local.wf (Thread.local e1) (Thread.memory e1))
          (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1))
          (CLOSED1: Memory.closed (Thread.memory e1))
          (DISJOINT1: Local.disjoint (Thread.local e1) lc)
          (WF: Local.wf lc (Thread.memory e1)):
      <<DISJOINT2: Local.disjoint (Thread.local e2) lc>> /\
      <<WF: Local.wf lc (Thread.memory e2)>>.
    Proof.
      inv STEP.
      - esplits; eauto.
      - eapply step_disjoint; eauto.
    Qed.

    Lemma rtc_all_step_disjoint
          e1 e2 lc
          (STEP: rtc all_step e1 e2)
          (WF1: Local.wf (Thread.local e1) (Thread.memory e1))
          (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1))
          (CLOSED1: Memory.closed (Thread.memory e1))
          (DISJOINT1: Local.disjoint (Thread.local e1) lc)
          (WF: Local.wf lc (Thread.memory e1)):
      <<DISJOINT2: Local.disjoint (Thread.local e2) lc>> /\
      <<WF: Local.wf lc (Thread.memory e2)>>.
    Proof.
      revert WF1 DISJOINT1 WF. induction STEP; eauto. i.
      inv H. inv USTEP.
      exploit step_future; eauto. i. des.
      exploit step_disjoint; eauto. i. des.
      exploit IHSTEP; eauto.
    Qed.

    Lemma rtc_tau_step_disjoint
          e1 e2 lc
          (STEP: rtc tau_step e1 e2)
          (WF1: Local.wf (Thread.local e1) (Thread.memory e1))
          (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1))
          (CLOSED1: Memory.closed (Thread.memory e1))
          (DISJOINT1: Local.disjoint (Thread.local e1) lc)
          (WF: Local.wf lc (Thread.memory e1)):
      <<DISJOINT2: Local.disjoint (Thread.local e2) lc>> /\
      <<WF: Local.wf lc (Thread.memory e2)>>.
    Proof.
      eapply rtc_all_step_disjoint; cycle 1; eauto.
      eapply rtc_implies; [|eauto].
      apply tau_union.
    Qed.


    (* step_no_reserve_except *)

    Lemma step_no_reserve_except
          pf e e1 e2
          (STEP: step pf e e1 e2)
          (WF1: Local.wf (Thread.local e1) (Thread.memory e1))
          (NORESERVE1: Thread.no_reserve_except e1):
      Thread.no_reserve_except e2.
    Proof.
      inv STEP; inv STEP0.
      - eapply ALocal.promise_step_no_reserve_except; eauto. apply WF1.
      - eapply ALocal.program_step_no_reserve_except; eauto. apply WF1.
    Qed.

    Lemma rtc_tau_step_no_reserve_except
          e1 e2
          (STEP: rtc tau_step e1 e2)
          (WF1: Local.wf (Thread.local e1) (Thread.memory e1))
          (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1))
          (CLOSED1: Memory.closed (Thread.memory e1))
          (NORESERVE1: Thread.no_reserve_except e1):
      Thread.no_reserve_except e2.
    Proof.
      induction STEP; ss; i.
      inv H. inv TSTEP. exploit step_future; eauto. i. des.
      eapply IHSTEP; eauto.
      eapply step_no_reserve_except; eauto.
    Qed.

    Lemma step_bot_no_reserve
          pf e e1 e2
          (STEP: step pf e e1 e2)
          (WF1: Local.wf (Thread.local e1) (Thread.memory e1))
          (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1))
          (CLOSED1: Memory.closed (Thread.memory e1))
          (NORESERVE1: Memory.no_reserve (Thread.memory e1))
          (PROMISES2: (Local.promises (Thread.local e2)) = Memory.bot):
      Memory.no_reserve (Thread.memory e2).
    Proof.
      exploit step_future; eauto. i. des.
      hexploit step_no_reserve_except; eauto; i.
      { eapply Memory.no_reserve_no_reserve_except; eauto. }
      unfold Thread.no_reserve_except in *. rewrite PROMISES2 in *.
      eapply Memory.no_reserve_except_bot_no_reserve; eauto.
      apply CLOSED2.
    Qed.

    Lemma rtc_tau_step_bot_no_reserve
          e1 e2
          (STEP: rtc tau_step e1 e2)
          (WF1: Local.wf (Thread.local e1) (Thread.memory e1))
          (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1))
          (CLOSED1: Memory.closed (Thread.memory e1))
          (NORESERVE1: Memory.no_reserve (Thread.memory e1))
          (PROMISES2: (Local.promises (Thread.local e2)) = Memory.bot):
      Memory.no_reserve (Thread.memory e2).
    Proof.
      exploit rtc_tau_step_future; eauto. i. des.
      hexploit rtc_tau_step_no_reserve_except; eauto; i.
      { eapply Memory.no_reserve_no_reserve_except; eauto. }
      unfold Thread.no_reserve_except in *. rewrite PROMISES2 in *.
      eapply Memory.no_reserve_except_bot_no_reserve; eauto.
      apply CLOSED2.
    Qed.


    Lemma bot_program_step_bot
          e e1 e2
          (STEP: program_step e e1 e2)
          (PROMISES: (Local.promises (Thread.local e1)) = Memory.bot):
      (Local.promises (Thread.local e2)) = Memory.bot.
    Proof.
      inv STEP. eapply ALocal.bot_program_step_bot; eauto.
    Qed.
  End AThread.
End AThread.
