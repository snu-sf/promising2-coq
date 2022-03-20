Require Import Omega.
Require Import Bool.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.

Require Import Event.
Require Import Time.
From PromisingLib Require Import Language.

Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.

Require Import AMemory.
Require Import ATView.

Set Implicit Arguments.


Module ALocal.
  Inductive promise_step (lc1:Local.t) (mem1:Memory.t) (loc:Loc.t) (from to:Time.t) (msg:Message.t) (lc2:Local.t) (mem2:Memory.t) (kind:Memory.op_kind): Prop :=
  | promise_step_intro
      promises2
      (PROMISE: AMemory.promise (Local.promises lc1) mem1 loc from to msg promises2 mem2 kind)
      (CLOSED: Memory.closed_message msg mem2)
      (LC2: lc2 = Local.mk (Local.tview lc1) promises2):
      promise_step lc1 mem1 loc from to msg lc2 mem2 kind
  .
  #[global]
  Hint Constructors promise_step: core.

  Inductive write_step (lc1:Local.t) (sc1:TimeMap.t) (mem1:Memory.t) (loc:Loc.t) (from to:Time.t) (val:Const.t) (releasedm released:option View.t) (ord:Ordering.t) (lc2:Local.t) (sc2:TimeMap.t) (mem2:Memory.t) (kind:Memory.op_kind): Prop :=
  | write_step_intro
      promises2
      (RELEASED: released = TView.write_released (Local.tview lc1) sc1 loc to releasedm ord)
      (WRITABLE: TView.writable (TView.cur (Local.tview lc1)) sc1 loc to ord)
      (WRITE: AMemory.write (Local.promises lc1) mem1 loc from to val released promises2 mem2 kind)
      (RELEASE: Ordering.le Ordering.strong_relaxed ord -> Memory.nonsynch_loc loc (Local.promises lc1))
      (LC2: lc2 = Local.mk (TView.write_tview (Local.tview lc1) sc1 loc to ord) promises2)
      (SC2: sc2 = sc1):
      write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
  .
  #[global]
  Hint Constructors write_step: core.

  Inductive program_step:
    forall (e:ThreadEvent.t) (lc1:Local.t) (sc1:TimeMap.t) (mem1:Memory.t) (lc2:Local.t) (sc2:TimeMap.t) (mem2:Memory.t), Prop :=
  | step_silent
      lc1 sc1 mem1:
      program_step ThreadEvent.silent lc1 sc1 mem1 lc1 sc1 mem1
  | step_read
      lc1 sc1 mem1
      loc ts val released ord lc2
      (LOCAL: Local.read_step lc1 mem1 loc ts val released ord lc2):
      program_step (ThreadEvent.read loc ts val released ord) lc1 sc1 mem1 lc2 sc1 mem1
  | step_write
      lc1 sc1 mem1
      loc from to val released ord lc2 sc2 mem2 kind
      (LOCAL: write_step lc1 sc1 mem1 loc from to val None released ord lc2 sc2 mem2 kind):
      program_step (ThreadEvent.write loc from to val released ord) lc1 sc1 mem1 lc2 sc2 mem2
  | step_update
      lc1 sc1 mem1
      loc ordr ordw
      tsr valr releasedr releasedw lc2
      tsw valw lc3 sc3 mem3 kind
      (LOCAL1: Local.read_step lc1 mem1 loc tsr valr releasedr ordr lc2)
      (LOCAL2: write_step lc2 sc1 mem1 loc tsr tsw valw releasedr releasedw ordw lc3 sc3 mem3 kind):
      program_step (ThreadEvent.update loc tsr tsw valr valw releasedr releasedw ordr ordw) lc1 sc1 mem1 lc3 sc3 mem3
  | step_fence
      lc1 sc1 mem1
      ordr ordw lc2 sc2
      (LOCAL: Local.fence_step lc1 sc1 ordr ordw lc2 sc2):
      program_step (ThreadEvent.fence ordr ordw) lc1 sc1 mem1 lc2 sc2 mem1
  | step_syscall
      lc1 sc1 mem1
      e lc2 sc2
      (LOCAL: Local.fence_step lc1 sc1 Ordering.seqcst Ordering.seqcst lc2 sc2):
      program_step (ThreadEvent.syscall e) lc1 sc1 mem1 lc2 sc2 mem1
  | step_failure
      lc1 sc1 mem1
      (LOCAL: Local.failure_step lc1):
      program_step ThreadEvent.failure lc1 sc1 mem1 lc1 sc1 mem1
  .
  #[global]
  Hint Constructors program_step: core.


  (* step_future *)

  Lemma promise_step_future
        lc1 sc1 mem1 loc from to msg lc2 mem2 kind
        (STEP: promise_step lc1 mem1 loc from to msg lc2 mem2 kind)
        (WF1: Local.wf lc1 mem1)
        (SC1: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1):
    <<WF2: Local.wf lc2 mem2>> /\
    <<SC2: Memory.closed_timemap sc1 mem2>> /\
    <<CLOSED2: Memory.closed mem2>> /\
    <<FUTURE: Memory.future mem1 mem2>> /\
    <<TVIEW_FUTURE: TView.le (Local.tview lc1) (Local.tview lc2)>> /\
    <<MSG_WF: Message.wf msg>> /\
    <<MSG_TS: Memory.message_to msg loc to>> /\
    <<MSG_CLOSED: Memory.closed_message msg mem2>>.
  Proof.
    inv WF1. inv STEP.
    exploit AMemory.promise_future; eauto. i. des.
    splits; ss.
    - econs; ss. eapply TView.future_closed; eauto.
    - eapply Memory.future_closed_timemap; eauto.
    - refl.
    - inv PROMISE.
      + inv PROMISES0. inv ADD. auto.
      + inv PROMISES0. inv SPLIT. auto.
      + inv PROMISES0. inv LOWER. auto.
      + econs.
    - by inv PROMISE.
  Qed.

  Lemma write_step_future
        lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
        (STEP: write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind)
        (REL_WF: View.opt_wf releasedm)
        (REL_CLOSED: Memory.closed_opt_view releasedm mem1)
        (WF1: Local.wf lc1 mem1)
        (SC1: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1):
    <<WF2: Local.wf lc2 mem2>> /\
    <<SC2: Memory.closed_timemap sc2 mem2>> /\
    <<CLOSED2: Memory.closed mem2>> /\
    <<TVIEW_FUTURE: TView.le (Local.tview lc1) (Local.tview lc2)>> /\
    <<SC_FUTURE: TimeMap.le sc1 sc2>> /\
    <<MEM_FUTURE: Memory.future mem1 mem2>> /\
    <<REL_WF: View.opt_wf released>> /\
    <<REL_TS: Time.le ((View.rlx (View.unwrap released)) loc) to>> /\
    <<REL_CLOSED: Memory.closed_opt_view released mem2>>.
  Proof.
    inv WF1. inv STEP.
    exploit TViewFacts.write_future; eauto.
    { inv WRITE. eapply AMemory.promise_op. eauto. }
    s. i. des.
    exploit AMemory.write_future; try apply WRITE; eauto. i. des.
    exploit AMemory.write_get2; try apply WRITE; eauto; try by viewtac. i. des.
    splits; eauto.
    - apply TViewFacts.write_tview_incr. auto.
    - refl.
    - inv WRITE. inv PROMISE; try inv TS; ss.
  Qed.

  Lemma write_step_strong_relaxed
        lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
        (STEP: write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind)
        (ORD: Ordering.le Ordering.strong_relaxed ord):
    negb (Memory.op_kind_is_lower kind).
  Proof.
    inv STEP. inv WRITE. ss.
    destruct kind; ss.
    inv PROMISE. des. subst.
    exploit Memory.lower_get0; try exact PROMISES. i. des.
    exploit RELEASE; eauto. inv MSG_LE; eauto. i. subst.
    inv RELEASED. revert H0.
    unfold TView.write_released. condtac; ss. destruct ord; ss.
  Qed.

  Lemma program_step_future
        e lc1 sc1 mem1 lc2 sc2 mem2
        (STEP: program_step e lc1 sc1 mem1 lc2 sc2 mem2)
        (WF1: Local.wf lc1 mem1)
        (SC1: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1):
    <<WF2: Local.wf lc2 mem2>> /\
    <<SC2: Memory.closed_timemap sc2 mem2>> /\
    <<CLOSED2: Memory.closed mem2>> /\
    <<TVIEW_FUTURE: TView.le (Local.tview lc1) (Local.tview lc2)>> /\
    <<SC_FUTURE: TimeMap.le sc1 sc2>> /\
    <<MEM_FUTURE: Memory.future mem1 mem2>>.
  Proof.
    inv STEP.
    - esplits; eauto; try refl.
    - exploit Local.read_step_future; eauto. i. des.
      esplits; eauto; try refl.
    - exploit write_step_future; eauto; try by econs. i. des.
      esplits; eauto; try refl.
    - exploit Local.read_step_future; eauto. i. des.
      exploit write_step_future; eauto; try by econs. i. des.
      esplits; eauto. etrans; eauto.
    - exploit Local.fence_step_future; eauto. i. des. esplits; eauto; try refl.
    - exploit Local.fence_step_future; eauto. i. des. esplits; eauto; try refl.
    - esplits; eauto; try refl.
  Qed.

  Lemma promise_step_inhabited
        lc1 mem1 loc from to msg lc2 mem2 kind
        (STEP: promise_step lc1 mem1 loc from to msg lc2 mem2 kind)
        (INHABITED1: Memory.inhabited mem1):
    <<INHABITED2: Memory.inhabited mem2>>.
  Proof.
    inv STEP.
    inv PROMISE; eauto using Memory.add_inhabited, Memory.split_inhabited, Memory.lower_inhabited, Memory.cancel_inhabited.
  Qed.

  Lemma program_step_inhabited
        e lc1 sc1 mem1 lc2 sc2 mem2
        (STEP: program_step e lc1 sc1 mem1 lc2 sc2 mem2)
        (INHABITED1: Memory.inhabited mem1):
    <<INHABITED2: Memory.inhabited mem2>>.
  Proof.
    inv STEP; eauto.
    - inv LOCAL. inv WRITE.
      inv PROMISE; eauto using Memory.add_inhabited, Memory.split_inhabited, Memory.lower_inhabited, Memory.cancel_inhabited.
    - inv LOCAL2. inv WRITE.
      inv PROMISE; eauto using Memory.add_inhabited, Memory.split_inhabited, Memory.lower_inhabited, Memory.cancel_inhabited.
  Qed.


  (* step_disjoint *)

  Lemma promise_step_disjoint
        lc1 sc1 mem1 loc from to msg lc2 mem2 lc kind
        (STEP: promise_step lc1 mem1 loc from to msg lc2 mem2 kind)
        (WF1: Local.wf lc1 mem1)
        (SC1: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1)
        (DISJOINT1: Local.disjoint lc1 lc)
        (WF: Local.wf lc mem1):
    <<DISJOINT2: Local.disjoint lc2 lc>> /\
    <<WF: Local.wf lc mem2>>.
  Proof.
    inv WF1. inv DISJOINT1. inversion WF. inv STEP.
    exploit AMemory.promise_future; try apply PROMISE; eauto. i. des.
    exploit AMemory.promise_disjoint; try apply PROMISE; eauto. i. des.
    splits; ss. econs; eauto.
    eapply TView.future_closed; eauto.
  Qed.

  Lemma write_step_disjoint
        lc1 sc1 mem1 lc2 sc2 loc from to val releasedm released ord mem2 kind lc
        (STEP: write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind)
        (WF1: Local.wf lc1 mem1)
        (SC1: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1)
        (DISJOINT1: Local.disjoint lc1 lc)
        (WF: Local.wf lc mem1):
    <<DISJOINT2: Local.disjoint lc2 lc>> /\
    <<WF: Local.wf lc mem2>>.
  Proof.
    inv WF1. inv DISJOINT1. inversion WF. inv STEP.
    exploit AMemory.write_disjoint; try apply WRITE; eauto. i. des.
    splits; ss. econs; eauto.
    inv WRITE. eapply ATView.promise_closed; eauto.
  Qed.

  Lemma program_step_disjoint
        e lc1 sc1 mem1 lc2 sc2 mem2 lc
        (STEP: program_step e lc1 sc1 mem1 lc2 sc2 mem2)
        (WF1: Local.wf lc1 mem1)
        (SC1: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1)
        (DISJOINT1: Local.disjoint lc1 lc)
        (WF: Local.wf lc mem1):
    <<DISJOINT2: Local.disjoint lc2 lc>> /\
    <<WF: Local.wf lc mem2>>.
  Proof.
    inv STEP.
    - esplits; eauto.
    - exploit Local.read_step_disjoint; eauto.
    - exploit write_step_disjoint; eauto.
    - exploit Local.read_step_future; eauto. i. des.
      exploit Local.read_step_disjoint; eauto. i. des.
      exploit write_step_disjoint; eauto.
    - exploit Local.fence_step_disjoint; eauto.
    - exploit Local.fence_step_disjoint; eauto.
    - esplits; eauto.
  Qed.


  (* step_no_reserve_except *)

  Lemma promise_step_no_reserve_except
        lc1 mem1 loc from to msg lc2 mem2 kind
        (STEP: promise_step lc1 mem1 loc from to msg lc2 mem2 kind)
        (RESERVE1: Memory.reserve_wf (Local.promises lc1) mem1)
        (NORESERVE1: Memory.no_reserve_except (Local.promises lc1) mem1):
    Memory.no_reserve_except (Local.promises lc2) mem2.
  Proof.
    ii. inv STEP. s.
    eapply AMemory.promise_no_reserve_except; eauto.
  Qed.

  Lemma program_step_no_reserve_except
        e lc1 sc1 mem1 lc2 sc2 mem2
        (STEP: program_step e lc1 sc1 mem1 lc2 sc2 mem2)
        (RESERVE1: Memory.reserve_wf (Local.promises lc1) mem1)
        (NORESERVE1: Memory.no_reserve_except (Local.promises lc1) mem1):
    Memory.no_reserve_except (Local.promises lc2) mem2.
  Proof.
    ii. inv STEP; try inv LOCAL; eauto; ss.
    - inv WRITE.
      erewrite Memory.remove_o; eauto. condtac; ss.
      + des. subst.
        exploit AMemory.promise_get0; eauto.
        { inv PROMISE; ss. }
        i. des. congr.
      + eapply AMemory.promise_no_reserve_except; eauto.
    - inv LOCAL1. inv LOCAL2. inv WRITE. ss.
      erewrite Memory.remove_o; eauto. condtac; ss.
      + des. subst.
        exploit AMemory.promise_get0; eauto.
        { inv PROMISE; ss. }
        i. des. congr.
      + eapply AMemory.promise_no_reserve_except; eauto.
  Qed.


  Lemma bot_program_step_bot
        e lc1 sc1 mem1 lc2 sc2 mem2
        (STEP: program_step e lc1 sc1 mem1 lc2 sc2 mem2)
        (PROMISES: (Local.promises lc1) = Memory.bot):
    (Local.promises lc2) = Memory.bot.
  Proof.
    inv STEP; try inv LOCAL; ss.
    - eapply AMemory.bot_write_bot; eauto.
    - inv LOCAL1. inv LOCAL2.
      eapply AMemory.bot_write_bot; eauto.
  Qed.
End ALocal.
