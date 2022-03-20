Require Import Bool.
Require Import List.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
Require Import Event.
From PromisingLib Require Import Language.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.

Require Import FulfillStep.
Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import Compatibility.
Require Import SimThread.

Require MergeTView.
Require ReorderTView.
Require Import MemoryReorder.
Require Import MemorySplit.
Require Import MemoryMerge.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Lemma merge_read_read
      loc ts val released ord
      lc0 lc2 mem0
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.read_step lc0 mem0 loc ts val released ord lc2):
  Local.read_step lc2 mem0 loc ts val released ord lc2.
Proof.
  inv STEP1. econs; s; eauto.
  - unfold View.singleton_ur_if.
    econs; repeat (try condtac; aggrtac); try apply READABLE; auto.
    + inv MEM0. exploit CLOSED; eauto. i. des. inv MSG_WF. inv MSG_TS.
      etrans; eauto. apply View.unwrap_opt_wf. ss.
    + inv MEM0. exploit CLOSED; eauto. i. des. inv MSG_WF. inv MSG_TS.
      etrans; eauto. apply View.unwrap_opt_wf. ss.
    + inv MEM0. exploit CLOSED; eauto. i. des. inv MSG_WF. inv MSG_TS.
      auto.
  - f_equal. apply TView.antisym.
    + apply TViewFacts.read_tview_incr.
    + apply MergeTView.read_read_tview; try refl; try apply WF0.
      inv MEM0. exploit CLOSED; eauto. i. des. inv MSG_WF. inv MSG_TS.
      auto.
Qed.

Lemma merge_write_read
      loc from to val releasedm released ord1 ord2 kind
      lc0 sc0 mem0
      lc1 sc1 mem1
      (ORD: Ordering.le Ordering.seqcst ord2 -> Ordering.le Ordering.seqcst ord1)
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (WF_RELEASED: View.opt_wf releasedm)
      (WF_CLOSED: Memory.closed_opt_view releasedm mem0)
      (RLX: Ordering.le Ordering.relaxed ord2 -> View.le (View.unwrap releasedm) (TView.acq (Local.tview lc0)))
      (ACQ: Ordering.le Ordering.acqrel ord2 -> View.le (View.unwrap releasedm) (TView.cur (Local.tview lc0)))
      (STEP: Local.write_step lc0 sc0 mem0 loc from to val releasedm released ord1 lc1 sc1 mem1 kind):
  Local.read_step lc1 mem1 loc to val released ord2 lc1.
Proof.
  inv STEP. econs; eauto.
  - inv WRITE.
    hexploit Memory.promise_op; eauto. i.
    hexploit TViewFacts.write_future; try exact H; eauto; try apply WF0; try by viewtac. i. des.
    hexploit Memory.promise_future; try apply PROMISE; try apply WF0; eauto; try by viewtac. i. des.
    eapply Memory.promise_get2; eauto.
    inv PROMISE; ss.
  - inv WRITABLE. unfold TView.write_released. s.
    econs; repeat (try condtac; aggrtac); (try by left; eauto).
    + etrans; [|left; eauto]. apply WF0.
  - unfold TView.read_tview, TView.write_released, TView.write_tview. s.
    f_equal. apply TView.antisym; econs;
      repeat (try condtac; aggrtac; rewrite <- ? View.join_l; try apply WF0; eauto).
    etrans; apply WF0.
Qed.

Lemma promise_promise_promise
      loc from to msg1 msg2 kind
      lc0 mem0
      lc1 mem1
      lc2 mem2
      (PROMISE1: Local.promise_step lc0 mem0 loc from to msg1 lc1 mem1 kind)
      (PROMISE2: Local.promise_step lc1 mem1 loc from to msg2 lc2 mem2 (Memory.op_kind_lower msg1)):
  Local.promise_step lc0 mem0 loc from to msg2 lc2 mem2 kind.
Proof.
  inv PROMISE1. inv PROMISE2. ss.
  exploit MemoryMerge.promise_promise_promise; try exact PROMISE; eauto.
Qed.

Lemma to_lt_from_le
      mem loc
      from1 to1 msg1
      from2 to2 msg2
      (GET1: Memory.get loc to1 mem = Some (from1, msg1))
      (GET2: Memory.get loc to2 mem = Some (from2, msg2))
      (LT: Time.lt to1 to2):
  Time.le to1 from2.
Proof.
  destruct (TimeFacts.le_lt_dec to1 from2); auto.
  destruct (Cell.WF (mem loc)). exfalso. eapply DISJOINT.
  - apply GET1.
  - apply GET2.
  - ii. subst. eapply Time.lt_strorder. eauto.
  - apply Interval.mem_ub. exploit VOLUME; try exact GET1; eauto. intro x. des; auto.
    inv x. inv l.
  - econs.
    + apply l.
    + left. auto.
Qed.

Lemma fulfill_step_lc_from
      loc from to val releasedm released ord
      lc0 sc0 mem0
      lc1 sc1
      (WF: Local.wf lc0 mem0)
      (MEM: Memory.closed mem0)
      (STEP: fulfill_step lc0 sc0 loc from to val releasedm released ord lc1 sc1):
  Time.le ((TView.cur (Local.tview lc0)).(View.rlx) loc) from.
Proof.
  inv WF. inv STEP.
  exploit Memory.remove_get0; eauto. i. des.
  exploit PROMISES; eauto. i.
  inv TVIEW_CLOSED. inv CUR. exploit RLX; eauto. instantiate (1 := loc). i. des.
  eapply to_lt_from_le; eauto.
  inv WRITABLE. auto.
Qed.

Lemma merge_split
      loc ts1 ts2 ts3 val2 val3 released0 released3 ord
      lc0 sc0 mem0
      lc3 sc3
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (LC0_TS: Time.le ((TView.cur (Local.tview lc0)).(View.rlx) loc) ts1)
      (REL0_TS: Time.le ((View.rlx (View.unwrap released0)) loc) ts1)
      (REL0_WF: View.opt_wf released0)
      (REL0_CLOSED: Memory.closed_opt_view released0 mem0)
      (TS12: Time.lt ts1 ts2)
      (TS23: Time.lt ts2 ts3)
      (STEP: fulfill_step lc0 sc0 loc ts1 ts3 val3 released0 released3 ord lc3 sc3):
  exists lc1' lc2' lc3' sc2' sc3' mem1' released1',
    <<STEP1: Local.promise_step lc0 mem0 loc ts1 ts2 (Message.full val2 released1') lc1' mem1' (Memory.op_kind_split ts3 (Message.full val3 released3))>> /\
    <<STEP2: fulfill_step lc1' sc0 loc ts1 ts2 val2 released0 released1' ord lc2' sc2'>> /\
    <<STEP3: fulfill_step lc2' sc2' loc ts2 ts3 val3 released1' released3 ord lc3' sc3'>> /\
    <<LOCAL3: sim_local SimPromises.bot lc3' lc3>> /\
    <<SC3: TimeMap.le sc3' sc3>> /\
    <<MEM3: sim_memory mem1' mem0>> /\
    <<REL1': released1' = TView.write_released (Local.tview lc0) sc0 loc ts2 released0 ord>>.
Proof.
  set (released1' := TView.write_released (Local.tview lc0) sc0 loc ts2 released0 ord).
  assert (REL1'_WF: View.opt_wf released1').
  { unfold released1', TView.write_released. condtac; econs. repeat (try condtac; aggrtac; try by apply WF0). }
  exploit fulfill_step_future; eauto. i. des.
  inv STEP.
  exploit MemorySplit.remove_promise_promise_remove_remove;
    try exact TS12; try exact TS23; try exact REMOVE.
  { instantiate (1 := released1'). instantiate (1 := val2). econs; eauto. }
  { econs. unfold released1', TView.write_released. repeat (try condtac; aggrtac).
    - etrans; eauto. left. auto.
    - etrans; eauto. left. auto.
    - etrans; [apply WF0|]. etrans; eauto. left. auto.
  }
  { apply WF0. }
  i. des.
  assert (REL1'_CLOSED: Memory.closed_opt_view released1' mem1).
  { unfold released1'. eapply TViewFacts.op_closed_released; eauto; try apply WF0.
    eapply Memory.promise_op. eauto.
  }
  exploit Memory.promise_future; try eexact STEP1; (try by apply WF0); (try by viewtac); eauto. i. des.
  esplits.
  - econs; eauto.
  - econs; try exact STEP2; auto.
    + unfold Local.tview at 1 2. refl.
    + s. inv WF0. inv WRITABLE.
      exploit Memory.remove_get0; try exact REMOVE; eauto. i. des.
      exploit PROMISES; eauto. i.
      inv TVIEW_CLOSED. inv CUR.
      exploit RLX; eauto. i. des. eauto.
      econs; i;
        eapply TimeFacts.le_lt_lt; try eexact TS12;
        eapply to_lt_from_le; eauto.
  - unfold Local.tview at 1.
    econs; try exact STEP3; auto.
    + etrans; eauto. unfold released1', TView.write_released. s. condtac; econs.
      repeat (try condtac; aggrtac; try by apply WF0).
    + s. inv WRITABLE. econs; repeat (try condtac; aggrtac; eauto).
  - s. econs; ss.
    + eapply MergeTView.write_write_tview; eauto. apply WF0.
    + apply SimPromises.sem_bot.
  - refl.
  - inv STEP1. eapply split_sim_memory; eauto.
  - refl.
Qed.

Lemma merge_write_write_relaxed
      loc ts1 ts2 ts3 val2 val3 released0 released3 ord kind
      lc0 sc0 mem0
      lc3 sc3 mem3
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (REL0_WF: View.opt_wf released0)
      (REL0_TS: Time.le ((View.rlx (View.unwrap released0)) loc) ts1)
      (REL0_CLOSED: Memory.closed_opt_view released0 mem0)
      (ORD: Ordering.le ord Ordering.relaxed)
      (TS12: Time.lt ts1 ts2)
      (TS23: Time.lt ts2 ts3)
      (STEP: Local.write_step lc0 sc0 mem0 loc ts1 ts3 val3 released0 released3 ord lc3 sc3 mem3 kind):
  exists lc1' lc2' lc3' sc2' sc3' mem1' mem2' mem3' released2' released3',
    <<STEP1: Local.promise_step lc0 mem0 loc ts1 ts3 (Message.full val3 released3) lc1' mem1' kind>> /\
    <<STEP2: Local.write_step lc1' sc0 mem1' loc ts1 ts2 val2 released0 released2' ord lc2' sc2' mem2' (Memory.op_kind_split ts3 (Message.full val3 released3))>> /\
    <<STEP3: Local.write_step lc2' sc2' mem2' loc ts2 ts3 val3 released2' released3' ord lc3' sc3' mem3' (Memory.op_kind_lower (Message.full val3 released3))>> /\
    <<REL3: View.opt_le released3' released3>> /\
    <<LOCAL3: sim_local SimPromises.bot lc3' lc3>> /\
    <<SC3: TimeMap.le sc3' sc3>> /\
    <<MEM3: sim_memory mem3' mem3>>.
Proof.
  exploit Local.write_step_future; eauto. i. des.
  exploit write_promise_fulfill; eauto. i. des.
  exploit Local.promise_step_future; eauto. i. des.
  exploit merge_split; try exact STEP2; eauto; try by viewtac.
  { eapply fulfill_step_lc_from; eauto. }
  i. des.
  exploit Local.promise_step_future; try exact STEP0; eauto. i. des.
  exploit promise_fulfill_write; try eexact STEP3; eauto; try by viewtac.
  { i. destruct ord; inv ORD; inv H. }
  i. des.
  exploit Local.write_step_future; eauto; try by viewtac. i. des.
  exploit sim_local_fulfill_bot; try eexact STEP4; try exact REL_LE; try refl; eauto.
  { inv MSG_WF0. eauto. }
  i. des.
  exploit (@fulfill_write lc2' sc2' mem2'); try eexact STEP_SRC; eauto. i. des.
  esplits; eauto.
  - etrans; eauto.
  - etrans; eauto. etrans; eauto.
Qed.

Lemma promise_add_promise_split_promise_add_promise_add
      loc ts1 ts2 ts3 msg2 msg3
      lc0 sc0 mem0
      lc1 mem1
      lc2 mem2
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (REL_CLOSED: forall promises1' mem1'
                     (PROMISE1: Memory.promise (Local.promises lc0) mem0 loc ts1 ts2 msg2 promises1' mem1' Memory.op_kind_add),
          Memory.closed_message msg2 mem1')
      (STEP1: Local.promise_step lc0 mem0 loc ts1 ts3 msg3 lc1 mem1 Memory.op_kind_add)
      (STEP2: Local.promise_step lc1 mem1 loc ts1 ts2 msg2 lc2 mem2 (Memory.op_kind_split ts3 msg3)):
  exists lc1' mem1',
    <<STEP1: Local.promise_step lc0 mem0 loc ts1 ts2 msg2 lc1' mem1' Memory.op_kind_add>> /\
    <<STEP2: Local.promise_step lc1' mem1' loc ts2 ts3 msg3 lc2 mem2 Memory.op_kind_add>>.
Proof.
  exploit Local.promise_step_future; try exact STEP1; eauto. i. des.
  inv STEP1. inv STEP2.
  exploit MemoryReorder.promise_add_promise_split_same; eauto. i. des.
  esplits.
  - econs; eauto.
  - econs; eauto. inv MSG_CLOSED; ss. econs.
    eauto using Memory.promise_closed_opt_view.
Qed.

Lemma promise_lower_promise_split_promise_split_promise_lower
      loc ts1 ts2 ts3 msg0 val2 released2 msg3
      lc0 sc0 mem0
      lc1 mem1
      lc2 mem2
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (REL_CLOSED: forall promises1' mem1' msg ts
                     (PROMISE1: Memory.promise (Local.promises lc0) mem0 loc ts1 ts2 (Message.full val2 released2) promises1' mem1' (Memory.op_kind_split ts msg)),
          Memory.closed_message (Message.full val2 released2) mem1')
      (STEP1: Local.promise_step lc0 mem0 loc ts1 ts3 msg3 lc1 mem1 (Memory.op_kind_lower msg0))
      (STEP2: Local.promise_step lc1 mem1 loc ts1 ts2 (Message.full val2 released2) lc2 mem2 (Memory.op_kind_split ts3 msg3)):
  exists lc1' mem1',
    <<STEP1: Local.promise_step lc0 mem0 loc ts1 ts2 (Message.full val2 released2) lc1' mem1' (Memory.op_kind_split ts3 msg0)>> /\
    <<STEP2: Local.promise_step lc1' mem1' loc ts2 ts3 msg3 lc2 mem2 (Memory.op_kind_lower msg0)>>.
Proof.
  exploit Local.promise_step_future; try exact STEP1; eauto. i. des.
  inv STEP1. inv STEP2.
  exploit MemoryReorder.promise_lower_promise_split_same; eauto. i. des.
  esplits.
  - econs; eauto.
  - econs; eauto. inv MSG_CLOSED; ss. econs.
    eauto using Memory.promise_closed_opt_view.
Qed.

Lemma reorder_promise_split_promise_split
      loc ts1 ts2 ts3 ts4 val2 released2 msg3 msg4
      lc0 sc0 mem0
      lc1 mem1
      lc2 mem2
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (REL_CLOSED: forall promises1' mem1' ts5 msg5
                     (PROMISE1: Memory.promise (Local.promises lc0) mem0 loc ts1 ts2 (Message.full val2 released2) promises1' mem1' (Memory.op_kind_split ts5 msg5)),
          Memory.closed_message (Message.full val2 released2) mem1')
      (STEP1: Local.promise_step lc0 mem0 loc ts1 ts3 msg3 lc1 mem1 (Memory.op_kind_split ts4 msg4))
      (STEP2: Local.promise_step lc1 mem1 loc ts1 ts2 (Message.full val2 released2) lc2 mem2 (Memory.op_kind_split ts3 msg3)):
  exists lc1' mem1',
    <<STEP1: Local.promise_step lc0 mem0 loc ts1 ts2 (Message.full val2 released2) lc1' mem1' (Memory.op_kind_split ts4 msg4)>> /\
    <<STEP2: Local.promise_step lc1' mem1' loc ts2 ts3 msg3 lc2 mem2 (Memory.op_kind_split ts4 msg4)>>.
Proof.
  exploit Local.promise_step_future; try exact STEP1; eauto. i. des.
  inv STEP1. inv STEP2.
  exploit MemoryReorder.promise_split_promise_split_same; try exact PROMISE; eauto. s. i. des.
  esplits.
  - econs; eauto.
  - econs; eauto. inv MSG_CLOSED; ss. econs.
    eauto using Memory.promise_closed_opt_view.
Qed.

Lemma reorder_promise_add_fulfill
      loc1 from1 to1 msg1
      loc2 from2 to2 val2 releasedm2 released2 ord2
      lc0 sc0 mem0
      lc1 mem1
      lc2 sc2
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (RELM_WF: Memory.closed_opt_view releasedm2 mem0)
      (DIFF: (loc1, to1) <> (loc2, to2))
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg1 lc1 mem1 Memory.op_kind_add)
      (STEP2: fulfill_step lc1 sc0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2):
  exists lc1',
    <<STEP1: fulfill_step lc0 sc0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc1' sc2>> /\
    <<STEP2: Local.promise_step lc1' mem0 loc1 from1 to1 msg1 lc2 mem1 Memory.op_kind_add>>.
Proof.
  exploit Local.promise_step_future; try exact STEP1; eauto. i. des.
  exploit fulfill_step_future; try exact STEP2; try exact WF2; eauto; try by viewtac. i. des.
  inv STEP1. inv STEP2.
  exploit MemoryReorder.promise_add_remove; try exact PROMISE; eauto. i. des.
  esplits.
  - econs; eauto.
  - econs; eauto.
Qed.

Lemma reorder_promise_split_fulfill
      loc1 from1 to1 msg1
      loc2 from2 to2 val2 releasedm2 released2 ord2
      to3 msg3
      lc0 sc0 mem0
      lc1 mem1
      lc2 sc2
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (RELM_WF: Memory.closed_opt_view releasedm2 mem0)
      (DIFF1: (loc1, to1) <> (loc2, to2))
      (DIFF2: (loc1, to3) <> (loc2, to2))
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg1 lc1 mem1 (Memory.op_kind_split to3 msg3))
      (STEP2: fulfill_step lc1 sc0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2):
  exists lc1',
    <<STEP1: fulfill_step lc0 sc0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc1' sc2>> /\
    <<STEP2: Local.promise_step lc1' mem0 loc1 from1 to1 msg1 lc2 mem1 (Memory.op_kind_split to3 msg3)>>.
Proof.
  exploit Local.promise_step_future; try exact STEP1; eauto. i. des.
  exploit fulfill_step_future; try exact STEP2; try exact WF2; eauto; try by viewtac. i. des.
  inv STEP1. inv STEP2.
  exploit MemoryReorder.promise_split_remove; try exact PROMISE; eauto. i. des.
  esplits.
  - econs; eauto.
  - econs; eauto.
Qed.

Lemma reorder_promise_lower_fulfill
      loc1 from1 to1 msg1 msg2
      loc2 from2 to2 val2 releasedm2 released2 ord2
      lc0 sc0 mem0
      lc1 mem1
      lc2 sc2
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (RELM_WF: Memory.closed_opt_view releasedm2 mem0)
      (DIFF: (loc1, to1) <> (loc2, to2))
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg2 lc1 mem1 (Memory.op_kind_lower msg1))
      (STEP2: fulfill_step lc1 sc0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2):
  exists lc1',
    <<STEP1: fulfill_step lc0 sc0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc1' sc2>> /\
    <<STEP2: Local.promise_step lc1' mem0 loc1 from1 to1 msg2 lc2 mem1 (Memory.op_kind_lower msg1)>>.
Proof.
  exploit Local.promise_step_future; try exact STEP1; eauto. i. des.
  exploit fulfill_step_future; try exact STEP2; try exact WF2; eauto; try by viewtac. i. des.
  inv STEP1. inv STEP2.
  exploit MemoryReorder.promise_lower_remove; try exact PROMISE; eauto. i. des.
  esplits.
  - econs; eauto.
  - econs; eauto.
Qed.

Lemma write_step_nonsynch_loc
      lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind l
      (STEP: Local.write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind)
      (PROMISES: Memory.nonsynch_loc l (Local.promises lc1)):
  Memory.nonsynch_loc l (Local.promises lc2).
Proof.
  inv STEP. inv WRITE. s. ii. revert GET.
  erewrite Memory.remove_o; eauto. condtac; ss. inv PROMISE; ss.
  - erewrite Memory.add_o; eauto. condtac; ss. apply PROMISES.
  - erewrite Memory.split_o; eauto. repeat condtac; ss.
    + guardH o. guardH o0. des. subst.
      exploit Memory.split_get0; try exact PROMISES0; eauto. i. des. inv GET.
      eapply PROMISES. eauto.
    + apply PROMISES.
  - erewrite Memory.lower_o; eauto. condtac; ss. apply PROMISES.
Qed.

Lemma merge_write_write_add
      loc ts1 ts2 ts3 val1 val2 released0 released2 ord
      lc0 sc0 mem0
      lc2 sc2 mem2
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (REL0_WF: View.opt_wf released0)
      (REL0_TS: Time.le ((View.rlx (View.unwrap released0)) loc) ts1)
      (REL0_CLOSED: Memory.closed_opt_view released0 mem0)
      (TS12: Time.lt ts1 ts2)
      (TS23: Time.lt ts2 ts3)
      (STEP: Local.write_step lc0 sc0 mem0 loc ts1 ts3 val2 released0 released2 ord lc2 sc2 mem2 Memory.op_kind_add):
  exists lc1' lc2' sc1' sc2' mem1' mem2' released1' released2',
    <<STEP1: Local.write_step lc0 sc0 mem0 loc ts1 ts2 val1 released0 released1' ord lc1' sc1' mem1' Memory.op_kind_add>> /\
    <<STEP2: Local.write_step lc1' sc1' mem1' loc ts2 ts3 val2 released1' released2' ord lc2' sc2' mem2' Memory.op_kind_add>> /\
    <<REL2: View.opt_le released2' released2>> /\
    <<LOCAL2: sim_local SimPromises.bot lc2' lc2>> /\
    <<SC2: TimeMap.le sc2' sc2>> /\
    <<MEM2: sim_memory mem2' mem2>>.
Proof.
  exploit Local.write_step_future; eauto. i. des.
  exploit write_promise_fulfill; eauto. i. des.
  exploit Local.promise_step_future; eauto. i. des.
  exploit merge_split; try exact STEP2; eauto; try by viewtac.
  { eapply fulfill_step_lc_from; eauto. }
  i. des.
  exploit promise_add_promise_split_promise_add_promise_add; try exact STEP1; try exact STEP0; eauto.
  { i. rewrite REL1'.
    instantiate (1 := val1).
    exploit Memory.promise_op; eauto. i. econs.
    eapply TViewFacts.op_closed_released; try exact x0; eauto.
    inv STEP1. apply WF0.
  }
  i. des.
  exploit Local.promise_step_future; try eexact STEP5; eauto. i. des.
  exploit reorder_promise_add_fulfill; try exact STEP6; try eexact STEP3; eauto; try by viewtac.
  { ii. inv H. exfalso. eapply Time.lt_strorder. eauto. }
  i. des.
  exploit fulfill_step_future; try eexact STEP7; try exact WF3; eauto; try by viewtac. i. des.
  exploit promise_fulfill_write; try eexact STEP5; eauto. i. des.
  exploit Local.write_step_future; eauto. i. des.
  exploit promise_fulfill_write; try eexact STEP8; eauto.
  { inv MSG_WF0. ss. }
  { inv MSG_CLOSED0. ss. }
  { i. hexploit ORD; eauto. i. des. splits; auto.
    eapply write_step_nonsynch_loc; eauto.
  }
  i. des.
  hexploit sim_local_write_bot; try exact MEM; try exact REL_LE; try refl; eauto.
  { inv MSG_WF0. ss. }
  { inv MSG_CLOSED0. ss. }
  i. des.
  esplits; eauto.
  - etrans; eauto.
  - etrans; eauto. etrans; eauto.
Qed.

Lemma merge_write_write_split
      loc ts1 ts2 ts3 ts4 val1 val2 released0 released2 msg4 ord
      lc0 sc0 mem0
      lc2 sc2 mem2
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (REL0_WF: View.opt_wf released0)
      (REL0_TS: Time.le ((View.rlx (View.unwrap released0)) loc) ts1)
      (REL0_CLOSED: Memory.closed_opt_view released0 mem0)
      (TS12: Time.lt ts1 ts2)
      (TS23: Time.lt ts2 ts3)
      (STEP: Local.write_step lc0 sc0 mem0 loc ts1 ts3 val2 released0 released2 ord lc2 sc2 mem2 (Memory.op_kind_split ts4 msg4)):
  exists lc1' lc2' sc1' sc2' mem1' mem2' released1' released2',
    <<STEP1: Local.write_step lc0 sc0 mem0 loc ts1 ts2 val1 released0 released1' ord lc1' sc1' mem1' (Memory.op_kind_split ts4 msg4)>> /\
    <<STEP2: Local.write_step lc1' sc1' mem1' loc ts2 ts3 val2 released1' released2' ord lc2' sc2' mem2' (Memory.op_kind_split ts4 msg4)>> /\
    <<REL2: View.opt_le released2' released2>> /\
    <<LOCAL2: sim_local SimPromises.bot lc2' lc2>> /\
    <<SC2: TimeMap.le sc2' sc2>> /\
    <<MEM2: sim_memory mem2' mem2>>.
Proof.
  exploit Local.write_step_future; eauto. i. des.
  exploit write_promise_fulfill; eauto. i. des.
  exploit Local.promise_step_future; eauto. i. des.
  exploit merge_split; try exact STEP2; eauto; try by viewtac.
  { eapply fulfill_step_lc_from; eauto. }
  i. des.
  exploit reorder_promise_split_promise_split; try exact STEP1; try exact STEP0; eauto.
  { i. rewrite REL1'.
    instantiate (1 := val1).
    exploit Memory.promise_op; eauto. i. econs.
    eapply TViewFacts.op_closed_released; try exact x0; eauto.
    inv STEP1. apply WF0.
  }
  i. des.
  exploit Local.promise_step_future; try eexact STEP5; eauto. i. des.
  exploit reorder_promise_split_fulfill; try exact STEP6; try eexact STEP3; eauto; try by viewtac.
  { ii. inv H. eapply Time.lt_strorder. eauto. }
  { ii. inv H. inv STEP5. inv PROMISE. inv MEM. inv SPLIT. eapply Time.lt_strorder. eauto. }
  i. des.
  exploit fulfill_step_future; try eexact STEP7; try exact WF3; eauto; try by viewtac. i. des.
  exploit promise_fulfill_write; try eexact STEP5; eauto. i. des.
  exploit Local.write_step_future; eauto. i. des.
  exploit promise_fulfill_write; try eexact STEP8; eauto.
  { inv MSG_WF0. ss. }
  { inv MSG_CLOSED0. ss. }
  { i. hexploit ORD; eauto. i. des. splits; auto.
    eapply write_step_nonsynch_loc; eauto.
  }
  i. des.
  hexploit sim_local_write_bot; try exact MEM; try exact REL_LE; try refl; eauto.
  { inv MSG_WF0. ss. }
  { inv MSG_CLOSED0. ss. }
  i. des.
  esplits; eauto.
  - etrans; eauto.
  - etrans; eauto. etrans; eauto.
Qed.

Lemma merge_write_write_lower
      loc ts1 ts2 ts3 val1 val2 released0 released2 ord msg0
      lc0 sc0 mem0
      lc2 sc2 mem2
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (REL0_WF: View.opt_wf released0)
      (REL0_TS: Time.le ((View.rlx (View.unwrap released0)) loc) ts1)
      (REL0_CLOSED: Memory.closed_opt_view released0 mem0)
      (TS12: Time.lt ts1 ts2)
      (TS23: Time.lt ts2 ts3)
      (STEP: Local.write_step lc0 sc0 mem0 loc ts1 ts3 val2 released0 released2 ord lc2 sc2 mem2 (Memory.op_kind_lower msg0)):
  exists lc1' lc2' sc1' sc2' mem1' mem2' released1' released2',
    <<STEP1: Local.write_step lc0 sc0 mem0 loc ts1 ts2 val1 released0 released1' ord lc1' sc1' mem1' (Memory.op_kind_split ts3 msg0)>> /\
    <<STEP2: Local.write_step lc1' sc1' mem1' loc ts2 ts3 val2 released1' released2' ord lc2' sc2' mem2' (Memory.op_kind_lower msg0)>> /\
    <<REL3: View.opt_le released2' released2>> /\
    <<LOCAL3: sim_local SimPromises.bot lc2' lc2>> /\
    <<SC3: TimeMap.le sc2' sc2>> /\
    <<MEM3: sim_memory mem2' mem2>>.
Proof.
  exploit Local.write_step_future; eauto. i. des.
  exploit write_promise_fulfill; eauto. i. des.
  exploit Local.promise_step_future; eauto. i. des.
  exploit merge_split; try exact STEP2; eauto; try by viewtac.
  { eapply fulfill_step_lc_from; eauto. }
  i. des.
  exploit promise_lower_promise_split_promise_split_promise_lower; try exact STEP1; try exact STEP0; eauto.
  { i. rewrite REL1'.
    instantiate (1 := val1).
    exploit Memory.promise_op; eauto. i. econs.
    eapply TViewFacts.op_closed_released; try exact x0; eauto.
    inv STEP1. apply WF0.
  }
  i. des.
  exploit Local.promise_step_future; try eexact STEP5; eauto. i. des.
  (* start from here *)
  exploit reorder_promise_lower_fulfill; try exact STEP6; try eexact STEP3; eauto; try by viewtac.
  { ii. inv H. exfalso. eapply Time.lt_strorder. eauto. }
  i. des.
  exploit fulfill_step_future; try eexact STEP7; try exact WF3; eauto; try by viewtac. i. des.
  exploit promise_fulfill_write; try eexact STEP5; eauto. i. des.
  exploit Local.write_step_future; eauto. i. des.
  exploit promise_fulfill_write; try eexact STEP8; eauto.
  { inv MSG_WF0. ss. }
  { inv MSG_CLOSED0. ss. }
  { i. hexploit ORD; eauto. i. des. splits; auto.
    eapply write_step_nonsynch_loc; eauto.
  }
  i. des.
  hexploit sim_local_write_bot; try exact MEM; try exact REL_LE; try refl; eauto.
  { inv MSG_WF0. ss. }
  { inv MSG_CLOSED0. ss. }
  i. des.
  esplits; eauto.
  - etrans; eauto.
  - etrans; eauto. etrans; eauto.
Qed.

Lemma merge_write_write
      loc ts1 ts2 ts3 val1 val2 released0 released2 ord kind
      lc0 sc0 mem0
      lc3 sc3 mem3
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (REL0_WF: View.opt_wf released0)
      (REL0_TS: Time.le ((View.rlx (View.unwrap released0)) loc) ts1)
      (REL0_CLOSED: Memory.closed_opt_view released0 mem0)
      (TS12: Time.lt ts1 ts2)
      (TS23: Time.lt ts2 ts3)
      (STEP: Local.write_step lc0 sc0 mem0 loc ts1 ts3 val2 released0 released2 ord lc3 sc3 mem3 kind):
  exists lc1' lc2' lc3' sc2' sc3' mem1' mem2' mem3' released1' released2' kind2 kind3,
    <<STEP1: Local.promise_step lc0 mem0 loc ts1 ts3 (Message.full val2 released2) lc1' mem1' kind \/ (lc0, mem0) = (lc1', mem1')>> /\
    <<STEP2: Local.write_step lc1' sc0 mem1' loc ts1 ts2 val1 released0 released1' ord lc2' sc2' mem2' kind2>> /\
    <<STEP3: Local.write_step lc2' sc2' mem2' loc ts2 ts3 val2 released1' released2' ord lc3' sc3' mem3' kind3>> /\
    <<REL3: View.opt_le released2' released2>> /\
    <<LOCAL3: sim_local SimPromises.bot lc3' lc3>> /\
    <<SC3: TimeMap.le sc3' sc3>> /\
    <<MEM3: sim_memory mem3' mem3>>.
Proof.
  destruct kind; ss.
  - (* add *)
    exploit merge_write_write_add; try apply TS12; eauto. i. des.
    esplits; try apply STEP2; eauto.
  - (* split *)
    exploit merge_write_write_split; try apply TS12; eauto. i. des.
    esplits; try apply STEP2; eauto.
  - (* lower *)
    exploit merge_write_write_lower; try apply TS12; eauto. i. des.
    esplits; try apply STEP2; eauto.
  - inv STEP. inv WRITE. inv PROMISE; ss.
Qed.

Lemma merge_write_write_None
      loc ts1 ts2 ts3 val1 val2 released0 released2 ord kind
      lc0 sc0 mem0
      lc3 sc3 mem3
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (REL0_WF: View.opt_wf released0)
      (REL0_TS: Time.le ((View.rlx (View.unwrap released0)) loc) ts1)
      (REL0_CLOSED: Memory.closed_opt_view released0 mem0)
      (TS12: Time.lt ts1 ts2)
      (TS23: Time.lt ts2 ts3)
      (STEP: Local.write_step lc0 sc0 mem0 loc ts1 ts3 val2 released0 released2 ord lc3 sc3 mem3 kind):
  exists lc1' lc2' lc3' sc2' sc3' mem1' mem2' mem3' released1' released2' kind2 kind3,
    <<STEP1: Local.promise_step lc0 mem0 loc ts1 ts3 (Message.full val2 released2) lc1' mem1' kind \/ (lc0, mem0) = (lc1', mem1')>> /\
    <<STEP2: Local.write_step lc1' sc0 mem1' loc ts1 ts2 val1 released0 released1' ord lc2' sc2' mem2' kind2>> /\
    <<STEP3: Local.write_step lc2' sc2' mem2' loc ts2 ts3 val2 None released2' ord lc3' sc3' mem3' kind3>> /\
    <<REL3: View.opt_le released2' released2>> /\
    <<LOCAL3: sim_local SimPromises.bot lc3' lc3>> /\
    <<SC3: TimeMap.le sc3' sc3>> /\
    <<MEM3: sim_memory mem3' mem3>>.
Proof.
  exploit merge_write_write; try apply TS12; eauto. i. des.
  - exploit Local.promise_step_future; eauto. i. des.
    exploit Memory.future_closed_opt_view; try exact REL0_CLOSED; eauto. i.
    exploit Local.write_step_future; try apply STEP2; eauto. i. des.
    hexploit sim_local_write_bot; try apply STEP3;
      try apply View.opt_None_spec; try refl; eauto; try by viewtac. i. des.
    esplits; cycle 1; eauto; try (etrans; eauto).
  - inv STEP1.
    exploit Local.write_step_future; try apply STEP2; eauto. i. des.
    hexploit sim_local_write_bot; try apply STEP3;
      try apply View.opt_None_spec; try refl; eauto; viewtac. i. des.
    esplits; cycle 1; eauto; try (etrans; eauto).
Qed.

Lemma merge_fence_fence
      ordr ordw
      lc0 sc0 mem0
      lc2 sc2
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP: Local.fence_step lc0 sc0 ordr ordw lc2 sc2):
  exists lc1 lc2' sc1' sc2',
    <<STEP1: Local.fence_step lc0 sc0 ordr ordw lc1 sc1'>> /\
    <<STEP2: Local.fence_step lc1 sc1' ordr ordw lc2' sc2'>> /\
    <<LOCAL: sim_local SimPromises.bot lc2' lc2>> /\
    <<SC2: TimeMap.le sc2' sc2>>.
Proof.
  inv STEP. esplits.
  - econs; eauto.
  - econs; eauto.
  - s. econs; ss.
    + unfold TView.read_fence_tview, TView.write_fence_tview, TView.write_fence_sc.
      econs; repeat (try condtac; aggrtac; try apply WF0).
    + apply SimPromises.sem_bot.
  - unfold TView.read_fence_tview, TView.write_fence_tview, TView.write_fence_sc.
    repeat (try condtac; aggrtac; try apply WF0).
Qed.
