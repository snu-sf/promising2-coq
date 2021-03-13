Require Import Omega.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
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

Require Import PromiseConsistent.
Require Import ReorderPromise.
Require Import ReorderPromises.
Require Import PredStep.
Require Import MemoryReorder.
Require Import MemoryFacts.
Require Import Pred.
Require Import DRF_PF0.

Set Implicit Arguments.



Lemma reorder_read_cancel
      lc0 mem0
      lc1 mem1
      lc2
      loc1 from1 to1 msg1
      loc2 to2 val2 released2 ord2
      (STEP1: Local.read_step lc0 mem0 loc2 to2 val2 released2 ord2 lc1)
      (STEP2: Local.promise_step lc1 mem0 loc1 from1 to1 msg1 lc2 mem1 Memory.op_kind_cancel)
  (* (LOCAL0: Local.wf lc0 mem0) *)
  (* (MEM0: Memory.closed mem0) *)
  (* (LOCTS: (loc1, to1) <> (loc2, to2)): *)
  :
    exists lc1',
      (<<STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg1 lc1' mem1 Memory.op_kind_cancel>>) /\
      (<<STEP2: Local.read_step lc1' mem1 loc2 to2 val2 released2 ord2 lc2>>).
Proof.
  inv STEP1. inv STEP2.
  hexploit MemoryFacts.promise_get1_diff; eauto.
  { ii. clarify. ss. inv PROMISE.
    eapply Memory.remove_get0 in MEM. des. clarify. }
  i. des. esplits; eauto.
Qed.

Lemma reorder_promise_read
      lc0 mem0
      lc1 mem1
      lc2
      loc1 from1 to1 msg1
      loc2 to2 val2 released2 ord2
      (STEP1: Local.read_step lc0 mem0 loc2 to2 val2 released2 ord2 lc1)
      (STEP2: Local.promise_step lc1 mem0 loc1 from1 to1 msg1 lc2 mem1 Memory.op_kind_cancel)
  :
    exists lc1',
      (<<STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg1 lc1' mem1 Memory.op_kind_cancel>>) /\
      (<<STEP2: Local.read_step lc1' mem1 loc2 to2 val2 released2 ord2 lc2>>).
Proof.
  inv STEP1. inv STEP2.
  hexploit MemoryFacts.promise_get1_diff; eauto.
  { ii. clarify. ss. inv PROMISE.
    eapply Memory.remove_get0 in MEM. des. clarify. }
  i. des. esplits; eauto.
Qed.

Lemma reorder_promise_promise_cancel2
      lc0 mem0
      lc1 mem1
      lc2 mem2
      loc1 from1 to1 msg1 kind1
      loc2 from2 to2 msg2 kind2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg1 lc1 mem1 kind1)
      (STEP2: Local.promise_step lc1 mem1 loc2 from2 to2 msg2 lc2 mem2 kind2)
      (LOCAL0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (KIND1: Memory.op_kind_is_cancel kind1 = false)
      (KIND2: Memory.op_kind_is_cancel kind2 = true):
  (loc1 = loc2 /\ from1 = from2 /\ to1 = to2 /\ msg1 = Message.reserve /\ kind1 = Memory.op_kind_add /\
   lc0 = lc2 /\ mem0 = mem2) \/
  (loc1 = loc2 /\ from1 = from2 /\ to1 = to2 /\ msg1 = Message.reserve /\ kind1 = Memory.op_kind_lower Message.reserve /\
   <<STEP: Local.promise_step lc0 mem0 loc1 from1 to1 Message.reserve lc2 mem2 kind2>>) \/
  (exists lc1' mem1' from2' kind1',
      (<<STEP1: Local.promise_step lc0 mem0 loc2 from2' to2 msg2 lc1' mem1' kind2>>) /\
      (<<STEP2: Local.promise_step lc1' mem1' loc1 from1 to1 msg1 lc2 mem2 kind1'>>) /\
      (<<KIND1': Memory.op_kind_is_cancel kind1 = false>>) /\
      (<<KINDEQ: (Memory.op_kind_is_lower_full kind1' && Message.is_released_none msg1
                  || Memory.op_kind_is_cancel kind1')%bool =
                 (Memory.op_kind_is_lower_full kind1 && Message.is_released_none msg1
                  || Memory.op_kind_is_cancel kind1)%bool>>) /\
      (<<CANCEL: Memory.op_kind_is_cancel kind1' = false>>))
.
Proof.
  inv STEP1. inv STEP2. ss. inv PROMISE0; inv KIND2. inv PROMISE; ss.
  - destruct (classic ((loc1, to1) = (loc2, to2))).
    + inv H.
      exploit MemoryReorder.add_remove_same; try exact PROMISES0; eauto. i. des. subst.
      exploit MemoryReorder.add_remove_same; try exact MEM1; eauto. i. des. subst.
      left. splits; auto. destruct lc0; ss.
    + exploit MemoryReorder.add_remove; try exact PROMISES0; eauto. i. des.
      exploit MemoryReorder.add_remove; try exact MEM1; eauto. i. des.
      right. right. esplits; ss; [eauto|econs; eauto|..].
      * econs; eauto.
        { i. subst.
          exploit RESERVE; eauto. i. des.
          exploit Memory.remove_get1; try exact x; eauto. i. des; eauto.
          subst. exploit Memory.remove_get0; try exact REMOVE0; eauto. i. des. congr. }
        { i. revert GET.
          erewrite Memory.remove_o; eauto. condtac; ss. eauto. }
      * eapply Memory.cancel_closed_message; eauto.
      * ss.
      * ss.
  - destruct (classic ((loc1, ts3) = (loc2, to2))).
    + des. subst. inv H.
      exploit MemoryReorder.split_remove_same; try exact PROMISES0; eauto. i. des. subst.
      exploit MemoryReorder.split_remove_same; try exact MEM1; eauto. i. des. subst.
      right. right. esplits; ss; [eauto|econs; eauto|..].
      * econs 1; eauto; ss.
        i. revert GET.
        erewrite Memory.remove_o; eauto. condtac; ss. i. des; ss.
        exploit Memory.split_get0; try exact MEM1. i. des.
        clear GET0 GET2 GET3.
        exploit Memory.get_ts; try exact GET. i. des.
        { subst. inv ADD2. inv ADD. inv TO. }
        exploit Memory.get_ts; try exact GET1. i. des.
        { subst. inv MEM1. inv SPLIT. inv TS23. }
        exploit Memory.get_disjoint; [exact GET|exact GET1|..]. i. des.
        { subst. inv MEM1. inv SPLIT. timetac. }
        destruct (TimeFacts.le_lt_dec to' to2).
        { apply (x4 to'); econs; ss; try refl.
          inv MEM1. inv SPLIT. etrans; eauto. }
        { apply (x4 to2); econs; ss; try refl.
          - inv MEM1. inv SPLIT. ss.
          - econs. ss. }
      * eapply Memory.cancel_closed_message; eauto.
      * ss.
      * ss.
    + destruct (classic ((loc1, to1) = (loc2, to2))).
      { des. inv H0.
        exploit Memory.split_get0; try exact MEM1. i. des.
        exploit Memory.remove_get0; try exact MEM. i. des. congr. }
      exploit MemoryReorder.split_remove; try exact PROMISES0; eauto. i. des.
      exploit MemoryReorder.split_remove; try exact MEM1; eauto. i. des.
      right. right. esplits; ss; [eauto|econs; eauto|..].
      * eapply Memory.cancel_closed_message; eauto.
      * ss.
      * ss.
  - des. subst.
    destruct (classic ((loc1, to1) = (loc2, to2))).
    + inv H.
      exploit MemoryReorder.lower_remove_same; try exact PROMISES0; eauto. i. des. subst.
      exploit MemoryReorder.lower_remove_same; try exact MEM1; eauto. i. des. subst.
      exploit Memory.lower_get0; try exact MEM1. i. des. inv MSG_LE.
    + exploit MemoryReorder.lower_remove; try exact PROMISES0; eauto. i. des.
      exploit MemoryReorder.lower_remove; try exact MEM1; eauto. i. des.
      right. right. esplits; ss; [eauto|econs; eauto|..].
      * eapply Memory.cancel_closed_message; eauto.
      * ss.
      * ss.
Qed.

Lemma remove_non_synch_loc loc0 prom0 loc1 from to msg prom1
      (NONSYNCH: Memory.nonsynch_loc loc0 prom0)
      (REMOVE: Memory.remove prom0 loc1 from to msg prom1)
  :
    Memory.nonsynch_loc loc0 prom1.
Proof.
  ii. erewrite Memory.remove_o in GET; eauto.
  des_ifs. exploit NONSYNCH; eauto.
Qed.

Lemma remove_non_synch prom0 loc from to msg prom1
      (NONSYNCH: Memory.nonsynch prom0)
      (REMOVE: Memory.remove prom0 loc from to msg prom1)
  :
    Memory.nonsynch prom1.
Proof.
  ii. erewrite Memory.remove_o in GET; eauto.
  des_ifs. exploit NONSYNCH; eauto.
Qed.

Lemma reorder_write_cancel
      lc0 sc0 mem0
      lc1 mem1
      lc2 sc2 mem2
      loc1 from1 to1 msg1
      loc2 from2 to2 val2 releasedm2 released2 ord2 kind2
      (STEP1: Local.write_step lc0 sc0 mem0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc1 sc2 mem1 kind2)
      (STEP2: Local.promise_step lc1 mem1 loc1 from1 to1 msg1 lc2 mem2 Memory.op_kind_cancel)
  :
    exists kind2' lc1' mem1',
      (exists from1', <<STEP2: Local.promise_step lc0 mem0 loc1 from1' to1 msg1 lc1' mem1' Memory.op_kind_cancel>>) /\
      (<<STEP2: Local.write_step lc1' sc0 mem1' loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2 mem2 kind2'>>).
Proof.
  inv STEP2. inv PROMISE.
  inv STEP1. ss. inv WRITE.
  exploit MemoryReorder.remove_remove.
  { eapply REMOVE. }
  { eapply PROMISES. } i. des.
  assert (LOCTS: (loc2, to2) <> (loc1, to1)).
  { ii. clarify. apply Memory.remove_get0 in MEM. inv PROMISE.
    - apply Memory.add_get0 in MEM0. des. clarify.
    - apply Memory.split_get0 in MEM0. des. clarify.
    - apply Memory.lower_get0 in MEM0. des. clarify.
    - clarify. }
  inv PROMISE.
  - exploit MemoryReorder.add_remove.
    { eapply LOCTS. }
    { eapply PROMISES0. }
    { eauto. } i. des.
    exploit MemoryReorder.add_remove.
    { eapply LOCTS. }
    { eapply MEM0. }
    { eauto. } i. des.
    esplits.
    + econs; eauto.
    + econs; ss.
      * econs.
        { econs 1; eauto.
          - i. clarify.
          - i. erewrite Memory.remove_o in GET; eauto.
            des_ifs. eapply ATTACH; eauto. }
        { eauto. }
      * intros ORD. eapply RELEASE in ORD.
        eapply remove_non_synch_loc; eauto.
  - destruct (classic ((loc2, ts3) = (loc1, to1))) as [|LOCTS2]; clarify.
    { exploit MemoryReorder.split_remove_same.
      { eapply PROMISES0. }
      { eauto. } i. des. clarify.
      exploit MemoryReorder.split_remove_same.
      { eapply MEM0. }
      { eauto. } i. des. clarify.
      esplits.
      + econs; eauto.
      + econs; ss.
        * econs.
          { econs 1; eauto.
            - i. clarify.
            - i. clarify.
              eapply split_succeed_wf in MEM0. des.
              erewrite Memory.remove_o in GET; eauto. des_ifs.
              exploit Memory.get_disjoint.
              + eapply GET.
              + eapply GET2.
              + i. des; clarify.
                eapply Memory.get_ts in GET. des; ss; clarify.
                * eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
                  { eapply TS12. }
                  { eapply Time.bot_spec. }
                * eapply x2.
                  { instantiate (1:=Time.meet to' to1). econs; ss.
                    - unfold Time.meet. des_ifs.
                    - eapply Time.meet_l. }
                  { econs; ss.
                    - unfold Time.meet. des_ifs.
                      + etrans; eauto.
                      + etrans; eauto.
                    - eapply Time.meet_r. }
          }
          { eauto. }
        * intros ORD. eapply RELEASE in ORD.
          eapply remove_non_synch_loc; eauto. }
    { exploit MemoryReorder.split_remove.
      { eapply LOCTS. }
      { eapply LOCTS2. }
      { eapply PROMISES0. }
      { eauto. } i. des.
      exploit MemoryReorder.split_remove.
      { eapply LOCTS. }
      { eapply LOCTS2. }
      { eapply MEM0. }
      { eauto. } i. des.
      esplits.
      + econs; eauto.
      + econs; ss.
        * econs.
          { econs 2; eauto. }
          { eauto. }
        * intros ORD. eapply RELEASE in ORD.
          eapply remove_non_synch_loc; eauto. }
  - exploit MemoryReorder.lower_remove.
    { eapply LOCTS. }
    { eapply PROMISES0. }
    { eauto. } i. des.
    exploit MemoryReorder.lower_remove.
    { eapply LOCTS. }
    { eapply MEM0. }
    { eauto. } i. des.
    esplits.
    + econs; eauto.
    + econs; ss.
      * econs.
        { econs 3; eauto. }
        { eauto. }
      * intros ORD. eapply RELEASE in ORD.
        eapply remove_non_synch_loc; eauto.
  - clarify.
Qed.

Lemma reorder_fence_cancel
      lc0 mem0
      lc1 mem1
      lc2
      loc1 from1 to1 msg1
      ord1 ord2 sc0 sc1
      (STEP1: Local.fence_step lc0 sc0 ord1 ord2 lc1 sc1)
      (STEP2: Local.promise_step lc1 mem0 loc1 from1 to1 msg1 lc2 mem1 Memory.op_kind_cancel)
  :
    exists lc1',
      (<<STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg1 lc1' mem1 Memory.op_kind_cancel>>) /\
      (<<STEP2: Local.fence_step lc1' sc0 ord1 ord2 lc2 sc1>>).
Proof.
  inv STEP1. inv STEP2. ss. esplits.
  - econs; eauto.
  - econs; eauto.
    inv PROMISE. i. eapply remove_non_synch; eauto.
Qed.

Lemma reorder_pf_step_cancel
      lang
      e1 e2 th0 th1 th2
      (STEP1: @pred_step (promise_free /1\ (fun e => ~ is_cancel e)) lang
                         e1 th0 th1)
      (STEP2: pred_step is_cancel e2 th1 th2)
      (LOCAL: Local.wf (Thread.local th0) (Thread.memory th0))
      (MEMORY: Memory.closed (Thread.memory th0)):
  exists e2' e1' th1',
    (<<STEP1: pred_step is_cancel e2' th0 th1'>>) /\
    (<<STEP2: pred_step (promise_free /1\ (fun e => ~ is_cancel e)) e1' th1' th2>>) /\
    (<<EVT: ThreadEvent.get_machine_event e1' = ThreadEvent.get_machine_event e1>>)
.
Proof.
  inv STEP1. inv STEP2. des. unfold is_cancel in SAT0. des_ifs.
  inv STEP0. inv STEP1; inv STEP0; [|inv LOCAL0]. ss.
  inv STEP. inv STEP0; ss.
  - inv STEP. ss. exploit reorder_promise_promise_cancel2; eauto.
    { des_ifs. }
    i. des; clarify. esplits.
    + econs.
      * econs. econs 1. econs; eauto.
      * ss.
    + econs.
      * econs. econs 1. econs; eauto.
      * ss. rewrite CANCEL. split; auto. des_ifs.
    + ss.
  - inv STEP. ss. inv LOCAL1; ss.
    + esplits.
      * econs.
        { econs. econs 1. econs; eauto. }
        { ss. }
      * econs.
        { econs. econs 2. econs; eauto; ss. }
        { ss. }
      * ss.
    + exploit reorder_read_cancel; eauto. i. des. esplits.
      * econs.
        { econs. econs 1. econs; eauto. }
        { ss. }
      * econs.
        { econs. econs 2. econs; eauto; ss. }
        { ss. }
      * ss.
    + exploit reorder_write_cancel; eauto. i. des. esplits.
      * econs.
        { econs. econs 1. econs; eauto. }
        { ss. }
      * econs.
        { econs. econs 2. econs; eauto; ss. }
        { ss. }
      * ss.
    + exploit reorder_write_cancel; eauto. i. des.
      exploit reorder_read_cancel; eauto. i. des.
      esplits.
      * econs.
        { econs. econs 1. econs; eauto. }
        { ss. }
      * econs.
        { econs. econs 2. econs; eauto; ss. }
        { ss. }
      * ss.
    + exploit reorder_fence_cancel; eauto. i. des. esplits.
      * econs.
        { econs. econs 1. econs; eauto. }
        { ss. }
      * econs.
        { econs. econs 2. econs; eauto; ss. }
        { ss. }
      * ss.
    + exploit reorder_fence_cancel; eauto. i. des. esplits.
      * econs.
        { econs. econs 1. econs; eauto. }
        { ss. }
      * econs.
        { econs. econs 2. econs; eauto; ss. eauto. }
        { ss. }
      * ss.
    + esplits.
      * econs; eauto.
        { econs. econs 1. econs; eauto. }
        { ss. }
      * econs.
        { econs. econs 2. econs.
          - instantiate (1:=ThreadEvent.failure). auto.
          - econs. econs. inv LOCAL2. inv LOCAL0. inv PROMISE.
            ii. ss. erewrite Memory.remove_o in PROMISE; eauto. des_ifs.
            eapply CONSISTENT; eauto. }
        { ss. }
      * ss.
Qed.

Lemma reorder_pf_step_cancels
      lang
      e1 th0 th1 th2
      (STEP1: @pred_step (promise_free /1\ (fun e => ~ is_cancel e)) lang
                         e1 th0 th1)
      (STEPS2: rtc (tau (@pred_step is_cancel _)) th1 th2)
      (LOCAL: Local.wf (Thread.local th0) (Thread.memory th0))
      (MEMORY: Memory.closed (Thread.memory th0))
      (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
  :
    exists e1' th1',
      (<<STEPS1: rtc (tau (@pred_step is_cancel _)) th0 th1'>>) /\
      (<<STEP2: pred_step (promise_free /1\ (fun e => ~ is_cancel e)) e1' th1' th2>>) /\
      (<<EVT: ThreadEvent.get_machine_event e1' = ThreadEvent.get_machine_event e1>>)
.
Proof.
  ginduction STEPS2; i.
  - esplits; eauto.
  - inv H. exploit reorder_pf_step_cancel.
    { eapply STEP1. }
    { eapply TSTEP. }
    { eauto. }
    { eauto. }
    i. des.
    dup STEP0. inv STEP3. inv STEP. exploit Thread.step_future.
    { eapply STEP3. }
    { eauto. }
    { eauto. }
    { eauto. } i. des.
    exploit IHSTEPS2; eauto. i. des.
    esplits.
    + econs 2.
      * econs; eauto.
        unfold is_cancel in SAT. des_ifs.
      * eauto.
    + eauto.
    + etrans; eauto.
Qed.

Lemma pf_steps_cancels_not_cancels
      lang th0 th2
      (STEPS: rtc (tau (@pred_step promise_free lang)) th0 th2)
      (LOCAL: Local.wf (Thread.local th0) (Thread.memory th0))
      (MEMORY: Memory.closed (Thread.memory th0))
      (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
  :
    exists th1,
      (<<STEPS1: rtc (tau (@pred_step is_cancel _)) th0 th1>>) /\
      (<<STEPS2: rtc (tau (@pred_step (promise_free /1\ (fun e => ~ is_cancel e)) _)) th1 th2>>)
.
Proof.
  ginduction STEPS; i.
  - esplits; eauto.
  - inv H. dup TSTEP. inv TSTEP0. inv STEP.
    exploit Thread.step_future; eauto. i. des.
    exploit IHSTEPS; eauto. i. des.
    destruct (classic (is_cancel e)).
    + esplits.
      * econs 2.
        { econs.
          - econs; eauto.
            econs. eapply STEP0.
          - unfold is_cancel in H. des_ifs. }
        { eapply STEPS1. }
      * eapply STEPS2.
    + exploit reorder_pf_step_cancels.
      { econs.
        - econs. eapply STEP0.
        - splits; auto. }
      { eapply STEPS1. }
      { eauto. }
      { eauto. }
      { eauto. }
      i. des. esplits.
      * eauto.
      * econs 2.
        { econs; eauto. etrans; eauto. }
        { eauto. }
Qed.
