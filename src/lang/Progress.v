Require Import Omega.
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
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.

Set Implicit Arguments.


Lemma write_step_promise
      lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
      (STEP: Local.write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind)
      (PROMISES: (Local.promises lc1) = Memory.bot):
  (Local.promises lc2) = Memory.bot.
Proof.
  inv STEP. rewrite PROMISES in *. s.
  apply Memory.ext. i. rewrite Memory.bot_get.
  inv WRITE.
  erewrite Memory.remove_o; eauto. condtac; ss. guardH o.
  inv PROMISE; ss.
  - erewrite Memory.add_o; eauto. condtac; ss.
    apply Memory.bot_get.
  - erewrite Memory.split_o; eauto. repeat condtac; ss.
    + guardH o0. des. subst.
      exploit Memory.split_get0; try exact PROMISES0; eauto. i. des.
      rewrite Memory.bot_get in *. congr.
    + apply Memory.bot_get.
  - erewrite Memory.lower_o; eauto. condtac; ss.
    apply Memory.bot_get.
Qed.

Lemma program_step_promise
      lang e
      st1 lc1 sc1 mem1
      st2 lc2 sc2 mem2
      (STEP: Thread.program_step e (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2))
      (PROMISES: (Local.promises lc1) = Memory.bot):
  (Local.promises lc2) = Memory.bot.
Proof.
  inv STEP. inv LOCAL; ss; try by inv LOCAL0.
  - eapply write_step_promise; eauto.
  - eapply write_step_promise; eauto.
    inv LOCAL1. auto.
Qed.

Lemma closed_timemap_max_ts
      loc tm mem
      (CLOSED: Memory.closed_timemap tm mem):
  Time.le (tm loc) (Memory.max_ts loc mem).
Proof.
  specialize (CLOSED loc). des.
  eapply Memory.max_ts_spec. eauto.
Qed.

Lemma closed_timemap_max_full_ts
      loc tm mem mts
      (CLOSED: Memory.closed_timemap tm mem)
      (MAX: Memory.max_full_ts mem loc mts):
  Time.le (tm loc) mts.
Proof.
  specialize (CLOSED loc). des.
  eapply Memory.max_full_ts_spec; eauto.
Qed.

Lemma progress_promise_step
      lc1 sc1 mem1
      loc to val releasedm ord
      (LT: Time.lt (Memory.max_ts loc mem1) to)
      (WF1: Local.wf lc1 mem1)
      (MEM1: Memory.closed mem1)
      (SC1: Memory.closed_timemap sc1 mem1)
      (WF_REL: View.opt_wf releasedm)
      (CLOSED_REL: Memory.closed_opt_view releasedm mem1):
  exists promises2 mem2,
    Local.promise_step lc1 mem1 loc (Memory.max_ts loc mem1) to
                       (Message.full val (TView.write_released (Local.tview lc1) sc1 loc to releasedm ord))
                       (Local.mk (Local.tview lc1) promises2) mem2 Memory.op_kind_add.
Proof.
  exploit (@Memory.add_exists_max_ts
             mem1 loc to
             (Message.full val (TView.write_released (Local.tview lc1) sc1 loc to releasedm ord))); eauto.
  { econs. eapply TViewFacts.write_future0; eauto. apply WF1. }
  i. des.
  exploit Memory.add_exists_le; try apply WF1; eauto. i. des.
  hexploit Memory.add_inhabited; try apply x0; [viewtac|]. i. des.
  esplits. econs; eauto.
  - econs; eauto; try congr.
    + econs. unfold TView.write_released.
      viewtac; repeat (condtac; viewtac);
        (try by apply Time.bot_spec);
        (try by unfold TimeMap.singleton, LocFun.add; condtac; [refl|congr]);
        (try by left; eapply TimeFacts.le_lt_lt; [|eauto];
         eapply closed_timemap_max_ts; apply WF1).
      left. eapply TimeFacts.le_lt_lt; [|eauto].
      eapply closed_timemap_max_ts. apply Memory.unwrap_closed_opt_view; viewtac.
    + i. inv x0. inv ADD. clear DISJOINT MSG_WF CELL2.
      exploit Memory.get_ts; try exact GET. i. des.
      { subst. inv TO. }
      exploit Memory.max_ts_spec; try exact GET. i. des.
      eapply Time.lt_strorder. etrans; try exact TO.
      eapply TimeFacts.lt_le_lt; eauto.
  - econs. unfold TView.write_released. condtac; econs.
    viewtac;
      repeat condtac; viewtac;
        (try eapply Memory.add_closed_view; eauto);
        (try apply WF1).
    + viewtac.
    + erewrite Memory.add_o; eauto. condtac; eauto. ss. des; congr.
    + erewrite Memory.add_o; eauto. condtac; eauto. ss. des; congr.
Qed.

Lemma progress_read_step
      lc1 mem1
      loc ord
      (WF1: Local.wf lc1 mem1)
      (MEM1: Memory.closed mem1):
  exists val released lc2 mts,
    <<MAX: Memory.max_full_ts mem1 loc mts>> /\
    <<READ: Local.read_step lc1 mem1 loc mts val released ord lc2>>.
Proof.
  dup MEM1. inv MEM0.
  exploit (Memory.max_full_ts_exists); eauto. i. des.
  exploit (Memory.max_full_ts_spec); eauto. i. des.
  esplits; eauto. econs; eauto.
  econs; i; eapply Memory.max_full_ts_spec2; eauto; apply WF1.
Qed.

Lemma progress_read_step_cur
      lc1 mem1
      loc ord
      (WF1: Local.wf lc1 mem1)
      (MEM1: Memory.closed mem1):
  exists val released lc2,
    <<READ: Local.read_step lc1 mem1 loc ((TView.cur (Local.tview lc1)).(View.rlx) loc) val released ord lc2>>.
Proof.
  dup WF1. inv WF0. inv TVIEW_CLOSED. inv CUR.
  specialize (RLX loc). des.
  esplits. econs; eauto.
  econs; try apply TVIEW_WF; try refl.
Qed.

Lemma progress_write_step
      lc1 sc1 mem1
      loc to val releasedm ord
      (LT: Time.lt (Memory.max_ts loc mem1) to)
      (WF1: Local.wf lc1 mem1)
      (SC1: Memory.closed_timemap sc1 mem1)
      (MEM1: Memory.closed mem1)
      (WF_REL: View.opt_wf releasedm)
      (CLOSED_REL: Memory.closed_opt_view releasedm mem1)
      (PROMISES1: Ordering.le Ordering.strong_relaxed ord -> Memory.nonsynch_loc loc (Local.promises lc1)):
  exists released lc2 sc2 mem2,
    Local.write_step lc1 sc1 mem1 loc (Memory.max_ts loc mem1) to val releasedm released ord lc2 sc2 mem2 Memory.op_kind_add.
Proof.
  exploit progress_promise_step; eauto. i. des.
  exploit Local.promise_step_future; eauto. i. des. inv x0.
  exploit Memory.remove_exists; eauto.
  { inv PROMISE. erewrite Memory.add_o; try eexact PROMISES.
    condtac; eauto. ss. des; exfalso; apply o; eauto.
  }
  i. des.
  esplits. econs; eauto.
  econs; i; (try eapply TimeFacts.le_lt_lt; [|eauto]).
  apply Memory.max_ts_spec2. apply WF1.
Qed.

Lemma progress_write_step_split
      lc1 sc1 mem1
      loc from to msg val releasedm ord
      (GET: Memory.get loc to (Local.promises lc1) = Some (from, msg))
      (CONS: Time.lt ((TView.cur (Local.tview lc1)).(View.rlx) loc) to)
      (WF1: Local.wf lc1 mem1)
      (SC1: Memory.closed_timemap sc1 mem1)
      (MEM1: Memory.closed mem1)
      (WF_REL: View.opt_wf releasedm)
      (TS_REL: Time.le ((View.rlx (View.unwrap releasedm)) loc) from)
      (CLOSED_REL: Memory.closed_opt_view releasedm mem1)
      (PROMISES1: Ordering.le Ordering.strong_relaxed ord -> Memory.nonsynch_loc loc (Local.promises lc1)):
  exists released lc2 sc2 mem2,
    Local.write_step lc1 sc1 mem1 loc from (Time.middle from to) val releasedm
                     released ord lc2 sc2 mem2 (Memory.op_kind_split to msg).
Proof.
  exploit Memory.get_ts; try exact GET. i. des.
  { subst. inv WF1. rewrite BOT in GET. ss. }
  exploit (@Memory.split_exists
             (Local.promises lc1) loc from (Time.middle from to) to
             (Message.full val (TView.write_released (Local.tview lc1) sc1 loc (Time.middle from to) releasedm ord))
             msg);
    try apply Time.middle_spec; auto.
  { econs. eapply TViewFacts.write_future0; eauto. apply WF1. }
  i. des.
  exploit Memory.split_exists_le; try apply WF1; eauto. i. des.
  exploit Memory.split_get0; try exact x1. i. des.
  exploit Memory.remove_exists; try exact GET2. i. des.
  clear GET0 GET1 GET2 GET3.
  assert (TS: Time.le ((TView.cur (Local.tview lc1)).(View.rlx) loc) from).
  { destruct (TimeFacts.le_lt_dec ((TView.cur (Local.tview lc1)).(View.rlx) loc) from); ss.
    inv WF1. inv TVIEW_CLOSED. inv CUR.
    specialize (RLX loc). des.
    clear REL ACQ PLN.
    exploit PROMISES; try exact GET. i.
    exploit Memory.get_ts; try exact RLX. i. des.
    { subst. rewrite x4 in l. inv l. }
    exploit Memory.get_disjoint; [exact RLX|exact x|..]. i. des.
    { subst. timetac. }
    exfalso.
    eapply x6; econs; [|refl|..]; ss. econs. ss.
  }
  esplits. econs; eauto.
  - econs; ss.
    eapply TimeFacts.le_lt_lt; eauto.
    apply Time.middle_spec. ss.
  - econs; eauto. econs; eauto.
    econs. unfold TView.write_released. ss.
    condtac; ss; try by unfold TimeMap.bot; apply Time.bot_spec.
    unfold LocFun.add. condtac; ss.
    unfold TimeMap.join. condtac; ss.
    + unfold TimeMap.join, TimeMap.singleton.
      unfold LocFun.add, LocFun.init, LocFun.find.
      condtac; ss.
      repeat apply Time.join_spec; ss; try refl.
      * etrans; eauto. econs. apply Time.middle_spec; ss.
      * etrans; eauto. econs. apply Time.middle_spec; ss.
    + unfold TimeMap.join, TimeMap.singleton.
      unfold LocFun.add, LocFun.init, LocFun.find.
      condtac; ss.
      repeat apply Time.join_spec; ss; try refl.
      * etrans; eauto. econs. apply Time.middle_spec; ss.
      * inv WF1. inv TVIEW_WF. etrans; try eapply REL_CUR.
        etrans; eauto. econs. apply Time.middle_spec; ss.
Qed.

Lemma progress_fence_step
      lc1 sc1
      ordr ordw
      (PROMISES1: Ordering.le Ordering.strong_relaxed ordw -> Memory.nonsynch (Local.promises lc1)):
  exists lc2 sc2,
    Local.fence_step lc1 sc1 ordr ordw lc2 sc2.
Proof.
  esplits. econs; eauto.
Qed.
