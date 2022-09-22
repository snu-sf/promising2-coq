Require Import Bool.
Require Import List.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.

Require Import Event.
From PromisingLib Require Import Language.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import Compatibility.
Require Import SimThread.

Require Import FulfillStep.
Require Import ReorderStep.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Definition local_relfenced (lc:Local.t) :=
  (Local.mk (TView.mk
               (fun _ => (TView.cur (Local.tview lc)))
               (TView.cur (Local.tview lc))
               (TView.acq (Local.tview lc)))
            (Local.promises lc)).

Lemma local_relfenced_wf
      lc mem
      (WF: Local.wf lc mem):
  Local.wf (local_relfenced lc) mem.
Proof.
  inv WF. econs; ss; eauto.
  - inv TVIEW_WF. econs; ss. refl.
  - inv TVIEW_CLOSED. econs; ss.
Qed.

Lemma sim_local_promise_relfenced
      pview
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      lc2_tgt mem2_tgt
      loc from to msg kind
      (STEP_TGT: Local.promise_step lc1_tgt mem1_tgt loc from to msg lc2_tgt mem2_tgt kind)
      (LOCAL1: sim_local pview lc1_src (local_relfenced lc1_tgt))
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  exists lc2_src mem2_src,
    <<STEP_SRC: Local.promise_step lc1_src mem1_src loc from to (SimPromises.none_if loc to pview msg) lc2_src mem2_src (SimPromises.kind_transf loc to pview kind)>> /\
    <<LOCAL2: sim_local pview lc2_src (local_relfenced lc2_tgt)>> /\
    <<MEM2: sim_memory mem2_src mem2_tgt>>.
Proof.
  inv LOCAL1. inv STEP_TGT.
  exploit SimPromises.promise; eauto.
  { apply WF1_SRC. }
  { apply WF1_TGT. }
  i. des.
  exploit Memory.promise_future; try apply PROMISE_SRC; try apply WF1_SRC; eauto.
  { SimPromises.none_if_tac; econs; ss. inv CLOSED.
    eapply sim_memory_closed_opt_view; eauto. }
  i. des.
  esplits; eauto.
  - econs; eauto.
    SimPromises.none_if_tac; econs; ss. inv CLOSED.
    eapply sim_memory_closed_opt_view; eauto.
  - econs; eauto.
Qed.

Lemma sim_local_read_relfenced
      pview
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      lc2_tgt
      loc ts val released_tgt ord_src ord_tgt
      (STEP_TGT: Local.read_step lc1_tgt mem1_tgt loc ts val released_tgt ord_tgt lc2_tgt)
      (LOCAL1: sim_local pview lc1_src (local_relfenced lc1_tgt))
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt)
      (ORD: Ordering.le ord_src ord_tgt):
  exists released_src lc2_src,
    <<REL: View.opt_le released_src released_tgt>> /\
    <<STEP_SRC: Local.read_step lc1_src mem1_src loc ts val released_src ord_src lc2_src>> /\
    <<LOCAL2: sim_local pview lc2_src (local_relfenced lc2_tgt)>>.
Proof.
  inv LOCAL1. inv STEP_TGT.
  exploit sim_memory_get; try apply GET; try apply MEM1. i. des. inv MSG.
  esplits; eauto.
  - econs; eauto. eapply TViewFacts.readable_mon; eauto. apply TVIEW.
  - econs; eauto. inv TVIEW. ss. econs; s.
    + i. unfold LocFun.find. etrans; [by apply WF1_SRC|].
      eauto using View.join_l.
    + repeat apply View.join_le; ss.
      * unfold View.singleton_ur_if. repeat condtac; viewtac.
      * repeat condtac; viewtac.
    + repeat apply View.join_le; ss.
      * unfold View.singleton_ur_if. repeat condtac; viewtac.
      * repeat condtac; viewtac.
Qed.

Lemma sim_local_fulfill_relfenced
      pview
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      lc2_tgt sc2_tgt
      loc from to val releasedm_src releasedm_tgt released ord_src ord_tgt
      (RELM_LE: View.opt_le releasedm_src releasedm_tgt)
      (RELM_WF: View.opt_wf releasedm_src)
      (RELM_CLOSED: Memory.closed_opt_view releasedm_src mem1_src)
      (WF_RELM_TGT: View.opt_wf releasedm_tgt)
      (ORD: Ordering.le ord_src ord_tgt)
      (PVIEW: (Ordering.le Ordering.acqrel ord_tgt /\ SimPromises.mem loc to pview = false) \/
              Ordering.le ord_tgt Ordering.plain)
      (STEP_TGT: fulfill_step lc1_tgt sc1_tgt loc from to val releasedm_tgt released ord_tgt lc2_tgt sc2_tgt)
      (LOCAL1: sim_local pview lc1_src (local_relfenced lc1_tgt))
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  exists lc2_src sc2_src,
    <<STEP_SRC: fulfill_step lc1_src sc1_src loc from to val releasedm_src (SimPromises.none_if_released loc to pview released) ord_src lc2_src sc2_src>> /\
    <<LOCAL2: sim_local (SimPromises.unset loc to pview) lc2_src (local_relfenced lc2_tgt)>> /\
    <<SC2: TimeMap.le sc2_src sc2_tgt>>.
Proof.
  guardH PVIEW.
  inv STEP_TGT.
  assert (RELT_LE:
   View.opt_le
     (TView.write_released (Local.tview lc1_src) sc1_src loc to releasedm_src ord_src)
     (TView.write_released (Local.tview lc1_tgt) sc2_tgt loc to releasedm_tgt ord_tgt)).
  { unguardH PVIEW. des.
    - unfold TView.write_released.
      condtac; [|by econs].
      condtac; cycle 1.
      { by destruct ord_src, ord_tgt; inv PVIEW; inv COND0. }
      econs. unfold TView.write_tview. s.
      repeat (condtac; aggrtac); try by apply WF1_TGT.
      + rewrite <- View.join_r. rewrite <- ? View.join_l. apply LOCAL1.
      + rewrite <- View.join_r. rewrite <- ? View.join_l.
        etrans; [|apply LOCAL1]. apply WF1_SRC.
    - unfold TView.write_released. repeat (condtac; viewtac).
  }
  assert (RELT_WF:
   View.opt_wf (TView.write_released (Local.tview lc1_src) sc1_src loc to releasedm_src ord_src)).
  { unfold TView.write_released. condtac; econs.
    repeat (try condtac; viewtac; try apply WF1_SRC).
  }
  exploit SimPromises.remove; try exact REMOVE;
    try exact MEM1; try apply LOCAL1; eauto.
  { econs. ss. }
  { apply WF1_SRC. }
  { apply WF1_TGT. }
  { apply WF1_TGT. }
  i. des. esplits.
  - econs; eauto.
    + unfold SimPromises.none_if_released. condtac.
      * unguardH PVIEW. des; ss. unfold TView.write_released. condtac; [|refl].
        destruct ord_src, ord_tgt; inv ORD; inv PVIEW; inv COND0.
      * etrans; eauto.
    + unfold SimPromises.none_if_released. condtac; viewtac.
    + eapply TViewFacts.writable_mon; try exact WRITABLE; eauto. apply LOCAL1.
  - econs; eauto. inv LOCAL1. inv TVIEW. ss. econs; s.
    + i. rewrite LocFun.add_spec. condtac; ss.
      { subst. unfold LocFun.find. condtac; apply View.join_le; viewtac.
        etrans; eauto. refl.
      }
      unfold LocFun.find. etrans; [by apply WF1_SRC|].
      eauto using View.join_l.
    + apply View.join_le; viewtac.
    + apply View.join_le; viewtac.
  - ss.
Qed.

Lemma sim_local_promise_not_lower
      pview
      lc1_src
      lc1_tgt mem1_tgt loc from to msg_tgt lc1 mem2_tgt kind
      (LOCAL: sim_local pview lc1_src (local_relfenced lc1_tgt))
      (STEP: Local.promise_step lc1_tgt mem1_tgt loc from to msg_tgt lc1 mem2_tgt kind)
      (KIND: negb (Memory.op_kind_is_lower kind)):
  SimPromises.mem loc to pview = false.
Proof.
  destruct (SimPromises.mem loc to pview) eqn:X; ss.
  inv LOCAL. inv PROMISES. exploit PVIEW; eauto. i.
  inv STEP. inv PROMISE; ss.
  - exploit Memory.add_get0; try exact PROMISES; eauto. i. des. congr.
  - exploit Memory.split_get0; try exact PROMISES; eauto. i. des. congr.
  - exploit Memory.remove_get0; try exact PROMISES; eauto. i. des. congr.
Qed.

Lemma sim_local_write_relfenced
      pview
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      lc2_tgt sc2_tgt mem2_tgt
      loc from to val releasedm_src releasedm_tgt released_tgt ord_src ord_tgt kind
      (RELM_LE: View.opt_le releasedm_src releasedm_tgt)
      (RELM_SRC_WF: View.opt_wf releasedm_src)
      (RELM_SRC_CLOSED: Memory.closed_opt_view releasedm_src mem1_src)
      (RELM_TGT_WF: View.opt_wf releasedm_tgt)
      (RELM_TGT_CLOSED: Memory.closed_opt_view releasedm_tgt mem1_tgt)
      (ORD: Ordering.le ord_src ord_tgt)
      (ORD_TGT: Ordering.le ord_tgt Ordering.plain \/ Ordering.le Ordering.acqrel ord_tgt)
      (STEP_TGT: Local.write_step lc1_tgt sc1_tgt mem1_tgt loc from to val releasedm_tgt released_tgt ord_tgt lc2_tgt sc2_tgt mem2_tgt kind)
      (LOCAL1: sim_local pview lc1_src (local_relfenced lc1_tgt))
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  exists released_src lc2_src sc2_src mem2_src,
    <<STEP_SRC: Local.write_step lc1_src sc1_src mem1_src loc from to val releasedm_src released_src ord_src lc2_src sc2_src mem2_src (SimPromises.kind_transf loc to pview kind)>> /\
    <<REL2: View.opt_le released_src released_tgt>> /\
    <<LOCAL2: sim_local (SimPromises.unset loc to pview) lc2_src (local_relfenced lc2_tgt)>> /\
    <<SC2: TimeMap.le sc2_src sc2_tgt>> /\
    <<MEM2: sim_memory mem2_src mem2_tgt>>.
Proof.
  guardH ORD_TGT.
  exploit write_promise_fulfill; eauto. i. des.
  exploit Local.promise_step_future; eauto. i. des.
  exploit sim_local_promise_relfenced; eauto. i. des.
  exploit Local.promise_step_future; eauto. i. des.
  assert (PVIEW: __guard__ ((Ordering.le Ordering.acqrel ord_tgt /\ SimPromises.mem loc to pview = false) \/
                              Ordering.le ord_tgt Ordering.plain)).
  { destruct (Ordering.le ord_tgt Ordering.strong_relaxed) eqn:X.
    - right. unguardH ORD_TGT. destruct ord_tgt; des; ss.
    - left. splits.
      { by destruct ord_tgt; inv X. }
      hexploit ORD0.
      { by destruct ord_tgt; inv X. }
      exploit Local.write_step_strong_relaxed; eauto.
      { by destruct ord_tgt. }
      i. eapply sim_local_promise_not_lower; try exact STEP1; eauto.
  }
  exploit sim_local_fulfill_relfenced; try apply STEP2;
    try apply LOCAL2; try apply MEM2; eauto.
  { eapply Memory.future_closed_opt_view; eauto. }
  i. des.
  exploit promise_fulfill_write; try exact STEP_SRC; try exact STEP_SRC0; eauto.
  { i. hexploit ORD0; eauto.
    i. des. subst. splits; auto. eapply sim_local_nonsynch_loc; eauto.
  }
  i. des. esplits; eauto.
  - unguardH PVIEW. des.
    + unfold SimPromises.none_if_released in *. rewrite PVIEW0 in *. ss.
    + subst. unfold TView.write_released at 1. condtac; [|by econs].
      destruct ord_src, ord_tgt; inv ORD; inv PVIEW; inv COND.
  - etrans; eauto.
Qed.

Lemma sim_local_update_relfenced
      pview
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      lc2_tgt
      lc3_tgt sc3_tgt mem3_tgt
      loc ts1 val1 released1_tgt ord1_src ord1_tgt
      from2 to2 val2 released2_tgt ord2_src ord2_tgt kind
      (STEP1_TGT: Local.read_step lc1_tgt mem1_tgt loc ts1 val1 released1_tgt ord1_tgt lc2_tgt)
      (STEP2_TGT: Local.write_step lc2_tgt sc1_tgt mem1_tgt loc from2 to2 val2 released1_tgt released2_tgt ord2_tgt lc3_tgt sc3_tgt mem3_tgt kind)
      (LOCAL1: sim_local pview lc1_src (local_relfenced lc1_tgt))
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt)
      (ORD1: Ordering.le ord1_src ord1_tgt)
      (ORD2: Ordering.le ord2_src ord2_tgt)
      (ORD2_TGT: Ordering.le ord2_tgt Ordering.plain \/ Ordering.le Ordering.acqrel ord2_tgt):
  exists released1_src released2_src lc2_src lc3_src sc3_src mem3_src,
    <<REL1: View.opt_le released1_src released1_tgt>> /\
    <<REL2: View.opt_le released2_src released2_tgt>> /\
    <<STEP1_SRC: Local.read_step lc1_src mem1_src loc ts1 val1 released1_src ord1_src lc2_src>> /\
    <<STEP2_SRC: Local.write_step lc2_src sc1_src mem1_src loc from2 to2 val2 released1_src released2_src ord2_src lc3_src sc3_src mem3_src (SimPromises.kind_transf loc to2 pview kind)>> /\
    <<LOCAL3: sim_local (SimPromises.unset loc to2 pview) lc3_src (local_relfenced lc3_tgt)>> /\
    <<SC3: TimeMap.le sc3_src sc3_tgt>> /\
    <<MEM3: sim_memory mem3_src mem3_tgt>>.
Proof.
  guardH ORD2_TGT.
  exploit Local.read_step_future; eauto. i. des.
  exploit sim_local_read_relfenced; eauto. i. des.
  exploit Local.read_step_future; eauto. i. des.
  hexploit sim_local_write_relfenced; eauto. i. des.
  esplits; eauto.
Qed.

Lemma sim_local_fence_relfenced
      pview
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      lc2_tgt sc2_tgt
      ordr_src ordw_src
      ordr_tgt ordw_tgt
      (STEP_TGT: Local.fence_step lc1_tgt sc1_tgt ordr_tgt ordw_tgt lc2_tgt sc2_tgt)
      (LOCAL1: sim_local pview lc1_src (local_relfenced lc1_tgt))
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (ORDR: Ordering.le ordr_src ordr_tgt)
      (ORDW: Ordering.le ordw_src ordw_tgt)
      (ORDR_TGT: Ordering.le ordr_tgt Ordering.acqrel)
      (ORDW_TGT: Ordering.le ordw_tgt Ordering.relaxed):
  exists lc2_src sc2_src,
    <<STEP_SRC: Local.fence_step lc1_src sc1_src ordr_src ordw_src lc2_src sc2_src>> /\
    <<LOCAL2: sim_local pview lc2_src (local_relfenced lc2_tgt)>> /\
    <<SC2: TimeMap.le sc2_src sc2_tgt>>.
Proof.
  inv STEP_TGT. esplits; eauto.
  - econs; eauto. i. eapply sim_local_nonsynch; eauto.
  - inv LOCAL1. inv TVIEW. econs; ss.
    econs; s; unfold LocFun.find; repeat condtac; aggrtac.
    + etrans; eauto. apply WF1_TGT.
    + etrans; eauto. apply WF1_TGT.
    + etrans; eauto. apply WF1_TGT.
  - unfold TView.write_fence_sc.
    repeat (condtac; viewtac).
Qed.

Lemma sim_local_intro_relfenced
      pview
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      (LOCAL1: sim_local pview lc1_src lc1_tgt)
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt):
  <<LOCAL2: sim_local pview lc1_src (local_relfenced lc1_tgt)>>.
Proof.
  esplits. inv LOCAL1. econs; eauto.
  inv TVIEW. econs; ss; eauto.
  etrans; eauto. apply WF1_TGT.
Qed.

Lemma sim_local_fence_src_relfenced
      pview
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      (NONSYNCH: Memory.nonsynch (Local.promises lc1_src))
      (LOCAL1: sim_local pview lc1_src (local_relfenced lc1_tgt))
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt):
  exists lc2_src sc2_src,
    <<STEP_SRC: Local.fence_step lc1_src sc1_src Ordering.plain Ordering.acqrel lc2_src sc2_src>> /\
    <<LOCAL2: sim_local pview lc2_src (local_relfenced lc1_tgt)>> /\
    <<SC2: TimeMap.le sc2_src sc1_tgt>>.
Proof.
  inv LOCAL1. inv TVIEW. ss.
  esplits; eauto. econs; eauto. econs; ss; eauto.
  repeat (condtac; aggrtac).
Qed.

Lemma sim_local_fence_tgt_relfenced
      pview
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      lc2_tgt sc2_tgt
      (STEP_TGT: Local.fence_step lc1_tgt sc1_tgt Ordering.plain Ordering.acqrel lc2_tgt sc2_tgt)
      (LOCAL1: sim_local pview lc1_src (local_relfenced lc1_tgt))
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt):
  <<LOCAL2: sim_local SimPromises.bot lc1_src lc2_tgt>> /\
  <<SC2: TimeMap.le sc1_src sc2_tgt>>.
Proof.
  inv LOCAL1. inv TVIEW. inv STEP_TGT. esplits; ss.
  econs; s.
  - unfold TView.read_fence_tview. condtac; ss.
    unfold TView.write_fence_tview. econs; repeat (condtac; aggrtac).
  - econs; try by apply PROMISES.
    + inv PROMISES. ii. exploit LE; eauto.
      SimPromises.none_if_tac.
      exploit RELEASE; eauto. s. i. subst. ss.
    + i. rewrite SimPromises.bot_spec in *. congr.
Qed.


Inductive reorder_release_fenceF: forall (i2:Instr.t), Prop :=
| reorder_release_fenceF_load
    r2 l2 o2:
    reorder_release_fenceF (Instr.load r2 l2 o2)
| reorder_release_fenceF_store
    l2 v2 o2
    (ORD2: Ordering.le o2 Ordering.plain \/ Ordering.le Ordering.acqrel o2):
    reorder_release_fenceF (Instr.store l2 v2 o2)
| reorder_release_fenceF_update
    r2 l2 rmw2 or2 ow2
    (ORDW2: Ordering.le ow2 Ordering.plain \/ Ordering.le Ordering.acqrel ow2):
    reorder_release_fenceF (Instr.update r2 l2 rmw2 or2 ow2)
| reorder_release_fenceF_fence:
    reorder_release_fenceF (Instr.fence Ordering.acqrel Ordering.plain)
.

Inductive sim_release_fenceF: forall (st_src:(Language.state lang)) (lc_src:Local.t) (sc1_src:TimeMap.t) (mem1_src:Memory.t)
                        (st_tgt:(Language.state lang)) (lc_tgt:Local.t) (sc1_tgt:TimeMap.t) (mem1_tgt:Memory.t), Prop :=
| sim_relese_fenceF_intro
    rs
    pview
    lc1_src sc1_src mem1_src
    lc1_tgt sc1_tgt mem1_tgt
    (LOCALF: sim_local pview lc1_src (local_relfenced lc1_tgt)):
    sim_release_fenceF
      (State.mk rs []) lc1_src sc1_src mem1_src
      (State.mk rs [Stmt.instr (Instr.fence Ordering.plain Ordering.acqrel)]) lc1_tgt sc1_tgt mem1_tgt
.

Lemma sim_release_fenceF_step
      st1_src lc1_src sc0_src mem0_src
      st1_tgt lc1_tgt sc0_tgt mem0_tgt
      (SIM: sim_release_fenceF st1_src lc1_src sc0_src mem0_src
                               st1_tgt lc1_tgt sc0_tgt mem0_tgt):
  forall sc1_src sc1_tgt
    mem1_src mem1_tgt
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
    (MEM_TGT: Memory.closed mem1_tgt),
    _sim_thread_step lang lang ((sim_thread (sim_terminal eq)) \8/ sim_release_fenceF)
                     st1_src lc1_src sc1_src mem1_src
                     st1_tgt lc1_tgt sc1_tgt mem1_tgt.
Proof.
  inv SIM; ii. right.
  inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL];
    try (inv STATE; inv INSTR); ss.
  - (* promise *)
    exploit sim_local_promise_relfenced; eauto. i. des.
    esplits.
    + ss.
    + eauto.
    + econs 2. econs 1. econs; eauto.
    + auto.
    + auto.
    + auto.
    + right. econs 1; eauto.
  - (* fence *)
    exploit sim_local_fence_tgt_relfenced; try exact SC; eauto. i. des.
    esplits.
    + ss.
    + eauto.
    + econs 1.
    + auto.
    + auto.
    + auto.
    + left. eapply paco9_mon; [apply sim_stmts_nil|]; ss.
Qed.

Lemma sim_release_fenceF_sim_thread:
  sim_release_fenceF <8= (sim_thread (sim_terminal eq)).
Proof.
  pcofix CIH. i. pfold. ii. ss. splits; ss; ii.
  - right. inv TERMINAL_TGT. inv PR; ss.
  - inv PR.
    exploit SimPromises.cap; (try by apply LOCALF); eauto using local_relfenced_wf.
  - right. inv PR.
    esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  - exploit sim_release_fenceF_step; try apply PR; try apply SC; eauto. i. des; eauto.
    + right. esplits; eauto.
      left. eapply paco9_mon; eauto. ss.
    + right. esplits; eauto.
Qed.

Lemma reorder_release_fenceF_sim_stmts
      i1 (REORDER: reorder_release_fenceF i1):
  sim_stmts eq
            [Stmt.instr (Instr.fence Ordering.plain Ordering.acqrel); Stmt.instr i1]
            [Stmt.instr i1; Stmt.instr (Instr.fence Ordering.plain Ordering.acqrel)]
            eq.
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits; ii.
  { inv TERMINAL_TGT. }
  { exploit SimPromises.cap; try apply LOCAL; eauto. }
  { right. esplits; eauto.
    inv LOCAL. apply SimPromises.sem_bot_inv in PROMISES; auto. rewrite PROMISES. auto.
  }
  right. inv STEP_TGT.
  { (* promise *)
    inv STEP.
    exploit sim_local_promise_bot; eauto. i. des.
    esplits; try apply SC; eauto; ss.
    econs 2. econs 1; eauto. econs; eauto.
  }
  exploit sim_local_intro_relfenced; eauto. i. des.
  exploit sim_local_nonsynch_src; try exact SC_SRC; eauto using local_relfenced_wf. i. des.
  exploit Thread.rtc_tau_step_future; eauto. s. i. des.
  exploit sim_local_fence_src_relfenced; eauto. i. des.
  exploit Local.fence_step_future; eauto. i. des.
  inv STEP. inv LOCAL1; inv STATE; inv INSTR; inv REORDER.
  - (* load *)
    exploit sim_local_read_relfenced; eauto; try refl. i. des.
    esplits.
    + ss.
    + etrans; [eauto|]. econs 2; [|refl]. econs.
      * econs. econs 2. econs; [|econs 5]; eauto. econs. econs.
      * ss.
    + econs 2. econs 2. econs; [|econs 2]; eauto. econs. econs.
    + auto.
    + etrans; eauto.
    + auto.
    + left. eapply paco9_mon; [apply sim_release_fenceF_sim_thread|]; ss.
      econs. eauto.
  - (* update-load *)
    guardH ORDW2.
    exploit sim_local_read_relfenced; eauto; try refl. i. des.
    esplits.
    + ss.
    + etrans; [eauto|]. econs 2; [|refl]. econs.
      * econs. econs 2. econs; [|econs 5]; eauto. econs. econs.
      * ss.
    + econs 2. econs 2. econs; [|econs 2]; eauto. econs. econs. eauto.
    + auto.
    + etrans; eauto.
    + auto.
    + left. eapply paco9_mon; [apply sim_release_fenceF_sim_thread|]; ss.
      econs. eauto.
  - (* write *)
    guardH ORD2.
    hexploit sim_local_write_relfenced; try exact SC; eauto;
      (try refl); (try by econs). i. des.
    esplits.
    + ss.
    + etrans; [eauto|]. econs 2; [|refl]. econs.
      * econs. econs 2. econs; [|econs 5]; eauto. econs. econs.
      * ss.
    + econs 2. econs 2. econs; [|econs 3]; eauto. econs. econs.
      replace sc2_src with sc1_src; eauto. apply TimeMap.antisym; ss.
    + auto.
    + auto.
    + auto.
    + left. eapply paco9_mon; [apply sim_release_fenceF_sim_thread|]; ss.
      econs. eauto.
  - (* update *)
    guardH ORDW2.
    exploit Local.read_step_future; eauto. i. des.
    exploit sim_local_read_relfenced; eauto; try refl. i. des.
    exploit Local.read_step_future; eauto. i. des.
    hexploit sim_local_write_relfenced; try exact SC; eauto;
      (try refl); (try by econs). i. des.
    esplits.
    + ss.
    + etrans; [eauto|]. econs 2; [|refl]. econs.
      * econs. econs 2. econs; [|econs 5]; eauto. econs. econs.
      * ss.
    + econs 2. econs 2. econs; [|econs 4]; eauto.
      * econs. econs. eauto.
      * replace sc2_src with sc1_src; eauto. apply TimeMap.antisym; ss.
    + auto.
    + auto.
    + auto.
    + left. eapply paco9_mon; [apply sim_release_fenceF_sim_thread|]; ss.
      econs. eauto.
  - (* fence *)
    exploit sim_local_fence_relfenced; try exact SC; eauto; try refl. i. des.
    esplits.
    + ss.
    + etrans; [eauto|]. econs 2; [|refl]. econs.
      * econs. econs 2. econs; [|econs 5]; eauto. econs. econs.
      * ss.
    + econs 2. econs 2. econs; [|econs 5]; eauto.
      * econs. econs.
      * replace sc2_src with sc1_src; eauto. apply TimeMap.antisym; ss.
    + auto.
    + auto.
    + auto.
    + left. eapply paco9_mon; [apply sim_release_fenceF_sim_thread|]; ss.
      econs. eauto.
Qed.
