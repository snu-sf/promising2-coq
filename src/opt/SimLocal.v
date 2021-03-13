Require Import RelationClasses.
Require Import Bool.
Require Import List.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.

Require Import Event.
Require Import Time.
From PromisingLib Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import MemoryDomain.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import FulfillStep.
Require Import SimMemory.
Require Import SimPromises.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Inductive sim_local (pview:SimPromises.t) (lc_src lc_tgt:Local.t): Prop :=
| sim_local_intro
    (TVIEW: TView.le (Local.tview lc_src) (Local.tview lc_tgt))
    (PROMISES: SimPromises.sem pview SimPromises.bot (Local.promises lc_src) (Local.promises lc_tgt))
.

Program Instance sim_local_PreOrder: PreOrder (sim_local SimPromises.bot).
Next Obligation.
  econs; try refl. apply SimPromises.sem_bot.
Qed.
Next Obligation.
  ii. inv H. inv H0. econs; try etrans; eauto.
  apply SimPromises.sem_bot_inv in PROMISES; auto.
  apply SimPromises.sem_bot_inv in PROMISES0; auto.
  rewrite PROMISES, PROMISES0. apply SimPromises.sem_bot.
Qed.

Lemma sim_local_nonsynch_loc
      pview loc lc_src lc_tgt
      (SIM: sim_local pview lc_src lc_tgt)
      (NONSYNCH: Memory.nonsynch_loc loc (Local.promises lc_tgt)):
  Memory.nonsynch_loc loc (Local.promises lc_src).
Proof.
  inv SIM. inv PROMISES.
  ii. destruct msg; ss.
  destruct (Memory.get loc t (Local.promises lc_tgt)) as [[? []]|] eqn:GET_TGT.
  - exploit NONSYNCH; eauto. ss. i. subst.
    exploit LE; eauto. intro X. rewrite GET in X. inv X.
    unfold SimPromises.none_if, SimPromises.none_if_released. condtac; ss.
  - exploit LE; eauto. s. i. congr.
  - exploit COMPLETE; eauto. rewrite SimPromises.bot_spec. ss.
Qed.

Lemma sim_local_nonsynch
      pview lc_src lc_tgt
      (SIM: sim_local pview lc_src lc_tgt)
      (NONSYNCH: Memory.nonsynch (Local.promises lc_tgt)):
  Memory.nonsynch (Local.promises lc_src).
Proof.
  ii. eapply sim_local_nonsynch_loc; eauto.
Qed.

Lemma sim_local_memory_bot
      pview lc_src lc_tgt
      (SIM: sim_local pview lc_src lc_tgt)
      (BOT: (Local.promises lc_tgt) = Memory.bot):
  (Local.promises lc_src) = Memory.bot.
Proof.
  inv SIM. inv PROMISES. rewrite BOT in *.
  apply Memory.ext. i. rewrite Memory.bot_get.
  destruct (Memory.get loc ts (Local.promises lc_src)) eqn:GET_SRC; ss.
  destruct p.
  exploit COMPLETE; eauto.
  - apply Memory.bot_get.
  - rewrite SimPromises.bot_spec. ss.
Qed.  

Lemma sim_local_promise
      pview
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      lc2_tgt mem2_tgt
      loc from to msg kind
      (STEP_TGT: Local.promise_step lc1_tgt mem1_tgt loc from to msg lc2_tgt mem2_tgt kind)
      (LOCAL1: sim_local pview lc1_src lc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  exists lc2_src mem2_src,
    <<STEP_SRC: Local.promise_step lc1_src mem1_src loc from to (SimPromises.none_if loc to pview msg) lc2_src mem2_src (SimPromises.kind_transf loc to pview kind)>> /\
    <<LOCAL2: sim_local pview lc2_src lc2_tgt>> /\
    <<MEM2: sim_memory mem2_src mem2_tgt>>.
Proof.
  inv LOCAL1. inv STEP_TGT.
  exploit SimPromises.promise; eauto.
  { apply WF1_SRC. }
  { apply WF1_TGT. }
  i. des.
  exploit sim_memory_closed_message; eauto. i.
  exploit Memory.promise_future; try apply PROMISE_SRC; try apply WF1_SRC; eauto.
  { unfold SimPromises.none_if, SimPromises.none_if_released.
    destruct msg; try condtac; eauto. }
  i. des.
  esplits; eauto.
  - econs; eauto. SimPromises.none_if_tac. eauto.
  - econs; eauto.
Qed.

Lemma sim_local_promise_bot
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      lc2_tgt mem2_tgt
      loc from to msg kind
      (STEP_TGT: Local.promise_step lc1_tgt mem1_tgt loc from to msg lc2_tgt mem2_tgt kind)
      (LOCAL1: sim_local SimPromises.bot lc1_src lc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  exists lc2_src mem2_src,
    <<STEP_SRC: Local.promise_step lc1_src mem1_src loc from to msg lc2_src mem2_src kind>> /\
    <<LOCAL2: sim_local SimPromises.bot lc2_src lc2_tgt>> /\
    <<MEM2: sim_memory mem2_src mem2_tgt>>.
Proof.
  exploit sim_local_promise; eauto.
  rewrite SimPromises.none_if_bot.
  rewrite SimPromises.kind_transf_bot. ss.
Qed.

Lemma sim_local_read
      pview
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      lc2_tgt
      loc ts val released_tgt ord_src ord_tgt
      (STEP_TGT: Local.read_step lc1_tgt mem1_tgt loc ts val released_tgt ord_tgt lc2_tgt)
      (LOCAL1: sim_local pview lc1_src lc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt)
      (ORD: Ordering.le ord_src ord_tgt):
  exists released_src lc2_src,
    <<REL: View.opt_le released_src released_tgt>> /\
    <<STEP_SRC: Local.read_step lc1_src mem1_src loc ts val released_src ord_src lc2_src>> /\
    <<LOCAL2: sim_local pview lc2_src lc2_tgt>>.
Proof.
  inv LOCAL1. inv STEP_TGT.
  exploit sim_memory_get; try apply GET; eauto. i. des.
  inv MSG. esplits; eauto.
  - econs; eauto. eapply TViewFacts.readable_mon; eauto. apply TVIEW.
  - econs; eauto. s. apply TViewFacts.read_tview_mon; auto.
    + apply WF1_TGT.
    + inv MEM1_TGT. exploit CLOSED; eauto. i. des. inv MSG_WF. auto.
Qed.

Lemma sim_local_fulfill
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
      (PVIEW: SimPromises.mem loc to pview = false \/ Ordering.le ord_tgt Ordering.plain)
      (STEP_TGT: fulfill_step lc1_tgt sc1_tgt loc from to val releasedm_tgt released ord_tgt lc2_tgt sc2_tgt)
      (LOCAL1: sim_local pview lc1_src lc1_tgt)
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
    <<LOCAL2: sim_local (SimPromises.unset loc to pview) lc2_src lc2_tgt>> /\
    <<SC2: TimeMap.le sc2_src sc2_tgt>>.
Proof.
  guardH PVIEW.
  inv STEP_TGT.
  assert (RELT_LE:
   View.opt_le
     (TView.write_released (Local.tview lc1_src) sc1_src loc to releasedm_src ord_src)
     (TView.write_released (Local.tview lc1_tgt) sc2_tgt loc to releasedm_tgt ord_tgt)).
  { apply TViewFacts.write_released_mon; ss.
    - apply LOCAL1.
    - apply WF1_TGT.
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
    + SimPromises.none_if_tac.
      * unguardH PVIEW. des; ss. unfold TView.write_released. condtac; [|refl].
        destruct ord_src, ord_tgt; inv ORD; inv PVIEW; inv COND0.
      * etrans; eauto.
    + SimPromises.none_if_tac; viewtac.
    + eapply TViewFacts.writable_mon; try exact WRITABLE; eauto. apply LOCAL1.
  - econs; eauto. s. apply TViewFacts.write_tview_mon; auto.
    + apply LOCAL1.
    + apply WF1_TGT.
  - ss.
Qed.

Lemma sim_local_fulfill_bot
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      lc2_tgt sc2_tgt
      loc from to val releasedm_src releasedm_tgt released ord_src ord_tgt
      (RELM_LE: View.opt_le releasedm_src releasedm_tgt)
      (RELM_WF: View.opt_wf releasedm_src)
      (RELM_CLOSED: Memory.closed_opt_view releasedm_src mem1_src)
      (WF_RELM_TGT: View.opt_wf releasedm_tgt)
      (ORD: Ordering.le ord_src ord_tgt)
      (STEP_TGT: fulfill_step lc1_tgt sc1_tgt loc from to val releasedm_tgt released ord_tgt lc2_tgt sc2_tgt)
      (LOCAL1: sim_local SimPromises.bot lc1_src lc1_tgt)
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  exists lc2_src sc2_src,
    <<STEP_SRC: fulfill_step lc1_src sc1_src loc from to val releasedm_src released ord_src lc2_src sc2_src>> /\
    <<LOCAL2: sim_local SimPromises.bot lc2_src lc2_tgt>> /\
    <<SC2: TimeMap.le sc2_src sc2_tgt>>.
Proof.
  exploit sim_local_fulfill; eauto.
  { rewrite SimPromises.bot_spec. intuition. }
  i. des. esplits; eauto.
  rewrite SimPromises.unset_bot in *; ss.
Qed.

Lemma sim_local_promise_not_lower
      pview
      lc1_src
      lc1_tgt mem1_tgt loc from to msg_tgt lc1 mem2_tgt kind
      (LOCAL: sim_local pview lc1_src lc1_tgt)
      (STEP: Local.promise_step lc1_tgt mem1_tgt loc from to msg_tgt lc1 mem2_tgt kind)
      (KIND: negb (Memory.op_kind_is_lower kind)):
  SimPromises.mem loc to pview = false.
Proof.
  destruct (SimPromises.mem loc to pview) eqn:X; ss.
  inv LOCAL. inv PROMISES. exploit PVIEW; eauto. i. des.
  inv STEP. inv PROMISE; ss.
  - exploit Memory.add_get0; try exact PROMISES; eauto. i. des. congr.
  - exploit Memory.split_get0; try exact PROMISES; eauto. i. des. congr.
  - exploit Memory.remove_get0; try exact PROMISES; eauto. i. des. congr.
Qed.

Lemma sim_local_write
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
      (PVIEW: SimPromises.mem loc to pview = false \/
              Ordering.le ord_tgt Ordering.plain \/
              Ordering.le Ordering.strong_relaxed ord_tgt)
      (STEP_TGT: Local.write_step lc1_tgt sc1_tgt mem1_tgt loc from to val releasedm_tgt released_tgt ord_tgt lc2_tgt sc2_tgt mem2_tgt kind)
      (LOCAL1: sim_local pview lc1_src lc1_tgt)
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  exists released_src lc2_src sc2_src mem2_src,
    <<STEP_SRC: Local.write_step lc1_src sc1_src mem1_src loc from to val releasedm_src
                                 released_src
                                 ord_src lc2_src sc2_src mem2_src
                                 (SimPromises.kind_transf loc to pview kind)>> /\
    <<REL2: View.opt_le released_src released_tgt>> /\
    <<LOCAL2: sim_local (SimPromises.unset loc to pview) lc2_src lc2_tgt>> /\
    <<SC2: TimeMap.le sc2_src sc2_tgt>> /\
    <<MEM2: sim_memory mem2_src mem2_tgt>>.
Proof.
  guardH PVIEW.
  exploit write_promise_fulfill; eauto. i. des.
  exploit Local.promise_step_future; eauto. i. des.
  exploit sim_local_promise; eauto. i. des.
  exploit Local.promise_step_future; eauto. i. des.
  exploit sim_local_fulfill; try apply STEP2;
    try apply LOCAL2; try apply MEM2; eauto.
  { eapply Memory.future_closed_opt_view; eauto. }
  { unguardH PVIEW. des; intuition.
    exploit Local.write_step_strong_relaxed; eauto. i.
    left. eapply sim_local_promise_not_lower; try exact STEP1; eauto.
  }
  i. des.
  exploit promise_fulfill_write; try exact STEP_SRC; try exact STEP_SRC0; eauto.
  { i. hexploit ORD0; eauto.
    eapply sim_local_nonsynch_loc; eauto.
  }
  i. des. subst. esplits; eauto.
  - apply TViewFacts.write_released_mon; ss;
      try apply LOCAL1; try apply WF1_TGT.
  - etrans; eauto.
Qed.

Lemma sim_local_write_bot
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
      (STEP_TGT: Local.write_step lc1_tgt sc1_tgt mem1_tgt loc from to val releasedm_tgt released_tgt ord_tgt lc2_tgt sc2_tgt mem2_tgt kind)
      (LOCAL1: sim_local SimPromises.bot lc1_src lc1_tgt)
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  exists released_src lc2_src sc2_src mem2_src,
    <<STEP_SRC: Local.write_step lc1_src sc1_src mem1_src loc from to val releasedm_src
                                 released_src
                                 ord_src lc2_src sc2_src mem2_src
                                 kind>> /\
    <<REL2: View.opt_le released_src released_tgt>> /\
    <<LOCAL2: sim_local SimPromises.bot lc2_src lc2_tgt>> /\
    <<SC2: TimeMap.le sc2_src sc2_tgt>> /\
    <<MEM2: sim_memory mem2_src mem2_tgt>>.
Proof.
  hexploit sim_local_write; eauto.
  { rewrite SimPromises.bot_spec. intuition. }
  i. des. esplits; eauto.
  - rewrite SimPromises.kind_transf_bot in *. eauto.
  - rewrite SimPromises.unset_bot in *; ss.
Qed.

Lemma sim_local_update
      pview
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      lc2_tgt
      lc3_tgt sc3_tgt mem3_tgt
      loc ts1 val1 released1_tgt ord1_src ord1_tgt
      from2 to2 val2 released2_tgt ord2_src ord2_tgt kind
      (STEP1_TGT: Local.read_step lc1_tgt mem1_tgt loc ts1 val1 released1_tgt ord1_tgt lc2_tgt)
      (STEP2_TGT: Local.write_step lc2_tgt sc1_tgt mem1_tgt loc from2 to2 val2 released1_tgt released2_tgt ord2_tgt lc3_tgt sc3_tgt mem3_tgt kind)
      (LOCAL1: sim_local pview lc1_src lc1_tgt)
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
      (PVIEW: SimPromises.mem loc to2 pview = false \/
              Ordering.le ord2_tgt Ordering.plain \/
              Ordering.le Ordering.strong_relaxed ord2_tgt):
  exists released1_src released2_src lc2_src lc3_src sc3_src mem3_src,
    <<REL1: View.opt_le released1_src released1_tgt>> /\
    <<REL2: View.opt_le released2_src released2_tgt>> /\
    <<STEP1_SRC: Local.read_step lc1_src mem1_src loc ts1 val1 released1_src ord1_src lc2_src>> /\
    <<STEP2_SRC: Local.write_step lc2_src sc1_src mem1_src loc from2 to2 val2 released1_src released2_src ord2_src lc3_src sc3_src mem3_src
                                  (SimPromises.kind_transf loc to2 pview kind)>> /\
    <<LOCAL3: sim_local (SimPromises.unset loc to2 pview) lc3_src lc3_tgt>> /\
    <<SC3: TimeMap.le sc3_src sc3_tgt>> /\
    <<MEM3: sim_memory mem3_src mem3_tgt>>.
Proof.
  guardH PVIEW.
  exploit Local.read_step_future; eauto. i. des.
  exploit sim_local_read; eauto. i. des.
  exploit Local.read_step_future; eauto. i. des.
  hexploit sim_local_write; eauto. i. des.
  esplits; eauto.
Qed.

Lemma sim_local_update_bot
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      lc2_tgt
      lc3_tgt sc3_tgt mem3_tgt
      loc ts1 val1 released1_tgt ord1_src ord1_tgt
      from2 to2 val2 released2_tgt ord2_src ord2_tgt kind
      (STEP1_TGT: Local.read_step lc1_tgt mem1_tgt loc ts1 val1 released1_tgt ord1_tgt lc2_tgt)
      (STEP2_TGT: Local.write_step lc2_tgt sc1_tgt mem1_tgt loc from2 to2 val2 released1_tgt released2_tgt ord2_tgt lc3_tgt sc3_tgt mem3_tgt kind)
      (LOCAL1: sim_local SimPromises.bot lc1_src lc1_tgt)
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt)
      (ORD1: Ordering.le ord1_src ord1_tgt)
      (ORD2: Ordering.le ord2_src ord2_tgt):
  exists released1_src released2_src lc2_src lc3_src sc3_src mem3_src,
    <<REL1: View.opt_le released1_src released1_tgt>> /\
    <<REL2: View.opt_le released2_src released2_tgt>> /\
    <<STEP1_SRC: Local.read_step lc1_src mem1_src loc ts1 val1 released1_src ord1_src lc2_src>> /\
    <<STEP2_SRC: Local.write_step lc2_src sc1_src mem1_src loc from2 to2 val2 released1_src released2_src ord2_src lc3_src sc3_src mem3_src kind>> /\
    <<LOCAL3: sim_local SimPromises.bot lc3_src lc3_tgt>> /\
    <<SC3: TimeMap.le sc3_src sc3_tgt>> /\
    <<MEM3: sim_memory mem3_src mem3_tgt>>.
Proof.
  exploit Local.read_step_future; eauto. i. des.
  exploit sim_local_read; eauto. i. des.
  exploit Local.read_step_future; eauto. i. des.
  hexploit sim_local_write_bot; eauto. i. des.
  esplits; eauto.
Qed.

Lemma sim_local_fence
      pview
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      lc2_tgt sc2_tgt
      ordr_src ordw_src
      ordr_tgt ordw_tgt
      (STEP_TGT: Local.fence_step lc1_tgt sc1_tgt ordr_tgt ordw_tgt lc2_tgt sc2_tgt)
      (LOCAL1: sim_local pview lc1_src lc1_tgt)
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (ORDR: Ordering.le ordr_src ordr_tgt)
      (ORDW: Ordering.le ordw_src ordw_tgt):
  exists lc2_src sc2_src,
    <<STEP_SRC: Local.fence_step lc1_src sc1_src ordr_src ordw_src lc2_src sc2_src>> /\
    <<LOCAL2: sim_local pview lc2_src lc2_tgt>> /\
    <<SC2: TimeMap.le sc2_src sc2_tgt>>.
Proof.
  inv STEP_TGT. esplits; eauto.
  - econs; eauto. i. eapply sim_local_nonsynch; eauto.
  - econs; try apply LOCAL1. s.
    apply TViewFacts.write_fence_tview_mon; auto; try refl.
    apply TViewFacts.read_fence_tview_mon; auto; try refl.
    + apply LOCAL1.
    + apply WF1_TGT.
    + eapply TViewFacts.read_fence_future; apply WF1_SRC.
  - apply TViewFacts.write_fence_sc_mon; auto; try refl.
    apply TViewFacts.read_fence_tview_mon; auto; try refl.
    + apply LOCAL1.
    + apply WF1_TGT.
Qed.

Lemma sim_local_promise_consistent
      pview
      lc_src lc_tgt
      (LOCAL: sim_local pview lc_src lc_tgt)
      (CONS_TGT: Local.promise_consistent lc_tgt):
  <<CONS_SRC: Local.promise_consistent lc_src>>.
Proof.
  inv LOCAL. inv PROMISES. ii.
  destruct (Memory.get loc ts (Local.promises lc_tgt)) as [[]|] eqn:GETP.
  - exploit LE; eauto. i. rewrite PROMISE in x. inv x.
    destruct t0; ss.
    exploit CONS_TGT; eauto. i.
    eapply TimeFacts.le_lt_lt; eauto.
    inv TVIEW. inv CUR. eauto.
  - exploit COMPLETE; eauto. i.
    rewrite MemoryDomain.bot_spec in x. ss.
Qed.

Lemma sim_local_failure
      pview
      lc1_src lc1_tgt
      (STEP_TGT: Local.failure_step lc1_tgt)
      (LOCAL1: sim_local pview lc1_src lc1_tgt):
  <<STEP_SRC: Local.failure_step lc1_src>>.
Proof.
  inv STEP_TGT.
  hexploit sim_local_promise_consistent; eauto.
Qed.

Lemma sim_local_program_step
      lang
      th1_src
      th1_tgt th2_tgt e_tgt
      (STEP_TGT: @Thread.program_step lang e_tgt th1_tgt th2_tgt)
      (WF1_SRC: Local.wf (Thread.local th1_src) (Thread.memory th1_src))
      (WF1_TGT: Local.wf (Thread.local th1_tgt) (Thread.memory th1_tgt))
      (SC1_SRC: Memory.closed_timemap (Thread.sc th1_src) (Thread.memory th1_src))
      (SC1_TGT: Memory.closed_timemap (Thread.sc th1_tgt) (Thread.memory th1_tgt))
      (MEM1_SRC: Memory.closed (Thread.memory th1_src))
      (MEM1_TGT: Memory.closed (Thread.memory th1_tgt))
      (STATE: (Thread.state th1_src) = (Thread.state th1_tgt))
      (LOCAL: sim_local SimPromises.bot (Thread.local th1_src) (Thread.local th1_tgt))
      (SC: TimeMap.le (Thread.sc th1_src) (Thread.sc th1_tgt))
      (MEM: sim_memory (Thread.memory th1_src) (Thread.memory th1_tgt)):
  exists e_src th2_src,
    <<STEP_SRC: @Thread.program_step lang e_src th1_src th2_src>> /\
    <<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>> /\
    <<STATE: (Thread.state th2_src) = (Thread.state th2_tgt)>> /\
    <<LOCAL: sim_local SimPromises.bot (Thread.local th2_src) (Thread.local th2_tgt)>> /\
    <<SC: TimeMap.le (Thread.sc th2_src) (Thread.sc th2_tgt)>> /\
    <<MEM: sim_memory (Thread.memory th2_src) (Thread.memory th2_tgt)>>.
Proof.
  destruct th1_src. ss. subst. inv STEP_TGT; ss.
  inv LOCAL0; ss.
  - esplits; (try by econs; [|econs 1]; eauto); ss.
  - exploit sim_local_read; eauto; try refl. i. des.
    esplits; (try by econs; [|econs 2]; eauto); ss.
  - hexploit sim_local_write_bot; eauto; try refl; try by viewtac. i. des.
    esplits; (try by econs; [|econs 3]; eauto); ss.
  - exploit Local.read_step_future; eauto. i. des.
    exploit sim_local_read; eauto; try refl. i. des.
    exploit Local.read_step_future; eauto. i. des.
    hexploit sim_local_write_bot; eauto; try refl; try by viewtac. i. des.
    esplits; (try by econs; [|econs 4]; eauto); ss.
  - exploit sim_local_fence; eauto; try refl. i. des.
    esplits; (try by econs; [|econs 5]; eauto); ss.
  - exploit sim_local_fence; eauto; try refl. i. des.
    esplits; (try by econs; [|econs 6]; eauto); ss.
  - exploit sim_local_failure; eauto. i. des.
    esplits; (try by econs; [|econs 7]; eauto); ss.
Qed.

Lemma sim_local_lower_src
      pview1
      lc1_src sc1_src mem1_src
      lc1_tgt mem1_tgt
      lc2_src mem2_src
      loc from to val released
      (LOCAL1: sim_local pview1 lc1_src lc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
      (MEM1_SRC: Memory.closed mem1_src)
      (STEP_SRC: Local.promise_step lc1_src mem1_src loc from to (Message.full val None) lc2_src mem2_src (Memory.op_kind_lower (Message.full val released))):
  <<LOCAL2: exists pview2, sim_local pview2 lc2_src lc1_tgt>> /\
  <<MEM2: sim_memory mem2_src mem1_tgt>> /\
  <<WF2_SRC: Local.wf lc2_src mem2_src>>.
Proof.
  splits.
  - inv STEP_SRC. inv PROMISE.
    exists (match Memory.get loc to (Local.promises lc1_tgt) with
       | Some _ => SimPromises.set loc to pview1
       | None => pview1
       end).
    inv LOCAL1. econs; ss. inv PROMISES0. econs; ss.
    + ii.
      exploit LE; eauto. i.
      exploit Memory.lower_get0; try exact PROMISES; eauto. i.
      erewrite Memory.lower_o; eauto.
      unfold SimPromises.none_if, SimPromises.none_if_released.
      destruct (Memory.get loc to (Local.promises lc1_tgt)) eqn:TGT.
      * rewrite SimPromises.set_o. condtac; ss.
        { des. subst. condtac; ss; cycle 1.
          { revert COND0. condtac; ss. des; congr. }
          rewrite GET in x. inv x. destruct msg; ss. inv H1; ss.
        }
        { guardH o. condtac.
          { revert COND0. condtac; ss.
            { des. subst. unguardH o. des; congr. }
            guardH o0. i.
            rewrite x. repeat f_equal. SimPromises.none_if_tac.
          }
          rewrite x. repeat f_equal. SimPromises.none_if_tac.
          revert COND0. condtac; ss.
        }
      * condtac; ss. des. subst. congr.
    + i. revert MEM0. condtac; ss; cycle 1.
      { eapply PVIEW. }
      rewrite SimPromises.set_o. condtac; ss; cycle 1.
      { eapply PVIEW. }
      i. des. subst. destruct p. destruct t0; eauto.
      exploit LE; eauto. ss. i.
      exploit Memory.lower_get0; try exact PROMISES; eauto. i. des. congr.
    + i. revert SRC. erewrite Memory.lower_o; eauto. condtac; ss.
      * i. des. inv SRC. eapply COMPLETE; eauto.
        hexploit Memory.lower_get0; try exact PROMISES; eauto. i. des. eauto.
      * i. eapply COMPLETE; eauto.
  - etrans; [|eauto]. inv STEP_SRC. inv PROMISE. eapply lower_sim_memory; eauto. econs.
  - eapply Local.promise_step_future; eauto.
Qed.

Lemma sim_local_nonsynch_src
      pview
      lang st sc
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      (LOCAL1: sim_local pview lc1_src lc1_tgt)
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (LOCAL1_SRC: Local.wf lc1_src mem1_src)
      (LOCAL2_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  exists pview2 lc2_src mem2_src,
    <<STEP_SRC: rtc (@Thread.tau_step lang)
                    (Thread.mk lang st lc1_src sc mem1_src)
                    (Thread.mk lang st lc2_src sc mem2_src)>> /\
    <<NONSYNCH2: Memory.nonsynch (Local.promises lc2_src)>> /\
    <<LOCAL2: sim_local pview2 lc2_src lc1_tgt>> /\
    <<MEM2: sim_memory mem2_src mem1_tgt>>.
Proof.
  inversion LOCAL1_SRC.
  destruct FINITE. rename x into dom.
  assert (FINITE' : forall (loc : Loc.t) (from to : Time.t) (msg : Message.t),
             Memory.get loc to (Local.promises lc1_src) = Some (from, msg) ->
             (match msg with
              | Message.full _ (Some _) => True
              | _ => False
              end) ->
             In (loc, to) dom).
  { ii. eapply H. eauto. }
  clear H. move dom after lc1_src. revert_until dom. revert pview.
  induction dom.
  { esplits; eauto. ii. destruct msg; ss. destruct released; ss.
    exfalso. eapply FINITE'; eauto. ss.
  }
  destruct a as [loc to]. i.
  destruct (Memory.get loc to (Local.promises lc1_src)) as [[? []]|] eqn:X; cycle 1.
  { eapply IHdom; eauto. i. exploit FINITE'; eauto. i. inv x; ss.
    inv H1. rewrite X in H. inv H. inv H0. }
  { eapply IHdom; eauto. i. exploit FINITE'; eauto. i. inv x; ss.
    inv H1. congr.
  }
  destruct released; cycle 1.
  { eapply IHdom; eauto. i. exploit FINITE'; eauto. i. inv x; ss.
    inv H1. rewrite H in X. inv X. ss.
  }
  exploit MemoryFacts.promise_exists_None; eauto.
  { eapply MemoryFacts.released_time_lt; [by apply MEM1_SRC|]. apply LOCAL1_SRC. eauto. }
  i. des.
  exploit Memory.promise_future; try exact x0; try apply LOCAL1_SRC; eauto. i. des.
  exploit sim_local_lower_src; eauto. i. des.
  exploit IHdom; eauto.
  { eapply Memory.future_closed_timemap; eauto. }
  { eapply TView.future_closed; eauto. }
  { s. i. inv x0. revert H.
    erewrite Memory.lower_o; eauto. condtac; ss.
    - i. des. inv H. ss.
    - guardH o. i. exploit FINITE'; eauto. i. des; ss. inv x.
      unguardH o. des; congr.
  }
  i. des. esplits; try exact NONSYNCH2; eauto.
  econs 2; eauto. econs.
  - econs. econs 1. econs; eauto.
  - ss.
Qed.
