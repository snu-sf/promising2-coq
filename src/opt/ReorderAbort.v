Require Import Bool.
Require Import List.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
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
Require Import Progress.

Require Import LowerPromises.

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import Compatibility.
Require Import SimThread.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Inductive reorder_abort: forall (i2:Instr.t), Prop :=
| reorder_abort_load
    r2 l2 o2
    (ORD2: Ordering.le o2 Ordering.relaxed):
    reorder_abort (Instr.load r2 l2 o2)
| reorder_abort_store
    l2 v2 o2
    (ORD: Ordering.le o2 Ordering.acqrel):
    reorder_abort (Instr.store l2 v2 o2)
| reorder_abort_fence
    or2 ow2
    (ORDR2: Ordering.le or2 Ordering.relaxed)
    (ORDW2: Ordering.le ow2 Ordering.acqrel):
    reorder_abort (Instr.fence or2 ow2)
.

Inductive sim_abort: forall (st_src:(Language.state lang)) (lc_src:Local.t) (sc1_src:TimeMap.t) (mem1_src:Memory.t)
                       (st_tgt:(Language.state lang)) (lc_tgt:Local.t) (sc1_tgt:TimeMap.t) (mem1_tgt:Memory.t), Prop :=
| sim_abort_intro
    rs i2
    lc1_src sc1_src mem1_src
    lc1_tgt sc1_tgt mem1_tgt
    (REORDER: reorder_abort i2)
    (FAILURE: Local.failure_step lc1_src)
    (LOCAL: sim_local SimPromises.bot lc1_src lc1_tgt)
    (SC: TimeMap.le sc1_src sc1_tgt)
    (MEMORY: sim_memory mem1_src mem1_tgt)
    (WF_SRC: Local.wf lc1_src mem1_src)
    (WF_TGT: Local.wf lc1_tgt mem1_tgt)
    (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
    (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
    (MEM_SRC: Memory.closed mem1_src)
    (MEM_TGT: Memory.closed mem1_tgt):
    sim_abort
      (State.mk rs [Stmt.instr i2; Stmt.instr Instr.abort]) lc1_src sc1_src mem1_src
      (State.mk rs [Stmt.instr i2]) lc1_tgt sc1_tgt mem1_tgt
.

Lemma sim_abort_mon
      st_src lc_src sc1_src mem1_src
      st_tgt lc_tgt sc1_tgt mem1_tgt
      sc2_src mem2_src
      sc2_tgt mem2_tgt
      (SIM1: sim_abort st_src lc_src sc1_src mem1_src
                       st_tgt lc_tgt sc1_tgt mem1_tgt)
      (SC_FUTURE_SRC: TimeMap.le sc1_src sc2_src)
      (SC_FUTURE_TGT: TimeMap.le sc1_tgt sc2_tgt)
      (MEM_FUTURE_SRC: Memory.future_weak mem1_src mem2_src)
      (MEM_FUTURE_TGT: Memory.future_weak mem1_tgt mem2_tgt)
      (SC1: TimeMap.le sc2_src sc2_tgt)
      (MEM1: sim_memory mem2_src mem2_tgt)
      (WF_SRC: Local.wf lc_src mem2_src)
      (WF_TGT: Local.wf lc_tgt mem2_tgt)
      (SC_SRC: Memory.closed_timemap sc2_src mem2_src)
      (SC_TGT: Memory.closed_timemap sc2_tgt mem2_tgt)
      (MEM_SRC: Memory.closed mem2_src)
      (MEM_TGT: Memory.closed mem2_tgt):
  sim_abort st_src lc_src sc2_src mem2_src
            st_tgt lc_tgt sc2_tgt mem2_tgt.
Proof.
  inv SIM1. econs; eauto.
Qed.

Lemma read_step_cur_future
      lc1 mem1 loc val released ord lc2
      (WF1: Local.wf lc1 mem1)
      (ORD: Ordering.le ord Ordering.relaxed)
      (READ: Local.read_step lc1 mem1 loc ((TView.cur (Local.tview lc1)).(View.rlx) loc) val released ord lc2):
  <<PROMISES: (Local.promises lc1) = (Local.promises lc2)>> /\
  <<TVIEW: (TView.cur (Local.tview lc1)).(View.rlx) = (TView.cur (Local.tview lc2)).(View.rlx)>>.
Proof.
  destruct lc1 as [tview1 promises1]. inv READ. ss.
  esplits; eauto. condtac; ss; try by destruct ord.
  apply TimeMap.antisym.
  - etrans; [|apply TimeMap.join_l]. apply TimeMap.join_l.
  - apply TimeMap.join_spec; auto using TimeMap.bot_spec.
    apply TimeMap.join_spec; try refl.
    unfold View.singleton_ur_if. condtac; ss.
    + ii. unfold TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
      condtac; try apply Time.bot_spec.
      subst. refl.
    + ii. unfold TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
      condtac; try apply Time.bot_spec.
      subst. refl.
Qed.

Lemma fence_step_future
      lc1 sc1 ordr ordw lc2 sc2
      (ORDR: Ordering.le ordr Ordering.relaxed)
      (ORDW: Ordering.le ordw Ordering.acqrel)
      (FENCE: Local.fence_step lc1 sc1 ordr ordw lc2 sc2):
  <<PROMISES: (Local.promises lc1) = (Local.promises lc2)>> /\
  <<TVIEW: (TView.cur (Local.tview lc1)) = (TView.cur (Local.tview lc2))>>.
Proof.
  destruct lc1 as [tview1 promises1]. inv FENCE. split; ss.
  condtac; try by destruct ordw.
  condtac; try by destruct ordr.
Qed.

Lemma write_step_consistent
      lc1 sc1 mem1
      loc val ord
      (WF1: Local.wf lc1 mem1)
      (SC1: Memory.closed_timemap sc1 mem1)
      (MEM1: Memory.closed mem1)
      (PROMISES1: Ordering.le Ordering.strong_relaxed ord -> Memory.nonsynch_loc loc (Local.promises lc1))
      (CONS1: Local.promise_consistent lc1):
  exists from to released lc2 sc2 mem2 kind,
    <<STEP: Local.write_step lc1 sc1 mem1 loc from to val None released ord lc2 sc2 mem2 kind>> /\
    <<CONS2: Local.promise_consistent lc2>>.
Proof.
  destruct (classic (exists f t v r, Memory.get loc t (Local.promises lc1) =
                                Some (f, Message.full v r))).
  { des.
    exploit Memory.min_full_ts_exists; eauto. i. des.
    exploit Memory.min_full_ts_spec; eauto. i. des.
    exploit Memory.get_ts; try exact GET. i. des.
    { subst. inv WF1. rewrite BOT in *. ss. }
    clear f t v r H MIN.
    exploit progress_write_step_split; try exact GET; eauto.
    { ss. unfold TimeMap.bot. apply Time.bot_spec. }
    i. des.
    esplits; eauto. ii.
    assert (TS: loc0 = loc -> Time.le ts ts0).
    { i. subst. inv x2. inv WRITE. inv PROMISE0. ss.
      revert PROMISE.
      erewrite Memory.remove_o; eauto. condtac; ss. des; ss.
      erewrite Memory.split_o; eauto. repeat condtac; ss; i.
      - des; ss. subst. refl.
      - des; ss.
        exploit Memory.min_full_ts_spec; eauto. i. des. ss. }
    inv x2. inv WRITE. inv PROMISE0. ss.
    clear RESERVE.
    unfold TimeMap.join, TimeMap.singleton.
    unfold LocFun.add, LocFun.init, LocFun.find.
    condtac; ss.
    - subst. apply TimeFacts.join_spec_lt.
      + eapply TimeFacts.lt_le_lt; try eapply TS; eauto.
      + eapply TimeFacts.lt_le_lt; try eapply TS; eauto.
        apply Time.middle_spec. ss.
    - revert PROMISE.
      erewrite Memory.remove_o; eauto. condtac; ss.
      erewrite Memory.split_o; eauto. repeat condtac; ss; try by des; ss.
      guardH o. guardH o0. guardH o1. i.
      apply TimeFacts.join_spec_lt; eauto.
      destruct (TimeFacts.le_lt_dec ts0 Time.bot); ss.
      inv l; inv H.
      inv WF1. rewrite BOT in *. ss.
  }
  { exploit progress_write_step; eauto.
    { apply Time.incr_spec. }
    i. des.
    esplits; eauto. ii.
    inv x0. inv WRITE. inv PROMISE0. ss.
    revert PROMISE.
    erewrite Memory.remove_o; eauto. condtac; ss.
    erewrite Memory.add_o; eauto. condtac; ss. i.
    destruct (Loc.eq_dec loc0 loc).
    - subst. exfalso. apply H; eauto.
    - unfold TimeMap.join, TimeMap.singleton.
      unfold LocFun.add, LocFun.init, LocFun.find.
      condtac; ss.
      apply TimeFacts.join_spec_lt; eauto.
      destruct (TimeFacts.le_lt_dec ts Time.bot); ss.
      inv l; inv H0.
      inv WF1. rewrite BOT in *. ss.
  }
Qed.

Lemma sim_abort_steps_failure
      st1_src lc1_src sc1_src mem1_src
      st1_tgt lc1_tgt sc1_tgt mem1_tgt
      (SIM: sim_abort st1_src lc1_src sc1_src mem1_src
                      st1_tgt lc1_tgt sc1_tgt mem1_tgt):
  Thread.steps_failure (Thread.mk lang st1_src lc1_src sc1_src mem1_src).
Proof.
  inv SIM. inv FAILURE. unfold Thread.steps_failure.
  inv REORDER.
  - (* load *)
    exploit progress_read_step_cur; try exact WF_SRC; eauto. i. des.
    exploit read_step_cur_future; try exact READ; eauto. i. des.
    esplits.
    + econs 2; try refl. econs.
      * econs. econs 2. econs; [|econs 2]; eauto. econs. econs.
      * ss.
    + econs 2. econs.
      * econs. econs.
      * econs. econs. ii.
        rewrite <- TVIEW. rewrite <- PROMISES in *. eauto.
  - (* store *)
    exploit (@LowerPromises.steps_promises_rel
               lang (Thread.mk lang (State.mk rs [Stmt.instr (Instr.store l2 v2 o2); Stmt.instr Instr.abort])
                               lc1_src sc1_src mem1_src)); s; eauto.
    i. des. destruct e2, state. ss.
    exploit LowerPromises.rtc_opt_promise_step_future; eauto. s. i. des. inv STATE.
    hexploit LowerPromises.promises_rel_promise_consistent; eauto. i.
    hexploit LowerPromises.promises_rel_nonsynch; eauto. i.
    exploit Thread.rtc_tau_step_future; try exact STEPS0; eauto. s. i. des.
    exploit write_step_consistent; try exact WF2; eauto. i. des.
    esplits.
    + eapply rtc_n1; eauto. econs.
      * econs. econs 2. econs; [|econs 3; eauto]. econs. econs.
      * ss.
    + econs 2. econs; [econs; econs|]. econs. econs. ss.
  - (* fence *)
    exploit (@LowerPromises.steps_promises_rel
               lang (Thread.mk lang (State.mk rs [Stmt.instr (Instr.fence or2 ow2); Stmt.instr Instr.abort])
                               lc1_src sc1_src mem1_src)); s; eauto.
    i. des. destruct e2, state. ss.
    exploit LowerPromises.rtc_opt_promise_step_future; eauto. s. i. des. inv STATE.
    hexploit LowerPromises.promises_rel_promise_consistent; eauto. i.
    hexploit LowerPromises.promises_rel_nonsynch; eauto. i.
    exploit progress_fence_step; eauto. i. des.
    esplits.
    + eapply rtc_n1; eauto. econs.
      * econs. econs 2. econs; [|econs 5; eauto]. econs. econs.
      * ss.
    + econs 2. econs; [econs; econs|]. econs. econs.
      exploit fence_step_future; eauto. i. des.
      ii. rewrite <- PROMISES in *. rewrite <- TVIEW0. eauto.
Qed.
