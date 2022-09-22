Require Import Lia.
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
Require Import Thread.

Set Implicit Arguments.


Lemma promise_step_promise_consistent
      lc1 mem1 loc from to msg lc2 mem2 kind
      (STEP: Local.promise_step lc1 mem1 loc from to msg lc2 mem2 kind)
      (CONS: Local.promise_consistent lc2):
  Local.promise_consistent lc1.
Proof.
  inv STEP. ii.
  destruct (Memory.op_kind_is_cancel kind) eqn:KIND.
  - destruct kind; ss. inv PROMISE.
    destruct (Memory.get loc0 ts promises2) as [[]|] eqn:GET2.
    + dup GET2. revert GET0.
      erewrite Memory.remove_o; eauto. condtac; ss. i.
      rewrite PROMISE0 in *. inv GET0. eauto.
    + revert GET2. erewrite Memory.remove_o; eauto. condtac; ss; i.
      * des. subst. exploit Memory.remove_get0; eauto. i. des. congr.
      * congr.
  - exploit Memory.promise_get1_promise; eauto. i. des.
    inv MSG_LE. exploit CONS; eauto.
Qed.

Lemma read_step_promise_consistent
      lc1 mem1 loc to val released ord lc2
      (STEP: Local.read_step lc1 mem1 loc to val released ord lc2)
      (CONS: Local.promise_consistent lc2):
  Local.promise_consistent lc1.
Proof.
  inv STEP. ii. exploit CONS; eauto. i.
  eapply TimeFacts.le_lt_lt; eauto. ss.
  etrans; [|apply Time.join_l]. etrans; [|apply Time.join_l]. refl.
Qed.

Lemma fulfill_unset_promises
      loc from ts msg
      promises1 promises2
      l t f m
      (FULFILL: Memory.remove promises1 loc from ts msg promises2)
      (TH1: Memory.get l t promises1 = Some (f, m))
      (TH2: Memory.get l t promises2 = None):
  l = loc /\ t = ts /\ f = from /\ Message.le msg m.
Proof.
  revert TH2. erewrite Memory.remove_o; eauto. condtac; ss; [|congr].
  des. subst. exploit Memory.remove_get0; eauto. i. des.
  rewrite GET in TH1. inv TH1.
  esplits; eauto. refl.
Qed.

Lemma write_step_promise_consistent
      lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
      (STEP: Local.write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind)
      (CONS: Local.promise_consistent lc2):
  Local.promise_consistent lc1.
Proof.
  inv STEP. inv WRITE. ii.
  exploit Memory.promise_get1_promise; eauto.
  { inv PROMISE; ss. }
  i. des. inv MSG_LE.
  destruct (Memory.get loc0 ts promises2) as [[]|] eqn:X.
  - dup X. revert X0.
    erewrite Memory.remove_o; eauto. condtac; ss; i.
    rewrite GET in *. inv X0.
    apply CONS in X. eapply TimeFacts.le_lt_lt; eauto.
    s. etrans; [|apply Time.join_l]. refl.
  - exploit fulfill_unset_promises; eauto. i. des. subst.
    apply WRITABLE.
Qed.

Lemma fence_step_promise_consistent
      lc1 sc1 mem1 ordr ordw lc2 sc2
      (STEP: Local.fence_step lc1 sc1 ordr ordw lc2 sc2)
      (WF: Local.wf lc1 mem1)
      (CONS: Local.promise_consistent lc2):
  Local.promise_consistent lc1.
Proof.
  inv STEP. ii.
  exploit CONS; eauto. i.
  eapply TimeFacts.le_lt_lt; eauto.
  cut (TView.le (Local.tview lc1)
                (TView.write_fence_tview (TView.read_fence_tview (Local.tview lc1) ordr) sc1 ordw)).
  { i. inv H. apply CUR. }
  etrans.
  - eapply TViewFacts.write_fence_tview_incr. apply WF.
  - eapply TViewFacts.write_fence_tview_mon; try refl; try apply WF.
    eapply TViewFacts.read_fence_tview_incr. apply WF.
Qed.

Lemma ordering_relaxed_dec
      ord:
  Ordering.le ord Ordering.relaxed \/ Ordering.le Ordering.strong_relaxed ord.
Proof. destruct ord; auto. Qed.

Lemma step_promise_consistent
      lang pf e th1 th2
      (STEP: @Thread.step lang pf e th1 th2)
      (CONS: Local.promise_consistent (Thread.local th2))
      (WF1: Local.wf (Thread.local th1) (Thread.memory th1))
      (SC1: Memory.closed_timemap (Thread.sc th1) (Thread.memory th1))
      (MEM1: Memory.closed (Thread.memory th1)):
  Local.promise_consistent (Thread.local th1).
Proof.
  inv STEP; [inv STEP0|inv STEP0; inv LOCAL]; ss.
  - eapply promise_step_promise_consistent; eauto.
  - eapply read_step_promise_consistent; eauto.
  - eapply write_step_promise_consistent; eauto.
  - eapply read_step_promise_consistent; eauto.
    eapply write_step_promise_consistent; eauto.
  - eapply fence_step_promise_consistent; eauto.
  - eapply fence_step_promise_consistent; eauto.
Qed.

Lemma rtc_all_step_promise_consistent
      lang th1 th2
      (STEP: rtc (@Thread.all_step lang) th1 th2)
      (CONS: Local.promise_consistent (Thread.local th2))
      (WF1: Local.wf (Thread.local th1) (Thread.memory th1))
      (SC1: Memory.closed_timemap (Thread.sc th1) (Thread.memory th1))
      (MEM1: Memory.closed (Thread.memory th1)):
  Local.promise_consistent (Thread.local th1).
Proof.
  revert_until STEP. induction STEP; auto. i.
  inv H. inv USTEP. exploit Thread.step_future; eauto. i. des.
  eapply step_promise_consistent; eauto.
Qed.

Lemma rtc_tau_step_promise_consistent
      lang th1 th2
      (STEP: rtc (@Thread.tau_step lang) th1 th2)
      (CONS: Local.promise_consistent (Thread.local th2))
      (WF1: Local.wf (Thread.local th1) (Thread.memory th1))
      (SC1: Memory.closed_timemap (Thread.sc th1) (Thread.memory th1))
      (MEM1: Memory.closed (Thread.memory th1)):
  Local.promise_consistent (Thread.local th1).
Proof.
  eapply rtc_all_step_promise_consistent; cycle 1; eauto.
  eapply rtc_implies; [|eauto].
  apply tau_union.
Qed.

Lemma consistent_promise_consistent
      lang th
      (CONS: @Thread.consistent lang th)
      (WF: Local.wf (Thread.local th) (Thread.memory th))
      (SC: Memory.closed_timemap (Thread.sc th) (Thread.memory th))
      (MEM: Memory.closed (Thread.memory th)):
  Local.promise_consistent (Thread.local th).
Proof.
  destruct th. ss.
  exploit Memory.cap_exists; eauto. i. des.
  exploit Memory.cap_closed; eauto. i.
  exploit Local.cap_wf; eauto. i.
  exploit Memory.max_full_timemap_exists; try apply x0. i. des.
  hexploit Memory.max_full_timemap_closed; eauto. i.
  exploit CONS; eauto. s. i. des.
  - inv FAILURE. des. inv FAILURE; inv STEP. inv LOCAL. inv LOCAL0.
    hexploit rtc_tau_step_promise_consistent; try exact STEPS; eauto.
  - hexploit rtc_tau_step_promise_consistent; try exact STEPS; eauto.
    ii. rewrite PROMISES, Memory.bot_get in *. congr.
Qed.

Lemma promise_consistent_promise_read
      lc1 mem1 loc to val ord released lc2
      f t v r
      (STEP: Local.read_step lc1 mem1 loc to val released ord lc2)
      (PROMISE: Memory.get loc t (Local.promises lc1) = Some (f, Message.full v r))
      (CONS: Local.promise_consistent lc2):
  Time.lt to t.
Proof.
  inv STEP. exploit CONS; eauto. s. intro x.
  apply TimeFacts.join_lt_des in x. des.
  apply TimeFacts.join_lt_des in AC. des.
  revert BC0. unfold View.singleton_ur_if. condtac; ss.
  - unfold TimeMap.singleton, LocFun.add. condtac; ss.
  - unfold TimeMap.singleton, LocFun.add. condtac; ss.
Qed.

Lemma promise_consistent_promise_write
      lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
      f t v r
      (STEP: Local.write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind)
      (PROMISE: Memory.get loc t (Local.promises lc1) = Some (f, Message.full v r))
      (CONS: Local.promise_consistent lc2):
  Time.le to t.
Proof.
  destruct (Memory.get loc t (Local.promises lc2)) as [[]|] eqn:X.
  - inv STEP. inv WRITE. ss.
    dup X. revert X0.
    erewrite Memory.remove_o; eauto. condtac; ss. i. guardH o.
    exploit Memory.promise_get1_promise; try exact PROMISE; eauto.
    { inv PROMISE0; ss. }
    i. des. inv MSG_LE.
    rewrite X0 in *. inv GET.
    exploit CONS; eauto. intro x. ss.
    apply TimeFacts.join_lt_des in x. des.
    left. revert BC. unfold TimeMap.singleton, LocFun.add. condtac; ss.
  - inv STEP. inv WRITE.
    exploit Memory.promise_get1_promise; eauto.
    { inv PROMISE0; ss. }
    i. des. inv MSG_LE.
    exploit fulfill_unset_promises; eauto. i. des. subst. refl.
Qed.
