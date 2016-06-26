Require Import Basics.
Require Import Bool.
Require Import List.

Require Import sflib.
Require Import paco.
Require Import respectful9.

Require Import Axioms.
Require Import Basic.
Require Import Event.
Require Import Time.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import Commit.
Require Import Thread.
Require Import Simulation.
Require Import MemInv.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Inductive fulfill_step (lc1:Local.t) (sc1:TimeMap.t) (loc:Loc.t) (from to:Time.t) (val:Const.t) (releasedm released:Capability.t) (ord:Ordering.t): forall (lc2:Local.t) (sc2:TimeMap.t), Prop :=
| step_fulfill
    promises2
    (RELEASED: released = Capability.join releasedm ((Commit.write_commit lc1.(Local.commit) sc1 loc to ord).(Commit.rel) loc))
    (WRITABLE: Commit.writable lc1.(Local.commit) sc1 loc to ord)
    (REMOVE: Memory.remove lc1.(Local.promises) loc from to val released promises2)
    (TIME: Time.lt from to):
    fulfill_step lc1 sc1 loc from to val releasedm released ord
                 (Local.mk (Commit.write_commit lc1.(Local.commit) sc1 loc to ord) promises2)
                 (Commit.write_sc sc1 loc to ord)
.

Lemma fulfill_step_future lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2
      (STEP: fulfill_step lc1 sc1 loc from to val releasedm released ord lc2 sc2)
      (REL: Memory.closed_capability releasedm mem1)
      (WF1: Local.wf lc1 mem1)
      (SC1: Memory.closed_timemap sc1 mem1)
      (CLOSED1: Memory.closed mem1):
  <<WF2: Local.wf lc2 mem1>> /\
  <<SC2: Memory.closed_timemap sc2 mem1>> /\
  <<SC_FUTURE: TimeMap.le sc1 sc2>>.
Proof.
  inv STEP.
  hexploit Memory.remove_future; try apply REMOVE; try apply WF1; eauto. i. des.
  exploit Memory.remove_get0; eauto. i.
  inversion WF1. exploit PROMISES; eauto. i.
  exploit CommitFacts.write_future; try apply x; try apply SC1; try apply WF1; eauto. i. des.
  esplits; eauto.
  - econs; eauto.
  - apply CommitFacts.write_sc_incr.
Qed.

Lemma fulfill_write
      lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2
      (FULFILL: fulfill_step lc1 sc1 loc from to val releasedm released ord lc2 sc2)
      (REL_WF: Capability.wf releasedm)
      (REL_CLOSED: Memory.closed_capability releasedm mem1)
      (ORD: Ordering.le ord Ordering.relaxed)
      (WF1: Local.wf lc1 mem1)
      (SC1: Memory.closed_timemap sc1 mem1)
      (MEM1: Memory.closed mem1):
  Local.write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem1 Memory.promise_kind_lower.
Proof.
  inv FULFILL. econs; eauto.
  - econs; eauto. apply Memory.promise_exists_same; try apply WF1; auto.
    + repeat (try condtac; committac; try apply WF1).
    + eapply Memory.remove_get0. eauto.
  - i. destruct ord; inv ORD; inv H.
Qed.

Lemma write_promise_fulfill
      lc0 sc0 mem0 loc from to val releasedm released ord lc2 sc2 mem2 kind
      (WRITE: Local.write_step lc0 sc0 mem0 loc from to val releasedm released ord lc2 sc2 mem2 kind)
      (REL_WF: Capability.wf releasedm)
      (REL_CLOSED: Memory.closed_capability releasedm mem0)
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0):
  exists lc1,
    <<STEP1: Local.promise_step lc0 mem0 loc from to val released lc1 mem2 kind>> /\
    <<STEP2: fulfill_step lc1 sc0 loc from to val releasedm released ord lc2 sc2>> /\
    <<ORD: Ordering.le Ordering.acqrel ord ->
           Local.promises lc0 loc = Cell.bot /\
           kind = Memory.promise_kind_add>>.
Proof.
  exploit Local.write_step_future; eauto. i. des.
  inv WRITE. inv WRITE0. esplits; eauto.
  - econs; eauto.
  - refine (step_fulfill _ _ _ _ _); auto.
    eapply promise_time_lt. eauto.
Qed.

Lemma promise_fulfill_write
      lc0 sc0 mem0 loc from to val releasedm released ord lc1 lc2 sc2 mem2 kind
      (PROMISE: Local.promise_step lc0 mem0 loc from to val released lc1 mem2 kind)
      (FULFILL: fulfill_step lc1 sc0 loc from to val releasedm released ord lc2 sc2)
      (REL_WF: Capability.wf releasedm)
      (REL_CLOSED: Memory.closed_capability releasedm mem0)
      (ORD: Ordering.le Ordering.acqrel ord -> lc0.(Local.promises) loc = Cell.bot /\
                                              kind = Memory.promise_kind_add)
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0):
  Local.write_step lc0 sc0 mem0 loc from to val releasedm released ord lc2 sc2 mem2 kind.
Proof.
  inv PROMISE. inv FULFILL.
  refine (Local.step_write _ _ _ _ _); auto. econs; eauto.
Qed.