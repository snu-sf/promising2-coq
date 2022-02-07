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

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import FulfillStep.
Require Import MemoryReorder.

Require Import PromiseConsistent.
Require Import ReorderPromises.

Set Implicit Arguments.


Definition pf_consistent lang (e:Thread.t lang): Prop :=
  forall mem1 sc1
         (CAP: Memory.cap (Local.promises (Thread.local e)) (Thread.memory e) mem1)
         (SC_MAX: Memory.max_full_timemap mem1 sc1),
  exists e2,
    (<<STEPS: rtc (tau (Thread.step true)) (Thread.mk _ (Thread.state e) (Thread.local e) sc1 mem1) e2>>) /\
    ((exists e3,
         (<< FAILURE: Thread.step true ThreadEvent.failure e2 e3 >>)) \/
     (<<PROMISES: (Local.promises (Thread.local e2)) = Memory.bot>>)).

Lemma rtc_union_step_nonpf_failure
      lang e1 e2 e2'
      (STEP: rtc (union (@Thread.step lang false)) e1 e2)
      (FAILURE: Thread.step true ThreadEvent.failure e2 e2')
  :
    exists e1',
      Thread.step true ThreadEvent.failure e1 e1'.
Proof.
  ginduction STEP; eauto.
  i. exploit IHSTEP; eauto. i. des.
  exists (Thread.mk _ (Thread.state e1') (Thread.local x) (Thread.sc x) (Thread.memory x)).
  inv x0; inv STEP0. inv LOCAL. inv LOCAL0.
  inv H. inv USTEP. inv STEP0.
  econs 2; eauto. econs; eauto. econs; eauto. econs; eauto.
  ss. eapply promise_step_promise_consistent; eauto.
Qed.

Lemma consistent_pf_consistent lang (e:Thread.t lang)
      (WF: Local.wf (Thread.local e) (Thread.memory e))
      (MEM: Memory.closed (Thread.memory e))
      (CONSISTENT: Thread.consistent e)
  :
    pf_consistent e.
Proof.
  ii. exploit CONSISTENT; eauto. i. des.
  - inv FAILURE. des.
    hexploit tau_steps_pf_tau_steps; eauto; ss.
    { inv FAILURE; inv STEP. inv LOCAL. inv LOCAL0.
      hexploit rtc_tau_step_promise_consistent; eauto; ss.
      { eapply Local.cap_wf; eauto. }
      { eapply Memory.max_full_timemap_closed; eauto. }
      { eapply Memory.cap_closed; eauto. }
    }
    { eapply Local.cap_wf; eauto. }
    { eapply Memory.max_full_timemap_closed; eauto. }
    { eapply Memory.cap_closed; eauto. }
    i. des.
    exploit rtc_union_step_nonpf_failure.
    { eapply rtc_implies; [|eauto]. apply tau_union. }
    { eauto. }
    i. des.
    esplits; eauto.
  - exploit tau_steps_pf_tau_steps; eauto; ss.
    { ii. rewrite PROMISES, Memory.bot_get in *.  congr. }
    { eapply Local.cap_wf; eauto. }
    { eapply Memory.max_full_timemap_closed; eauto. }
    { eapply Memory.cap_closed; eauto. }
    i. des.
    exploit rtc_union_step_nonpf_bot; [|eauto|].
    { eapply rtc_implies; [|eauto]. apply tau_union. }
    i. subst. esplits; eauto.
Qed.
