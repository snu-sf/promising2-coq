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

Set Implicit Arguments.


Lemma steps_pf_steps_aux
      lang
      n e1 e3
      (STEPS: rtcn (@Thread.all_step lang) n e1 e3)
      (CONS: Local.promise_consistent e3.(Thread.local))
      (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
      (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
      (MEM1: Memory.closed e1.(Thread.memory)):
  exists n' e2,
    <<N: n' <= n>> /\
    <<STEPS1: rtcn (union (Thread.step true)) n' e1 e2>> /\
    <<STEPS2: rtc (union (Thread.step false)) e2 e3>>.
Proof.
  revert_until n. induction n using strong_induction; i.
  inv STEPS.
  { esplits; eauto. }
  inv A12. inv USTEP. exploit Thread.step_future; eauto. i. des.
  destruct pf.
  { exploit Thread.step_future; eauto. i. des.
    exploit IH; eauto. i. des.
    esplits; cycle 1.
    + econs 2; eauto.
    + auto.
    + omega.
  }
  exploit IH; try exact A23; try refl; eauto. i. des.
  assert (CONS2: Local.promise_consistent (Thread.local e2)).
  { exploit rtcn_rtc; try exact A0; eauto. i.
    exploit rtc_implies; [|exact x0|i].
    { apply union_mon. apply Thread.allpf. }
    exploit Thread.rtc_all_step_future; eauto. i. des.
    eapply rtc_all_step_promise_consistent; try exact CONS; eauto.
    eapply rtc_implies; try exact STEPS2; eauto.
    apply union_mon. apply Thread.allpf.
  }
  inv STEPS1.
  { esplits; cycle 1.
    - eauto.
    - econs; eauto.
    - omega.
  }
  inversion A12. exploit Thread.step_future; eauto. i. des.
  exploit reorder_nonpf_pf; eauto.
  { exploit rtcn_rtc; try exact A0; eauto. i.
    eapply rtc_all_step_promise_consistent; try exact CONS; eauto.
    etrans.
    - eapply rtc_implies; [|exact x0]. apply union_mon. apply Thread.allpf.
    - eapply rtc_implies; [|exact STEPS2]. apply union_mon. apply Thread.allpf.
  }
  i. des.
  - subst. esplits; cycle 1; eauto. omega.
  - assert (STEPS: rtcn (@Thread.all_step lang) (S n) e1 e2).
    { econs 2.
      - econs. econs. eauto.
      - eapply rtcn_imply; [|exact A0]. apply union_mon. apply Thread.allpf.
    }
    exploit IH; try exact STEPS; eauto.
    { omega. }
    i. des. esplits; cycle 1; eauto.
    + etrans; eauto.
    + omega.
  - assert (STEPS: rtcn (@Thread.all_step lang) (S n) th1' e2).
    { econs 2.
      - econs. econs 1. eauto.
      - eapply rtcn_imply; [|exact A0]. apply union_mon. apply Thread.allpf.
    }
    exploit Thread.step_future; eauto. i. des.
    exploit IH; try exact STEPS; eauto.
    { omega. }
    i. des. esplits; cycle 1.
    + econs 2; eauto.
    + etrans; eauto.
    + omega.
Qed.

Lemma steps_pf_steps
      lang
      e1 e3
      (STEPS: rtc (@Thread.all_step lang) e1 e3)
      (CONS: Local.promise_consistent e3.(Thread.local))
      (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
      (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
      (MEM1: Memory.closed e1.(Thread.memory)):
  exists e2,
    <<STEPS1: rtc (union (Thread.step true)) e1 e2>> /\
    <<STEPS2: rtc (union (Thread.step false)) e2 e3>>.
Proof.
  apply rtc_rtcn in STEPS. des.
  exploit steps_pf_steps_aux; eauto. i. des.
  exploit rtcn_rtc; eauto.
Qed.

Lemma tau_steps_pf_tau_steps_aux
      lang
      n e1 e3
      (STEPS: rtcn (@Thread.tau_step lang) n e1 e3)
      (CONS: Local.promise_consistent e3.(Thread.local))
      (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
      (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
      (MEM1: Memory.closed e1.(Thread.memory)):
  exists n' e2,
    <<N: n' <= n>> /\
    <<STEPS1: rtcn (tau (Thread.step true)) n' e1 e2>> /\
    <<STEPS2: rtc (tau (Thread.step false)) e2 e3>>.
Proof.
  revert_until n. induction n using strong_induction; i.
  inv STEPS.
  { esplits; eauto. }
  inv A12. inv TSTEP. exploit Thread.step_future; eauto. i. des.
  destruct pf.
  { exploit Thread.step_future; eauto. i. des.
    exploit IH; eauto. i. des.
    esplits; cycle 1.
    + econs 2; eauto.
    + auto.
    + omega.
  }
  exploit IH; try exact A23; try refl; eauto. i. des.
  assert (CONS2: Local.promise_consistent (Thread.local e2)).
  { exploit rtcn_rtc; try exact A0; eauto. i.
    exploit rtc_implies; [|exact x0|i].
    { apply tau_mon. apply Thread.allpf. }
    exploit Thread.rtc_tau_step_future; eauto. i. des.
    eapply rtc_all_step_promise_consistent; try exact CONS; eauto.
    eapply rtc_implies; try exact STEPS2; eauto.
    i. apply tau_union. eapply tau_mon; [|eauto]. apply Thread.allpf.
  }
  inv STEPS1.
  { esplits; cycle 1.
    - eauto.
    - econs; eauto.
    - omega.
  }
  inversion A12. exploit Thread.step_future; eauto. i. des.
  exploit reorder_nonpf_pf; eauto.
  { exploit rtcn_rtc; try exact A0; eauto. i.
    eapply rtc_all_step_promise_consistent; try exact CONS; eauto.
    etrans.
    - eapply rtc_implies; [|exact x0]. i. apply tau_union. eapply tau_mon; [|eauto]. apply Thread.allpf.
    - eapply rtc_implies; [|exact STEPS2]. i. apply tau_union. eapply tau_mon; [|eauto]. apply Thread.allpf.
  }
  i. des.
  - subst. esplits; cycle 1; eauto. omega.
  - assert (STEPS: rtcn (@Thread.tau_step lang) (S n) e1 e2).
    { econs 2.
      - econs. econs; eauto. unguardH EVENT1. by destruct e2', e0; des.
      - eapply rtcn_imply; [|exact A0]. apply tau_mon. apply Thread.allpf.
    }
    exploit IH; try exact STEPS; eauto.
    { omega. }
    i. des. esplits; cycle 1; eauto.
    + etrans; eauto.
    + omega.
  - assert (STEPS: rtcn (@Thread.tau_step lang) (S n) th1' e2).
    { econs 2.
      - econs.
        + econs. econs 1. eauto.
        + inv STEP2. ss.
      - eapply rtcn_imply; [|exact A0]. apply tau_mon. apply Thread.allpf.
    }
    exploit Thread.step_future; eauto. i. des.
    exploit IH; try exact STEPS; eauto.
    { omega. }
    i. des. esplits; cycle 1.
    + econs 2; eauto. econs; eauto. unguardH EVENT1. by destruct e2', e0; des.
    + etrans; eauto.
    + omega.
Qed.

Lemma tau_steps_pf_tau_steps
      lang
      e1 e3
      (STEPS: rtc (@Thread.tau_step lang) e1 e3)
      (CONS: Local.promise_consistent e3.(Thread.local))
      (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
      (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
      (MEM1: Memory.closed e1.(Thread.memory)):
  exists e2,
    <<STEPS1: rtc (tau (Thread.step true)) e1 e2>> /\
    <<STEPS2: rtc (tau (Thread.step false)) e2 e3>>.
Proof.
  apply rtc_rtcn in STEPS. des.
  exploit tau_steps_pf_tau_steps_aux; eauto. i. des.
  exploit rtcn_rtc; eauto.
Qed.

Lemma union_step_nonpf_bot
      lang e1 e2
      (STEP: union (@Thread.step lang false) e1 e2)
      (PROMISE: e2.(Thread.local).(Local.promises) = Memory.bot):
  False.
Proof.
  inv STEP. inv USTEP. inv STEP. inv LOCAL. ss. subst. inv PROMISE0; ss.
  - exploit (@Memory.add_o Memory.bot lc1.(Local.promises) loc from to msg loc to)
    ; try exact PROMISES; eauto. condtac; ss; [|des; congr].
    rewrite Memory.bot_get. congr.
  - exploit (@Memory.split_o Memory.bot lc1.(Local.promises) loc from to ts3 msg msg3 loc to)
    ; try exact PROMISES; eauto. condtac; ss; [|des; congr].
    rewrite Memory.bot_get. congr.
  - exploit (@Memory.lower_o Memory.bot lc1.(Local.promises) loc from to msg0 msg loc to)
    ; try exact PROMISES; eauto. condtac; ss; [|des; congr].
    rewrite Memory.bot_get. congr.
Qed.

Lemma rtc_union_step_nonpf_bot
      lang e1 e2
      (STEP: rtc (union (@Thread.step lang false)) e1 e2)
      (PROMISE: e2.(Thread.local).(Local.promises) = Memory.bot):
  e1 = e2.
Proof.
  exploit rtc_tail; eauto. i. des; ss.
  exfalso. eapply union_step_nonpf_bot; eauto.
Qed.
