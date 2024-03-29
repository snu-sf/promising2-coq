Require Import Lia.
Require Import RelationClasses.

From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.

Set Implicit Arguments.


Module MemoryFacts.
  Lemma promise_time_lt
        promises1 mem1 loc from to msg promises2 mem2 kind
        (PROMISE: Memory.promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (KIND: Memory.op_kind_is_cancel kind = false):
    Time.lt from to.
  Proof.
    inv PROMISE; ss.
    - inv MEM. inv ADD. auto.
    - inv MEM. inv SPLIT. auto.
    - inv MEM. inv LOWER. auto.
  Qed.

  Lemma write_time_lt
        promises1 mem1 loc from to val released promises2 mem2 kind
        (WRITE: Memory.write promises1 mem1 loc from to val released promises2 mem2 kind):
    Time.lt from to.
  Proof.
    inv WRITE. eapply promise_time_lt; eauto.
    inv PROMISE; ss.
  Qed.

  Lemma promise_get1_diff
        promises1 mem1 loc from to msg promises2 mem2 kind
        l t f m
        (PROMISE: Memory.promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (GET: Memory.get l t mem1 = Some (f, m))
        (DIFF: (loc, to) <> (l, t)):
    exists f', Memory.get l t mem2 = Some (f', m).
  Proof.
    inv PROMISE.
    - erewrite Memory.add_o; eauto. condtac; ss.
      + des. subst. congr.
      + esplits; eauto.
    - erewrite Memory.split_o; eauto. repeat condtac; ss.
      + des. subst. congr.
      + guardH o. des. subst.
        exploit Memory.split_get0; try exact MEM. i. des.
        rewrite GET in *. inv GET1. esplits; eauto.
      + esplits; eauto.
    - erewrite Memory.lower_o; eauto. condtac; ss.
      + des. subst. congr.
      + esplits; eauto.
    - erewrite Memory.remove_o; eauto. condtac; ss.
      + des. subst. congr.
      + esplits; eauto.
  Qed.

  Lemma promise_get_inv_diff
        promises1 mem1 loc from to msg promises2 mem2 kind
        l t f m
        (PROMISE: Memory.promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (GET: Memory.get l t mem2 = Some (f, m))
        (DIFF: (loc, to) <> (l, t)):
    exists f', Memory.get l t mem1 = Some (f', m).
  Proof.
    revert GET. inv PROMISE.
    - erewrite Memory.add_o; eauto. condtac; ss.
      + des. subst. congr.
      + i. inv GET. esplits; eauto.
    - erewrite Memory.split_o; eauto. repeat condtac; ss.
      + des. subst. congr.
      + guardH o. des. subst. i. inv GET.
        exploit Memory.split_get0; try exact MEM; eauto. i. des. esplits; eauto.
      + i. esplits; eauto.
    - erewrite Memory.lower_o; eauto. condtac; ss.
      + des. subst. congr.
      + i. inv GET. esplits; eauto.
    - erewrite Memory.remove_o; eauto. condtac; ss.
      i. esplits; eauto.
  Qed.

  Lemma promise_get_promises_inv_diff
        promises1 mem1 loc from to msg promises2 mem2 kind
        l t f m
        (PROMISE: Memory.promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (GET: Memory.get l t promises2 = Some (f, m))
        (DIFF: (loc, to) <> (l, t)):
    exists f', Memory.get l t promises1 = Some (f', m).
  Proof.
    revert GET. inv PROMISE.
    - erewrite Memory.add_o; eauto. condtac; ss.
      + des. subst. congr.
      + i. inv GET. esplits; eauto.
    - erewrite Memory.split_o; eauto. repeat condtac; ss.
      + des. subst. congr.
      + guardH o. des. subst. i. inv GET.
        exploit Memory.split_get0; try exact PROMISES; eauto. i. des. esplits; eauto.
      + i. esplits; eauto.
    - erewrite Memory.lower_o; eauto. condtac; ss.
      + des. subst. congr.
      + i. inv GET. esplits; eauto.
    - erewrite Memory.remove_o; eauto. condtac; ss.
      i. esplits; eauto.
  Qed.

  Lemma remove_get_diff
        promises0 mem0 loc from to msg promises1
        l t
        (LOC: loc <> l)
        (LE: Memory.le promises0 mem0)
        (REMOVE: Memory.remove promises0 loc from to msg promises1):
    Memory.get l t promises1 = Memory.get l t promises0.
  Proof.
    erewrite Memory.remove_o; eauto. condtac; ss.
    des. subst. congr.
  Qed.

  Lemma remove_cell_diff
        promises0 loc from to msg promises1
        l
        (LOC: loc <> l)
        (REMOVE: Memory.remove promises0 loc from to msg promises1):
    promises1 l = promises0 l.
  Proof.
    apply Cell.ext. i. eapply remove_get_diff; eauto. refl.
  Qed.

  Lemma get_same_from_aux
        l f t1 t2 m msg1 msg2
        (GET1: Memory.get l t1 m = Some (f, msg1))
        (GET2: Memory.get l t2 m = Some (f, msg2))
        (LE: Time.le t1 t2)
        (T1: t1 <> Time.bot):
    t1 = t2 /\ msg1 = msg2.
  Proof.
    inv LE; cycle 1.
    { inv H. rewrite GET1 in GET2. inv GET2. ss. }
    destruct (Cell.WF (m l)). exfalso.
    assert (t1 <> t2).
    { ii. subst. eapply Time.lt_strorder. eauto. }
    eapply DISJOINT; try exact H0; eauto.
    - apply Interval.mem_ub. exploit VOLUME; try exact GET1; eauto. intro x. des; ss.
      inv x. congr.
    - econs; ss.
      + exploit VOLUME; try exact GET1; eauto. intro x. des; ss. inv x. congr.
      + left. ss.
  Qed.

  Lemma get_same_from
        l f t1 t2 m msg1 msg2
        (GET1: Memory.get l t1 m = Some (f, msg1))
        (GET2: Memory.get l t2 m = Some (f, msg2))
        (T1: t1 <> Time.bot)
        (T2: t2 <> Time.bot):
    t1 = t2 /\ msg1 = msg2.
  Proof.
    destruct (Time.le_lt_dec t1 t2).
    - eapply get_same_from_aux; eauto.
    - exploit get_same_from_aux; (try by left; eauto); eauto. i. des. ss.
  Qed.

  Lemma write_not_bot
        pm1 mem1 loc from to val released pm2 mem2 kind
        (WRITE: Memory.write pm1 mem1 loc from to val released pm2 mem2 kind):
    to <> Time.bot.
  Proof.
    ii. subst. inv WRITE. inv PROMISE; ss.
    - inv MEM. inv ADD. inv TO.
    - inv MEM. inv SPLIT. inv TS12.
    - inv MEM. inv LOWER. inv TS0.
  Qed.

  Lemma add_remove_eq
        mem1 mem2 mem3 loc from from' to msg msg'
        (ADD: Memory.add mem1 loc from to msg mem2)
        (REMOVE: Memory.remove mem2 loc from' to msg' mem3):
    mem3 = mem1.
  Proof.
    apply Memory.ext. i.
    erewrite (@Memory.remove_o mem3); eauto.
    erewrite (@Memory.add_o mem2); eauto.
    condtac; ss. des. subst. symmetry.
    eapply Memory.add_get0. eauto.
  Qed.

  Lemma write_add_promises
        promises1 mem1 loc from to val released promises2 mem2
        (WRITE: Memory.write promises1 mem1 loc from to val released promises2 mem2 Memory.op_kind_add):
    promises2 = promises1.
  Proof.
    inv WRITE. inv PROMISE. eapply add_remove_eq; eauto.
  Qed.

  Lemma promise_exists_None
        promises1 mem1 loc from to val released
        (LE: Memory.le promises1 mem1)
        (GET: Memory.get loc to promises1 = Some (from, Message.full val released))
        (LT: Time.lt from to):
    exists promises2 mem2,
      Memory.promise promises1 mem1 loc from to (Message.full val None) promises2 mem2 (Memory.op_kind_lower (Message.full val released)).
  Proof.
    exploit Memory.lower_exists; eauto; try by econs. i. des.
    exploit LE; eauto. i.
    exploit Memory.lower_exists; eauto; try by econs. i. des.
    esplits. econs; eauto. econs. apply Time.bot_spec.
  Qed.

  Lemma released_time_lt
        mem loc from to val released
        (CLOSED: Memory.closed mem)
        (GET: Memory.get loc to mem = Some (from, Message.full val (Some released))):
    Time.lt from to.
  Proof.
    destruct (Cell.WF (mem loc)). exploit VOLUME; eauto. intro x. des; ss. inv x.
    inv CLOSED. rewrite INHABITED in GET. inv GET.
  Qed.
End MemoryFacts.
