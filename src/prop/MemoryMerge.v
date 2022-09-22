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
Require Import View.
Require Import Cell.
Require Import Memory.

Set Implicit Arguments.


Module MemoryMerge.
  Lemma add_lower_add
        mem0 loc from to msg1 msg2 mem1 mem2
        (ADD1: Memory.add mem0 loc from to msg1 mem1)
        (LOWER2: Memory.lower mem1 loc from to msg1 msg2 mem2):
    Memory.add mem0 loc from to msg2 mem2.
  Proof.
    inv ADD1. inv ADD. inv LOWER2. inv LOWER.
    rewrite LocFun.add_add_eq. econs; auto.
    unfold Cell.add in *.
    destruct r, r0. ss. subst.
    unfold LocFun.add. condtac; [|congr]. s.
    rewrite DOMap.add_add_eq. econs; auto.
  Qed.

  Lemma split_lower_split
        mem0 loc ts1 ts2 ts3 msg2 msg2' msg3 mem1 mem2
        (SPLIT1: Memory.split mem0 loc ts1 ts2 ts3 msg2 msg3 mem1)
        (LOWER2: Memory.lower mem1 loc ts1 ts2 msg2 msg2' mem2):
    Memory.split mem0 loc ts1 ts2 ts3 msg2' msg3 mem2.
  Proof.
    inv SPLIT1. inv SPLIT. inv LOWER2. inv LOWER.
    rewrite LocFun.add_add_eq. econs; auto.
    unfold Cell.split in *.
    destruct r, r0. ss. subst.
    unfold LocFun.add. condtac; [|congr]. s.
    rewrite DOMap.add_add_eq. econs; auto.
  Qed.

  Lemma lower_lower_lower
        mem0 loc from to msg0 msg1 msg2 mem1 mem2
        (LOWER1: Memory.lower mem0 loc from to msg0 msg1 mem1)
        (LOWER2: Memory.lower mem1 loc from to msg1 msg2 mem2):
    Memory.lower mem0 loc from to msg0 msg2 mem2.
  Proof.
    inv LOWER1. inv LOWER. inv LOWER2. inv LOWER.
    rewrite LocFun.add_add_eq. econs; auto.
    unfold Cell.lower in *.
    destruct r, r0. ss. subst.
    unfold LocFun.add. condtac; [|congr]. s.
    rewrite DOMap.add_add_eq. econs; auto.
    etrans; eauto.
  Qed.

  Lemma promise_promise_promise
        loc from to msg1 msg2 promises0 promises1 promises2 mem0 mem1 mem2 kind
        (PROMISE1: Memory.promise promises0 mem0 loc from to msg1 promises1 mem1 kind)
        (PROMISE2: Memory.promise promises1 mem1 loc from to msg2 promises2 mem2 (Memory.op_kind_lower msg1)):
    Memory.promise promises0 mem0 loc from to msg2 promises2 mem2 kind.
  Proof.
    inv PROMISE2. inv PROMISE1.
    - econs; eauto.
      + eapply add_lower_add; eauto.
      + eapply add_lower_add; eauto.
      + i. subst. des. subst.
        inv MEM. inv LOWER. inv MSG_LE.
      + des. subst. eauto.
    - econs; eauto.
      + eapply split_lower_split; eauto.
      + eapply split_lower_split; eauto.
      + des. subst.
        exploit Memory.lower_get0; eauto. i. des.
        inv MSG_LE. eauto.
    - econs; eauto.
      + eapply lower_lower_lower; eauto.
      + eapply lower_lower_lower; eauto.
    - exploit Memory.remove_get0; try exact PROMISES0. i. des.
      exploit Memory.lower_get0; try exact PROMISES. i. des.
      congr.
  Qed.

  Lemma promise_write_write
        loc from to msg1 val released promises0 promises1 promises2 mem0 mem1 mem2 kind
        (PROMISE1: Memory.promise promises0 mem0 loc from to msg1 promises1 mem1 kind)
        (PROMISE2: Memory.write promises1 mem1 loc from to val released promises2 mem2 (Memory.op_kind_lower msg1)):
    Memory.write promises0 mem0 loc from to val released promises2 mem2 kind.
  Proof.
    inv PROMISE2.
    exploit promise_promise_promise; try exact PROMISE1; eauto.
  Qed.

  Lemma add_remove
        loc from to msg mem0 mem1 mem2
        (ADD1: Memory.add mem0 loc from to msg mem1)
        (REMOVE2: Memory.remove mem1 loc from to msg mem2):
    mem0 = mem2.
  Proof.
    apply Memory.ext. i. symmetry.
    exploit Memory.add_get0; eauto. i. des.
    erewrite Memory.remove_o; eauto. condtac; ss.
    - des. subst. rewrite GET. ss.
    - guardH o.
      erewrite Memory.add_o; eauto. condtac; ss; eauto.
  Qed.
End MemoryMerge.
