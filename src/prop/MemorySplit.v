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
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.

Set Implicit Arguments.


Module MemorySplit.
  Lemma remove_lower_remove
        mem0 loc from to msg1 msg2 mem2
        (MSG_LE: Message.le msg2 msg1)
        (MSG_WF1: Message.wf msg1)
        (MSG_WF2: Message.wf msg2)
        (TS: Time.lt from to)
        (REMOVE: Memory.remove mem0 loc from to msg1 mem2):
    exists mem1',
      <<LOWER: Memory.lower mem0 loc from to msg1 msg2 mem1'>> /\
      <<REMOVE: Memory.remove mem1' loc from to msg2 mem2>>.
  Proof.
    exploit Memory.remove_get0; eauto. i.
    inv REMOVE. inv REMOVE0.
    erewrite <- LocFun.add_add_eq.
    destruct r. ss. subst.
    esplits.
    - econs; ss. instantiate (1 := Cell.mk _). econs; ss.
    - econs; eauto. unfold LocFun.add. condtac; [|congr].
      unfold Cell.remove. s.
      replace (DOMap.remove to (Cell.raw (mem0 loc))) with
          (DOMap.remove to (DOMap.add to (from, msg2) (Cell.raw (mem0 loc)))).
      + econs; ss. rewrite DOMap.gss. auto.
      + apply DOMap.eq_leibniz. ii.
        rewrite ? DOMap.grspec, DOMap.gsspec. condtac; auto.
  Unshelve.
    { eapply Cell.Raw.lower_wf; eauto. apply mem0. }
  Qed.

  Lemma remove_promise_remove
        promises0 mem0 loc from to val1 released1 msg2 promises2
        (PROMISES: Memory.le promises0 mem0)
        (MSG_LE: Message.le msg2 (Message.full val1 released1))
        (MSG_WF1: Message.wf (Message.full val1 released1))
        (MSG_WF2: Message.wf msg2)
        (MSG_TS: Memory.message_to msg2 loc to)
        (TS: Time.lt from to)
        (REMOVE: Memory.remove promises0 loc from to (Message.full val1 released1) promises2):
    exists promises1' mem1',
      <<PROMISE: Memory.promise promises0 mem0 loc from to msg2 promises1' mem1' (Memory.op_kind_lower (Message.full val1 released1))>> /\
      <<REMOVE: Memory.remove promises1' loc from to msg2 promises2>>.
  Proof.
    exploit remove_lower_remove; eauto. i. des.
    exploit Memory.lower_exists_le; eauto. i. des.
    esplits; eauto.
  Qed.

  Lemma commute_remove_split_remove_remove
        mem0 loc ts1 ts2 ts3 msg2 msg3 mem1 mem3
        (REMOVE1: Memory.remove mem0 loc ts1 ts3 msg3 mem3)
        (SPLIT1: Memory.split mem0 loc ts1 ts2 ts3 msg2 msg3 mem1):
    exists mem2',
      <<REMOVE3: Memory.remove mem1 loc ts1 ts2 msg2 mem2'>> /\
      <<REMOVE4: Memory.remove mem2' loc ts2 ts3 msg3 mem3>>.
  Proof.
    exploit (@Memory.remove_exists mem1 loc ts1 ts2 msg2); eauto.
    { erewrite Memory.split_o; eauto. repeat condtac; ss.
      - guardH o. des. subst. inv SPLIT1. inv SPLIT.
        exfalso. eapply Time.lt_strorder. eauto.
      - guardH o0. des; congr.
    }
    i. des.
    exploit (@Memory.remove_exists mem2 loc ts2 ts3 msg3); eauto.
    { erewrite Memory.remove_o; eauto. condtac; ss.
      - des. subst. inv SPLIT1. inv SPLIT.
        exfalso. eapply Time.lt_strorder. eauto.
      - erewrite Memory.split_o; eauto. repeat condtac; ss.
        clear -o1. des; congr.
    }
    i. des. esplits; eauto.
    cut (mem4 = mem3); [by i; subst|].
    apply Memory.ext. i.
    erewrite Memory.remove_o; eauto. erewrite Memory.remove_o; eauto.
    erewrite Memory.split_o; eauto. erewrite (@Memory.remove_o mem3); eauto.
    repeat (condtac; ss). guardH o. des. subst.
    exploit Memory.split_get0; eauto. i. des. auto.
  Qed.

  Lemma remove_promise_promise_remove_remove
        loc ts1 ts2 ts3 val2 released2 msg3
        promises0 mem0
        promises3
        (TS12: Time.lt ts1 ts2)
        (TS23: Time.lt ts2 ts3)
        (MSG_WF2: Message.wf (Message.full val2 released2))
        (MSG_TS2: Memory.message_to (Message.full val2 released2) loc ts2)
        (LE: Memory.le promises0 mem0)
        (REMOVE: Memory.remove promises0 loc ts1 ts3 msg3 promises3):
    exists promises1 promises2 mem1,
      <<STEP1: Memory.promise promises0 mem0 loc ts1 ts2 (Message.full val2 released2) promises1 mem1 (Memory.op_kind_split ts3 msg3)>> /\
      <<STEP2: Memory.remove promises1 loc ts1 ts2 (Message.full val2 released2) promises2>> /\
      <<STEP3: Memory.remove promises2 loc ts2 ts3 msg3 promises3>>.
  Proof.
    exploit Memory.remove_get0; eauto. i. des.
    exploit Memory.split_exists; eauto. i. des.
    exploit LE; eauto. i.
    exploit Memory.split_exists; eauto. i. des.
    exploit commute_remove_split_remove_remove; try exact REMOVE; eauto. i. des.
    esplits; eauto.
  Qed.
End MemorySplit.
