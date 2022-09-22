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
Require Import MemoryFacts.

Set Implicit Arguments.


Inductive covered (loc:Loc.t) (ts:Time.t) (mem:Memory.t): Prop :=
| covered_intro
    from to msg
    (GET: Memory.get loc to mem = Some (from, msg))
    (ITV: Interval.mem (from, to) ts)
.

Inductive covered_reserve (loc: Loc.t) (ts: Time.t) (mem: Memory.t): Prop :=
| covered_reserve_intro
    from to
    (GET: Memory.get loc to mem = Some (from, Message.reserve))
    (ITV: Interval.mem (from, to) ts)
.

Lemma covered_disjoint
      mem1 mem2 loc from to
      (COVER: forall loc ts, covered loc ts mem1 -> covered loc ts mem2)
      (DISJOINT: forall to2 from2 msg2
                   (GET2: Memory.get loc to2 mem2 = Some (from2, msg2)),
          Interval.disjoint (from, to) (from2, to2)):
  forall to2 from2 msg2
    (GET2: Memory.get loc to2 mem1 = Some (from2, msg2)),
    Interval.disjoint (from, to) (from2, to2).
Proof.
  ii. exploit COVER; eauto.
  { econs; eauto. }
  intro x0. inv x0. eapply DISJOINT; eauto.
Qed.

Lemma get_disjoint_covered_disjoint
      mem loc from to:
  (forall t f m, Memory.get loc t mem = Some (f, m) -> Interval.disjoint (from, to) (f, t)) ->
  (forall ts, covered loc ts mem -> ~ Interval.mem (from, to) ts).
Proof.
  ii. inv H0. eapply H; eauto.
Qed.

Lemma covered_disjoint_get_disjoint
      mem loc from to:
  (forall ts, covered loc ts mem -> ~ Interval.mem (from, to) ts) ->
  (forall t f m, Memory.get loc t mem = Some (f, m) -> Interval.disjoint (from, to) (f, t)).
Proof.
  ii. eapply H; eauto. econs; eauto.
Qed.

Lemma add_covered
      mem2 mem1 loc from to msg
      l t
      (ADD: Memory.add mem1 loc from to msg mem2):
  covered l t mem2 <->
  covered l t mem1 \/ (l = loc /\ Interval.mem (from, to) t).
Proof.
  econs; i.
  - inv H. revert GET. erewrite Memory.add_o; eauto. condtac; ss.
    + des. subst. i. inv GET. auto.
    + left. econs; eauto.
  - des.
    + inv H. econs; eauto.
      erewrite Memory.add_o; eauto. condtac; ss; eauto.
      des. subst. exploit Memory.add_get0; eauto. i. des. congr.
    + subst. econs; eauto. erewrite Memory.add_o; eauto. condtac; ss.
      des; congr.
Qed.

Lemma split_covered
      mem2 mem1 loc ts1 ts2 ts3 msg2 msg3
      l t
      (SPLIT: Memory.split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2):
  covered l t mem2 <-> covered l t mem1.
Proof.
  econs; i.
  - exploit Memory.split_get0; eauto. i. des.
    inv H. revert GET3. erewrite Memory.split_o; eauto. repeat condtac; ss.
    + des. subst. i. inv GET3. econs; eauto.
      eapply Interval.le_mem; eauto. econs; [refl|].
      inv SPLIT. inv SPLIT0. left. auto.
    + guardH o. des. subst. i. inv GET3. econs; eauto.
      eapply Interval.le_mem; eauto. econs; [|refl].
      inv SPLIT. inv SPLIT0. left. auto.
    + i. econs; eauto.
  - exploit Memory.split_get0; eauto. i. des.
    inv H.
    destruct (loc_ts_eq_dec (l, to) (loc, ts3)); ss.
    + des. subst. rewrite GET0 in GET3. inv GET3.
      destruct (Time.le_lt_dec t ts2).
      * econs.
        { instantiate (2 := from). instantiate (2 := ts2).
          erewrite Memory.split_o; eauto. condtac; ss.
          des; congr.
        }
        { inv ITV. econs; ss. }
      * econs.
        { instantiate (2 := ts2). instantiate (2 := ts3).
          erewrite Memory.split_o; eauto. repeat condtac; ss.
          - des. subst. inv SPLIT. inv SPLIT0.
            exfalso. eapply Time.lt_strorder. eauto.
          - guardH o. des; congr.
        }
        { inv ITV. econs; ss. }
    + econs; eauto. erewrite Memory.split_o; eauto.
      repeat condtac; ss; eauto.
      * guardH o. des. subst. congr.
      * guardH o. guardH o0. des. subst.
        unguardH o. des; congr.
Qed.

Lemma lower_covered
      mem2 mem1 loc from to msg1 msg2
      l t
      (LOWER: Memory.lower mem1 loc from to msg1 msg2 mem2):
  covered l t mem2 <-> covered l t mem1.
Proof.
  econs; i.
  - inv H. revert GET. erewrite Memory.lower_o; eauto. condtac; ss.
    + des. subst. i. inv GET. econs; eauto.
      hexploit Memory.lower_get0; eauto. i. des. eauto.
    + i. econs; eauto.
  - exploit Memory.lower_get0; eauto. i. des.
    inv H.
    destruct (loc_ts_eq_dec (l, to0) (loc, to)); ss.
    + des. subst. econs; cycle 1; eauto.
      erewrite Memory.lower_o; eauto. condtac; [|by des].
      rewrite GET in GET1. inv GET1. eauto.
    + econs; eauto.
      erewrite Memory.lower_o; eauto. rewrite GET1. condtac; ss.
      des; congr.
Qed.

Lemma remove_covered
      mem2 mem1 loc from to msg
      l t
      (REMOVE: Memory.remove mem1 loc from to msg mem2):
  covered l t mem2 <->
  covered l t mem1 /\ (l <> loc \/ ~ Interval.mem (from, to) t).
Proof.
  econs; i.
  - inv H. revert GET. erewrite Memory.remove_o; eauto. condtac; ss.
    i. split.
    + econs; eauto.
    + destruct (Loc.eq_dec l loc); eauto. subst. des; ss.
      right. ii.
      exploit Memory.remove_get0; eauto. i. des.
      exploit Memory.get_disjoint; [exact GET|exact GET0|..]. i. des; ss.
      apply (x0 t); auto.
  - des.
    + inv H. econs; eauto.
      erewrite Memory.remove_o; eauto. condtac; ss; eauto.
      des. subst. exploit Memory.remove_get0; eauto. i. des. congr.
    + inv H. econs; eauto.
      erewrite Memory.remove_o; eauto. condtac; ss; eauto.
      des. subst.
      exploit Memory.remove_get0; eauto. i. des.
      rewrite GET in *. inv GET0. ss.
Qed.

Lemma cap_cover
      promises mem1 mem2 loc ts
      (CAP: Memory.cap promises mem1 mem2)
      (COVER: covered loc ts mem1):
  covered loc ts mem2.
Proof.
  inv CAP. inv COVER.
  exploit SOUND; eauto. i.
  econs; eauto.
Qed.
