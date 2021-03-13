Require Import Omega.
Require Import RelationClasses.
Require Import Coq.Lists.ListDec Decidable.

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
Require Import TView.
Require Import Local.
Require Import Thread.

Set Implicit Arguments.


Module LowerPromises.
  Inductive message_rel: forall (msg1 msg2: Message.t), Prop :=
  | message_rel_full
      val released:
      message_rel (Message.full val released) (Message.full val None)
  | message_rel_reserve:
      message_rel Message.reserve Message.reserve
  .
  Hint Constructors message_rel.

  Inductive promises_rel (promises1 promises2: Memory.t): Prop :=
  | promises_rel_intro
      (SOUND: forall loc from to msg1
                (GET1: Memory.get loc to promises1 = Some (from, msg1)),
          exists msg2,
            <<GET2: Memory.get loc to promises2 = Some (from, msg2)>>)
      (COMPLETE: forall loc from to msg2
                   (GET2: Memory.get loc to promises2 = Some (from, msg2)),
          exists msg1,
            <<GET1: Memory.get loc to promises1 = Some (from, msg1)>> /\
            <<MSG: message_rel msg1 msg2>>)
  .

  Inductive promises_rel_aux (dom: list (Loc.t * Time.t)) (promises1 promises2: Memory.t): Prop :=
  | promises_rel_aux_intro
      (SOUND: forall loc from to msg1
                (GET1: Memory.get loc to promises1 = Some (from, msg1)),
          exists msg2,
            <<GET2: Memory.get loc to promises2 = Some (from, msg2)>>)
      (COMPLETE1: forall loc from to msg2
                    (IN: List.In (loc, to) dom)
                    (GET2: Memory.get loc to promises2 = Some (from, msg2)),
          <<GET1: Memory.get loc to promises1 = Some (from, msg2)>>)
      (COMPLETE2: forall loc from to msg2
                    (IN: ~ List.In (loc, to) dom)
                    (GET2: Memory.get loc to promises2 = Some (from, msg2)),
          exists msg1,
            <<GET1: Memory.get loc to promises1 = Some (from, msg1)>> /\
            <<MSG: message_rel msg1 msg2>>)
  .

  Lemma promises_rel_aux_exists
        promises
        (FINITE: Memory.finite promises):
    exists dom, promises_rel_aux dom promises promises.
  Proof.
    inv FINITE. exists x. econs; i; eauto.
    exploit H; eauto. ss.
  Qed.

  Lemma promises_rel_aux_nil
        promises1 promises2
        (REL: promises_rel_aux [] promises1 promises2):
    promises_rel promises1 promises2.
  Proof.
    inv REL. econs; i; eauto.
  Qed.

  Lemma promises_rel_trans
        dom promises1 promises2 promises3
        (REL1: promises_rel_aux dom promises1 promises2)
        (REL2: promises_rel promises2 promises3):
    promises_rel promises1 promises3.
  Proof.
    inv REL1. inv REL2. econs; i.
    - exploit SOUND; eauto. i. des; eauto.
    - exploit COMPLETE; eauto. i. des.
      destruct (In_decidable loc_time_decidable (loc, to) dom); eauto.
      exploit COMPLETE2; eauto. i. des.
      inv MSG; inv MSG0; eauto.
  Qed.

  Lemma promises_rel_nonsynch
        promises1 promises2
        (REL: promises_rel promises1 promises2):
    Memory.nonsynch promises2.
  Proof.
    inv REL. ii.
    exploit COMPLETE; eauto. i. des. inv MSG; ss.
  Qed.

  Lemma promises_rel_aux_lower
        promises1 loc to dom
        (BOT: Memory.bot_none promises1)
        (REL: promises_rel_aux ((loc, to)::dom) promises1 promises1):
    <<REL1: promises_rel_aux dom promises1 promises1>> \/
    exists promises2 from val released,
      <<LOWER: Memory.lower promises1 loc from to (Message.full val released) (Message.full val None) promises2>> /\
      <<REL: promises_rel_aux dom promises1 promises2>> /\
      <<REL2: promises_rel_aux dom promises2 promises2>>.
  Proof.
    inv REL.
    destruct (Memory.get loc to promises1) as [[from msg1]|] eqn:GET1; cycle 1.
    { left. econs; i; eauto.
      exploit COMPLETE2; eauto. ii. inv H; ss.
      inv H0. congr.
    }
    destruct (In_decidable loc_time_decidable (loc, to) dom).
    { left. econs; i; eauto.
      exploit COMPLETE2; eauto. ii. inv H0; ss.
      inv H1. ss.
    }
    destruct msg1 as [val released|]; cycle 1.
    { left. econs; i; eauto.
      destruct (loc_ts_eq_dec (loc, to) (loc0, to0)).
      - ss. des. subst.
        rewrite GET1 in *. inv GET2.
        esplits; eauto.
      - ss. exploit COMPLETE2; eauto. ii. inv H0; ss.
        inv H1. des; ss.
    }
    right.
    exploit (@Memory.lower_exists promises1 loc from to (Message.full val released)
                                  (Message.full val None)); eauto.
    { exploit Memory.get_ts; eauto. i. des; ss.
      subst. rewrite BOT in GET1. ss. }
    { econs. ss. }
    i. des.
    esplits; eauto.
    - econs; i.
      + erewrite Memory.lower_o; eauto. condtac; ss; eauto.
        des. subst. rewrite GET1 in *. inv GET0. eauto.
      + revert GET2.
        erewrite Memory.lower_o; eauto. condtac; ss; eauto.
        des. subst. congr.
      + revert GET2.
        erewrite Memory.lower_o; eauto. condtac; ss; i.
        * des. subst. inv GET2. esplits; eauto.
        * guardH o.
          exploit COMPLETE2; eauto. ii. des; ss.
          inv H0. unguard. des; ss.
    - econs; i; eauto.
      revert GET2.
      erewrite Memory.lower_o; eauto. condtac; ss; i.
      + des. subst. inv GET2. esplits; eauto.
      + guardH o.
        exploit COMPLETE2; eauto. ii. inv H0; ss.
        inv H1. unguard. des; ss.
  Qed.

  Lemma steps_promises_rel
        lang e1
        (WF1: Local.wf (Thread.local e1) (Thread.memory e1))
        (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1))
        (CLOSED1: Memory.closed (Thread.memory e1)):
    exists e2,
      <<STEPS: rtc (union (@Thread.opt_promise_step lang)) e1 e2>> /\
      <<REL: promises_rel (Local.promises (Thread.local e1)) (Local.promises (Thread.local e2))>>.
  Proof.
    exploit promises_rel_aux_exists; try eapply WF1. i. des.
    revert e1 WF1 SC1 CLOSED1 x0.
    induction dom; i.
    { esplits; eauto. apply promises_rel_aux_nil; ss. }
    destruct a as [loc to].
    exploit promises_rel_aux_lower; try exact x0; try apply WF1. i. des; eauto.
    exploit Memory.lower_exists_le; try eapply WF1; eauto. i. des.
    cut (exists pf e e2,
            <<STEP: Thread.promise_step pf e e1 e2>> /\
            <<REL: promises_rel_aux dom (Local.promises (Thread.local e1)) (Local.promises (Thread.local e2))>> /\
            <<REL: promises_rel_aux dom (Local.promises (Thread.local e2)) (Local.promises (Thread.local e2))>>).
    { i. des.
      exploit Thread.step_future; eauto.
      { econs; eauto. }
      i. des.
      exploit IHdom; eauto. i. des.
      esplits.
      - econs 2; try exact STEPS. econs. econs. eauto.
      - eapply promises_rel_trans; eauto.
    }
    destruct e1. ss.
    esplits.
    - econs; eauto. econs.
      + econs 3; eauto. econs. ss.
        unfold TimeMap.bot. apply Time.bot_spec.
      + econs. ss.
      + eauto.
    - ss.
    - ss.
  Qed.

  Lemma rtc_opt_promise_step_future
        lang e1 e2
        (STEPS: rtc (union (@Thread.opt_promise_step lang)) e1 e2):
    <<STEPS: rtc (@Thread.tau_step lang) e1 e2>> /\
    <<STATE: (Thread.state e1) = (Thread.state e2)>> /\
    <<TVIEW: (Local.tview (Thread.local e1)) = (Local.tview (Thread.local e2))>>.
  Proof.
    induction STEPS; try by (splits; eauto). des.
    inv H. inv USTEP; eauto. splits.
    - econs 2; [|eauto].
      econs; [econs; econs; eauto|].
      inv STEP. ss.
    - rewrite <- STATE. inv STEP. ss.
    - rewrite <- TVIEW. inv STEP. inv LOCAL. ss.
  Qed.

  Lemma promises_rel_promise_consistent
        lc1 lc2
        (TVIEW: (Local.tview lc1) = (Local.tview lc2))
        (REL: promises_rel (Local.promises lc1) (Local.promises lc2))
        (CONS: Local.promise_consistent lc1):
    Local.promise_consistent lc2.
  Proof.
    inv REL. ii. rewrite <- TVIEW.
    exploit COMPLETE; eauto. i. des. inv MSG.
    eapply CONS; eauto.
  Qed.
End LowerPromises.
