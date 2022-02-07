Require Import RelationClasses.

From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.

Require Import Time.
Require Import Event.
From PromisingLib Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.

Require Import PromiseConsistent.

Set Implicit Arguments.


Module PFCommon.
  Inductive sim_local (lc_src lc_tgt: Local.t): Prop :=
  | sim_local_intro
      (TVIEW: (Local.tview lc_src) = (Local.tview lc_tgt))
      (PROMISES: (Local.promises lc_src) = Memory.bot)
  .
  Hint Constructors sim_local.

  Definition vals_incl (mem1 mem2: Memory.t): Prop :=
    forall loc from to val released
      (GET1: Memory.get loc to mem1 = Some (from, Message.full val released)),
    exists f t r,
      <<GET2: Memory.get loc t mem2 = Some (f, Message.full val r)>>.

  Program Instance vals_incl_PreOrder: PreOrder vals_incl.
  Next Obligation.
    ii. eauto.
  Qed.
  Next Obligation.
    ii. exploit H; eauto. i. des. eauto.
  Qed.


  (* lemmas on step *)

  Lemma fence_step
        lc1_src
        lc1_tgt sc1 ordr ordw lc2_tgt sc2
        (LOCAL1: sim_local lc1_src lc1_tgt)
        (STEP_TGT: Local.fence_step lc1_tgt sc1 ordr ordw lc2_tgt sc2):
    exists lc2_src,
      <<STEP_SRC: Local.fence_step lc1_src sc1 ordr ordw lc2_src sc2>> /\
      <<LOCAL2: sim_local lc2_src lc2_tgt>>.
  Proof.
    destruct lc1_src, lc1_tgt. inv LOCAL1. inv STEP_TGT. ss.
    subst. esplits.
    - econs; eauto. ii. ss.
      rewrite Memory.bot_get in *. ss.
    - econs; eauto.
  Qed.

  Lemma failure_step
        lc1_src lc1_tgt
        (LOCAL1: sim_local lc1_src lc1_tgt)
        (STEP_TGT: Local.failure_step lc1_tgt):
    <<STEP_SRC: Local.failure_step lc1_src>>.
  Proof.
    destruct lc1_src, lc1_tgt. inv LOCAL1. inv STEP_TGT. ss.
    subst. econs; eauto.
    eapply Local.bot_promise_consistent; ss.
  Qed.
End PFCommon.
