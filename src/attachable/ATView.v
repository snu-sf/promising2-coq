Require Import RelationClasses.

From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import Loc.

Require Import Event.
Require Import Time.
From PromisingLib Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.

Require Import AMemory.

Set Implicit Arguments.


Module ATView.
  Lemma promise_closed
        tview1
        promises1 mem1 loc from to msg promises2 mem2 kind
        (CLOSED: TView.closed tview1 mem1)
        (PROMISE: AMemory.promise promises1 mem1 loc from to msg promises2 mem2 kind):
    TView.closed tview1 mem2.
  Proof.
    inv CLOSED. econs; i; eapply AMemory.promise_closed_view; eauto.
  Qed.
End ATView.
