Require Import Bool.
Require Import List.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
Require Import Event.
From PromisingLib Require Import Language.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import Compatibility.
Require Import SimThread.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.

(* NOTE: Elimination of a unused relaxed load is unsound under the
 * liveness-aware semantics.  Consider the following example:

    while (!y_plain) {
        r = x_rlx;
        fence(acquire);
    }

    ||

    y =rlx 1;
    x =rel 1;

 * Under the liveness-aware semantics, the loop *should* break, as
 * once `x_rlx` will read `x =rel 1` and the acquire fence guarantees
 * that `y_plain` will read 1.  However, the elimination of
 * `x_rlx` will allow the loop to run forever.
 *)

Lemma elim_read
      lc0 mem0
      loc ord
      (ORD: Ordering.le ord Ordering.plain)
      (WF: Local.wf lc0 mem0)
      (MEM: Memory.closed mem0):
  exists ts val released,
    Local.read_step lc0 mem0 loc ts val released ord lc0.
Proof.
  destruct lc0.
  assert (exists from val released, Memory.get loc ((View.pln (TView.cur tview)) loc) mem0 = Some (from, Message.full val released)).
  { inv WF. ss. inv TVIEW_CLOSED. inv CUR.
    exploit PLN; eauto.
  }
  des. inv MEM. exploit CLOSED; eauto. i. des.
  esplits. econs; eauto.
  - econs; viewtac.
  - f_equal. apply TView.antisym.
    + apply TViewFacts.read_tview_incr.
    + unfold TView.read_tview. econs; repeat (condtac; aggrtac; try apply WF).
      etrans; apply WF.
Qed.

Lemma elim_load_sim_stmts
      r loc ord
      (ORD: Ordering.le ord Ordering.plain):
  sim_stmts (RegFile.eq_except (RegSet.singleton r))
            [Stmt.instr (Instr.load r loc ord)]
            []
            (RegFile.eq_except (RegSet.singleton r)).
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits; i.
  { right.
    exploit elim_read; eauto. i. des.
    exploit sim_local_read; eauto; try refl. i. des.
    esplits.
    - econs 2; eauto. econs.
      + econs. econs 2. econs; [|econs 2]; eauto. econs. econs.
      + eauto.
    - auto.
    - auto.
    - auto.
    - auto.
    - econs. s. etrans; eauto. apply RegFile.eq_except_singleton.
  }
  { exploit SimPromises.cap; try apply LOCAL; eauto. }
  { i. right. esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  ii. right.
  inv STEP_TGT; inv STEP; try (inv STATE; inv INSTR); ss.
  (* promise *)
  exploit sim_local_promise; eauto. i. des.
  esplits; try apply SC; eauto; ss.
  econs 2. econs 1; eauto. econs; eauto. eauto.
Qed.
