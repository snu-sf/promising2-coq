Require Import Omega.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.
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
Require Import Progress.

Require Import Syntax.
Require Import Semantics.

Require Import PromiseConsistent.

Require Import SimCommon.

Set Implicit Arguments.


Module PromotionProgress.
  Import SimCommon.

  Lemma progress_read_aux
        l view released b ts
        (RELEASED: View.le released view):
    sim_view l view (View.join (View.join view (View.singleton_ur_if b l ts)) released).
  Proof.
    destruct b; ss.
    - unfold View.singleton_ur, TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
      econs; ss; ii.
      + unfold TimeMap.join. condtac; ss.
        apply TimeFacts.antisym.
        * etrans; eauto using Time.join_l.
        * inv RELEASED.
          repeat eapply Time.join_spec; eauto using Time.bot_spec; try refl.
      + unfold TimeMap.join. condtac; ss.
        apply TimeFacts.antisym.
        * etrans; eauto using Time.join_l.
        * inv RELEASED.
          repeat eapply Time.join_spec; eauto using Time.bot_spec; try refl.
    - unfold View.singleton_rw, TimeMap.bot, TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
      econs; ss; ii.
      + unfold TimeMap.join.
        apply TimeFacts.antisym.
        * etrans; eauto using Time.join_l.
        * inv RELEASED.
          repeat eapply Time.join_spec; eauto using Time.bot_spec; try refl.
      + unfold TimeMap.join. condtac; ss.
        apply TimeFacts.antisym.
        * etrans; eauto using Time.join_l.
        * inv RELEASED.
          repeat eapply Time.join_spec; eauto using Time.bot_spec; try refl.
  Qed.

  Lemma progress_read
        l lc1 mem1 from val released ord
        (WF1: Local.wf lc1 mem1)
        (MEM1: Memory.closed mem1)
        (LATEST: Memory.get l (Memory.max_ts l mem1) mem1 = Some (from, Message.full val released))
        (SAFE: View.le (View.unwrap released) (TView.cur (Local.tview lc1))):
    exists lc2,
      <<STEP: Local.read_step lc1 mem1 l (Memory.max_ts l mem1) val released ord lc2>> /\
      <<LC: sim_local l lc1 lc2>>.
  Proof.
    esplits.
    - econs; eauto.
      econs; i; eapply Memory.max_ts_spec2; apply WF1.
    - econs; try refl. econs; ss.
      + eapply progress_read_aux.
        condtac; ss. apply View.bot_spec.
      + eapply progress_read_aux.
        condtac; ss; eauto using View.bot_spec.
        etrans; eauto. apply WF1.
  Qed.

  Lemma progress_write_aux l view ts:
    sim_view l view (View.join view (View.singleton_ur l ts)).
  Proof.
    unfold View.singleton_ur, TimeMap.singleton, LocFun.init,
    LocFun.add, LocFun.find, View.join, TimeMap.join.
    econs; ss; ii.
    - condtac; ss.
      apply TimeFacts.antisym; try apply Time.join_l.
      apply Time.join_spec; try refl.
      apply Time.bot_spec.
    - condtac; ss.
      apply TimeFacts.antisym; try apply Time.join_l.
      apply Time.join_spec; try refl.
      apply Time.bot_spec.
  Qed.

  Lemma progress_write
        l lc1 sc1 mem1 val releasedm ord
        (WF1: Local.wf lc1 mem1)
        (SC1: Memory.closed_timemap sc1 mem1)
        (MEM1: Memory.closed mem1)
        (WF_REL: View.opt_wf releasedm)
        (CLOSED_REL: Memory.closed_opt_view releasedm mem1)
        (PROMISES1: forall to, Memory.get l to (Local.promises lc1) = None)
        (SAFE1: View.le (View.unwrap releasedm) (TView.cur (Local.tview lc1))):
    exists released lc2 sc2 mem2,
      <<STEP: Local.write_step lc1 sc1 mem1 l (Memory.max_ts l mem1) (Time.incr (Memory.max_ts l mem1))
                               val releasedm released ord lc2 sc2 mem2 Memory.op_kind_add>> /\
      <<LC: sim_local l lc1 lc2>> /\
      <<SC: sc1 = sc2>> /\
      <<MEM: sim_memory l mem1 mem2>> /\
      <<PROMISES2: forall to, Memory.get l to (Local.promises lc2) = None>> /\
      <<SAFE2: View.le (View.unwrap released) (TView.cur (Local.tview lc2))>>.
  Proof.
    exploit (@progress_write_step lc1 sc1 mem1 l (Time.incr (Memory.max_ts l mem1)) val releasedm ord); eauto.
    { apply Time.incr_spec. }
    { ii. rewrite PROMISES1 in GET. ss. }
    i. des.
    destruct lc1, lc2. ss.
    replace promises0 with promises in *; cycle 1.
    { apply Memory.ext. i.
      inv x0. inv WRITE. inv PROMISE. ss. inv LC2.
      erewrite (@Memory.remove_o promises2); eauto. condtac; ss.
      - des. subst.
        exploit Memory.add_get0; try exact PROMISES. i. des. ss.
      - erewrite (@Memory.add_o promises1); eauto. condtac; ss.
    }
    esplits; eauto.
    - econs; try refl. ss.
      inv x0. inv LC2. ss.
      econs; ss; eauto using progress_write_aux; i.
      unfold LocFun.add. condtac; ss.
    - inv x0. ss.
    - inv x0. inv WRITE. inv PROMISE. ss.
      econs; i.
      + erewrite Memory.add_o; eauto. condtac; ss.
        * des. ss.
        * esplits; eauto. refl.
      + revert GET_TGT. erewrite Memory.add_o; eauto. condtac; ss; i.
        * des. ss.
        * esplits; eauto. refl.
    - inv x0. inv LC2. ss.
      unfold TView.write_released. condtac; ss; try apply View.bot_spec.
      apply View.join_spec.
      + etrans; eauto. apply View.join_l.
      + unfold LocFun.add. condtac; ss.
        condtac; ss; try refl.
        apply View.join_spec; try apply View.join_r.
        etrans; try eapply WF1. apply View.join_l.
  Qed.
End PromotionProgress.
