Require Import Omega.
Require Import RelationClasses.

Require Import sflib.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import DenseOrder.
Require Import Time.
Require Import Event.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.

Require Import PromiseConsistent.

Require Import PFStepCommon.

Set Implicit Arguments.


Module PFStep.
  Include PFStepCommon.

  Inductive sim_memory (promises mem_src mem_tgt: Memory.t): Prop :=
  | sim_memory_intro
      (SOUND: forall loc from to msg_src
                (GETP: Memory.get loc to promises = None)
                (GET_SRC: Memory.get loc to mem_src = Some (from, msg_src)),
          exists msg_tgt,
            <<GET_TGT: Memory.get loc to mem_tgt = Some (from, msg_tgt)>> /\
            <<MSG: sim_message msg_src msg_tgt>>)
      (COMPLETE: forall loc from to msg_tgt
                   (GETP: Memory.get loc to promises = None)
                   (GET_TGT: Memory.get loc to mem_tgt = Some (from, msg_tgt)),
          exists msg_src,
            <<GET_SRC: Memory.get loc to mem_src = Some (from, msg_src)>> /\
            <<MSG: sim_message msg_src msg_tgt>>)
  .

  Inductive sim_thread (lang: Language.t) (e_src e_tgt: @Thread.t lang): Prop :=
  | sim_thread_intro
      (STATE: e_src.(Thread.state) = e_tgt.(Thread.state))
      (LOCAL: sim_local e_src.(Thread.local) e_tgt.(Thread.local))
      (SC: TimeMap.le e_src.(Thread.sc) e_tgt.(Thread.sc))
      (MEMORY: sim_memory e_tgt.(Thread.local).(Local.promises)
                          e_src.(Thread.memory) e_tgt.(Thread.memory))
  .


  Lemma sim_memory_get_src
        promises_src promises_tgt
        mem_src mem_tgt
        loc from to msg_src
        (PROMISES: sim_promises promises_src promises_tgt)
        (MEM: sim_memory promises_tgt mem_src mem_tgt)
        (LE_SRC: Memory.le promises_src mem_src)
        (LE_TGT: Memory.le promises_tgt mem_tgt)
        (GET_SRC: Memory.get loc to mem_src = Some (from, msg_src)):
    exists msg_tgt,
      <<GET_TGT: Memory.get loc to mem_tgt = Some (from, msg_tgt)>> /\
      <<MSG: __guard__ (msg_src = Message.half \/ sim_message msg_src msg_tgt)>>.
  Proof.
    inv PROMISES. inv MEM.
    destruct (Memory.get loc to promises_tgt) as [[f m]|] eqn:GETP.
    - exploit LE_TGT; eauto. i.
      exploit COMPLETE; eauto. i. des.
      exploit LE_SRC; eauto. i.
      rewrite GET_SRC in x1. inv x1.
      esplits; eauto. unguard. des; eauto.
    - exploit SOUND0; eauto. i. des.
      unguard. esplits; eauto.
  Qed.

  Lemma sim_memory_get_tgt
        promises_src promises_tgt
        mem_src mem_tgt
        loc from to msg_tgt
        (PROMISES: sim_promises promises_src promises_tgt)
        (MEM: sim_memory promises_tgt mem_src mem_tgt)
        (LE_SRC: Memory.le promises_src mem_src)
        (LE_TGT: Memory.le promises_tgt mem_tgt)
        (GET_TGT: Memory.get loc to mem_tgt = Some (from, msg_tgt)):
    exists msg_src,
      <<GET_SRC: Memory.get loc to mem_src = Some (from, msg_src)>> /\
      <<MSG: __guard__ (msg_src = Message.half \/ sim_message msg_src msg_tgt)>>.
  Proof.
    inv PROMISES. inv MEM.
    destruct (Memory.get loc to promises_tgt) as [[f m]|] eqn:GETP.
    - exploit LE_TGT; eauto. i.
      rewrite GET_TGT in x. inv x.
      exploit COMPLETE; eauto. i. des.
      exploit LE_SRC; eauto. i.
      esplits; eauto. unguard. des; eauto.
    - exploit COMPLETE0; eauto. i. des.
      unguard. esplits; eauto.
  Qed.

  Lemma sim_memory_max_ts
        promises_src promises_tgt mem_src mem_tgt
        (PROMISES: sim_promises promises_src promises_tgt)
        (MEM: sim_memory promises_tgt mem_src mem_tgt)
        (LE_SRC: Memory.le promises_src mem_src)
        (LE_TGT: Memory.le promises_tgt mem_tgt)
        (INHABITED_SRC: Memory.inhabited mem_src)
        (INHABITED_TGT: Memory.inhabited mem_tgt):
    forall loc, Memory.max_ts loc mem_src = Memory.max_ts loc mem_tgt.
  Proof.
    i. inv PROMISES. inv MEM.
    exploit Memory.max_ts_spec; try eapply INHABITED_SRC.
    instantiate (1 := loc). i. des. clear MAX.
    exploit Memory.max_ts_spec; try eapply INHABITED_TGT.
    instantiate (1 := loc). i. des. clear MAX.
    apply TimeFacts.antisym.
    - destruct (Memory.get loc (Memory.max_ts loc mem_src) promises_tgt) as [[]|] eqn:GETP.
      + exploit LE_TGT; eauto. i.
        exploit Memory.max_ts_spec; try exact x. i. des. ss.
      + exploit SOUND0; eauto. i. des.
        exploit Memory.max_ts_spec; try exact GET_TGT. i. des. ss.
    - destruct (Memory.get loc (Memory.max_ts loc mem_tgt) promises_tgt) as [[]|] eqn:GETP.
      + exploit COMPLETE; eauto. i. des.
        exploit LE_SRC; eauto. i.
        exploit Memory.max_ts_spec; try exact x0. i. des. ss.
      + exploit COMPLETE0; eauto. i. des.
        exploit Memory.max_ts_spec; try exact GET_SRC. i. des. ss.
  Qed.

  Lemma sim_memory_adjacent_src
        promises_src promises_tgt mem_src mem_tgt
        loc from1 to1 from2 to2
        (PROMISES: sim_promises promises_src promises_tgt)
        (MEM: sim_memory promises_tgt mem_src mem_tgt)
        (LE_SRC: Memory.le promises_src mem_src)
        (LE_TGT: Memory.le promises_tgt mem_tgt)
        (ADJ_SRC: Memory.adjacent loc from1 to1 from2 to2 mem_src):
    Memory.adjacent loc from1 to1 from2 to2 mem_tgt.
  Proof.
    inv ADJ_SRC.
    exploit sim_memory_get_src; try exact GET1; eauto. i. des.
    exploit sim_memory_get_src; try exact GET2; eauto. i. des.
    econs; eauto. i.
    exploit EMPTY; eauto. i.
    inv PROMISES. inv MEM.
    destruct (Memory.get loc ts mem_tgt) as [[]|] eqn:GET; ss.
    destruct (Memory.get loc ts promises_tgt) as [[]|] eqn:GETP.
    - exploit COMPLETE; eauto. i. des.
      exploit LE_SRC; eauto. i. congr.
    - exploit COMPLETE0; eauto. i. des. congr.
  Qed.

  Lemma sim_memory_adjacent_tgt
        promises_src promises_tgt mem_src mem_tgt
        loc from1 to1 from2 to2
        (PROMISES: sim_promises promises_src promises_tgt)
        (MEM: sim_memory promises_tgt mem_src mem_tgt)
        (LE_SRC: Memory.le promises_src mem_src)
        (LE_TGT: Memory.le promises_tgt mem_tgt)
        (ADJ_TGT: Memory.adjacent loc from1 to1 from2 to2 mem_tgt):
    Memory.adjacent loc from1 to1 from2 to2 mem_src.
  Proof.
    inv ADJ_TGT.
    exploit sim_memory_get_tgt; try exact GET1; eauto. i. des.
    exploit sim_memory_get_tgt; try exact GET2; eauto. i. des.
    econs; eauto; i.
    exploit EMPTY; eauto. i.
    inv PROMISES. inv MEM.
    destruct (Memory.get loc ts mem_src) as [[]|] eqn:GET; ss.
    destruct (Memory.get loc ts promises_tgt) as [[]|] eqn:GETP.
    - exploit LE_TGT; eauto. i. congr.
    - exploit SOUND0; eauto. i. des. congr.
  Qed.


  (* lemmas on step *)

  Lemma promise
        msg_src
        promises1_src mem1_src
        promises1_tgt mem1_tgt loc from to msg_tgt promises2_tgt mem2_tgt kind_tgt
        (PROMISES1: sim_promises promises1_src promises1_tgt)
        (MEM1: sim_memory promises1_tgt mem1_src mem1_tgt)
        (LE1_SRC: Memory.le promises1_src mem1_src)
        (LE1_TGT: Memory.le promises1_tgt mem1_tgt)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (PROMISE_TGT: Memory.promise promises1_tgt mem1_tgt loc from to msg_tgt promises2_tgt mem2_tgt kind_tgt)
        (MSG_WF_SRC: Message.wf msg_src)
        (MSG_TO_SRC: Memory.message_to msg_src loc to):
    exists promises2_src mem2_src kind_src,
      <<PROMISE_SRC: Memory.promise promises1_src mem1_src loc from to msg_src promises2_src mem2_src kind_src>> /\
      <<HALF: msg_src = Message.half ->
              <<PROMISES2: sim_promises promises2_src promises2_tgt>> /\
              <<MEM2: sim_memory promises2_tgt mem2_src mem2_tgt>>>> /\
      <<KIND: Memory.op_kind_match kind_src kind_tgt>>.
  Proof.
    inv PROMISE_TGT.
    - (* add *)
      exploit (@Memory.add_exists mem1_src loc from to msg_src); eauto.
      { ii. exploit sim_memory_get_src; eauto. i. des.
        inv MEM. inv ADD. eapply DISJOINT; eauto. }
      { inv MEM. inv ADD. ss. }
      i. des.
      exploit Memory.add_exists_le; try eapply x0; eauto. i. des.
      esplits; eauto; [|econs].
      i. subst. split; econs; i.
      + erewrite Memory.add_o; eauto. condtac; ss.
        * des. subst.
          revert GET_SRC. erewrite Memory.add_o; eauto. condtac; ss; i.
          inv GET_SRC. eauto.
        * revert GET_SRC. erewrite Memory.add_o; eauto. condtac; ss; i.
          inv PROMISES1. eauto.
      + erewrite Memory.add_o; eauto. condtac; ss.
        * des. subst.
          revert GET_TGT. erewrite Memory.add_o; eauto. condtac; ss; i.
          inv GET_TGT. unguard. esplits; eauto.
        * revert GET_TGT. erewrite Memory.add_o; eauto. condtac; ss; i.
          inv PROMISES1. eauto.
      + exploit Memory.add_get0; try exact PROMISES. i. des.
        erewrite Memory.add_o; eauto. condtac; ss.
        * des. subst. congr.
        * revert GET_SRC. erewrite Memory.add_o; eauto. condtac; ss; i.
          inv MEM1. eapply SOUND; eauto.
          destruct (Memory.get loc0 to0 promises1_tgt) as [[]|] eqn:GETP1; eauto.
          exploit Memory.add_get1; try exact GETP1; eauto. i. congr.
      + exploit Memory.add_get0; try exact PROMISES. i. des.
        erewrite Memory.add_o; eauto. condtac; ss.
        * des. subst. congr.
        * revert GET_TGT. erewrite Memory.add_o; eauto. condtac; ss; i.
          inv MEM1. eapply COMPLETE; eauto.
          destruct (Memory.get loc0 to0 promises1_tgt) as [[]|] eqn:GETP1; eauto.
          exploit Memory.add_get1; try exact GETP1; eauto. i. congr.
    - (* split *)
      exploit Memory.split_get0; try exact PROMISES. i. des.
      inv PROMISES1. exploit COMPLETE; try exact GET0. i. des.
      exploit (@Memory.split_exists promises1_src loc from to ts3 msg_src Message.half); eauto.
      { inv MEM. inv SPLIT. ss. }
      { inv MEM. inv SPLIT. ss. }
      i. des.
      exploit Memory.split_exists_le; try exact x1; eauto. i. des.
      esplits; eauto; [|econs].
      i. subst. split; econs; i.
      + erewrite Memory.split_o; eauto. repeat condtac; ss.
        * des. subst.
          revert GET_SRC. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          inv GET_SRC. eauto.
        * guardH o. des. subst.
          revert GET_SRC. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          inv GET_SRC. eauto.
        * revert GET_SRC. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          eauto.
      + erewrite Memory.split_o; eauto. repeat condtac; ss.
        * des. subst.
          revert GET_TGT. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          inv GET_TGT. unguard. esplits; eauto.
        * guardH o. des. subst.
          revert GET_TGT. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          inv GET_TGT. unguard. esplits; eauto.
        * revert GET_TGT. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          eauto.
      + erewrite Memory.split_o; eauto. repeat condtac; ss.
        * des. subst. congr.
        * guardH o. des. subst. congr.
        * revert GET_SRC. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          guardH o. guardH o0. guardH o1. guardH o2.
          inv MEM1. eapply SOUND0; eauto.
          destruct (Memory.get loc0 to0 promises1_tgt) as [[]|] eqn:GETP1; eauto.
          exploit Memory.split_get1; try exact GETP1; eauto. i. des. congr.
      + erewrite Memory.split_o; eauto. repeat condtac; ss.
        * des. subst. congr.
        * guardH o. des. subst. congr.
        * revert GET_TGT. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          guardH o. guardH o0. guardH o1. guardH o2.
          inv MEM1. eapply COMPLETE0; eauto.
          destruct (Memory.get loc0 to0 promises1_tgt) as [[]|] eqn:GETP1; eauto.
          exploit Memory.split_get1; try exact GETP1; eauto. i. des. congr.
    - (* lower *)
      exploit Memory.lower_get0; try exact PROMISES. i. des.
      inv PROMISES1. exploit COMPLETE; eauto. i. des.
      exploit (@Memory.lower_exists promises1_src loc from to Message.half msg_src); eauto.
      { inv MEM. inv LOWER. ss. }
      i. des.
      exploit Memory.lower_exists_le; try eapply x1; eauto. i. des.
      esplits; eauto; [|econs].
      i. subst. split; econs; i.
      + erewrite Memory.lower_o; eauto. condtac; ss.
        * des. subst.
          revert GET_SRC. erewrite Memory.lower_o; eauto. condtac; ss; i.
          inv GET_SRC. eauto.
        * revert GET_SRC. erewrite Memory.lower_o; eauto. condtac; ss; i.
          eauto.
      + erewrite Memory.lower_o; eauto. condtac; ss.
        * des. subst.
          revert GET_TGT. erewrite Memory.lower_o; eauto. condtac; ss; i.
          inv GET_TGT. unguard. esplits; eauto.
        * revert GET_TGT. erewrite Memory.lower_o; eauto. condtac; ss; i.
          eauto.
      + erewrite Memory.lower_o; eauto. condtac; ss.
        * des. subst. congr.
        * revert GET_SRC. erewrite Memory.lower_o; eauto. condtac; ss; i.
          guardH o. guardH o0.
          inv MEM1. eapply SOUND0; eauto.
          destruct (Memory.get loc0 to0 promises1_tgt) as [[]|] eqn:GETP1; eauto.
          exploit Memory.lower_get1; try exact GETP1; eauto. i. des. congr.
      + erewrite Memory.lower_o; eauto. condtac; ss.
        * des. subst. congr.
        * revert GET_TGT. erewrite Memory.lower_o; eauto. condtac; ss; i.
          guardH o. guardH o0.
          inv MEM1. eapply COMPLETE0; eauto.
          destruct (Memory.get loc0 to0 promises1_tgt) as [[]|] eqn:GETP1; eauto.
          exploit Memory.lower_get1; try exact GETP1; eauto. i. des. congr.
  Qed.

  Lemma promise_step
        lc1_src mem1_src
        lc1_tgt mem1_tgt loc from to msg lc2_tgt mem2_tgt kind_tgt
        (LOCAL1: sim_local lc1_src lc1_tgt)
        (MEM1: sim_memory lc1_tgt.(Local.promises) mem1_src mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (STEP_TGT: Local.promise_step lc1_tgt mem1_tgt loc from to msg lc2_tgt mem2_tgt kind_tgt):
    exists lc2_src mem2_src kind_src,
      <<STEP_SRC: Local.promise_step lc1_src mem1_src loc from to Message.half lc2_src mem2_src kind_src>> /\
      <<LOCAL2: sim_local lc2_src lc2_tgt>> /\
      <<MEM2: sim_memory lc2_tgt.(Local.promises) mem2_src mem2_tgt>>.
  Proof.
    inv STEP_TGT.
    exploit promise; try exact PROMISE; eauto.
    { apply LOCAL1. }
    { apply WF1_SRC. }
    { apply WF1_TGT. }
    { econs. }
    i. des.
    exploit HALF; eauto. i. des.
    esplits; eauto. econs; eauto. apply LOCAL1.
  Qed.

  Lemma read_step
        lc1_src mem1_src
        lc1_tgt mem1_tgt loc to val released_tgt ord lc2_tgt
        (LOCAL1: sim_local lc1_src lc1_tgt)
        (MEM1: sim_memory lc1_tgt.(Local.promises) mem1_src mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (STEP_TGT: Local.read_step lc1_tgt mem1_tgt loc to val released_tgt ord lc2_tgt)
        (CONS_TGT: promise_consistent lc2_tgt):
    exists released_src lc2_src,
      <<STEP_SRC: Local.read_step lc1_src mem1_src loc to val released_src ord lc2_src>> /\
      <<LOCAL2: sim_local lc2_src lc2_tgt>> /\
      <<RELEASED: View.opt_le released_src released_tgt>>.
  Proof.
    exploit promise_consistent_read_step_promise; try exact STEP_TGT; eauto. i.
    inv MEM1. inv LOCAL1. inv STEP_TGT.
    exploit COMPLETE; eauto. i. des. inv MSG.
    esplits.
    - econs; eauto.
      inv READABLE. inv TVIEW. econs; eauto.
      + etrans; try exact PLN. apply CUR.
      + i. exploit RLX; eauto. i.
        etrans; try exact x. apply CUR.
    - econs; eauto. ss.
      eapply TViewFacts.read_tview_mon; eauto.
      { apply WF1_TGT. }
      { inv CLOSED1_TGT. exploit CLOSED; eauto. i. des.
        inv MSG_WF. ss. }
      { refl. }
    - auto.
  Qed.

  Lemma promise_remove_sim
        promises1_src mem1_src loc from to msg_src promises2_src mem2_src kind_src
        promises3_src
        promises1_tgt mem1_tgt msg_tgt promises2_tgt mem2_tgt kind_tgt
        promises3_tgt
        (PROMISES1: sim_promises promises1_src promises1_tgt)
        (MEM1: sim_memory promises1_tgt mem1_src mem1_tgt)
        (LE1_SRC: Memory.le promises1_src mem1_src)
        (LE1_TGT: Memory.le promises1_tgt mem1_tgt)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (MSG: sim_message msg_src msg_tgt)
        (KIND: Memory.op_kind_match kind_src kind_tgt)
        (PROMISE_SRC: Memory.promise promises1_src mem1_src loc from to msg_src promises2_src mem2_src kind_src)
        (REMOVE_SRC: Memory.remove promises2_src loc from to msg_src promises3_src)
        (PROMISE_TGT: Memory.promise promises1_tgt mem1_tgt loc from to msg_tgt promises2_tgt mem2_tgt kind_tgt)
        (REMOVE_TGT: Memory.remove promises2_tgt loc from to msg_tgt promises3_tgt):
    <<PROMISES2: sim_promises promises3_src promises3_tgt>> /\
    <<MEM2: sim_memory promises3_tgt mem2_src mem2_tgt>>.
  Proof.
    split; econs; i.
    - erewrite Memory.remove_o; eauto. condtac; ss.
      + des. subst.
        revert GET_SRC. erewrite Memory.remove_o; eauto. condtac; ss.
      + revert GET_SRC. erewrite Memory.remove_o; eauto. condtac; ss. i.
        guardH o. guardH o0.
        inv PROMISE_SRC; inv PROMISE_TGT; inv KIND.
        * erewrite Memory.add_o; eauto. condtac; ss.
          revert GET_SRC. erewrite Memory.add_o; eauto. condtac; ss. i.
          inv PROMISES1. eauto.
        * erewrite Memory.split_o; eauto. repeat condtac; ss.
          { guardH o1. des. subst.
            revert GET_SRC. erewrite Memory.split_o; eauto. repeat condtac; ss. i.
            inv GET_SRC. inv PROMISES1. eauto. }
          { guardH o1. guardH o2.
            revert GET_SRC. erewrite Memory.split_o; eauto. repeat condtac; ss. i.
            inv PROMISES1. eauto. }
        * erewrite Memory.lower_o; eauto. condtac; ss.
          revert GET_SRC. erewrite Memory.lower_o; eauto. condtac; ss. i.
          inv PROMISES1. eauto.
    - erewrite Memory.remove_o; eauto. condtac; ss.
      + des. subst.
        revert GET_TGT. erewrite Memory.remove_o; eauto. condtac; ss.
      + revert GET_TGT. erewrite Memory.remove_o; eauto. condtac; ss. i.
        guardH o. guardH o0.
        inv PROMISE_SRC; inv PROMISE_TGT; inv KIND.
        * erewrite Memory.add_o; eauto. condtac; ss.
          revert GET_TGT. erewrite Memory.add_o; eauto. condtac; ss. i.
          inv PROMISES1. eauto.
        * erewrite Memory.split_o; eauto. repeat condtac; ss.
          { guardH o1. des. subst.
            revert GET_TGT. erewrite Memory.split_o; eauto. repeat condtac; ss. i.
            guardH o2.
            exploit Memory.split_get0; try exact PROMISES. i. des.
            exploit sim_promises_get_src; try exact GET0; eauto. i. des. subst.
            inv GET_TGT. inv PROMISES1. eauto. }
          { guardH o1. guardH o2.
            revert GET_TGT. erewrite Memory.split_o; eauto. repeat condtac; ss. i.
            inv PROMISES1. eauto. }
        * erewrite Memory.lower_o; eauto. condtac; ss.
          revert GET_TGT. erewrite Memory.lower_o; eauto. condtac; ss. i.
          inv PROMISES1. eauto.
    - revert GETP. erewrite Memory.remove_o; eauto. condtac; ss; i.
      + des. subst.
        exploit Memory.promise_get0; try exact PROMISE_SRC. i. des.
        exploit Memory.promise_get0; try exact PROMISE_TGT. i. des.
        rewrite GET_MEM, GET_MEM0 in *. inv GET_SRC. eauto.
      + guardH o.
        inv PROMISE_SRC; inv PROMISE_TGT; inv KIND.
        * erewrite Memory.add_o; eauto. condtac; ss.
          revert GET_SRC. erewrite Memory.add_o; eauto. condtac; ss. i.
          revert GETP. erewrite Memory.add_o; eauto. condtac; ss. i.
          inv MEM1. eauto.
        * erewrite Memory.split_o; eauto. repeat condtac; ss.
          { guardH o0. des. subst.
            revert GET_SRC. erewrite Memory.split_o; eauto. repeat condtac; ss. i.
            revert GETP. erewrite Memory.split_o; eauto. repeat condtac; ss. }
          { guardH o0. guardH o1.
            revert GET_SRC. erewrite Memory.split_o; eauto. repeat condtac; ss. i.
            revert GETP. erewrite Memory.split_o; eauto. repeat condtac; ss. i.
            inv MEM1. eauto. }
        * erewrite Memory.lower_o; eauto. condtac; ss.
          revert GET_SRC. erewrite Memory.lower_o; eauto. condtac; ss. i.
          revert GETP. erewrite Memory.lower_o; eauto. condtac; ss. i.
          inv MEM1. eauto.
    - revert GETP. erewrite Memory.remove_o; eauto. condtac; ss; i.
      + des. subst.
        exploit Memory.promise_get0; try exact PROMISE_SRC. i. des.
        exploit Memory.promise_get0; try exact PROMISE_TGT. i. des.
        rewrite GET_MEM, GET_MEM0 in *. inv GET_TGT. eauto.
      + guardH o.
        inv PROMISE_SRC; inv PROMISE_TGT; inv KIND.
        * erewrite Memory.add_o; eauto. condtac; ss.
          revert GET_TGT. erewrite Memory.add_o; eauto. condtac; ss. i.
          revert GETP. erewrite Memory.add_o; eauto. condtac; ss. i.
          inv MEM1. eauto.
        * erewrite Memory.split_o; eauto. repeat condtac; ss.
          { guardH o0. des. subst.
            revert GET_TGT. erewrite Memory.split_o; eauto. repeat condtac; ss. i.
            revert GETP. erewrite Memory.split_o; eauto. repeat condtac; ss. }
          { guardH o0. guardH o1.
            revert GET_TGT. erewrite Memory.split_o; eauto. repeat condtac; ss. i.
            revert GETP. erewrite Memory.split_o; eauto. repeat condtac; ss. i.
            inv MEM1. eauto. }
        * erewrite Memory.lower_o; eauto. condtac; ss.
          revert GET_TGT. erewrite Memory.lower_o; eauto. condtac; ss. i.
          revert GETP. erewrite Memory.lower_o; eauto. condtac; ss. i.
          inv MEM1. eauto.
  Qed.

  Lemma write_step
        lc1_src sc1_src mem1_src releasedm_src
        lc1_tgt sc1_tgt mem1_tgt loc from to val releasedm_tgt released_tgt ord lc2_tgt sc2_tgt mem2_tgt kind_tgt
        (LOCAL1: sim_local lc1_src lc1_tgt)
        (SC1: TimeMap.le sc1_src sc1_tgt)
        (MEM1: sim_memory lc1_tgt.(Local.promises) mem1_src mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
        (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (RELEASEDM_SRC: View.opt_wf releasedm_src)
        (RELEASEDM_TGT: View.opt_wf releasedm_tgt)
        (RELEASEDM: View.opt_le releasedm_src releasedm_tgt)
        (STEP_TGT: Local.write_step lc1_tgt sc1_tgt mem1_tgt loc from to val
                                    releasedm_tgt released_tgt ord lc2_tgt sc2_tgt mem2_tgt kind_tgt):
    exists released_src lc2_src sc2_src mem2_src kind_src,
      <<STEP_SRC: Local.write_step lc1_src sc1_src mem1_src loc from to val
                                   releasedm_src released_src ord lc2_src sc2_src mem2_src kind_src>> /\
      <<LOCAL2: sim_local lc2_src lc2_tgt>> /\
      <<SC2: TimeMap.le sc2_src sc2_tgt>> /\
      <<MEM2: sim_memory lc2_tgt.(Local.promises) mem2_src mem2_tgt>>.
  Proof.
    inv STEP_TGT. inv WRITE.
    exploit (@promise (Message.full val (TView.write_released lc1_src.(Local.tview) sc1_src loc to releasedm_src ord)));
      try exact PROMISE; eauto.
    { apply LOCAL1. }
    { apply WF1_SRC. }
    { apply WF1_TGT. }
    { econs. eapply TViewFacts.write_future0; ss. apply WF1_SRC. }
    { econs. etrans; try by (inv PROMISE; inv TS; eauto).
      apply View.opt_le_ts.
      apply TViewFacts.write_released_mon; try refl; ss.
      - apply LOCAL1.
      - apply WF1_TGT. }
    i. des.
    exploit Memory.promise_get0; try exact PROMISE_SRC. i. des.
    exploit Memory.remove_exists; try exact GET_PROMISES. i. des.
    exploit promise_remove_sim; try eapply LOCAL1; try exact MEM1;
      try exact PROMISE_SRC; try exact PROMISE; eauto.
    { apply WF1_SRC. }
    { apply WF1_TGT. }
    { econs. apply TViewFacts.write_released_mon; try refl; ss.
      - apply LOCAL1.
      - apply WF1_TGT. }
    i. des. esplits.
    - econs; eauto.
      + econs. inv WRITABLE.
        eapply TimeFacts.le_lt_lt; eauto.
        inv LOCAL1. inv TVIEW. inv CUR. ss.
      + ii. inv LOCAL1.
        exploit sim_promises_get_src; eauto. i. des. subst. ss.
    - inv LOCAL1. econs; ss; eauto.
      eapply TViewFacts.write_tview_mon; try refl; ss. apply WF1_TGT.
    - ss.
    - ss.
  Qed.

  Lemma program_step
        lc1_src sc1_src mem1_src
        e_tgt lc1_tgt sc1_tgt mem1_tgt lc2_tgt sc2_tgt mem2_tgt
        (LOCAL1: sim_local lc1_src lc1_tgt)
        (SC1: TimeMap.le sc1_src sc1_tgt)
        (MEM1: sim_memory lc1_tgt.(Local.promises) mem1_src mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
        (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (STEP_TGT: Local.program_step e_tgt lc1_tgt sc1_tgt mem1_tgt lc2_tgt sc2_tgt mem2_tgt)
        (CONS: promise_consistent lc2_tgt):
    exists e_src lc2_src sc2_src mem2_src,
      <<STEP_SRC: Local.program_step e_src lc1_src sc1_src mem1_src lc2_src sc2_src mem2_src>> /\
      <<LOCAL2: sim_local lc2_src lc2_tgt>> /\
      <<SC2: TimeMap.le sc2_src sc2_tgt>> /\
      <<MEM2: sim_memory lc2_tgt.(Local.promises) mem2_src mem2_tgt>> /\
      <<EVENT: ThreadEvent.get_program_event e_src = ThreadEvent.get_program_event e_tgt>>.
  Proof.
    inv STEP_TGT.
    - esplits; eauto.
    - exploit read_step; eauto. i. des.
      esplits; try exact LOCAL2; eauto.
      inv LOCAL. ss.
    - exploit write_step; try exact LOCAL; eauto. i. des.
      esplits; try exact LOCAL2; eauto.
    - exploit read_step; eauto.
      { eapply write_step_promise_consistent; eauto. }
      i. des.
      exploit Local.read_step_future; try exact LOCAL0; eauto. i. des.
      exploit Local.read_step_future; try exact STEP_SRC; eauto. i. des.
      exploit write_step; try exact LOCAL2; eauto.
      { inv LOCAL0. ss. }
      i. des.
      esplits; try exact LOCAL4; eauto.
    - exploit fence_step; eauto. i. des.
      esplits; try exact LOCAL2; eauto.
      inv LOCAL. ss.
    - exploit fence_step; eauto. i. des.
      esplits; try exact LOCAL2; eauto.
      inv LOCAL. ss.
  Qed.

  Lemma thread_promise_step
        lang e1_src
        pf e_tgt e1_tgt e2_tgt
        (SIM1: @sim_thread lang e1_src e1_tgt)
        (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
        (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
        (SC1_SRC: Memory.closed_timemap e1_src.(Thread.sc) e1_src.(Thread.memory))
        (SC1_TGT: Memory.closed_timemap e1_tgt.(Thread.sc) e1_tgt.(Thread.memory))
        (MEM1_SRC: Memory.closed e1_src.(Thread.memory))
        (MEM1_TGT: Memory.closed e1_tgt.(Thread.memory))
        (STEP_TGT: Thread.promise_step pf e_tgt e1_tgt e2_tgt):
    exists e_src e2_src,
      <<STEP_SRC: Thread.promise_step true e_src e1_src e2_src>> /\
      <<SIM2: sim_thread e2_src e2_tgt>>.
  Proof.
    destruct e1_src, e1_tgt, e2_tgt. ss.
    inv SIM1. inv STEP_TGT. ss. subst.
    exploit promise_step; try exact LOCAL; try exact MEMORY; eauto. i. des.
    esplits.
    - econs; eauto.
    - econs; eauto.
  Qed.

  Lemma thread_program_step
        lang e1_src
        e_tgt e1_tgt e2_tgt
        (SIM1: @sim_thread lang e1_src e1_tgt)
        (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
        (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
        (SC1_SRC: Memory.closed_timemap e1_src.(Thread.sc) e1_src.(Thread.memory))
        (SC1_TGT: Memory.closed_timemap e1_tgt.(Thread.sc) e1_tgt.(Thread.memory))
        (MEM1_SRC: Memory.closed e1_src.(Thread.memory))
        (MEM1_TGT: Memory.closed e1_tgt.(Thread.memory))
        (STEP_TGT: Thread.program_step e_tgt e1_tgt e2_tgt)
        (CONS: promise_consistent e2_tgt.(Thread.local)):
    exists e_src e2_src,
      <<STEP_SRC: Thread.program_step e_src e1_src e2_src>> /\
      <<SIM2: sim_thread e2_src e2_tgt>>.
  Proof.
    destruct e1_src, e1_tgt, e2_tgt. ss.
    inv SIM1. inv STEP_TGT. ss. subst.
    exploit program_step; try exact LOCAL; try exact MEMORY; eauto. i. des.
    esplits.
    - econs; try exact STEP_SRC. rewrite EVENT. eauto.
    - econs; eauto.
  Qed.

  Lemma thread_step
        lang e1_src
        pf e_tgt e1_tgt e2_tgt
        (SIM1: @sim_thread lang e1_src e1_tgt)
        (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
        (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
        (SC1_SRC: Memory.closed_timemap e1_src.(Thread.sc) e1_src.(Thread.memory))
        (SC1_TGT: Memory.closed_timemap e1_tgt.(Thread.sc) e1_tgt.(Thread.memory))
        (MEM1_SRC: Memory.closed e1_src.(Thread.memory))
        (MEM1_TGT: Memory.closed e1_tgt.(Thread.memory))
        (STEP_TGT: Thread.step pf e_tgt e1_tgt e2_tgt)
        (CONS: promise_consistent e2_tgt.(Thread.local)):
    exists e_src e2_src,
      <<STEP_SRC: Thread.step true e_src e1_src e2_src>> /\
      <<SIM2: sim_thread e2_src e2_tgt>>.
  Proof.
    inv STEP_TGT.
    - exploit thread_promise_step; eauto. i. des.
      esplits; eauto. econs 1; eauto.
    - exploit thread_program_step; eauto. i. des.
      esplits; eauto. econs 2; eauto.
  Qed.

  Lemma thread_rtc_all_step
        lang e1_src
        e1_tgt e2_tgt
        (SIM1: @sim_thread lang e1_src e1_tgt)
        (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
        (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
        (SC1_SRC: Memory.closed_timemap e1_src.(Thread.sc) e1_src.(Thread.memory))
        (SC1_TGT: Memory.closed_timemap e1_tgt.(Thread.sc) e1_tgt.(Thread.memory))
        (MEM1_SRC: Memory.closed e1_src.(Thread.memory))
        (MEM1_TGT: Memory.closed e1_tgt.(Thread.memory))
        (STEPS_TGT: rtc (@Thread.all_step lang) e1_tgt e2_tgt)
        (CONS: promise_consistent e2_tgt.(Thread.local)):
    exists e2_src,
      <<STEPS_SRC: rtc (union (@Thread.step lang true)) e1_src e2_src>> /\
      <<SIM2: sim_thread e2_src e2_tgt>>.
  Proof.
    revert e1_src SIM1 WF1_SRC SC1_SRC MEM1_SRC.
    induction STEPS_TGT; eauto; i.
    inv H. inv USTEP.
    exploit Thread.step_future; eauto. i. des.
    exploit thread_step; try exact STEP; eauto.
    { eapply rtc_all_step_promise_consistent; eauto. }
    i. des.
    exploit Thread.step_future; try exact STEP_SRC; eauto. i. des.
    exploit IHSTEPS_TGT; try exact SIM2; eauto. i. des.
    esplits; try exact SIM0.
    econs 2; eauto.
  Qed.

  Lemma thread_rtc_tau_step
        lang e1_src
        e1_tgt e2_tgt
        (SIM1: @sim_thread lang e1_src e1_tgt)
        (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
        (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
        (SC1_SRC: Memory.closed_timemap e1_src.(Thread.sc) e1_src.(Thread.memory))
        (SC1_TGT: Memory.closed_timemap e1_tgt.(Thread.sc) e1_tgt.(Thread.memory))
        (MEM1_SRC: Memory.closed e1_src.(Thread.memory))
        (MEM1_TGT: Memory.closed e1_tgt.(Thread.memory))
        (STEPS_TGT: rtc (@Thread.tau_step lang) e1_tgt e2_tgt)
        (CONS: promise_consistent e2_tgt.(Thread.local)):
    exists e2_src,
      <<STEPS_SRC: rtc (union (@Thread.step lang true)) e1_src e2_src>> /\
      <<SIM2: sim_thread e2_src e2_tgt>>.
  Proof.
    eapply thread_rtc_all_step; eauto.
    eapply rtc_implies; [|eauto].
    apply tau_union.
  Qed.


  (* existence of sim *)

  Inductive sim_memory_aux (dom: list (Loc.t * Time.t)) (promises mem_src mem_tgt: Memory.t): Prop :=
  | sim_memory_aux_intro
      (INHABITED: Memory.inhabited mem_src)
      (SOUND: forall loc from to msg_src
                (GET_SRC: Memory.get loc to mem_src = Some (from, msg_src)),
          (to = Time.bot /\ from = Time.bot \/ List.In (loc, to) dom) /\
          exists msg_tgt, Memory.get loc to mem_tgt = Some (from, msg_tgt))
      (COMPLETE_FULL: forall loc from to val released
                        (TO: to <> Time.bot)
                        (IN: List.In (loc, to) dom)
                        (GETP: Memory.get loc to promises = None)
                        (GET_TGT: Memory.get loc to mem_tgt = Some (from, Message.full val released)),
          Memory.get loc to mem_src = Some (from, Message.full val None))
      (COMPLETE_HALF: forall loc from to
                        (TO: to <> Time.bot)
                        (IN: List.In (loc, to) dom)
                        (GETP: Memory.get loc to promises = None)
                        (GET_TGT: Memory.get loc to mem_tgt = Some (from, Message.half)),
          Memory.get loc to mem_src = Some (from, Message.half))
      (PROMISE: forall loc from to msg
                  (IN: List.In (loc, to) dom)
                  (GETP: Memory.get loc to promises = Some (from, msg)),
          Memory.get loc to mem_src = Some (from, Message.half))
  .

  Lemma sim_memory_aux_exists
        dom promises mem_tgt
        (BOT: Memory.bot_none promises)
        (LE: Memory.le promises mem_tgt)
        (INHABITED: Memory.inhabited mem_tgt):
    exists mem_src, sim_memory_aux dom promises mem_src mem_tgt.
  Proof.
    induction dom.
    { exists Memory.init. econs; i; ss.
      unfold Memory.get, Memory.init, Cell.get, Cell.init in GET_SRC. ss.
      apply DOMap.singleton_find_inv in GET_SRC. des. inv GET_SRC0.
      esplits; eauto.
    }
    des. destruct a as [loc to]. inv IHdom.
    destruct (Time.eq_dec to Time.bot).
    { subst. exists mem_src. econs; i; ss.
      - exploit SOUND; eauto. i. des; eauto.
      - inv IN; eauto. inv H. ss.
      - inv IN; eauto. inv H. ss.
      - inv IN; eauto. inv H. rewrite BOT in *. ss.
    }
    destruct (Memory.get loc to mem_tgt) as [[from msg]|] eqn:GETT; cycle 1.
    { exists mem_src. econs; i; ss.
      - exploit SOUND; eauto. i. des; eauto.
      - inv IN; eauto. inv H. congr.
      - inv IN; eauto. inv H. congr.
      - inv IN; eauto. inv H. exploit LE; eauto. congr.
    }
    destruct (Memory.get loc to mem_src) as [[from_src msg_src]|] eqn:GETS.
    { exploit SOUND; eauto. i. des; ss.
      rewrite GETT in x0. symmetry in x0. inv x0.
      exists mem_src. econs; i; ss.
      - exploit SOUND; try exact GET_SRC. i. des; eauto.
      - inv IN; eauto. inv H. eauto.
      - inv IN; eauto. inv H. eauto.
      - inv IN; eauto. inv H. eauto.
    }
    destruct (Memory.get loc to promises) as [[]|] eqn:GETP.
    - exploit LE; eauto. i.
      rewrite GETT in x. symmetry in x. inv x.
      exploit (@Memory.add_exists mem_src loc from to Message.half); ii.
      { exploit SOUND; eauto. i. des.
        - subst. inv RHS. ss. inv TO.
          { eapply Time.lt_strorder. etrans; eauto. }
          inv H. inv FROM.
        - exploit Memory.get_disjoint; [exact GETT|exact x1|..].
          i. des; eauto. subst. congr. }
      { exploit Memory.get_ts; try exact GETP. i. des; ss. }
      { econs. }
      des. exists mem2. econs; i.
      + eapply Memory.add_inhabited; eauto.
      + revert GET_SRC. erewrite Memory.add_o; eauto. condtac; ss.
        * des. subst. i. inv GET_SRC. eauto.
        * guardH o. i. exploit SOUND; eauto. i. des; eauto.
      + inv IN.
        * inv H. congr.
        * exploit COMPLETE_FULL; eauto. i.
          exploit Memory.add_get1; try exact x; eauto.
      + inv IN.
        * inv H. congr.
        * exploit COMPLETE_HALF; eauto. i.
          exploit Memory.add_get1; try exact x; eauto.
      + inv IN.
        * inv H. rewrite GETP in GETP0. inv GETP0.
          exploit Memory.add_get0; eauto. i. des. ss.
        * exploit PROMISE; eauto. i.
          exploit Memory.add_get1; try exact x; eauto.
    - exploit (@Memory.add_exists mem_src loc from to
                                  (match msg with
                                   | Message.full val _ => Message.full val None
                                   | Message.half => Message.half
                                   end)); ii.
      { exploit SOUND; eauto. i. des.
        - subst. inv RHS. ss. inv TO.
          + eapply Time.lt_strorder. etrans; eauto.
          + inv H. inv FROM.
        - exploit Memory.get_disjoint; [exact GETT|exact x1|..].
          i. des; eauto. subst. congr. }
      { exploit Memory.get_ts; try exact GETT. i. des; ss. }
      { destruct msg; econs; ss. }
      des. exists mem2. econs; i.
      + eapply Memory.add_inhabited; eauto.
      + revert GET_SRC. erewrite Memory.add_o; eauto. condtac; ss.
        * i. des. subst. inv GET_SRC. eauto.
        * i. guardH o. exploit SOUND; eauto. i. des; eauto.
      + inv IN.
        * inv H. rewrite GETT in GET_TGT. inv GET_TGT.
          exploit Memory.add_get0; eauto. i. des. ss.
        * exploit COMPLETE_FULL; eauto. i.
          exploit Memory.add_get1; try exact x; eauto.
      + inv IN.
        * inv H. rewrite GETT in GET_TGT. inv GET_TGT.
          exploit Memory.add_get0; eauto. i. des. ss.
        * exploit COMPLETE_HALF; eauto. i.
          exploit Memory.add_get1; try exact x; eauto.
      + inv IN.
        * inv H. congr.
        * exploit PROMISE; eauto. i.
          exploit Memory.add_get1; try exact x; eauto.
  Qed.

  Lemma sim_memory_exists
        promises mem_tgt
        (BOT: Memory.bot_none promises)
        (LE: Memory.le promises mem_tgt)
        (INHABITED: Memory.inhabited mem_tgt):
    exists mem_src,
      sim_memory promises mem_src mem_tgt /\
      Memory.closed mem_src /\
      (forall loc from to msg
         (GETP: Memory.get loc to promises = Some (from, msg)),
          Memory.get loc to mem_src = Some (from, Message.half)).
  Proof.
    destruct (@Memory.finite mem_tgt).
    exploit (@sim_memory_aux_exists x promises mem_tgt); eauto. i. des.
    inv x1. exists mem_src. splits; eauto; econs; eauto; i.
    - exploit SOUND; eauto. i. des.
      + subst. rewrite INHABITED, INHABITED0 in *.
        inv GET_SRC. inv x1. esplits; eauto. econs; ss.
      + esplits; eauto.
        destruct (Time.eq_dec to Time.bot).
        { subst. rewrite INHABITED, INHABITED0 in *.
          inv GET_SRC. inv x1. econs; ss. }
        destruct msg_tgt.
        * exploit COMPLETE_FULL; eauto. i.
          rewrite GET_SRC in x2. inv x2. econs; ss.
        * exploit COMPLETE_HALF; eauto. i.
          rewrite GET_SRC in x2. inv x2. econs; ss.
    - destruct (Time.eq_dec to Time.bot).
      { subst. rewrite INHABITED, INHABITED0 in *.
        inv GET_TGT. esplits; eauto. econs; ss. }
      destruct msg_tgt.
      + exploit COMPLETE_FULL; eauto.
      + exploit COMPLETE_HALF; eauto.
    - destruct (Time.eq_dec to Time.bot).
      { subst. rewrite INHABITED0 in *. inv MSG.
        splits; econs; ss.
        unfold TimeMap.bot. apply Time.bot_spec. }
      exploit SOUND; eauto. i. des; ss.
      destruct (Memory.get loc to promises) as [[]|] eqn:GETP.
      + exploit LE; eauto. i. rewrite x2 in x1. inv x1.
        exploit PROMISE; eauto. i. rewrite MSG in x1. inv x1.
        splits; econs; ss.
      + destruct msg_tgt.
        * exploit COMPLETE_FULL; eauto. i.
          rewrite MSG in x2. inv x2. splits; econs; ss.
          unfold TimeMap.bot. apply Time.bot_spec.
        * exploit COMPLETE_HALF; eauto. i.
          rewrite MSG in x2. inv x2. splits; econs; ss.
  Qed.

  Lemma sim_thread_exists
        lang e
        (WF: Local.wf e.(Thread.local) e.(Thread.memory))
        (SC: Memory.closed_timemap e.(Thread.sc) e.(Thread.memory))
        (MEM: Memory.closed e.(Thread.memory)):
    exists e_src,
      <<SIM: @sim_thread lang e_src e>> /\
      <<WF_SRC: Local.wf e_src.(Thread.local) e_src.(Thread.memory)>> /\
      <<SC_SRC: Memory.closed_timemap e_src.(Thread.sc) e_src.(Thread.memory)>> /\
      <<MEM_SRC: Memory.closed e_src.(Thread.memory)>>.
  Proof.
    destruct e. destruct local. inv WF. ss.
    exploit sim_promises_exists; eauto. i. des.
    exploit sim_memory_exists; eauto; try apply MEM. i. des.
    exists (Thread.mk lang state (Local.mk TView.bot promises_src) TimeMap.bot mem_src).
    ss. splits; eauto.
    - econs; ss.
      + econs; eauto. ss.
        econs; ss; eauto using View.bot_spec.
      + ii. unfold TimeMap.bot. apply Time.bot_spec.
    - econs; ss.
      + apply TView.bot_wf.
      + inv x2. econs; ss; i.
        * unfold LocFun.init. econs; ss; ii.
          { unfold TimeMap.bot. rewrite INHABITED. esplits; refl. }
          { unfold TimeMap.bot. rewrite INHABITED. esplits; refl. }
        * econs; ss; ii.
          { unfold TimeMap.bot. rewrite INHABITED. esplits; refl. }
          { unfold TimeMap.bot. rewrite INHABITED. esplits; refl. }
        * econs; ss; ii.
          { unfold TimeMap.bot. rewrite INHABITED. esplits; refl. }
          { unfold TimeMap.bot. rewrite INHABITED. esplits; refl. }
      + ii. inv x0. exploit SOUND; eauto. i. des.
        exploit COMPLETE; eauto. i. des.
        rewrite LHS in x. inv x. eauto.
      + ii. inv x0.
        destruct (Memory.get loc Time.bot promises_src) as [[]|] eqn:GETP; ss.
        exploit SOUND; eauto. i. des.
        rewrite BOT in *. ss.
    - ii. inv x2. rewrite INHABITED. esplits; refl.
  Qed.


  (* lemmas on sim_memory and vals_incl *)

  Lemma sim_memory_vals_incl
        promises_src promises_tgt mem_src mem_tgt
        (PROMISES: sim_promises promises_src promises_tgt)
        (MEM: sim_memory promises_tgt mem_src mem_tgt)
        (LE_SRC: Memory.le promises_src mem_src)
        (LE_TGT: Memory.le promises_tgt mem_tgt):
    vals_incl mem_src mem_tgt.
  Proof.
    inv PROMISES. inv MEM. ii.
    destruct (Memory.get loc to promises_tgt) as [[]|] eqn:GETP.
    - exploit COMPLETE; eauto. i. des.
      exploit LE_SRC; eauto. i. congr.
    - exploit SOUND0; eauto. i. des. inv MSG. eauto.
  Qed.
End PFStep.
