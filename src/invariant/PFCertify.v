Require Import Omega.
Require Import RelationClasses.
Require Import Coq.Lists.ListDec Decidable.

From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
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
Require Import MemoryMerge.

Require Import AMemory.
Require Import ALocal.
Require Import ATView.
Require Import AThread.

Require Import PFCommon.
Require Import PFStep.

Set Implicit Arguments.


Module PFCertify.
  Include PFCommon.

  Definition cap_src (latests: TimeMap.t) (loc: Loc.t) (promises: Memory.t)
                     (from: Time.t) (val: Const.t) (released: option View.t):
    option (Time.t * Message.t) :=
    if Memory.get loc (latests loc) promises
    then None
    else Some (from, Message.full val released).

  Inductive sim_memory (latests: TimeMap.t) (caps: Loc.t -> option Time.t) (promises mem_src mem_tgt: Memory.t): Prop :=
  | sim_memory_intro
      (SOUND: Memory.le mem_src mem_tgt)
      (COMPLETE1: forall loc to from msg
                   (CAP: Some to <> caps loc)
                   (GETP: Memory.get loc to promises = Some (from, msg))
                   (GET_TGT: Memory.get loc to mem_tgt = Some (from, msg)),
          <<GET_SRC: Memory.get loc to mem_src = None>>)
      (COMPLETE2: forall loc to from msg
                   (CAP: Some to <> caps loc)
                   (GETP: Memory.get loc to promises = None)
                   (GET_TGT: Memory.get loc to mem_tgt = Some (from, msg)),
          <<GET_SRC: Memory.get loc to mem_src = Some (from, msg)>>)
      (LATESTS: forall loc to (CAP: Some to = caps loc), Time.lt (latests loc) to)
      (CAPS: forall loc to (CAP: Some to = caps loc),
          exists f val r from released,
            <<LATEST: Memory.get loc (latests loc) mem_tgt = Some (f, Message.full val r)>> /\
            <<CAP_SRC: Memory.get loc to mem_src = cap_src latests loc promises from val released>> /\
            <<CAP_TGT: Memory.get loc to mem_tgt = Some (from, Message.full val released)>> /\
            <<CAPP: Memory.get loc to promises = None>>)
  .

  Inductive sim_thread (lang: language) (latests: TimeMap.t) (caps: Loc.t -> option Time.t) (e_src e_tgt: @Thread.t lang): Prop :=
  | sim_thread_intro
      (STATE: (Thread.state e_src) = (Thread.state e_tgt))
      (LOCAL: sim_local (Thread.local e_src) (Thread.local e_tgt))
      (SC: (Thread.sc e_src) = (Thread.sc e_tgt))
      (MEMORY: sim_memory latests caps
                          (Local.promises (Thread.local e_tgt))
                          (Thread.memory e_src) (Thread.memory e_tgt))
  .


  Lemma opt_ts_eq_dec (lhs rhs: option Time.t): {lhs = rhs} + {lhs <> rhs}.
  Proof.
    destruct lhs, rhs; eauto.
    - destruct (Time.eq_dec t t0); subst; eauto.
      right. ii. inv H. ss.
    - right. ii. ss.
    - right. ii. ss.
  Qed.

  Lemma sim_memory_get
        latests caps promises mem_src mem_tgt
        loc from to msg
        (MEM: sim_memory latests caps promises mem_src mem_tgt)
        (LE_TGT: Memory.le promises mem_tgt)
        (GET_TGT: Memory.get loc to mem_tgt = Some (from, msg)):
    <<GETP: Memory.get loc to promises = Some (from, msg)>> /\
    <<GET_SRC: Memory.get loc to mem_src = None>> \/
    <<GETP: Memory.get loc to promises = None>> /\
    <<GET_SRC: Memory.get loc to mem_src = Some (from, msg)>> \/
    <<TO: Some to = caps loc>> /\
    <<GETP: Memory.get loc (latests loc) promises>> /\
    <<GET_SRC: Memory.get loc to mem_src = None>>.
  Proof.
    inv MEM.
    destruct (opt_ts_eq_dec (Some to) (caps loc)).
    - exploit CAPS; eauto. i. des.
      unfold cap_src in *.
      destruct (Memory.get loc (latests loc) promises) as [[]|] eqn:LATESTP.
      + right. right. exploit LE_TGT; eauto.
      + right. left.
        rewrite GET_TGT in *. inv CAP_TGT.
        splits; auto.
    - destruct (Memory.get loc to promises) as [[]|] eqn:GETP.
      + exploit LE_TGT; eauto. i.
        rewrite GET_TGT in x. inv x. eauto.
      + exploit COMPLETE2; eauto.
  Qed.


  (* lemmas on step *)

  Lemma promise
        latests caps mem1_src
        promises1 mem1_tgt loc from to msg promises2 mem2_tgt kind
        (MEM1: sim_memory latests caps promises1 mem1_src mem1_tgt)
        (LE1_TGT: Memory.le promises1 mem1_tgt)
        (PROMISE_TGT: Memory.promise promises1 mem1_tgt loc from to msg promises2 mem2_tgt kind):
    sim_memory latests caps promises2 mem1_src mem2_tgt.
  Proof.
    inv MEM1. inv PROMISE_TGT.
    - (* add *)
      clear TS RESERVE.
      exploit Memory.add_get0; try exact PROMISES. i. des.
      exploit Memory.add_get0; try exact MEM. i. des.
      econs; ii.
      + erewrite Memory.add_o; eauto. condtac; ss; eauto.
        des. subst. exploit SOUND; eauto. congr.
      + revert GETP.
        erewrite Memory.add_o; eauto. condtac; ss; eauto. i.
        des. subst.
        destruct (Memory.get loc to mem1_src) as [[]|] eqn:GET_SRC; ss.
        exploit SOUND; eauto. congr.
      + revert GETP.
        erewrite Memory.add_o; eauto. condtac; ss; eauto. i.
        revert GET_TGT.
        erewrite Memory.add_o; eauto. condtac; ss; eauto.
      + auto.
      + exploit CAPS; eauto. i. des.
        erewrite Memory.add_o; eauto. condtac; ss.
        { des. subst. congr. }
        esplits; eauto.
        * unfold cap_src in *. des_ifs; eauto.
          { revert Heq.
            erewrite Memory.add_o; eauto. condtac; ss. congr. }
          { revert Heq.
            erewrite Memory.add_o; eauto. condtac; ss. congr. }
        * erewrite Memory.add_o; eauto. condtac; ss.
          des; subst; congr.
        * erewrite Memory.add_o; eauto. condtac; ss.
          des; subst; congr.
    - (* split *)
      clear TS RESERVE.
      exploit Memory.split_get0; try exact PROMISES. i. des.
      exploit Memory.split_get0; try exact MEM. i. des.
      econs; ii.
      + erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
        * des. subst. exploit SOUND; eauto. congr.
        * guardH o. des. subst.
          exploit COMPLETE1; try exact GET0; eauto; try congr.
          ii. exploit CAPS; eauto. i. des. congr.
      + revert GETP.
        erewrite Memory.split_o; eauto. repeat condtac; ss; eauto; i.
        * des. subst.
          destruct (Memory.get loc to mem1_src) as [[]|] eqn:GET_SRC; ss.
          exploit SOUND; eauto. congr.
        * guardH o. des. subst. inv GETP. eauto.
      + revert GETP.
        erewrite Memory.split_o; eauto. repeat condtac; ss; eauto; i.
        revert GET_TGT.
        erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
      + auto.
      + exploit CAPS; eauto. i. des.
        erewrite Memory.split_o; eauto. repeat condtac; ss.
        * des. subst. congr.
        * guardH o. des. subst.
          rewrite GET4 in *. inv LATEST.
          esplits; eauto.
          { unfold cap_src in *. des_ifs; eauto. }
          { erewrite Memory.split_o; eauto. repeat condtac; [| |eauto]; ss.
            - des; subst; congr.
            - des; subst; congr. }
          { erewrite Memory.split_o; eauto. repeat condtac; ss.
            - des; subst; congr.
            - des; subst; congr. }
        * guardH o. guardH o0.
          esplits; eauto.
          { unfold cap_src in *. des_ifs; eauto.
            - revert Heq.
              erewrite Memory.split_o; eauto. repeat condtac; ss. congr.
            - revert Heq.
              erewrite Memory.split_o; eauto. repeat condtac; ss. congr. }
          { erewrite Memory.split_o; eauto. repeat condtac; [| |eauto]; ss.
            - des; subst; congr.
            - des; subst; congr. }
          { erewrite Memory.split_o; eauto. repeat condtac; ss.
            - des; subst; congr.
            - des; subst; congr. }
    - (* lower *)
      clear TS.
      exploit Memory.lower_get0; try exact PROMISES. i. des.
      exploit Memory.lower_get0; try exact MEM. i. des.
      econs; ii.
      + erewrite Memory.lower_o; eauto. condtac; ss; eauto.
        des. subst. exploit COMPLETE1; eauto; try congr.
        ii. exploit CAPS; eauto. i. des. congr.
      + revert GETP.
        erewrite Memory.lower_o; eauto. condtac; ss; eauto. i.
        des. subst. inv GETP.
        revert GET_TGT.
        erewrite Memory.lower_o; eauto.
      + revert GETP.
        erewrite Memory.lower_o; eauto. condtac; ss; eauto. i.
        revert GET_TGT.
        erewrite Memory.lower_o; eauto. condtac; ss; eauto.
      + auto.
      + exploit CAPS; eauto. i. des.
        erewrite Memory.lower_o; eauto. condtac; ss.
        * des. subst.
          rewrite GET1 in *. inv LATEST. inv MSG_LE.
          esplits; eauto.
          { unfold cap_src in *. des_ifs; eauto. }
          { erewrite Memory.lower_o; eauto. condtac; [|eauto]; ss.
            des. subst. congr. }
          { erewrite Memory.lower_o; eauto. condtac; [|eauto]; ss.
            des. subst. congr. }
        * guardH o. esplits; eauto.
          { unfold cap_src in *. des_ifs; eauto.
            - revert Heq.
              erewrite Memory.lower_o; eauto. condtac; ss. congr.
            - revert Heq.
              erewrite Memory.lower_o; eauto. condtac; ss. congr. }
          { erewrite Memory.lower_o; eauto. condtac; [|eauto]; ss.
            des. subst. congr. }
          { erewrite Memory.lower_o; eauto. condtac; [|eauto]; ss.
            des. subst. congr. }
    - (* cancel *)
      exploit Memory.remove_get0; try exact PROMISES. i. des.
      exploit Memory.remove_get0; try exact MEM. i. des.
      econs; ii.
      + erewrite Memory.remove_o; eauto. condtac; ss; eauto.
        des. subst. exploit COMPLETE1; eauto; try congr.
        ii. exploit CAPS; eauto. i. des. congr.
      + revert GETP.
        erewrite Memory.remove_o; eauto. condtac; ss; eauto.
      + revert GETP.
        erewrite Memory.remove_o; eauto. condtac; ss; i.
        * revert GET_TGT.
          erewrite Memory.remove_o; eauto. condtac; ss; eauto.
        * revert GET_TGT.
          erewrite Memory.remove_o; eauto. condtac; ss; eauto.
      + auto.
      + exploit CAPS; eauto. i. des.
        erewrite Memory.remove_o; eauto. condtac; ss.
        * des. subst.
          rewrite GET1 in *. inv LATEST.
        * guardH o. esplits; eauto.
          { unfold cap_src in *. des_ifs; eauto.
            - revert Heq.
              erewrite Memory.remove_o; eauto. condtac; ss. congr.
            - revert Heq.
              erewrite Memory.remove_o; eauto. condtac; ss. congr. }
          { erewrite Memory.remove_o; eauto. condtac; [|eauto]; ss.
            des. subst. congr. }
          { erewrite Memory.remove_o; eauto. condtac; [|eauto]; ss. }
  Qed.

  Lemma read_cap
        latests caps mem1_src
        lc1 mem1_tgt loc to val released ord lc2
        (MEM1: sim_memory latests caps (Local.promises lc1) mem1_src mem1_tgt)
        (WF1: Local.wf lc1 mem1_tgt)
        (TO: Some to = caps loc)
        (STEP: Local.read_step lc1 mem1_tgt loc to val released ord lc2)
        (CONS: Local.promise_consistent lc2):
    Memory.get loc (latests loc) (Local.promises lc1) = None.
  Proof.
    destruct (Memory.get loc (latests loc) (Local.promises lc1)) as [[]|] eqn:PROMISE; ss.
    exfalso. destruct t0; cycle 1.
    { inv MEM1. exploit CAPS; eauto. i. des.
      inv WF1. exploit PROMISES; eauto. i. congr. }
    inv STEP. exploit CONS; eauto. i.
    eapply Time.lt_strorder.
    etrans; eauto.
    inv MEM1. clear SOUND COMPLETE1 COMPLETE2 CAPS.
    exploit (LATESTS loc to); eauto. i.
    eapply TimeFacts.lt_le_lt; eauto. ss.
    etrans; [|apply Time.join_l]. etrans; [|apply Time.join_r].
    unfold View.singleton_ur_if. condtac; ss.
    - unfold TimeMap.singleton.
      exploit LocFun.add_spec_eq. unfold LocFun.find. i.
      rewrite x2. refl.
    - unfold TimeMap.singleton.
      exploit LocFun.add_spec_eq. unfold LocFun.find. i.
      rewrite x2. refl.
  Qed.

  Lemma read_step
        latests caps
        lc1_src mem1_src
        lc1_tgt mem1_tgt loc to val released ord lc2_tgt
        (LOCAL1: sim_local lc1_src lc1_tgt)
        (MEM1: sim_memory latests caps (Local.promises lc1_tgt) mem1_src mem1_tgt)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (STEP_TGT: Local.read_step lc1_tgt mem1_tgt loc to val released ord lc2_tgt)
        (CONS_TGT: Local.promise_consistent lc2_tgt):
    exists lc2_src,
      <<STEP_SRC: Local.read_step lc1_src mem1_src loc to val released ord lc2_src>> /\
      <<LOCAL2: sim_local lc2_src lc2_tgt>>.
  Proof.
    destruct (Memory.get loc to mem1_src) as [[]|] eqn:GET_SRC.
    { inv MEM1. exploit SOUND; eauto. i.
      inv STEP_TGT. rewrite GET in *. inv x.
      destruct lc1_src, lc1_tgt. inv LOCAL1. ss. subst.
      esplits; econs; eauto.
    }
    dup STEP_TGT. inv STEP_TGT0.
    exploit sim_memory_get; eauto; try apply WF1_TGT. i. des.
    - exploit promise_consistent_promise_read; eauto. i. timetac.
    - congr.
    - exploit read_cap; eauto. i. rewrite x0 in *. ss.
  Qed.

  Lemma promise_remove
        latests caps
        mem1_src loc from to msg mem2_src
        promises1 mem1_tgt promises2 mem2_tgt kind
        promises3
        (MEM1: sim_memory latests caps promises1 mem1_src mem1_tgt)
        (LE1_TGT: Memory.le promises1 mem1_tgt)
        (ADD_SRC: Memory.add mem1_src loc from to msg mem2_src)
        (PROMISE_TGT: Memory.promise promises1 mem1_tgt loc from to msg promises2 mem2_tgt kind)
        (REMOVE_SRC: Memory.remove promises2 loc from to msg promises3)
        (TO: to <> latests loc):
    <<MEM2: sim_memory latests caps promises3 mem2_src mem2_tgt>>.
  Proof.
    exploit promise; try exact PROMISE_TGT; eauto. i. inv x0.
    exploit Memory.add_get0; try exact ADD_SRC. i. des.
    exploit Memory.remove_get0; eauto. i. des.
    inv PROMISE_TGT.
    - (* add *)
      clear TS RESERVE.
      exploit MemoryMerge.add_remove; try exact PROMISES; eauto. i. subst.
      exploit Memory.add_get0; try exact MEM. i. des.
      econs; ii.
      + revert LHS.
        erewrite Memory.add_o; eauto. condtac; ss; eauto. i.
        des. subst. inv LHS. ss.
      + erewrite Memory.add_o; eauto. condtac; ss.
        * des. subst. congr.
        * revert GET_TGT.
          erewrite Memory.add_o; eauto. condtac; ss. i.
          inv MEM1. eauto.
      + erewrite Memory.add_o; eauto. condtac; ss.
        * des. subst. congr.
        * revert GET_TGT.
          erewrite Memory.add_o; eauto. condtac; ss. i.
          inv MEM1. eauto.
      + auto.
      + exploit CAPS; eauto. i. des.
        esplits; eauto.
        * unfold cap_src in *. des_ifs; eauto.
          { revert Heq.
            erewrite Memory.remove_o; eauto. condtac; ss. i.
            erewrite Memory.add_o; eauto. condtac; ss.
            guardH o. des. subst. congr. }
          { revert Heq.
            erewrite Memory.remove_o; eauto. condtac; ss. i.
            erewrite Memory.add_o; eauto. condtac; ss; try congr. }
          { revert Heq.
            erewrite Memory.remove_o; eauto. condtac; ss; i.
            - des. subst.
              erewrite Memory.add_o; eauto. condtac; ss; try congr.
            - guardH o.
              erewrite Memory.add_o; eauto. condtac; ss; try congr. }
          { revert Heq.
            erewrite Memory.remove_o; eauto. condtac; ss; i.
            - des. subst. congr.
            - erewrite Memory.add_o; eauto. condtac; ss.
              guardH o. des. subst. congr. }
        * erewrite Memory.remove_o; eauto. condtac; ss.
    - (* SPLIT *)
      clear TS RESERVE.
      exploit Memory.split_get0; try exact PROMISES. i. des.
      exploit Memory.split_get0; try exact MEM. i. des.
      econs; ii.
      + erewrite Memory.split_o; eauto. repeat condtac; ss; i.
        * des. subst. rewrite GET0 in *. inv LHS. ss.
        * guardH o. des. subst.
          revert LHS.
          erewrite Memory.add_o; eauto. condtac; ss. i.
          exploit SOUND; try exact LHS. i.
          rewrite x in *. ss.
        * revert LHS.
          erewrite Memory.add_o; eauto. condtac; ss. i.
          inv MEM1. eauto.
      + revert GETP.
        erewrite Memory.remove_o; eauto. condtac; ss; i.
        erewrite Memory.add_o; eauto. condtac; ss. eauto.
      + revert GETP.
        erewrite Memory.remove_o; eauto. condtac; ss; i.
        * des. subst.
          erewrite Memory.add_o; eauto. condtac; ss.
          rewrite GET_TGT in *. ss.
        * erewrite Memory.add_o; eauto. condtac; ss. eauto.
      + auto.
      + exploit CAPS; eauto. i. des.
        esplits; eauto.
        * unfold cap_src in *. des_ifs; eauto.
          { revert Heq.
            erewrite Memory.remove_o; eauto. condtac; ss. i.
            erewrite Memory.add_o; eauto. condtac; ss.
            guardH o. des. subst. congr. }
          { revert Heq.
            erewrite Memory.remove_o; eauto. condtac; ss. i.
            erewrite Memory.add_o; eauto. condtac; ss; try congr. }
          { revert Heq.
            erewrite Memory.remove_o; eauto. condtac; ss; i.
            - des. subst.
              erewrite Memory.add_o; eauto. condtac; ss; try congr.
            - guardH o.
              erewrite Memory.add_o; eauto. condtac; ss; try congr. }
          { revert Heq.
            erewrite Memory.remove_o; eauto. condtac; ss; i.
            - des. subst. congr.
            - erewrite Memory.add_o; eauto. condtac; ss.
              guardH o. des. subst. congr. }
        * erewrite Memory.remove_o; eauto. condtac; ss.
    - (* lower *)
      clear TS.
      exploit Memory.lower_get0; try exact PROMISES. i. des.
      exploit Memory.lower_get0; try exact MEM. i. des.
      econs; ii.
      + revert LHS.
        erewrite Memory.add_o; eauto. condtac; ss; eauto. i.
        des. subst. inv LHS. ss.
      + erewrite Memory.add_o; eauto. condtac; ss.
        * des. subst. congr.
        * revert GET_TGT.
          erewrite Memory.lower_o; eauto. condtac; ss. i.
          revert GETP.
          erewrite Memory.remove_o; eauto. condtac; ss.
          erewrite Memory.lower_o; eauto. condtac; ss.
          inv MEM1. eauto.
      + revert GETP.
        erewrite Memory.remove_o; eauto. condtac; ss.
        * i. des. subst. congr.
        * erewrite Memory.lower_o; eauto. condtac; ss. i.
          erewrite Memory.add_o; eauto. condtac; ss.
          revert GET_TGT.
          erewrite Memory.lower_o; eauto. condtac; ss.
          inv MEM1. eauto.
      + auto.
      + exploit CAPS; eauto. i. des.
        esplits; eauto.
        * unfold cap_src in *. des_ifs; eauto.
          { revert Heq.
            erewrite Memory.remove_o; eauto. condtac; ss. i.
            erewrite Memory.add_o; eauto. condtac; ss.
            guardH o. des. subst. congr. }
          { revert Heq.
            erewrite Memory.remove_o; eauto. condtac; ss. i.
            erewrite Memory.add_o; eauto. condtac; ss; try congr. }
          { revert Heq.
            erewrite Memory.remove_o; eauto. condtac; ss; i.
            - des. subst.
              erewrite Memory.add_o; eauto. condtac; ss; try congr.
            - guardH o.
              erewrite Memory.add_o; eauto. condtac; ss; try congr. }
          { revert Heq.
            erewrite Memory.remove_o; eauto. condtac; ss; i.
            - des. subst. congr.
            - erewrite Memory.add_o; eauto. condtac; ss.
              guardH o. des. subst. congr. }
        * erewrite Memory.remove_o; eauto. condtac; ss.
    - (* cancel *)
      exploit Memory.remove_get0; try exact REMOVE_SRC. i. des.
      exploit Memory.remove_get0; try exact PROMISES. i. des. congr.
  Qed.

  Lemma promise_remove_latest_Some
        latests caps
        mem1_src loc from val released mem2_src
        promises1 mem1_tgt promises2 mem2_tgt kind
        promises3
        to
        (MEM1: sim_memory latests caps promises1 mem1_src mem1_tgt)
        (LE1_TGT: Memory.le promises1 mem1_tgt)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (ADD_SRC: Memory.add mem1_src loc from (latests loc) (Message.full val released) mem2_src)
        (PROMISE_TGT: Memory.promise promises1 mem1_tgt loc from (latests loc) (Message.full val released) promises2 mem2_tgt kind)
        (REMOVE_SRC: Memory.remove promises2 loc from (latests loc) (Message.full val released) promises3)
        (TO: caps loc = Some to):
    exists from_cap released_cap mem3_src,
      <<CAP_TGT: Memory.get loc to mem2_tgt = Some (from_cap, Message.full val released_cap)>> /\
      <<ADD: Memory.add mem2_src loc from_cap to (Message.full val released_cap) mem3_src>> /\
      <<MEM2: sim_memory latests caps promises3 mem3_src mem2_tgt>>.
  Proof.
    inv PROMISE_TGT; ss.
    { (* add *)
      inv MEM1. exploit CAPS; eauto. i. des.
      exploit Memory.add_get0; try exact MEM. i. des. congr.
    }
    { (* split *)
      inv MEM1. exploit CAPS; eauto. i. des.
      exploit Memory.split_get0; try exact MEM. i. des. congr.
    }
    (* lower *)
    clear TS RESERVE.
    inv MEM1. exploit CAPS; eauto. i. des.
    exploit Memory.lower_get0; try exact PROMISES. i. des.
    exploit Memory.lower_get0; try exact MEM. i. des.
    rewrite GET1 in *. inv LATEST. inv MSG_LE. clear MSG_LE0.
    unfold cap_src in CAP_SRC. rewrite GET in *.
    exploit LATESTS; eauto. intro LATEST_LT.
    exploit (@Memory.add_exists mem2_src loc from0 to (Message.full val0 released0)).
    { ii. revert GET3.
      erewrite Memory.add_o; eauto. condtac; ss; i.
      - des. subst. inv GET3.
        exploit Memory.get_disjoint; [exact CAP_TGT|exact GET1|..]. i. des.
        + subst. timetac.
        + eapply x1; eauto.
      - guardH o. exploit SOUND; eauto. i.
        exploit Memory.get_disjoint; [exact CAP_TGT|exact x0|..]. i. des.
        + subst. congr.
        + eapply x2; eauto. }
    { exploit Memory.get_ts; try exact CAP_TGT. i. des; ss.
      subst. exploit LATESTS; eauto. i. inv x. }
    { inv CLOSED1_TGT. exploit CLOSED; try exact CAP_TGT. i. des. ss. }
    i. des.
    erewrite Memory.lower_o; eauto. condtac; ss.
    { des. subst. timetac. }
    clear o COND.
    esplits; eauto.
    econs; ii.
    - revert LHS.
      erewrite Memory.add_o; eauto. condtac; ss.
      + i. des. subst. inv LHS.
        erewrite Memory.lower_o; eauto. condtac; ss.
        des. subst. timetac.
      + guardH o.
        erewrite Memory.add_o; eauto. condtac; ss; i.
        * des. subst. inv LHS. ss.
        * erewrite Memory.lower_o; eauto. condtac; ss. eauto.
    - erewrite Memory.add_o; eauto. condtac; ss.
      + des. subst. congr.
      + guardH o.
        erewrite Memory.add_o; eauto. condtac; ss.
        * des. subst.
          exploit Memory.remove_get0; eauto. i. des. congr.
        * revert GETP.
          erewrite Memory.remove_o; eauto. condtac; ss.
          erewrite Memory.lower_o; eauto. condtac; ss. i.
          revert GET_TGT.
          erewrite Memory.lower_o; eauto.
    - erewrite Memory.add_o; eauto. condtac; ss.
      + des. subst. congr.
      + guardH o.
        erewrite Memory.add_o; eauto. condtac; ss.
        * des. subst.
          exploit Memory.remove_get0; eauto. i. des. congr.
        * revert GETP.
          erewrite Memory.remove_o; eauto. condtac; ss.
          erewrite Memory.lower_o; eauto. condtac; ss. i.
          revert GET_TGT.
          erewrite Memory.lower_o; eauto. condtac; ss. i.
          eauto.
    - auto.
    - erewrite Memory.lower_o; eauto. condtac; ss.
      + des. subst. rewrite TO in *. inv CAP.
        esplits; eauto.
        * erewrite Memory.add_o; eauto. condtac; ss.
          { unfold cap_src.
            erewrite Memory.remove_o; eauto. condtac; ss.
            revert COND1. condtac; ss. }
          { des; ss. }
        * erewrite Memory.lower_o; eauto. condtac; ss.
          des. subst. timetac.
        * erewrite Memory.remove_o; eauto. condtac; ss.
          erewrite Memory.lower_o; eauto. condtac; ss.
      + destruct (Loc.eq_dec loc0 loc).
        { subst. des; ss. }
        guardH o.
        exploit CAPS; try exact CAP. i. des.
        esplits; eauto.
        * erewrite Memory.add_o; eauto. condtac; ss.
          { des; subst; ss. }
          erewrite Memory.add_o; eauto. condtac; ss.
          { des; subst; ss. }
          unfold cap_src in *. des_ifs; eauto.
          { revert Heq.
            erewrite Memory.remove_o; eauto. condtac; ss.
            erewrite Memory.lower_o; eauto. condtac; ss.
            congr. }
          { revert Heq.
            erewrite Memory.remove_o; eauto. condtac; ss.
            erewrite Memory.lower_o; eauto. condtac; ss.
            congr. }
        * erewrite Memory.lower_o; eauto. condtac; ss.
          des. subst. ss.
        * erewrite Memory.remove_o; eauto. condtac; ss.
          erewrite Memory.lower_o; eauto. condtac; ss.
  Qed.

  Lemma promise_remove_latest_None
        latests caps
        mem1_src loc from msg mem2_src
        promises1 mem1_tgt promises2 mem2_tgt kind
        promises3
        (MEM1: sim_memory latests caps promises1 mem1_src mem1_tgt)
        (LE1_TGT: Memory.le promises1 mem1_tgt)
        (ADD_SRC: Memory.add mem1_src loc from (latests loc) msg mem2_src)
        (PROMISE_TGT: Memory.promise promises1 mem1_tgt loc from (latests loc) msg promises2 mem2_tgt kind)
        (REMOVE_SRC: Memory.remove promises2 loc from (latests loc) msg promises3)
        (TO: caps loc = None):
    <<MEM2: sim_memory latests caps promises3 mem2_src mem2_tgt>>.
  Proof.
    exploit promise; try exact PROMISE_TGT; eauto. i. inv x0.
    exploit Memory.add_get0; try exact ADD_SRC. i. des.
    exploit Memory.remove_get0; eauto. i. des.
    inv PROMISE_TGT.
    - (* add *)
      clear TS RESERVE.
      exploit MemoryMerge.add_remove; try exact PROMISES; eauto. i. subst.
      exploit Memory.add_get0; try exact MEM. i. des.
      econs; ii.
      + revert LHS.
        erewrite Memory.add_o; eauto. condtac; ss; eauto. i.
        des. subst. inv LHS. ss.
      + erewrite Memory.add_o; eauto. condtac; ss.
        * des. subst. congr.
        * revert GET_TGT.
          erewrite Memory.add_o; eauto. condtac; ss. i.
          inv MEM1. eauto.
      + erewrite Memory.add_o; eauto. condtac; ss.
        * des. subst. congr.
        * revert GET_TGT.
          erewrite Memory.add_o; eauto. condtac; ss. i.
          inv MEM1. eauto.
      + auto.
      + exploit CAPS; eauto. i. des.
        esplits; eauto.
        * unfold cap_src in *. des_ifs; eauto.
          { revert Heq.
            erewrite Memory.remove_o; eauto. condtac; ss. i.
            erewrite Memory.add_o; eauto. condtac; ss.
            guardH o. des. subst. congr. }
          { revert Heq.
            erewrite Memory.remove_o; eauto. condtac; ss. i.
            erewrite Memory.add_o; eauto. condtac; ss; try congr. }
          { revert Heq.
            erewrite Memory.remove_o; eauto. condtac; ss; i.
            - des. subst. congr.
            - guardH o.
              erewrite Memory.add_o; eauto. condtac; ss; try congr. }
          { revert Heq.
            erewrite Memory.remove_o; eauto. condtac; ss; i.
            - des. subst. congr.
            - erewrite Memory.add_o; eauto. condtac; ss.
              guardH o. des. subst. congr. }
        * erewrite Memory.remove_o; eauto. condtac; ss.
    - (* SPLIT *)
      clear TS RESERVE.
      exploit Memory.split_get0; try exact PROMISES. i. des.
      exploit Memory.split_get0; try exact MEM. i. des.
      econs; ii.
      + erewrite Memory.split_o; eauto. repeat condtac; ss; i.
        * des. subst. rewrite GET0 in *. inv LHS. ss.
        * guardH o. des. subst.
          revert LHS.
          erewrite Memory.add_o; eauto. condtac; ss. i.
          exploit SOUND; try exact LHS. i.
          rewrite x in *. ss.
        * revert LHS.
          erewrite Memory.add_o; eauto. condtac; ss. i.
          inv MEM1. eauto.
      + revert GETP.
        erewrite Memory.remove_o; eauto. condtac; ss; i.
        erewrite Memory.add_o; eauto. condtac; ss. eauto.
      + revert GETP.
        erewrite Memory.remove_o; eauto. condtac; ss; i.
        * des. subst.
          erewrite Memory.add_o; eauto. condtac; ss.
          rewrite GET_TGT in *. ss.
        * erewrite Memory.add_o; eauto. condtac; ss. eauto.
      + auto.
      + exploit CAPS; eauto. i. des.
        esplits; eauto.
        * unfold cap_src in *. des_ifs; eauto.
          { revert Heq.
            erewrite Memory.remove_o; eauto. condtac; ss. i.
            erewrite Memory.add_o; eauto. condtac; ss.
            guardH o. des. subst. congr. }
          { revert Heq.
            erewrite Memory.remove_o; eauto. condtac; ss. i.
            erewrite Memory.add_o; eauto. condtac; ss; try congr. }
          { revert Heq.
            erewrite Memory.remove_o; eauto. condtac; ss; i.
            - des. subst.
              erewrite Memory.add_o; eauto. condtac; ss; try congr.
            - guardH o.
              erewrite Memory.add_o; eauto. condtac; ss; try congr. }
          { revert Heq.
            erewrite Memory.remove_o; eauto. condtac; ss; i.
            - des. subst. congr.
            - erewrite Memory.add_o; eauto. condtac; ss.
              guardH o. des. subst. congr. }
        * erewrite Memory.remove_o; eauto. condtac; ss.
    - (* lower *)
      clear TS.
      exploit Memory.lower_get0; try exact PROMISES. i. des.
      exploit Memory.lower_get0; try exact MEM. i. des.
      econs; ii.
      + revert LHS.
        erewrite Memory.add_o; eauto. condtac; ss; eauto. i.
        des. subst. inv LHS. ss.
      + erewrite Memory.add_o; eauto. condtac; ss.
        * des. subst. congr.
        * revert GET_TGT.
          erewrite Memory.lower_o; eauto. condtac; ss. i.
          revert GETP.
          erewrite Memory.remove_o; eauto. condtac; ss.
          erewrite Memory.lower_o; eauto. condtac; ss.
          inv MEM1. eauto.
      + revert GETP.
        erewrite Memory.remove_o; eauto. condtac; ss.
        * i. des. subst. congr.
        * erewrite Memory.lower_o; eauto. condtac; ss. i.
          erewrite Memory.add_o; eauto. condtac; ss.
          revert GET_TGT.
          erewrite Memory.lower_o; eauto. condtac; ss.
          inv MEM1. eauto.
      + auto.
      + exploit CAPS; eauto. i. des.
        esplits; eauto.
        * unfold cap_src in *. des_ifs; eauto.
          { revert Heq.
            erewrite Memory.remove_o; eauto. condtac; ss. i.
            erewrite Memory.add_o; eauto. condtac; ss.
            guardH o. des. subst. congr. }
          { revert Heq.
            erewrite Memory.remove_o; eauto. condtac; ss. i.
            erewrite Memory.add_o; eauto. condtac; ss; try congr. }
          { revert Heq.
            erewrite Memory.remove_o; eauto. condtac; ss; i.
            - des. subst.
              erewrite Memory.add_o; eauto. condtac; ss; try congr.
            - guardH o.
              erewrite Memory.add_o; eauto. condtac; ss; try congr. }
          { revert Heq.
            erewrite Memory.remove_o; eauto. condtac; ss; i.
            - des. subst. congr.
            - erewrite Memory.add_o; eauto. condtac; ss.
              guardH o. des. subst. congr. }
        * erewrite Memory.remove_o; eauto. condtac; ss.
    - (* cancel *)
      exploit Memory.remove_get0; try exact REMOVE_SRC. i. des.
      exploit Memory.remove_get0; try exact PROMISES. i. des. congr.
  Qed.

  Lemma write_aux
        latests caps
        mem1_src
        lc1_tgt sc1 mem1_tgt loc from to val releasedm released ord lc2_tgt sc2 mem2_tgt kind
        (MEM1: sim_memory latests caps (Local.promises lc1_tgt) mem1_src mem1_tgt)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (RELEASEDM: View.opt_wf releasedm)
        (STEP_TGT: Local.write_step lc1_tgt sc1 mem1_tgt loc from to val
                                    releasedm released ord lc2_tgt sc2 mem2_tgt kind):
    exists mem2_src,
      Memory.add mem1_src loc from to
                 (Message.full val (TView.write_released (Local.tview lc1_tgt) sc1 loc to releasedm ord)) mem2_src.
  Proof.
    inv STEP_TGT. inv WRITE.
    exploit (@Memory.add_exists mem1_src loc from to
                                (Message.full val (TView.write_released (Local.tview lc1_tgt) sc1 loc to releasedm ord))); eauto.
    { inv MEM1. inv PROMISE; ss; ii.
      - clear TS RESERVE.
        exploit SOUND; eauto. i.
        exploit Memory.add_get1; eauto. i.
        exploit Memory.add_get0; try exact MEM. i. des.
        exploit Memory.get_disjoint; [exact x2|exact GET0|..]. i. des.
        + subst.
          exploit Memory.add_get0; try exact PROMISES. i. des.
          exploit COMPLETE2; try exact GET1; eauto.
          { ii. exploit CAPS; eauto. i. des. congr. }
          i. des. congr.
        + eapply x3; eauto.
      - clear TS RESERVE.
        exploit SOUND; eauto. i.
        exploit Memory.split_get0; eauto. i. des.
        exploit Memory.get_disjoint; [exact x0|exact GET0|..]. i. des.
        + subst.
          exploit Memory.split_get0; try exact PROMISES. i. des.
          exploit COMPLETE1; try exact GET5; eauto.
          { ii. exploit CAPS; eauto. i. des. congr. }
          i. des. congr.
        + eapply x2; eauto.
          inv LHS. ss. econs; ss.
          etrans; eauto. econs.
          inv MEM. inv SPLIT. ss.
      - clear TS.
        exploit SOUND; eauto. i.
        exploit Memory.lower_get0; try exact MEM. i. des.
        exploit Memory.get_disjoint; [exact x0|exact GET|..]. i. des.
        + subst.
          exploit Memory.lower_get0; try exact PROMISES. i. des.
          exploit COMPLETE1; try exact GET1; eauto.
          { ii. exploit CAPS; eauto. i. des. congr. }
          i. des. congr.
        + eapply x2; eauto.
    }
    { inv PROMISE; ss.
      - inv MEM. inv ADD. ss.
      - inv MEM. inv SPLIT. ss.
      - inv MEM. inv LOWER. ss.
    }
    { inv PROMISE; ss.
      - inv MEM. inv ADD. ss.
      - inv MEM. inv SPLIT. ss.
      - inv MEM. inv LOWER. ss.
    }
  Qed.

  Lemma write_step
        latests caps
        lc1_src mem1_src
        lc1_tgt sc1 mem1_tgt loc from to val releasedm released ord lc2_tgt sc2 mem2_tgt kind
        (LOCAL1: sim_local lc1_src lc1_tgt)
        (MEM1: sim_memory latests caps (Local.promises lc1_tgt) mem1_src mem1_tgt)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (RELEASEDM: View.opt_wf releasedm)
        (STEP_TGT: Local.write_step lc1_tgt sc1 mem1_tgt loc from to val
                                    releasedm released ord lc2_tgt sc2 mem2_tgt kind)
        (TO: to <> latests loc):
    exists lc2_src mem2_src,
      <<STEP_SRC: ALocal.write_step lc1_src sc1 mem1_src loc from to val
                                    releasedm released ord lc2_src sc2 mem2_src Memory.op_kind_add>> /\
      <<LOCAL2: sim_local lc2_src lc2_tgt>> /\
      <<MEM2: sim_memory latests caps (Local.promises lc2_tgt) mem2_src mem2_tgt>>.
  Proof.
    exploit write_aux; eauto. i. des.
    exploit Memory.add_exists_le; try eapply Memory.bot_le; eauto. i. des.
    exploit Memory.add_get0; try exact x1. i. des.
    exploit Memory.remove_exists; try exact GET0. i. des.
    destruct lc1_src, lc1_tgt. ss.
    inv LOCAL1. inv STEP_TGT. ss. subst.
    esplits.
    - econs; ss.
      + econs; eauto. econs; eauto; ss.
        inv WRITE. inv PROMISE; ss.
      + ii. rewrite Memory.bot_get in *. ss.
    - exploit MemoryMerge.add_remove; eauto.
    - inv WRITE. eapply promise_remove; eauto. apply WF1_TGT.
  Qed.

  Lemma write_step_latest_Some
        latests caps
        lc1_src mem1_src
        lc1_tgt sc1 mem1_tgt loc from val releasedm released ord lc2_tgt sc2 mem2_tgt kind
        to
        (LOCAL1: sim_local lc1_src lc1_tgt)
        (MEM1: sim_memory latests caps (Local.promises lc1_tgt) mem1_src mem1_tgt)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (RELEASEDM: View.opt_wf releasedm)
        (STEP_TGT: Local.write_step lc1_tgt sc1 mem1_tgt loc from (latests loc) val
                                    releasedm released ord lc2_tgt sc2 mem2_tgt kind)
        (CAP: caps loc = Some to):
    exists lc2_src mem2_src mem3_src from_cap released_cap,
      <<STEP_SRC: ALocal.write_step lc1_src sc1 mem1_src loc from (latests loc) val
                                    releasedm released ord lc2_src sc2 mem2_src Memory.op_kind_add>> /\
      <<ADD: Memory.add mem2_src loc from_cap to (Message.full val released_cap) mem3_src>> /\
      <<LOCAL2: sim_local lc2_src lc2_tgt>> /\
      <<MEM2: sim_memory latests caps (Local.promises lc2_tgt) mem3_src mem2_tgt>>.
  Proof.
    exploit write_aux; eauto. i. des.
    exploit Memory.add_exists_le; try eapply Memory.bot_le; eauto. i. des.
    exploit Memory.add_get0; try exact x1. i. des.
    exploit Memory.remove_exists; try exact GET0. i. des.
    destruct lc1_src, lc1_tgt. ss.
    inv LOCAL1. inv STEP_TGT. inv WRITE. ss. subst.
    exploit promise_remove_latest_Some; eauto; try apply WF1_TGT. i. des.
    esplits.
    - econs; ss.
      + econs; try exact x2. econs; eauto; ss.
        inv PROMISE; ss.
      + ii. rewrite Memory.bot_get in *. ss.
    - eauto.
    - econs; eauto. ss.
      exploit MemoryMerge.add_remove; try exact x1; eauto.
    - auto.
  Qed.

  Lemma write_step_latest_None
        latests caps
        lc1_src mem1_src
        lc1_tgt sc1 mem1_tgt loc from val releasedm released ord lc2_tgt sc2 mem2_tgt kind
        (LOCAL1: sim_local lc1_src lc1_tgt)
        (MEM1: sim_memory latests caps (Local.promises lc1_tgt) mem1_src mem1_tgt)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (RELEASEDM: View.opt_wf releasedm)
        (STEP_TGT: Local.write_step lc1_tgt sc1 mem1_tgt loc from (latests loc) val
                                    releasedm released ord lc2_tgt sc2 mem2_tgt kind)
        (CAP: caps loc = None):
    exists lc2_src mem2_src,
      <<STEP_SRC: ALocal.write_step lc1_src sc1 mem1_src loc from (latests loc) val
                                    releasedm released ord lc2_src sc2 mem2_src Memory.op_kind_add>> /\
      <<LOCAL2: sim_local lc2_src lc2_tgt>> /\
      <<MEM2: sim_memory latests caps (Local.promises lc2_tgt) mem2_src mem2_tgt>>.
  Proof.
    exploit write_aux; eauto. i. des.
    exploit Memory.add_exists_le; try eapply Memory.bot_le; eauto. i. des.
    exploit Memory.add_get0; try exact x1. i. des.
    exploit Memory.remove_exists; try exact GET0. i. des.
    destruct lc1_src, lc1_tgt. ss.
    inv LOCAL1. inv STEP_TGT. ss. subst.
    esplits.
    - econs; ss.
      + econs; eauto. econs; eauto; ss.
        inv WRITE. inv PROMISE; ss.
      + ii. rewrite Memory.bot_get in *. ss.
    - exploit MemoryMerge.add_remove; eauto.
    - inv WRITE. eapply promise_remove_latest_None; eauto. apply WF1_TGT.
  Qed.

  Inductive add_cap (caps: Loc.t -> option Time.t): forall (mem1 mem2: Memory.t), Prop :=
  | add_cap_refl mem:
      add_cap caps mem mem
  | add_cap_add
      mem1 mem2
      loc from to val released
      from_cap to_cap released_cap
      (GET: Memory.get loc to mem1 = Some (from, Message.full val released))
      (CAPTS: caps loc = Some to_cap)
      (LOWER: Memory.add mem1 loc from_cap to_cap (Message.full val released_cap) mem2):
      add_cap caps mem1 mem2
  .
  Hint Constructors add_cap.

  Program Instance add_cap_Reflexive: forall caps, Reflexive (add_cap caps).

  Inductive pf_step (lang: language) (caps: Loc.t -> option Time.t) (e: ThreadEvent.t):
    forall (e1 e2: Thread.t lang), Prop :=
  | pf_step_intro
      e1 st2 lc2 sc2 mem2 mem3
      (STEP: @AThread.program_step lang e e1 (Thread.mk lang st2 lc2 sc2 mem2))
      (ADD: @add_cap caps mem2 mem3):
      pf_step caps e e1 (Thread.mk lang st2 lc2 sc2 mem3)
  .
  Hint Constructors pf_step.

  Lemma add_cap_vals_incl
        caps mem1 mem2
        (ADD: add_cap caps mem1 mem2):
    vals_incl mem2 mem1.
  Proof.
    inv ADD; try refl. ii. revert GET1.
    erewrite Memory.add_o; eauto. condtac; ss; eauto. i.
    des. subst. inv GET1. eauto.
  Qed.

  Lemma pf_step_inhabited
        lang caps e e1 e2
        (STEP: @pf_step lang caps e e1 e2)
        (INHABITED1: Memory.inhabited (Thread.memory e1)):
    <<INHABITED2: Memory.inhabited (Thread.memory e2)>>.
  Proof.
    inv STEP.
    hexploit AThread.program_step_inhabited; eauto. i.
    inv ADD; ss.
    eapply Memory.add_inhabited; eauto.
  Qed.

  Lemma program_step
        latests caps
        lc1_src mem1_src
        e lc1_tgt sc1 mem1_tgt lc2_tgt sc2 mem2_tgt
        (LOCAL1: sim_local lc1_src lc1_tgt)
        (MEM1: sim_memory latests caps (Local.promises lc1_tgt) mem1_src mem1_tgt)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (SC1_TGT: Memory.closed_timemap sc1 mem1_tgt)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (STEP_TGT: Local.program_step e lc1_tgt sc1 mem1_tgt lc2_tgt sc2 mem2_tgt)
        (CONS: Local.promise_consistent lc2_tgt):
    exists lc2_src mem2_src mem3_src,
      <<STEP_SRC: ALocal.program_step e lc1_src sc1 mem1_src lc2_src sc2 mem2_src>> /\
      <<ADD: add_cap caps mem2_src mem3_src>> /\
      <<LOCAL2: sim_local lc2_src lc2_tgt>> /\
      <<MEM2: sim_memory latests caps (Local.promises lc2_tgt) mem3_src mem2_tgt>>.
  Proof.
    inv STEP_TGT.
    - esplits; eauto.
    - exploit read_step; eauto. i. des.
      esplits; try exact LOCAL2; eauto.
      inv LOCAL. ss.
    - destruct (Time.eq_dec to (latests loc)).
      + destruct (caps loc) as [c|] eqn:CAPTS.
        * subst. exploit write_step_latest_Some; try exact LOCAL; eauto. i. des.
          esplits; try exact LOCAL2; try exact MEM2; eauto.
          inv STEP_SRC.
          exploit AMemory.write_get2; eauto. i. des. eauto.
        * subst. exploit write_step_latest_None; try exact LOCAL; eauto. i. des.
          esplits; try exact LOCAL2; eauto.
      + exploit write_step; try exact LOCAL; eauto. i. des.
        esplits; try exact LOCAL2; eauto.
    - exploit read_step; eauto.
      { eapply write_step_promise_consistent; eauto. }
      i. des.
      exploit Local.read_step_future; try exact LOCAL0; eauto. i. des.
      destruct (Time.eq_dec tsw (latests loc)).
      + destruct (caps loc) as [c|] eqn:CAPTS.
        * subst. exploit write_step_latest_Some; try exact LOCAL2; eauto.
          { inv LOCAL0. eauto. }
          i. des.
          esplits; try exact LOCAL4; try exact MEM2; eauto.
          inv STEP_SRC0.
          exploit AMemory.write_get2; eauto. i. des. eauto.
        * subst. exploit write_step_latest_None; try exact LOCAL2; eauto.
          { inv LOCAL0. eauto. }
          i. des.
          esplits; try exact LOCAL4; eauto.
      + exploit write_step; try exact LOCAL2; eauto.
        { inv LOCAL0. eauto. }
        i. des.
        esplits; try exact LOCAL4; eauto.
    - exploit fence_step; eauto. i. des.
      esplits; try exact LOCAL2; eauto.
      inv LOCAL. ss.
    - exploit fence_step; eauto. i. des.
      esplits; try exact LOCAL2; eauto.
      inv LOCAL. ss.
    - exploit failure_step; eauto. i. des.
      esplits; eauto.
  Qed.

  Lemma thread_promise_step
        lang latests caps e1_src
        pf e e1_tgt e2_tgt
        (SIM1: @sim_thread lang latests caps e1_src e1_tgt)
        (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
        (MEM1_TGT: Memory.closed (Thread.memory e1_tgt))
        (STEP_TGT: Thread.promise_step pf e e1_tgt e2_tgt):
    sim_thread latests caps e1_src e2_tgt.
  Proof.
    destruct e1_src, e1_tgt, e2_tgt. ss.
    inv SIM1. inv LOCAL. inv STEP_TGT. ss. subst.
    destruct local, local0; ss. subst.
    inv LOCAL.
    econs; ss; eauto.
    eapply promise; eauto. apply WF1_TGT.
  Qed.

  Lemma thread_program_step
        lang latests caps e1_src
        e e1_tgt e2_tgt
        (SIM1: @sim_thread lang latests caps e1_src e1_tgt)
        (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
        (SC1_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
        (MEM1_TGT: Memory.closed (Thread.memory e1_tgt))
        (STEP_TGT: Thread.program_step e e1_tgt e2_tgt)
        (CONS: Local.promise_consistent (Thread.local e2_tgt)):
    exists e2_src,
      <<STEP_SRC: pf_step caps e e1_src e2_src>> /\
      <<SIM2: sim_thread latests caps e2_src e2_tgt>>.
  Proof.
    destruct e1_src, e1_tgt, e2_tgt. ss.
    inv SIM1. inv STEP_TGT. ss. subst.
    exploit program_step; try exact LOCAL; try exact MEMORY; eauto. i. des.
    esplits; eauto.
    - econs; eauto. econs; eauto.
    - econs; ss.
  Qed.

  Lemma thread_rtc_all_step
        lang latests caps e1_src
        e1_tgt e2_tgt
        (SIM1: @sim_thread lang latests caps e1_src e1_tgt)
        (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
        (SC1_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
        (MEM1_TGT: Memory.closed (Thread.memory e1_tgt))
        (STEPS_TGT: rtc (@Thread.all_step lang) e1_tgt e2_tgt)
        (CONS: Local.promise_consistent (Thread.local e2_tgt)):
    exists e2_src,
      <<STEPS_SRC: rtc (union (@pf_step lang caps)) e1_src e2_src>> /\
      <<SIM2: sim_thread latests caps e2_src e2_tgt>>.
  Proof.
    revert e1_src SIM1.
    induction STEPS_TGT; eauto; i.
    inv H. inv USTEP.
    exploit Thread.step_future; eauto. i. des.
    inv STEP.
    - exploit thread_promise_step; eauto.
    - exploit thread_program_step; eauto.
      { eapply rtc_all_step_promise_consistent; eauto. }
      i. des.
      exploit IHSTEPS_TGT; eauto. i. des.
      esplits; try exact SIM0.
      econs 2; eauto.
  Qed.

  Lemma thread_rtc_tau_step
        lang latests caps e1_src
        e1_tgt e2_tgt
        (SIM1: @sim_thread lang latests caps e1_src e1_tgt)
        (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
        (SC1_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
        (MEM1_TGT: Memory.closed (Thread.memory e1_tgt))
        (STEPS_TGT: rtc (@Thread.tau_step lang) e1_tgt e2_tgt)
        (CONS: Local.promise_consistent (Thread.local e2_tgt)):
    exists e2_src,
      <<STEPS_SRC: rtc (union (@pf_step lang caps)) e1_src e2_src>> /\
      <<SIM2: sim_thread latests caps e2_src e2_tgt>>.
  Proof.
    eapply thread_rtc_all_step; eauto.
    eapply rtc_implies; [|eauto].
    apply tau_union.
  Qed.


  (* existence of sim *)

  Definition cap_src_cell (latest: Time.t) (promises: Cell.t)
                          (from: Time.t) (val: Const.t) (released: option View.t):
    option (Time.t * Message.t) :=
    if Cell.get latest promises
    then None
    else Some (from, Message.full val released).

  Inductive sim_cell (latest: Time.t) (cap: option Time.t) (promises cell_src cell_tgt: Cell.t): Prop :=
  | sim_cell_intro
      (LATEST: exists from val released,
          Cell.get latest cell_tgt = Some (from, Message.full val released))
      (SOUND: Cell.le cell_src cell_tgt)
      (COMPLETE1: forall to from msg
                   (CAP: Some to <> cap)
                   (GETP: Cell.get to promises = Some (from, msg))
                   (GET_TGT: Cell.get to cell_tgt = Some (from, msg)),
          <<GET_SRC: Cell.get to cell_src = None>>)
      (COMPLETE2: forall to from msg
                   (CAP: Some to <> cap)
                   (GETP: Cell.get to promises = None)
                   (GET_TGT: Cell.get to cell_tgt = Some (from, msg)),
          <<GET_SRC: Cell.get to cell_src = Some (from, msg)>>)
      (LATEST: forall to (CAP: Some to = cap), Time.lt latest to)
      (CAP: forall to (CAP: Some to = cap),
          exists f val r from released,
            <<LATEST: Cell.get latest cell_tgt = Some (f, Message.full val r)>> /\
            <<CAP_SRC: Cell.get to cell_src = cap_src_cell latest promises from val released>> /\
            <<CAP_TGT: Cell.get to cell_tgt = Some (from, Message.full val released)>> /\
            <<CAPP: Cell.get to promises = None>>)
  .

  Inductive sim_cell_aux (latest: Time.t) (cap: option Time.t) (dom: list Time.t) (promises cell_src cell_tgt: Cell.t): Prop :=
  | sim_cell_aux_intro
      (LATEST: exists from val released,
          Cell.get latest cell_tgt = Some (from, Message.full val released))
      (SOUND: Cell.le cell_src cell_tgt)
      (COMPLETE1: forall from to msg
                    (CAP: Some to <> cap)
                    (GETP: Cell.get to promises = Some (from, msg))
                    (GET_TGT: Cell.get to cell_tgt = Some (from, msg)),
          <<GET_SRC: Cell.get to cell_src = None>>)
      (COMPLETE2: forall from to val released
                    (CAP: Some to <> cap)
                    (GETP: Cell.get to promises = None)
                    (GET_TGT: Cell.get to cell_tgt = Some (from, Message.full val released)),
          <<GET_SRC: Cell.get to cell_src = Some (from, Message.full val released)>>)
      (RESERVE: forall from to
               (IN: List.In to dom)
               (GETP: Cell.get to promises = None)
               (GET_TGT: Cell.get to cell_tgt = Some (from, Message.reserve)),
          <<GET_SRC: Cell.get to cell_src = Some (from, Message.reserve)>>)
      (LATESTS: forall to (CAP: Some to = cap), Time.lt latest to)
      (CAP: forall to (CAP: Some to = cap),
          exists f val r from released,
            <<LATEST: Cell.get latest cell_tgt = Some (f, Message.full val r)>> /\
            <<CAP_SRC: List.In to dom /\
                       Cell.get to cell_src = cap_src_cell latest promises from val released \/
                       ~ List.In to dom /\
                       Cell.get to cell_src = None>> /\
            <<CAP_TGT: Cell.get to cell_tgt = Some (from, Message.full val released)>> /\
            <<CAPP: Cell.get to promises = None>>)
  .

  Inductive cap_cell (promises cell1 cell2: Cell.t): Prop :=
  | cap_cell_intro
      latest
      (LATEST: Cell.max_full_ts cell1 latest)
      (SOUND: Cell.le cell1 cell2)
      (MIDDLE: forall from1 to1 from2 to2
                 (ADJ: Cell.adjacent from1 to1 from2 to2 cell1)
                 (TS: Time.lt to1 from2),
          Cell.get from2 cell2 = Some (to1, Message.reserve))
      (BACK: forall to
               (TO: to = Time.incr (Cell.max_ts cell1))
               (PROMISE: Cell.latest_reserve promises cell1),
          exists f val r released,
            Cell.get latest cell1 = Some (f, Message.full val r) /\
            Cell.get to cell2 = Some (Cell.max_ts cell1, Message.full val released))
      (COMPLETE: forall from to msg
                   (GET2: Cell.get to cell2 = Some (from, msg)),
          <<GET1: Cell.get to cell1 = Some (from, msg)>> \/
          <<GET1: Cell.get to cell1 = None>> /\
          <<TS: Time.lt from to>> /\
          <<MSG: msg = Message.reserve>> /\
          (exists from1 to1, <<ADJ: Cell.adjacent from1 from to to1 cell1>>) \/
          <<GET1: Cell.get to cell1 = None>> /\
          <<FROM: from = Cell.max_ts cell1>> /\
          <<TO: to = Time.incr (Cell.max_ts cell1)>> /\
          <<PROMISE: Cell.latest_reserve promises cell1>>)
  .

  Definition vals_incl_cell (cell1 cell2: Cell.t): Prop :=
    forall from to val released
      (GET1: Cell.get to cell1 = Some (from, Message.full val released)),
    exists f t r,
      <<GET2: Cell.get t cell2 = Some (f, Message.full val r)>>.

  Program Instance vals_incl_cell_PreOrder: PreOrder vals_incl_cell.
  Next Obligation.
    ii. eauto.
  Qed.
  Next Obligation.
    ii. exploit H; eauto. i. des. eauto.
  Qed.

  Lemma cap_cap_cell
        promises mem1 mem2
        (CAP: Memory.cap promises mem1 mem2)
        (CLOSED: Memory.closed mem1):
    forall loc, cap_cell (promises loc) (mem1 loc) (mem2 loc).
  Proof.
    exploit Memory.max_full_timemap_exists; try apply CLOSED. i. des.
    dup CAP. inv CAP0.
    econs; i; eauto.
    - apply x0.
    - ii. eauto.
    - inv ADJ. eapply MIDDLE; eauto. econs; eauto.
    - exploit (@Memory.latest_val_exists loc mem1); try apply CLOSED. i. des.
      exploit BACK; eauto. i.
      inv x1. specialize (x0 loc).
      exploit Memory.max_full_ts_inj; [exact MAX|exact x0|..]. i. subst.
      inv x0. des.
      unfold Memory.get in GET. rewrite GET in *. inv GET0.
      esplits; eauto.
    - exploit Memory.cap_inv; eauto. i. des; eauto.
      + subst. right. left.
        inv x2. esplits; eauto. econs; eauto.
      + subst. right. right. esplits; eauto.
  Qed.

  Lemma cap_exists promises mem loc:
    exists (cap: option Time.t),
      if cap
      then Memory.latest_reserve loc promises mem /\
           cap = Some (Time.incr (Memory.max_ts loc mem))
      else ~ Memory.latest_reserve loc promises mem.
  Proof.
    destruct (@Memory.latest_reserve_dec loc promises mem).
    - eexists (Some _). esplits; eauto.
    - exists None. eauto.
  Qed.

  Lemma sim_cell_exists
        promises mem1_src mem1_tgt mem2_tgt latests
        (SIM: PFStep.sim_memory promises mem1_src mem1_tgt)
        (LE_TGT: Memory.le promises mem1_tgt)
        (FINITE_TGT: Memory.finite promises)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (CLOSED2_TGT: Memory.closed mem2_tgt)
        (CAP: Memory.cap promises mem1_tgt mem2_tgt)
        (MAX: Memory.max_full_timemap mem1_tgt latests):
    forall loc,
    exists cap cell_src,
      sim_cell (latests loc) cap (promises loc) cell_src (mem2_tgt loc) /\
      vals_incl_cell cell_src (mem1_src loc).
  Proof.
    i.
    destruct (Cell.finite (mem2_tgt loc)).
    rename x into dom.
    destruct (@cap_exists promises mem1_tgt loc).
    rename x into cap.
    cut (exists cell_src,
            sim_cell_aux (latests loc) cap dom (promises loc) cell_src (mem2_tgt loc) /\
            vals_incl_cell cell_src (mem1_src loc)).
    { i. des.
      exists cap. exists cell_src. split; auto.
      inv H1. econs; ii; eauto.
      - destruct msg; eauto.
      - exploit CAP0; eauto. i. des.
        + esplits; eauto.
        + exploit H; eauto. i. ss.
    }
    clear H. induction dom.
    { exists (mem1_src loc). split; try refl.
      exploit cap_cap_cell; eauto. i.
      instantiate (1 := loc) in x0.
      inv SIM. inv x0.
      specialize (MAX loc).
      exploit Memory.max_full_ts_inj; [exact MAX|apply LATEST|..]. i. subst.
      econs; ii; eauto.
      - inv MAX. des. exploit SOUND0; eauto.
      - exploit COMPLETE; eauto. i. des; eauto; ss.
        subst. destruct cap; ss.
        des. inv H1. ss.
      - inv IN.
      - rewrite <- CAP0 in *. des. inv H1.
        inv LATEST. des.
        exploit Cell.max_ts_spec; eauto. i. des.
        eapply TimeFacts.le_lt_lt; eauto.
        apply Time.incr_spec.
      - rewrite <- CAP0 in *. des. inv H1.
        inv LATEST. des.
        destruct (Memory.get loc (Time.incr (Memory.max_ts loc mem1_tgt)) mem1_tgt) as [[]|] eqn:GETT.
        { exploit Memory.max_ts_spec; try exact GETT. i. des.
          specialize (Time.incr_spec (Memory.max_ts loc mem1_tgt)). i.
          timetac. }
        exploit BACK; eauto. i. des.
        esplits; eauto.
        + right. split; ss.
          destruct (Memory.get loc (Time.incr (Memory.max_ts loc mem1_tgt)) mem1_src) as [[]|] eqn:GETS; ss.
          exploit SOUND; eauto. i. congr.
        + destruct (Memory.get loc (Time.incr (Memory.max_ts loc mem1_tgt)) promises) as [[]|] eqn:GETP; ss.
          exploit LE_TGT; eauto. i. congr.
    }
    des. rename a into to.
    destruct (In_decidable time_decidable to dom).
    { exists cell_src. split; auto.
      inv IHdom. econs; ii; eauto; ss.
      - inv IN; eauto.
      - exploit CAP0; eauto. i. des.
        + esplits; eauto.
        + esplits; eauto. right. split; ss.
          ii. des; ss. inv H1. ss.
    }
    destruct (Cell.get to (mem2_tgt loc)) as [[]|] eqn:GETT; cycle 1.
    { exists cell_src. split; auto.
      inv IHdom. econs; ii; eauto; ss.
      - inv IN; eauto. congr.
      - exploit CAP0; eauto. i. des; esplits; eauto.
        right. split; ss.
        ii. des; ss. inv H1. congr.
    }
    destruct (Cell.get to cell_src) as [[]|] eqn:GETS.
    { exists cell_src. split; auto.
      inv IHdom. exploit SOUND; eauto. i.
      rewrite GETT in *. inv x.
      econs; ii; eauto; ss.
      - inv IN; eauto.
        rewrite GET_TGT in *. inv GETT. ss.
      - exploit CAP0; eauto. i. des; esplits; eauto.
        right. split; ss. ii. des; ss.
        inv H1. congr.
    }
    destruct (Cell.get to (promises loc)) as [[]|] eqn:GETP.
    { exists cell_src. split; auto.
      inv IHdom. econs; ii; eauto; ss.
      - inv IN; eauto. congr.
      - exploit CAP0; eauto. i. des; esplits; eauto.
        right. split; ss. ii. des; ss. inv H1. congr.
    }
    destruct (opt_ts_eq_dec cap (Some to)); cycle 1.
    { destruct t0.
      { exists cell_src. split; auto.
        inv IHdom. econs; ii; eauto; ss.
        - inv IN; eauto.
          exploit COMPLETE2; eauto. i. congr.
        - exploit CAP0; eauto. i. des; esplits; eauto.
          right. split; ss. ii. des; ss. inv H1. congr.
      }
      exploit (@Cell.add_exists cell_src t to Message.reserve).
      { ii. inv IHdom.
        exploit SOUND; try exact GET2. i.
        exploit Cell.get_disjoint; [exact GETT|exact x0|..]. i. des.
        - subst. congr.
        - eapply x2; eauto. }
      { exploit Cell.get_ts; try exact GETT. i. des; ss.
        subst. inv CLOSED1_TGT. specialize (INHABITED loc).
        inv CAP. exploit SOUND; try exact INHABITED. i.
        unfold Memory.get in *. rewrite x in *. inv GETT. }
      { econs. }
      i. des.
      exists cell2.
      split; cycle 1.
      { etrans; eauto. ii. revert GET1.
        erewrite Cell.add_o; eauto. condtac; ss; eauto. }
      inv IHdom. econs; ii; eauto; ss.
      - revert LHS.
        erewrite Cell.add_o; eauto. condtac; ss; eauto.
        i. des. subst. inv LHS. ss.
      - erewrite Cell.add_o; eauto. condtac; ss; eauto.
        des. subst. congr.
      - erewrite Cell.add_o; eauto. condtac; ss; eauto.
        des. subst. congr.
      - erewrite Cell.add_o; eauto. condtac; ss; eauto.
        + des; subst; ss.
          rewrite GETT in *. inv GET_TGT. ss.
        + guardH n0. des; eauto. inv IN. unguard. des; ss.
      - exploit CAP0; eauto. i. des; esplits; eauto.
        + left. split; eauto.
          erewrite Cell.add_o; eauto. condtac; ss; eauto.
          des. subst. congr.
        + right. split.
          * ii. des; ss. inv H1; eauto.
          * erewrite Cell.add_o; eauto. condtac; ss.
            des. subst. congr.
    }
    rewrite e in *. des. inv H1.
    exploit cap_cap_cell; eauto. i.
    instantiate (1 := loc) in x0. inv x0.
    exploit BACK; eauto. i. des.
    exploit Cell.max_full_ts_inj; [eapply MAX|exact LATEST|..]. i. subst.
    clear LATEST SOUND MIDDLE BACK COMPLETE.
    unfold Memory.max_ts in *. rewrite GETT in *. inv x0.
    destruct (Cell.get (latests loc) (promises loc)) as [[]|] eqn:LATESTP.
    { exploit LE_TGT; try exact LATESTP. i.
      unfold Memory.get in *. rewrite x in *. inv x0.
      exists cell_src. split; auto.
      inv IHdom. econs; ii; eauto; ss.
      - inv IN; eauto. congr.
      - exploit CAP0; eauto. i. des; esplits; eauto.
        left. inv CAP1. split; eauto.
        unfold cap_src_cell. rewrite LATESTP. ss.
    }
    exploit (@Cell.add_exists cell_src (Cell.max_ts (mem1_tgt loc))
                              (Time.incr (Cell.max_ts (mem1_tgt loc))) (Message.full val released)).
    { ii. inv IHdom. exploit SOUND; try exact GET2. i.
      exploit Memory.get_disjoint; [exact GETT|exact x1|..]. i. des.
      - subst. congr.
      - eapply x3; eauto. }
    { apply Time.incr_spec. }
    { inv CLOSED2_TGT. exploit CLOSED; try exact GETT. i. des. ss. }
    i. des.
    exists cell2.
    split; cycle 1.
    { etrans; eauto. ii. revert GET1.
      erewrite Cell.add_o; eauto. condtac; ss; eauto. i.
      des. subst. inv GET1.
      inv CAP. exploit SOUND; try exact x. i.
      inv IHdom. exploit COMPLETE2; try exact x0; eauto.
      ii. exploit LATESTS; eauto. i. timetac. }
    inv IHdom. econs; ii; eauto; ss.
    - revert LHS.
      erewrite Cell.add_o; eauto. condtac; ss; eauto.
      i. des. subst. inv LHS. ss.
    - erewrite Cell.add_o; eauto. condtac; ss; eauto.
      des. subst. congr.
    - erewrite Cell.add_o; eauto. condtac; ss; eauto.
      des. subst. congr.
    - erewrite Cell.add_o; eauto. condtac; ss.
      + des; subst; ss. congr.
      + guardH n. des; eauto. inv IN. unguard. des; ss.
    - exploit CAP0; eauto. i. des; esplits; eauto.
      + left. split; eauto.
        erewrite Cell.add_o; eauto. condtac; ss; eauto.
        des. subst. ss.
      + left. inv CAP1. split; eauto.
        rewrite GETT in *. inv CAP_TGT.
        unfold cap_src_cell. rewrite LATESTP.
        exploit Cell.add_get0; eauto. i. des. ss.
  Qed.

  Lemma sim_memory_exists
        promises mem1_src mem1_tgt mem2_tgt
        (SIM: PFStep.sim_memory promises mem1_src mem1_tgt)
        (LE_TGT: Memory.le promises mem1_tgt)
        (FINITE_TGT: Memory.finite promises)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (CLOSED2_TGT: Memory.closed mem2_tgt)
        (CAP: Memory.cap promises mem1_tgt mem2_tgt):
    exists latests caps mem2_src,
      sim_memory latests caps promises mem2_src mem2_tgt /\
      vals_incl mem2_src mem1_src.
  Proof.
    exploit Memory.max_full_timemap_exists; try apply CLOSED1_TGT. i. des.
    exists tm.
    cut (exists (caps_mem: Loc.t -> ((option Time.t) * Cell.t)),
            forall loc,
              (fun loc cap_cell =>
                 sim_cell (tm loc) (fst cap_cell) (promises loc) (snd cap_cell) (mem2_tgt loc) /\
                 vals_incl_cell (snd cap_cell) (mem1_src loc))
                loc (caps_mem loc)).
    { i. des.
      exists (fun loc => (fst (caps_mem loc))).
      exists (fun loc => (snd (caps_mem loc))).
      split.
      - econs; ii; eauto.
        + destruct (H loc). inv H0. eauto.
        + destruct (H loc). inv H0. eapply COMPLETE1; eauto.
        + destruct (H loc). inv H0. eauto.
        + destruct (H loc). inv H0.
          exploit LATEST0; eauto.
        + destruct (H loc). inv H0. eauto.
      - ii. destruct (H loc). eauto.
    }
    apply choice. intro loc.
    exploit sim_cell_exists; eauto. i. des.
    instantiate (1 := loc) in x1.
    exists (cap, cell_src). ss.
  Qed.

  Lemma sim_thread_exists
        lang e_src e_tgt
        sc1 mem1_tgt
        (SIM: @PFStep.sim_thread lang e_src e_tgt)
        (WF1_TGT: Local.wf (Thread.local e_tgt) (Thread.memory e_tgt))
        (SC1_TGT: Memory.closed_timemap (Thread.sc e_tgt) (Thread.memory e_tgt))
        (MEM1_TGT: Memory.closed (Thread.memory e_tgt))
        (SC_TGT: Memory.max_full_timemap mem1_tgt sc1)
        (CAP_TGT: Memory.cap (Local.promises (Thread.local e_tgt)) (Thread.memory e_tgt) mem1_tgt):
    exists latests caps mem1_src,
      <<SIM: sim_thread latests caps
                        (Thread.mk lang (Thread.state e_src) (Thread.local e_src) sc1 mem1_src)
                        (Thread.mk lang (Thread.state e_tgt) (Thread.local e_tgt) sc1 mem1_tgt)>> /\
      <<VALS: vals_incl mem1_src (Thread.memory e_src)>>.
  Proof.
    exploit Memory.cap_closed; eauto. i.
    exploit sim_memory_exists; try apply SIM; try apply WF1_TGT; eauto. i. des.
    esplits; eauto.
    econs; eauto.
    - inv SIM. ss.
    - inv SIM. ss.
  Qed.

  Lemma sim_memory_inhabited
        latests caps promises mem_src mem_tgt
        (SIM: sim_memory latests caps promises mem_src mem_tgt)
        (BOT: Memory.bot_none promises)
        (INHABITED_TGT: Memory.inhabited mem_tgt):
    <<INHABITED_SRC: Memory.inhabited mem_src>>.
  Proof.
    inv SIM. ii.
    specialize (BOT loc). specialize (INHABITED_TGT loc).
    exploit COMPLETE2; eauto. ii.
    exploit LATESTS; eauto. i. inv x.
  Qed.

  Lemma sim_memory_bot
        latests caps promises mem_src mem_tgt
        (SIM: sim_memory latests caps promises mem_src mem_tgt)
        (PROMISES: promises = Memory.bot):
    mem_src = mem_tgt.
  Proof.
    inv SIM. apply Memory.ext. i.
    destruct (Memory.get loc ts mem_src) as [[]|] eqn:GETS.
    { exploit SOUND; eauto. }
    destruct (Memory.get loc ts mem_tgt) as [[]|] eqn:GETT; ss.
    destruct (opt_ts_eq_dec (Some ts) (caps loc)).
    - exploit CAPS; eauto. i. des.
      unfold cap_src in *. rewrite Memory.bot_get in *.
      congr.
    - exploit COMPLETE2; eauto; try congr.
      apply Memory.bot_get.
  Qed.
End PFCertify.
