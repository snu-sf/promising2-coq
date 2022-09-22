Require Import RelationClasses.
Require Import Bool.
Require Import List.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.

Require Import Event.
From PromisingLib Require Import DenseOrder.
Require Import Time.
From PromisingLib Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import MemoryDomain.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import MemorySplit.
Require Import MemoryMerge.
Require Import Cover.
Require Import SimMemory.

Set Implicit Arguments.


Module SimPromises.
  Include MemoryDomain.

  Definition none_if_released loc ts (pview:t) (released:option View.t): option View.t :=
    if mem loc ts pview
    then None
    else released.

  Definition none_if loc ts (pview:t) (msg:Message.t): Message.t :=
    match msg with
    | Message.full val released =>
      Message.full val (none_if_released loc ts pview released)
    | Message.reserve => Message.reserve
    end.

  Lemma none_if_bot loc ts msg:
    none_if loc ts bot msg = msg.
  Proof.
    destruct msg; ss.
  Qed.

  Ltac none_if_tac :=
    repeat
      (try match goal with
           | [ |- context[none_if _ _ _ (Message.full ?val ?released)]] =>
             unfold none_if; ss
           | [ |- context[none_if _ _ _ ?msg]] =>
             unfold none_if; destruct msg; ss
           | [ |- context[none_if_released _ _ ?msg]] =>
             unfold none_if_released; condtac; ss
           end).

  Definition mem_le_transf (pview:t) (lhs rhs:Memory.t): Prop :=
    forall loc to from msg
      (LHS: Memory.get loc to lhs = Some (from, msg)),
      Memory.get loc to rhs = Some (from, none_if loc to pview msg).

  Definition kind_transf loc ts (pview:t) (kind:Memory.op_kind): Memory.op_kind :=
    match kind with
    | Memory.op_kind_add => Memory.op_kind_add
    | Memory.op_kind_split ts msg => Memory.op_kind_split ts (none_if loc ts pview msg)
    | Memory.op_kind_lower msg => Memory.op_kind_lower (none_if loc ts pview msg)
    | Memory.op_kind_cancel => Memory.op_kind_cancel
    end.

  Lemma kind_transf_bot loc ts kind:
    kind_transf loc ts bot kind = kind.
  Proof.
    destruct kind; ss; rewrite none_if_bot; ss.
  Qed.

  Inductive sem (pview:t) (inv:t) (promises_src promises_tgt:Memory.t): Prop :=
  | sem_intro
      (LE: mem_le_transf pview promises_tgt promises_src)
      (PVIEW: forall l t (MEM: mem l t pview), exists f val released, Memory.get l t promises_tgt = Some (f, Message.full val released))
      (SOUND: forall l t (INV: mem l t inv),
          Memory.get l t promises_tgt = None /\
          exists f m, Memory.get l t promises_src = Some (f, m))
      (COMPLETE: forall l t f m
                   (SRC: Memory.get l t promises_src = Some (f, m))
                   (TGT: Memory.get l t promises_tgt = None),
          mem l t inv)
  .

  Lemma promise
        pview inv
        loc from to msg
        promises1_src mem1_src
        promises1_tgt mem1_tgt promises2_tgt mem2_tgt
        kind_tgt
        (PROMISE_TGT: Memory.promise promises1_tgt mem1_tgt loc from to msg promises2_tgt mem2_tgt kind_tgt)
        (INV1: sem pview inv promises1_src promises1_tgt)
        (SIM1: sim_memory mem1_src mem1_tgt)
        (LE1_SRC: Memory.le promises1_src mem1_src)
        (LE1_TGT: Memory.le promises1_tgt mem1_tgt)
        (MEM1_SRC: Memory.closed mem1_src)
        (MEM1_TGT: Memory.closed mem1_tgt):
    exists promises2_src mem2_src,
      <<PROMISE_SRC: Memory.promise promises1_src mem1_src loc from to (none_if loc to pview msg) promises2_src mem2_src (kind_transf loc to pview kind_tgt)>> /\
      <<INV2: sem pview inv promises2_src promises2_tgt>> /\
      <<SIM2: sim_memory mem2_src mem2_tgt>>.
  Proof.
    inv PROMISE_TGT.
    - exploit (@Memory.add_exists mem1_src loc from to msg);
        try by inv MEM; inv ADD.
      { eapply covered_disjoint.
        - apply SIM1.
        - inv MEM. inv ADD. auto. }
      i. des.
      exploit Memory.add_exists_le; try apply LE1_SRC; eauto. i. des.
      exploit sim_memory_add; try apply SIM1; try refl; eauto. i.
      esplits; eauto.
      + none_if_tac.
        * inv INV1. exploit PVIEW; eauto. intro x. des.
          hexploit Memory.add_get0; try exact PROMISES; eauto. i. des. congr.
        * econs 1; eauto; try congr.
          i. exploit sim_memory_get_inv; try exact GET; eauto.
          { apply MEM1_SRC. }
          { apply MEM1_TGT. }
          i. des. inv FROM; cycle 1.
          { inv H. eauto. }
          exploit Memory.add_get0; try exact MEM. i. des.
          exploit Memory.add_get1; try exact GET_TGT; eauto. i.
          exploit Memory.get_ts; try exact GET1. i. des.
          { subst. inv H. }
          exploit Memory.get_ts; try exact x3. i. des.
          { subst. inv TO; inv H0.
            exploit Memory.get_ts; try exact GET. i. des; timetac. inv x5. }
          exploit Memory.get_disjoint; [exact GET1|exact x3|..]. i. des.
          { subst. congr. }
          apply (x6 to); econs; ss; try refl.
          exploit Memory.get_ts; try exact GET. i. des.
          { subst. eauto. }
          { etrans; eauto. econs. ss. }
        * econs 1; eauto; ss.
          i. exploit RESERVE; eauto. i. des.
          inv SIM1. exploit MSG; eauto. i. des. inv MSG0. eauto.
      + econs.
        * ii. erewrite Memory.add_o; eauto.
          erewrite (@Memory.add_o promises2_tgt) in LHS; try exact PROMISES. revert LHS.
          condtac; ss.
          { i. des. inv LHS. none_if_tac.
            inv INV1. exploit PVIEW; eauto. i. des.
            exploit Memory.add_get0; try exact PROMISES; eauto. i. des. congr. }
          { apply INV1. }
        * i. inv INV1. exploit PVIEW; eauto. i. des.
          erewrite Memory.add_o; eauto. condtac; eauto.
          ss. des. subst. exploit LE; eauto. intro x.
          inv x1. inv ADD. exfalso.
          eapply DISJOINT; eauto; econs; eauto; try refl. ss.
          exploit Memory.get_ts; try eapply x. i. des; ss.
          subst. inv TO.
        * i. inv INV1. exploit SOUND; eauto. i.
          erewrite Memory.add_o; eauto. erewrite (@Memory.add_o promises2); eauto.
          condtac; ss. des. subst.
          exploit Memory.add_get0; eauto. i. des. congr.
        * i. revert SRC TGT.
          erewrite Memory.add_o; eauto. erewrite (@Memory.add_o promises2_tgt); eauto.
          condtac; ss. inv INV1. eapply COMPLETE; eauto.
    - exploit Memory.split_get0; try exact PROMISES; eauto. i. des.
      exploit (@Memory.split_exists promises1_src loc from to ts3 msg (none_if loc ts3 pview msg3));
        try by inv PROMISES; inv SPLIT.
      { apply INV1. eauto. }
      i. des.
      exploit Memory.split_exists_le; try apply LE1_SRC; eauto. i. des.
      exploit sim_memory_split; try apply SIM1; try refl; eauto. i.
      esplits; eauto.
      + unfold none_if. destruct msg; ss.
        unfold none_if_released. condtac; ss.
        * inv INV1. exploit PVIEW; eauto. intro x. des.
          hexploit Memory.split_get0; try exact PROMISES; eauto. congr.
        * econs 2; eauto; congr.
      + econs.
        * ii. revert LHS.
          erewrite Memory.split_o; eauto. erewrite (@Memory.split_o mem2); try exact x0.
          repeat condtac; ss.
          { i. des. inv LHS. none_if_tac.
            inv INV1. exploit PVIEW; eauto. i. des.
            exploit Memory.split_get0; try exact PROMISES; eauto. congr. }
          { guardH o. i. des. inv LHS. ss. }
          { apply INV1. }
        * i. inv INV1. exploit PVIEW; eauto. intro x. des.
          erewrite Memory.split_o; eauto. repeat condtac; eauto.
          des; ss. subst. rewrite GET0 in x. inv x. eauto.
        * i. inv INV1. exploit SOUND; eauto. i.
          erewrite Memory.split_o; eauto. erewrite (@Memory.split_o mem2); eauto.
          exploit Memory.split_get0; try exact x0; eauto. i. des.
          repeat condtac; ss.
          { des. subst. congr. }
          { guardH o. des. subst. congr. }
          esplits; eauto.
        * i. revert SRC TGT.
          erewrite Memory.split_o; eauto. erewrite (@Memory.split_o promises2_tgt); eauto.
          repeat condtac; ss. inv INV1. eapply COMPLETE; eauto.
    - exploit Memory.lower_get0; try exact PROMISES; eauto. i. des.
      exploit (@Memory.lower_exists promises1_src loc from to (none_if loc to pview msg0) (none_if loc to pview msg));
        try by inv MEM; inv LOWER.
      { apply INV1. eauto. }
      { none_if_tac; econs; ss.
        inv MEM. inv LOWER. inv MSG_WF. ss. }
      { none_if_tac; destruct msg0; ss.
        - inv MEM. inv LOWER. inv MSG_LE. econs. refl.
        - inv PROMISES. inv MSG_LE. }
      i. des.
      exploit Memory.lower_exists_le; try apply LE1_SRC; eauto. i. des.
      exploit sim_memory_lower; try exact SIM1; try exact x1; try exact x2; eauto.
      { none_if_tac; try refl. econs. econs. }
      i. esplits; eauto.
      + econs 3; eauto.
        * none_if_tac; viewtac. econs. viewtac.
        * subst. ss. esplits; eauto.
      + econs.
        * ii. revert LHS.
          erewrite Memory.lower_o; eauto. erewrite (@Memory.lower_o mem2); try exact x0.
          condtac; ss.
          { i. des. inv LHS. ss. }
          { apply INV1. }
        * i. inv INV1. exploit PVIEW; eauto. intro x. des.
          erewrite Memory.lower_o; eauto. condtac; eauto.
          des. ss. subst. rewrite GET in x. inv x.
          inv MSG_LE. esplits; eauto.
        * i. inv INV1. exploit SOUND; eauto. i.
          erewrite Memory.lower_o; eauto. erewrite (@Memory.lower_o mem2); eauto.
          exploit Memory.lower_get0; try exact x1; eauto. i. des.
          condtac; ss.
          { des. subst. congr. }
          esplits; eauto.
        * i. revert SRC TGT.
          erewrite Memory.lower_o; eauto. erewrite (@Memory.lower_o promises2_tgt); eauto.
          repeat condtac; ss. inv INV1. eapply COMPLETE; eauto.
    - exploit Memory.remove_get0; try exact PROMISES. i. des.
      exploit (@Memory.remove_exists promises1_src loc from to Message.reserve).
      { inv INV1. exploit LE; eauto. }
      i. des.
      exploit (@Memory.remove_exists mem1_src loc from to Message.reserve).
      { inv INV1. exploit LE; eauto. }
      i. des.
      exploit sim_memory_remove; try exact SIM1; eauto. i.
      esplits; try exact x2; eauto.
      inv INV1. econs; ii.
      + erewrite Memory.remove_o in LHS; eauto.
        erewrite Memory.remove_o; eauto.
        condtac; ss. eauto.
      + exploit PVIEW; eauto. i. des.
        erewrite Memory.remove_o; eauto. condtac; ss; eauto.
        des. subst. congr.
      + exploit SOUND; eauto. i. des. split.
        * erewrite Memory.remove_o; eauto. condtac; ss; eauto.
        * erewrite Memory.remove_o; eauto. condtac; ss; eauto.
          des. subst. congr.
      + erewrite Memory.remove_o in SRC; eauto.
        erewrite Memory.remove_o in TGT; eauto.
        des_ifs. eauto.
  Qed.

  Lemma promise_bot
        inv
        loc from to msg
        promises1_src mem1_src
        promises1_tgt mem1_tgt promises2_tgt mem2_tgt
        kind
        (PROMISE_TGT: Memory.promise promises1_tgt mem1_tgt loc from to msg promises2_tgt mem2_tgt kind)
        (INV1: sem bot inv promises1_src promises1_tgt)
        (SIM1: sim_memory mem1_src mem1_tgt)
        (LE1_SRC: Memory.le promises1_src mem1_src)
        (LE1_TGT: Memory.le promises1_tgt mem1_tgt)
        (MEM1_SRC: Memory.closed mem1_src)
        (MEM1_TGT: Memory.closed mem1_tgt):
    exists promises2_src mem2_src,
      <<PROMISE_SRC: Memory.promise promises1_src mem1_src loc from to msg promises2_src mem2_src kind>> /\
      <<INV2: sem bot inv promises2_src promises2_tgt>> /\
      <<SIM2: sim_memory mem2_src mem2_tgt>>.
  Proof.
    exploit promise; eauto. i. des.
    rewrite none_if_bot in *.
    rewrite kind_transf_bot in *.
    esplits; eauto.
  Qed.

  Lemma remove_tgt
        pview inv
        loc from to msg
        promises1_src mem1_src
        promises1_tgt mem1_tgt promises2_tgt
        (REMOVE_TGT: Memory.remove promises1_tgt loc from to msg promises2_tgt)
        (INV1: sem pview inv promises1_src promises1_tgt)
        (SIM1: sim_memory mem1_src mem1_tgt)
        (LE1_SRC: Memory.le promises1_src mem1_src)
        (LE1_TGT: Memory.le promises1_tgt mem1_tgt)
        (FINITE1_TGT: Memory.finite promises1_tgt):
      <<INV2: sem (unset loc to pview) (set loc to inv) promises1_src promises2_tgt>> /\
      <<INV2': mem loc to inv = false>>.
  Proof.
    hexploit Memory.remove_future; eauto. i. des.
    exploit Memory.remove_get0; [eauto|]. i. des.
    inv INV1. exploit LE0; eauto. i.
    esplits.
    - econs.
      + ii. revert LHS.
        erewrite Memory.remove_o; eauto. condtac; ss. i.
        exploit LE0; eauto.
        unfold none_if, none_if_released. repeat condtac; ss.
        * revert COND1. rewrite unset_o. condtac; ss; [|congr].
          guardH o. des. subst. unguardH o. des; congr.
        * revert COND1. rewrite unset_o. condtac; ss. congr.
      + i. revert MEM. rewrite unset_o. condtac; ss. guardH o. i.
        exploit PVIEW; eauto. i. des.
        erewrite Memory.remove_o; eauto. condtac; ss; eauto.
        des. subst. unguardH o. des; congr.
      + i. erewrite Memory.remove_o; eauto.
        revert INV. rewrite set_o.
        unfold Time.t, DOSet.elt. condtac; ss; i.
        * des. subst. esplits; eauto.
        * exploit SOUND; eauto.
      + i. revert TGT.
        erewrite Memory.remove_o; eauto. rewrite set_o.
        unfold Time.t, DOSet.elt. condtac; ss; i.
        eapply COMPLETE; eauto.
    - destruct (mem loc to inv) eqn:X; auto.
      exploit SOUND; [eauto|]. i. des. congr.
  Qed.

  Lemma remove_src
        pview inv
        loc from to msg
        promises1_src mem1_src
        promises1_tgt mem1_tgt
        (INV1: sem pview inv promises1_src promises1_tgt)
        (INV1': mem loc to inv)
        (SIM1: sim_memory mem1_src mem1_tgt)
        (GET: Memory.get loc to promises1_src = Some (from, msg))
        (LE1_SRC: Memory.le promises1_src mem1_src)
        (LE1_TGT: Memory.le promises1_tgt mem1_tgt):
    exists promises2_src,
      <<REMOVE_SRC: Memory.remove promises1_src loc from to msg promises2_src>> /\
      <<INV2: sem pview (unset loc to inv) promises2_src promises1_tgt>>.
  Proof.
    inv INV1.
    exploit Memory.remove_exists; eauto. i. des.
    esplits; eauto.
    econs.
    - ii. revert LHS.
      erewrite (@Memory.remove_o mem2); eauto. condtac; ss; eauto.
      des. subst. exploit SOUND; eauto. i. des. congr.
    - i. exploit PVIEW; eauto.
    - i. rewrite unset_o in INV. revert INV. condtac; ss.
      guardH o.
      i. exploit SOUND; eauto. i. des. splits; eauto.
      erewrite Memory.remove_o; eauto. condtac; ss; eauto.
      des. subst. unguardH o. des; congr.
    - i. revert SRC.
      erewrite Memory.remove_o; eauto. rewrite unset_o.
      unfold Time.t, DOSet.elt. condtac; ss; i.
      eapply COMPLETE; eauto.
  Qed.

  Lemma remove
        pview inv
        loc from to msg
        promises1_src mem1_src
        promises1_tgt mem1_tgt promises2_tgt
        (MSG_WF: Message.wf msg)
        (TIME: Time.lt from to)
        (REMOVE_TGT: Memory.remove promises1_tgt loc from to msg promises2_tgt)
        (INV1: sem pview inv promises1_src promises1_tgt)
        (SIM1: sim_memory mem1_src mem1_tgt)
        (LE1_SRC: Memory.le promises1_src mem1_src)
        (LE1_TGT: Memory.le promises1_tgt mem1_tgt)
        (FINITE1_TGT: Memory.finite promises1_tgt):
    exists promises2_src,
      <<REMOVE_SRC: Memory.remove promises1_src loc from to (none_if loc to pview msg) promises2_src>> /\
      <<INV2: sem (unset loc to pview) inv promises2_src promises2_tgt>>.
  Proof.
    hexploit Memory.remove_future; try apply REMOVE_TGT; eauto. i. des.
    exploit remove_tgt; eauto. i. des.
    exploit Memory.remove_get0; eauto. i. des.
    inv INV1. exploit LE0; eauto. i.
    exploit remove_src; try apply set_eq; eauto. i. des.
    esplits; eauto.
    rewrite unset_set in INV0; auto.
  Qed.

  Lemma remove_bot
        inv
        loc from to msg
        promises1_src mem1_src
        promises1_tgt mem1_tgt promises2_tgt
        (MSG_WF: Message.wf msg)
        (TIME: Time.lt from to)
        (REMOVE_TGT: Memory.remove promises1_tgt loc from to msg promises2_tgt)
        (INV1: sem bot inv promises1_src promises1_tgt)
        (SIM1: sim_memory mem1_src mem1_tgt)
        (LE1_SRC: Memory.le promises1_src mem1_src)
        (LE1_TGT: Memory.le promises1_tgt mem1_tgt)
        (FINITE1_TGT: Memory.finite promises1_tgt):
    exists promises2_src,
      <<REMOVE_SRC: Memory.remove promises1_src loc from to msg promises2_src>> /\
      <<INV2: sem bot inv promises2_src promises2_tgt>>.
  Proof.
    exploit remove; eauto. i. des.
    rewrite none_if_bot in *.
    esplits; eauto.
    replace bot with (unset loc to bot); ss. apply ext. i.
    rewrite unset_o. condtac; ss.
  Qed.

  Lemma sem_bot promises:
    sem bot bot promises promises.
  Proof.
    econs.
    - ii. rewrite none_if_bot. ss.
    - i. revert MEM. rewrite bot_spec. congr.
    - i. inv INV.
    - i. congr.
  Qed.

  Lemma sem_bot_inv
        promises_src promises_tgt
        (SEM: sem bot bot promises_src promises_tgt):
    promises_src = promises_tgt.
  Proof.
    apply Memory.ext. i.
    destruct (Memory.get loc ts promises_tgt) as [[? []]|] eqn:X.
    - inv SEM. exploit LE; eauto.
    - destruct (Memory.get loc ts promises_src) as [[? []]|] eqn:Y.
      + inv SEM. exploit LE; eauto. s. i. congr.
      + inv SEM. exploit LE; eauto. s. i. congr.
      + inv SEM. exploit LE; eauto. s. i. congr.
    - destruct (Memory.get loc ts promises_src) as [[? []]|] eqn:Y.
      + inv SEM. exploit COMPLETE; eauto. intro x. inv x.
      + inv SEM. exploit COMPLETE; eauto. intro x. inv x.
      + ss.
  Qed.


  Lemma latest_reserve
        pview
        promises_src mem_src
        promises_tgt mem_tgt
        loc
        (INV: sem pview bot promises_src promises_tgt)
        (MEM: sim_memory mem_src mem_tgt)
        (MEM_SRC: Memory.closed mem_src)
        (MEM_TGT: Memory.closed mem_tgt):
    Memory.latest_reserve loc promises_src mem_src <->
    Memory.latest_reserve loc promises_tgt mem_tgt.
  Proof.
    inv INV. unfold Memory.latest_reserve.
    split; i.
    - erewrite <- sim_memory_max_ts; eauto. des_ifs.
      + exploit LE; eauto. i. ss. congr.
      + exploit LE; eauto. i. ss. congr.
    - erewrite sim_memory_max_ts; eauto. des_ifs.
      + exploit LE; eauto. i. ss. congr.
      + exploit COMPLETE; eauto.
  Qed.

  Lemma cap_get_src
        pview
        promises_src mem1_src mem2_src
        promises_tgt mem1_tgt mem2_tgt
        loc from to msg
        (INV1: sem pview bot promises_src promises_tgt)
        (MEM1: sim_memory mem1_src mem1_tgt)
        (CAP_SRC: Memory.cap promises_src mem1_src mem2_src)
        (CAP_TGT: Memory.cap promises_tgt mem1_tgt mem2_tgt)
        (MEM1_SRC: Memory.closed mem1_src)
        (MEM1_TGT: Memory.closed mem1_tgt)
        (GET1_SRC: Memory.get loc to mem1_src = None)
        (GET2_SRC: Memory.get loc to mem2_src = Some (from, msg)):
    <<GET1_TGT: Memory.get loc to mem1_tgt = None>> /\
    <<GET2_TGT: Memory.get loc to mem2_tgt = Some (from, msg)>>.
  Proof.
    exploit Memory.cap_inv; try exact CAP_SRC; eauto. i. des; try congr.
    - subst.
      exploit sim_memory_adjacent_src; try exact x1; eauto. i. des.
      inv CAP_TGT. exploit MIDDLE; eauto. i. splits; auto.
      inv x3. apply EMPTY; eauto. refl.
    - subst.
      erewrite sim_memory_max_ts; eauto.
      rewrite latest_reserve in *; eauto.
      exploit sim_memory_latest_val_src; eauto. i.
      exploit Memory.max_full_view_exists; try apply MEM1_TGT. i. des.
      exploit sim_memory_max_full_view; try exact MEM1; eauto. i. subst.
      inv CAP_TGT. exploit BACK; eauto. i. splits; auto.
      destruct (Memory.get loc (Time.incr (Memory.max_ts loc mem1_tgt)) mem1_tgt) as [[]|] eqn:MAX; ss.
      exploit Memory.max_ts_spec; eauto. i. des.
      specialize (Time.incr_spec (Memory.max_ts loc mem1_tgt)). i. timetac.
  Qed.

  Lemma cap_get_tgt
        pview
        promises_src mem1_src mem2_src
        promises_tgt mem1_tgt mem2_tgt
        loc from to msg
        (INV1: sem pview bot promises_src promises_tgt)
        (MEM1: sim_memory mem1_src mem1_tgt)
        (CAP_SRC: Memory.cap promises_src mem1_src mem2_src)
        (CAP_TGT: Memory.cap promises_tgt mem1_tgt mem2_tgt)
        (MEM1_SRC: Memory.closed mem1_src)
        (MEM1_TGT: Memory.closed mem1_tgt)
        (GET1_TGT: Memory.get loc to mem1_tgt = None)
        (GET2_TGT: Memory.get loc to mem2_tgt = Some (from, msg)):
    <<GET1_SRC: Memory.get loc to mem1_src = None>> /\
    <<GET2_SRC: Memory.get loc to mem2_src = Some (from, msg)>>.
  Proof.
    exploit Memory.cap_inv; try exact CAP_TGT; eauto. i. des; try congr.
    - subst.
      exploit sim_memory_adjacent_tgt; try exact x1; eauto. i. des.
      inv CAP_SRC. exploit MIDDLE; eauto. i. splits; auto.
      inv x3. apply EMPTY; eauto. refl.
    - subst.
      erewrite <- sim_memory_max_ts; eauto.
      rewrite <- latest_reserve in *; eauto.
      exploit sim_memory_latest_val_tgt; eauto. i.
      exploit Memory.max_full_view_exists; try apply MEM1_SRC. i. des.
      exploit sim_memory_max_full_view; try exact MEM1; eauto. i. subst.
      inv CAP_SRC. exploit BACK; eauto. i. splits; auto.
      destruct (Memory.get loc (Time.incr (Memory.max_ts loc mem1_src)) mem1_src) as [[]|] eqn:MAX; ss.
      exploit Memory.max_ts_spec; eauto. i. des.
      specialize (Time.incr_spec (Memory.max_ts loc mem1_src)). i. timetac.
  Qed.

  Lemma cap
        pview
        lc_src mem1_src mem2_src
        lc_tgt mem1_tgt
        (INV1: sem pview bot (Local.promises lc_src) (Local.promises lc_tgt))
        (MEM1: sim_memory mem1_src mem1_tgt)
        (CAP_SRC: Memory.cap (Local.promises lc_src) mem1_src mem2_src)
        (MEM1_SRC: Memory.closed mem1_src)
        (MEM1_TGT: Memory.closed mem1_tgt):
    exists mem2_tgt,
      <<MEM2: sim_memory mem2_src mem2_tgt>> /\
      <<CAP_TGT: Memory.cap (Local.promises lc_tgt) mem1_tgt mem2_tgt>>.
  Proof.
    exploit Memory.cap_exists; try exact MEM1_TGT; eauto. i. des.
    esplits; eauto.
    rename mem2 into mem2_tgt. econs; i; try split; i.
    - inv H.
      destruct (Memory.get loc to mem1_src) as [[]|] eqn:GET1.
      + inv CAP_SRC. exploit SOUND; eauto. intro x.
        rewrite x in GET. inv GET.
        eapply cap_cover; eauto.
        inv MEM1. rewrite <- COVER.
        econs; eauto.
      + exploit cap_get_src; eauto. i. des.
        econs; eauto.
    - inv H.
      destruct (Memory.get loc to mem1_tgt) as [[]|] eqn:GET1.
      + inv CAP. exploit SOUND; eauto. intro x.
        rewrite x in GET. inv GET.
        eapply cap_cover; eauto.
        inv MEM1. rewrite COVER.
        econs; eauto.
      + exploit cap_get_tgt; eauto. i. des.
        econs; eauto.
    - destruct (Memory.get loc to mem1_tgt) as [[]|] eqn:GET1.
      + inv CAP. exploit SOUND; eauto. intro x.
        rewrite x in GET. inv GET.
        inv MEM1. exploit MSG; eauto. i. des.
        inv CAP_SRC. exploit SOUND; eauto. i.
        esplits; eauto.
      + exploit cap_get_tgt; eauto. i. des.
        esplits; eauto. refl.
    - destruct (Memory.get loc to mem1_src) as [[]|] eqn:GET1.
      + inv CAP_SRC. exploit SOUND; eauto. intro x.
        rewrite x in H. inv H.
        inv MEM1. rewrite RESERVE in GET1.
        inv CAP. exploit SOUND0; eauto.
      + exploit cap_get_src; eauto. i. des. auto.
    - destruct (Memory.get loc to mem1_tgt) as [[]|] eqn:GET1.
      + inv CAP. exploit SOUND; eauto. intro x.
        rewrite x in H. inv H.
        inv MEM1. rewrite <- RESERVE in GET1.
        inv CAP_SRC. exploit SOUND0; eauto.
      + exploit cap_get_tgt; eauto. i. des. auto.
  Qed.
End SimPromises.
