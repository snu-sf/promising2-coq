Require Import Omega.
Require Import RelationClasses.

From sflib Require Import sflib.

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

Set Implicit Arguments.


Module AMemory.
  Inductive promise
            (promises1 mem1:Memory.t)
            (loc:Loc.t) (from to:Time.t) (msg:Message.t)
            (promises2 mem2:Memory.t): forall (kind:Memory.op_kind), Prop :=
  | promise_add
      (PROMISES: Memory.add promises1 loc from to msg promises2)
      (MEM: Memory.add mem1 loc from to msg mem2)
      (TS: Memory.message_to msg loc to)
      (RESERVE: msg = Message.reserve ->
             exists from' val' released',
               Memory.get loc from mem1 = Some (from', Message.full val' released')):
      promise promises1 mem1 loc from to msg promises2 mem2 Memory.op_kind_add
  | promise_split
      ts3 msg3
      (PROMISES: Memory.split promises1 loc from to ts3 msg msg3 promises2)
      (MEM: Memory.split mem1 loc from to ts3 msg msg3 mem2)
      (TS: Memory.message_to msg loc to)
      (RESERVE: exists val' released', msg = Message.full val' released'):
      promise promises1 mem1 loc from to msg promises2 mem2 (Memory.op_kind_split ts3 msg3)
  | promise_lower
      msg0
      (PROMISES: Memory.lower promises1 loc from to msg0 msg promises2)
      (MEM: Memory.lower mem1 loc from to msg0 msg mem2)
      (TS: Memory.message_to msg loc to)
      (RESERVE: exists val released, msg0 = Message.full val released):
      promise promises1 mem1 loc from to msg promises2 mem2 (Memory.op_kind_lower msg0)
  | promise_cancel
      (PROMISES: Memory.remove promises1 loc from to msg promises2)
      (MEM: Memory.remove mem1 loc from to msg mem2)
      (RESERVE: msg = Message.reserve):
      promise promises1 mem1 loc from to msg promises2 mem2 Memory.op_kind_cancel
  .
  Hint Constructors promise.

  Inductive write
            (promises1 mem1:Memory.t)
            (loc:Loc.t) (from1 to1:Time.t) (val:Const.t) (released: option View.t)
            (promises3 mem2:Memory.t) (kind:Memory.op_kind): Prop :=
  | write_intro
      promises2
      (PROMISE: promise promises1 mem1 loc from1 to1 (Message.full val released) promises2 mem2 kind)
      (REMOVE: Memory.remove promises2 loc from1 to1 (Message.full val released) promises3)
  .
  Hint Constructors write.


  (* Lemmas on op *)

  Lemma promise_op
        promises1 mem1 loc from to msg promises2 mem2 kind
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind):
    Memory.op mem1 loc from to msg mem2 kind.
  Proof.
    inv PROMISE.
    - econs 1. ss.
    - econs 2. ss.
    - econs 3. ss.
    - econs 4; ss.
  Qed.

  Lemma promise_op_promise
        promises1 mem1 loc from to msg promises2 mem2 kind
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind):
    Memory.op promises1 loc from to msg promises2 kind.
  Proof.
    inv PROMISE.
    - econs 1. ss.
    - econs 2. ss.
    - econs 3. ss.
    - econs 4; ss.
  Qed.


  (* Lemmas on closedness *)

  Lemma promise_closed_timemap
        times
        promises1 mem1 loc from to msg promises2 mem2 kind
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (CLOSED: Memory.closed_timemap times mem1):
    Memory.closed_timemap times mem2.
  Proof.
    eapply Memory.op_closed_timemap; eauto.
    eapply promise_op. eauto.
  Qed.

  Lemma promise_closed_view
        view
        promises1 mem1 loc from to msg promises2 mem2 kind
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (CLOSED: Memory.closed_view view mem1):
    Memory.closed_view view mem2.
  Proof.
    eapply Memory.op_closed_view; eauto.
    eapply promise_op. eauto.
  Qed.

  Lemma promise_closed_opt_view
        view
        promises1 mem1 loc from to msg promises2 mem2 kind
        (CLOSED: Memory.closed_opt_view view mem1)
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind):
    Memory.closed_opt_view view mem2.
  Proof.
    inv CLOSED; econs. eapply promise_closed_view; eauto.
  Qed.


  (* reserve_wf *)

  Lemma promise_reserve_wf
        promises1 mem1 loc from to msg promises2 mem2 kind
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (RESERVE1: Memory.reserve_wf promises1 mem1):
    <<RESERVE2: Memory.reserve_wf promises2 mem2>>.
  Proof.
    inv PROMISE; ii; revert GET.
    - erewrite Memory.add_o; eauto. condtac; ss; i.
      + des. subst. inv GET.
        exploit RESERVE; eauto. i. des.
        exploit Memory.add_get1; try exact x; eauto.
      + guardH o.
        exploit RESERVE1; eauto. i. des.
        exploit Memory.add_get1; try exact x; eauto.
    - erewrite Memory.split_o; eauto. repeat condtac; ss; i.
      + des. subst. inv GET.
      + guardH o. des. subst. inv GET.
        exploit Memory.split_get0; try exact MEM. i. des. eauto.
      + guardH o. guardH o0.
        exploit RESERVE1; eauto. i. des.
        exploit Memory.split_get1; try exact x; eauto. i. des. eauto.
    - erewrite Memory.lower_o; eauto. condtac; ss; i.
      + des. subst. inv GET.
        exploit Memory.lower_get0; try exact PROMISES. i. des. inv MSG_LE.
      + guardH o.
        exploit RESERVE1; eauto. i. des.
        exploit Memory.lower_get1; try exact x; eauto. i. des.
        inv MSG_LE. eauto.
    - erewrite Memory.remove_o; eauto. condtac; ss. i.
      guardH o.
      exploit RESERVE1; eauto. i. des.
      erewrite Memory.remove_o; eauto. condtac; ss; eauto.
      des. subst.
      exploit Memory.remove_get0; try exact MEM. i. des. congr.
  Qed.


  (* Lemmas on promise & remove *)

  Lemma promise_get0
        promises1 promises2 mem1 mem2
        loc from to msg kind
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (KIND: Memory.op_kind_is_cancel kind = false):
    <<GET_PROMISES: Memory.get loc to promises2 = Some (from, msg)>> /\
    <<GET_MEM: Memory.get loc to mem2 = Some (from, msg)>>.
  Proof.
    inv PROMISE; ss.
    - erewrite (Memory.add_o _ _ PROMISES).
      erewrite (Memory.add_o _ _ MEM).
      condtac; ss. des; congr.
    - erewrite (Memory.split_o _ _ PROMISES).
      erewrite (Memory.split_o _ _ MEM).
      repeat condtac; ss; des; intuition.
    - erewrite (Memory.lower_o _ _ PROMISES).
      erewrite (Memory.lower_o _ _ MEM).
      condtac; ss. des; congr.
  Qed.

  Lemma promise_get1
        promises1 mem1 loc from to msg promises2 mem2 kind
        l t f m
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (KIND: Memory.op_kind_is_cancel kind = false)
        (GET: Memory.get l t mem1 = Some (f, m)):
    exists f' m',
      <<GET: Memory.get l t mem2 = Some (f', m')>> /\
      <<FROM: Time.le f f'>> /\
      <<MSG_LE: Message.le m' m>>.
  Proof.
    inv PROMISE; ss.
    - eapply Memory.op_get1; eauto.
    - eapply Memory.op_get1; eauto.
    - eapply Memory.op_get1; eauto.
  Qed.

  Lemma promise_get1_promise
        promises1 mem1 loc from to msg promises2 mem2 kind
        l t f m
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (KIND: Memory.op_kind_is_cancel kind = false)
        (GET: Memory.get l t promises1 = Some (f, m)):
    exists f' m',
      <<GET: Memory.get l t promises2 = Some (f', m')>> /\
      <<FROM: Time.le f f'>> /\
      <<MSG_LE: Message.le m' m>>.
  Proof.
    inv PROMISE; eapply Memory.op_get1; eauto.
  Qed.

  Lemma promise_get2
        promises1 mem1 loc from to msg promises2 mem2 kind
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (KIND: Memory.op_kind_is_cancel kind = false):
    <<GET_PROMISE: Memory.get loc to promises2 = Some (from, msg)>> /\
    <<GET_MEM: Memory.get loc to mem2 = Some (from, msg)>>.
  Proof.
    inv PROMISE; splits; eauto using Memory.op_get2.
  Qed.

  Lemma promise_le
        promises1 mem1 loc from to msg promises2 mem2 kind
        (LE_PROMISES1: Memory.le promises1 mem1)
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind):
    <<LE_PROMISES2: Memory.le promises2 mem2>>.
  Proof.
    inv PROMISE.
    - ii. revert LHS.
      erewrite Memory.add_o; eauto.
      erewrite (@Memory.add_o mem2); try exact MEM; eauto.
      condtac; ss. auto.
    - ii. revert LHS.
      erewrite Memory.split_o; eauto.
      erewrite (@Memory.split_o mem2); try exact MEM; eauto.
      repeat condtac; ss. auto.
    - ii. revert LHS.
      erewrite Memory.lower_o; eauto.
      erewrite (@Memory.lower_o mem2); try exact MEM; eauto.
      condtac; ss. auto.
    - ii. revert LHS.
      erewrite Memory.remove_o; eauto.
      erewrite (@Memory.remove_o mem2); try exact MEM; eauto.
      condtac; ss. auto.
  Qed.

  Lemma promise_future
        promises1 mem1 loc from to msg promises2 mem2 kind
        (LE_PROMISES1: Memory.le promises1 mem1)
        (FINITE1: Memory.finite promises1)
        (BOT1: Memory.bot_none promises1)
        (RESERVE1: Memory.reserve_wf promises1 mem1)
        (CLOSED1: Memory.closed mem1)
        (MSG_CLOSED: Memory.closed_message msg mem2)
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind):
    <<LE_PROMISES2: Memory.le promises2 mem2>> /\
    <<FINITE2: Memory.finite promises2>> /\
    <<BOT2: Memory.bot_none promises2>> /\
    <<RESERVE2: Memory.reserve_wf promises2 mem2>> /\
    <<CLOSED2: Memory.closed mem2>> /\
    <<FUTURE: Memory.future mem1 mem2>>.
  Proof.
    hexploit promise_le; eauto. i. des.
    hexploit Memory.op_inhabited; try apply CLOSED1.
    { eapply promise_op. eauto. }
    hexploit Memory.op_finite; eauto.
    { eapply promise_op_promise. eauto. }
    hexploit Memory.op_future; eauto.
    { eapply promise_op. eauto. }
    { by inv PROMISE. }
    i. des.
    hexploit promise_reserve_wf; eauto. i. des.
    splits; auto.
    inv PROMISE.
    - eapply Memory.add_bot_none; eauto.
    - eapply Memory.split_bot_none; eauto.
    - eapply Memory.lower_bot_none; eauto.
    - eapply Memory.cancel_bot_none; eauto.
  Qed.

  Lemma promise_disjoint
        promises1 mem1 loc from to msg promises2 mem2 ctx kind
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (LE_CTX: Memory.le ctx mem1)
        (RESERVE_CTX: Memory.reserve_wf ctx mem1)
        (DISJOINT: Memory.disjoint promises1 ctx):
    <<DISJOINT: Memory.disjoint promises2 ctx>> /\
    <<LE_CTX: Memory.le ctx mem2>> /\
    <<RESERVE_CTX: Memory.reserve_wf ctx mem2>>.
  Proof.
    inv PROMISE.
    - splits.
      + inv DISJOINT. econs. i. revert GET1. erewrite Memory.add_o; eauto. condtac; ss.
        * des. subst. i. inv GET1. splits.
          { inv MEM. inv ADD. eauto. }
          { ii. inv H. inv MEM. inv ADD. inv TO. }
        * i. eapply DISJOINT0; eauto.
      + ii. erewrite Memory.add_o; eauto. condtac; ss; eauto.
        des. subst. exfalso. inv MEM. inv ADD. eapply DISJOINT0; eauto.
        * apply Interval.mem_ub. auto.
        * apply Interval.mem_ub.
          destruct (Cell.WF (mem1 loc)). exploit VOLUME; eauto. i. des; auto.
          inv x. inv TO.
      + ii. exploit RESERVE_CTX; eauto. i. des.
        exploit Memory.add_get1; try exact x; eauto.
    - splits.
      + inv DISJOINT. econs. i. revert GET1. erewrite Memory.split_o; eauto. repeat condtac; ss.
        * des. subst. i. inv GET1.
          exploit Memory.split_get0; try exact PROMISES; eauto. i. des.
          exploit DISJOINT0; try exact GET0; eauto. i. des.
          splits.
          { eapply Interval.le_disjoint; eauto. econs; [refl|].
            left. inv MEM. inv SPLIT. auto.
          }
          { ii. inv H. inv MEM. inv SPLIT. inv TS12. }
        * guardH o. des. subst. i. inv GET1.
          exploit Memory.split_get0; try exact PROMISES; eauto. i. des.
          exploit DISJOINT0; try exact GET0; eauto. i. des.
          splits.
          { eapply Interval.le_disjoint; eauto. econs; [|refl].
            left. inv MEM. inv SPLIT. auto.
          }
          { ii. inv H. inv MEM. inv SPLIT. inv TS23. }
        * i. eapply DISJOINT0; eauto.
      + ii. erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
        * des. subst. exfalso. inv DISJOINT. exploit DISJOINT0; eauto.
          { hexploit Memory.split_get0; try exact PROMISES; eauto. i. des. eauto. }
          i. des. eapply x.
          { inv MEM. inv SPLIT. econs. eauto. left. auto. }
          { apply Interval.mem_ub.
            destruct (Cell.WF (mem1 loc)). exploit VOLUME; eauto. i. des; auto.
            inv x1. inv MEM. inv SPLIT. inv TS12.
          }
        * guardH o. des. subst. exfalso. inv DISJOINT. exploit DISJOINT0; eauto.
          { hexploit Memory.split_get0; try exact PROMISES; eauto. i. des. eauto. }
          i. des. eapply x.
          { apply Interval.mem_ub. inv MEM. inv SPLIT. etrans; eauto. }
          { apply Interval.mem_ub.
            destruct (Cell.WF (ctx loc)). exploit VOLUME; eauto. i. des; auto.
            inv x1. inv MEM. inv SPLIT. inv TS23.
          }
      + ii. exploit RESERVE_CTX; eauto. i. des.
        exploit Memory.split_get1; try exact x; eauto. i. des. eauto.
    - splits.
      + inv DISJOINT. econs. i. revert GET1. erewrite Memory.lower_o; eauto. condtac; ss.
        * des. subst. i. inv GET1. eapply DISJOINT0; eauto.
          hexploit Memory.lower_get0; try eapply PROMISES; eauto. i. des. eauto.
        * i. eapply DISJOINT0; eauto.
      + ii. erewrite Memory.lower_o; eauto. condtac; ss; eauto.
        des. subst. exfalso. eapply Memory.disjoint_get; eauto.
        hexploit Memory.lower_get0; try exact PROMISES; eauto. i. des. eauto.
      + ii. exploit RESERVE_CTX; eauto. i. des.
        exploit Memory.lower_get1; try exact x; eauto. i. des.
        inv MSG_LE. eauto.
    - splits.
      + inv DISJOINT. econs. i. revert GET1. erewrite Memory.remove_o; eauto. condtac; ss.
        des. subst. i. inv GET1. eapply DISJOINT0; eauto.
        hexploit Memory.remove_get0; try eapply PROMISES; eauto.
      + ii. erewrite Memory.remove_o; eauto. condtac; ss; eauto.
        des. subst. exfalso. eapply Memory.disjoint_get; eauto.
        hexploit Memory.remove_get0; try exact PROMISES; eauto. i. des. eauto.
      + ii. exploit RESERVE_CTX; eauto. i. des.
        destruct (Memory.get loc0 from0 mem2) as [[]|] eqn:GET2.
        * revert GET2. erewrite Memory.remove_o; eauto. condtac; ss. i.
          rewrite GET2 in *. inv x. eauto.
        * exploit Memory.remove_get0; try exact MEM. i. des.
          revert GET2. erewrite Memory.remove_o; eauto. condtac; ss; try congr.
          des. subst. congr.
  Qed.

  Lemma write_get2
        promises1 mem1 loc from to val released promises2 mem2 kind
        (WRITE: write promises1 mem1 loc from to val released promises2 mem2 kind):
    <<GET_PROMISE: Memory.get loc to promises2 = None>> /\
    <<GET_MEM: Memory.get loc to mem2 = Some (from, Message.full val released)>>.
  Proof.
    inv WRITE. splits.
    - erewrite Memory.remove_o; eauto. condtac; ss. des; ss.
    - eapply promise_get2; eauto. inv PROMISE; ss.
  Qed.

  Lemma write_future
        promises1 mem1 loc from to val released promises2 mem2 kind
        (WRITE: write promises1 mem1 loc from to val released promises2 mem2 kind)
        (CLOSED: Memory.closed mem1)
        (MSG_CLOSED: Memory.closed_message (Message.full val released) mem2)
        (LE: Memory.le promises1 mem1)
        (FINITE: Memory.finite promises1)
        (BOT: Memory.bot_none promises1)
        (RESERVE: Memory.reserve_wf promises1 mem1):
    <<CLOSED: Memory.closed mem2>> /\
    <<LE: Memory.le promises2 mem2>> /\
    <<FINITE: Memory.finite promises2>> /\
    <<BOT: Memory.bot_none promises2>> /\
    <<RESERVE: Memory.reserve_wf promises2 mem2>> /\
    <<FUTURE: Memory.future mem1 mem2>>.
  Proof.
    inv WRITE.
    hexploit promise_future; eauto. i. des.
    hexploit Memory.remove_future; eauto. i. des.
    splits; auto.
    - ii. erewrite Memory.remove_o; eauto. condtac; ss.
    - ii. revert GET.
      erewrite Memory.remove_o; eauto. condtac; ss.
      i. exploit RESERVE2; eauto.
  Qed.

  Lemma write_disjoint
        promises1 mem1 loc from to val released promises2 mem2 ctx kind
        (WRITE: write promises1 mem1 loc from to val released promises2 mem2 kind)
        (DISJOINT: Memory.disjoint promises1 ctx)
        (LE_CTX: Memory.le ctx mem1)
        (RESERVE_CTX: Memory.reserve_wf ctx mem1):
    <<DISJOINT: Memory.disjoint promises2 ctx>> /\
    <<LE_CTX: Memory.le ctx mem2>> /\
    <<RESERVE_CTX: Memory.reserve_wf ctx mem2>>.
  Proof.
    inv WRITE.
    hexploit promise_disjoint; try apply PROMISE; eauto. i. des.
    hexploit Memory.remove_disjoint; try apply REMOVE; eauto.
  Qed.

  Lemma bot_write_bot
        promises1 mem1 loc from to val released promises2 mem2 kind
        (WRITE: write promises1 mem1 loc from to val released promises2 mem2 kind)
        (PROMISES: promises1 = Memory.bot):
    promises2 = Memory.bot.
  Proof.
    subst. inv WRITE. inv PROMISE.
    - apply Memory.ext. i.
      exploit Memory.add_get0; try exact PROMISES. i. des.
      exploit Memory.remove_get0; eauto. i. des.
      erewrite Memory.remove_o; eauto. condtac; ss.
      + des. subst. ss.
      + erewrite Memory.add_o; eauto. condtac; ss.
    - exploit Memory.split_get0; try exact PROMISES. i. des.
      rewrite Memory.bot_get in *. ss.
    - exploit Memory.lower_get0; try exact PROMISES. i. des.
      rewrite Memory.bot_get in *. ss.
    - exploit Memory.remove_get0; try exact PROMISES. i. des.
      rewrite Memory.bot_get in *. ss.
  Qed.


  (* no_reserve *)

  Lemma promise_no_reserve_except
        promises1 promises2 mem1 mem2
        loc from to msg kind
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (RESERVE1: Memory.reserve_wf promises1 mem1)
        (NORESERVE1: Memory.no_reserve_except promises1 mem1):
    Memory.no_reserve_except promises2 mem2.
  Proof.
    ii. inv PROMISE.
    - erewrite Memory.add_o; try exact PROMISES.
      erewrite Memory.add_o in GET; try exact MEM.
      condtac; eauto.
      guardH o.
      exploit Memory.max_ts_spec; try exact GET. i. des.
      exploit Memory.add_get1; try exact GET0; eauto. i.
      exploit Memory.max_ts_spec; try exact x0. i. des.
      exploit TimeFacts.antisym; eauto. i.
      rewrite <- x1 in *. eauto.
    - erewrite Memory.split_o; try exact PROMISES.
      erewrite Memory.split_o in GET; try exact MEM.
      repeat condtac; eauto.
      guardH o. guardH o0.
      exploit Memory.max_ts_spec; try exact GET. i. des.
      exploit Memory.split_get1; try exact GET0; eauto. i. des.
      exploit Memory.max_ts_spec; try exact GET2. i. des.
      exploit TimeFacts.antisym; eauto. i.
      rewrite <- x0 in *. eauto.
    - erewrite Memory.lower_o; try exact PROMISES.
      erewrite Memory.lower_o in GET; try exact MEM.
      condtac; eauto.
      guardH o.
      exploit Memory.max_ts_spec; try exact GET. i. des.
      exploit Memory.lower_get1; try exact GET0; eauto. i. des.
      exploit Memory.max_ts_spec; try exact GET2. i. des.
      exploit TimeFacts.antisym; eauto. i.
      rewrite <- x0 in *. eauto.
    - erewrite Memory.remove_o; eauto.
      erewrite Memory.remove_o in GET; try exact MEM.
      condtac; ss.
      guardH o.
      destruct (Loc.eq_dec loc0 loc); cycle 1.
      { cut (Memory.max_ts loc0 mem2 = Memory.max_ts loc0 mem1).
        { i. rewrite H in *. eapply NORESERVE1; eauto. }
        exploit Memory.max_ts_spec; try exact GET. i. des.
        destruct (Memory.get loc0 (Memory.max_ts loc0 mem1) mem2) as [[]|] eqn:GET2.
        - exploit Memory.max_ts_spec; try exact GET2. i. des.
          apply TimeFacts.antisym; auto.
        - revert GET2. erewrite Memory.remove_o; eauto. condtac; ss; i.
          + des. subst. ss.
          + congr.
      }
      subst. unguard. des; ss. clear COND.
      exploit Memory.max_ts_spec; eauto. i. des. inv MAX; cycle 1.
      { inv H. rewrite H1 in *. eapply NORESERVE1; eauto. }
      destruct (Memory.get loc (Memory.max_ts loc mem1) mem2) as [[]|] eqn:GET2.
      { exploit Memory.max_ts_spec; try exact GET2. i. des. timetac. }
      revert GET2. erewrite Memory.remove_o; eauto.
      condtac; ss; try congr. des. subst.
      i. clear COND GET2 a.
      exploit Memory.remove_get0; try exact MEM. i. des.
      rewrite GET0 in *. inv GET1.
      exploit RESERVE1; eauto. i. des.
      cut (from = Memory.max_ts loc mem2); try congr.
      exploit Memory.get_ts; try exact GET0. i. des.
      { subst. rewrite x0 in *. congr. }
      destruct (Memory.get loc from mem2) as [[]|] eqn:GETF; cycle 1.
      { revert GETF. erewrite Memory.remove_o; eauto. condtac; ss.
        - des. subst. rewrite GET0 in x. inv x.
        - congr. }
      exploit Memory.max_ts_spec; try exact GETF. i. des.
      inv MAX; eauto.
      revert GET1. erewrite Memory.remove_o; eauto. condtac; ss. i.
      clear o0 COND.
      exploit Memory.get_ts; try exact GET1. i. des.
      { subst. rewrite x0 in *. inv H0. }
      exploit Memory.get_disjoint; [exact GET0|exact GET1|..]. i. des; try congr.
      exfalso.
      apply (x3 (Memory.max_ts loc mem2)); econs; ss; try refl.
      econs. ss.
  Qed.
End AMemory.
