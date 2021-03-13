Require Import Omega.
Require Import RelationClasses.

From Paco Require Import paco.
From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
Require Import Time.
Require Import Event.
From PromisingLib Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import Cover.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.
Require Import APromiseConsistent.
From PromisingLib Require Import Loc.

Require Import APF.
Require Import Race.
Require Import Behavior.
Require Import SimMemory.
Require Import yjtac.
Require Import Program.
Require Import Cell.
Require Import Time.
(* Require Import PredStep. *)
Require Import ReorderPromises2.

Require Import Pred.
Require Import PredStep.
Require Import AMemory.
Require Import ALocal.
Require Import AThread.
Require Import APredStep.
Require Import APFPF.

Require Import ADRF_PF0.
Require Import ADRF_PF1.

Require Import PFConsistent.

Set Implicit Arguments.


Section CANCEL.

  Inductive only_reserves (proms: Memory.t): Prop :=
  | only_reserves_intro
      (RESERVES: forall loc to from msg (GET: Memory.get loc to proms = Some (from, msg)),
          msg = Message.reserve)
      (FINITE: Memory.finite proms)
  .

  Lemma areserves_cancelable lang st vw proms0 sc mem0
        (FINITE: Memory.finite proms0)
        (MLE: Memory.le proms0 mem0)
    :
      exists proms1 mem1,
        (<<STEPS: rtc (tau (@pred_step is_cancel lang))
                      (Thread.mk lang st (Local.mk vw proms0) sc mem0)
                      (Thread.mk lang st (Local.mk vw proms1) sc mem1)>>) /\
        (<<NORESERVES: no_reserves proms1>>).
  Proof.
    assert (exists dom,
               (<<COMPLETE: forall loc to,
                   (exists from, (<<GET: Memory.get loc to proms0 = Some (from, Message.reserve)>>))
                   <-> (<<IN: List.In (loc, to) dom>>)>>)).
    { unfold Memory.finite in *. des.
      generalize (list_filter_exists (fun locto =>
                                        match locto with
                                        | (loc, to) =>
                                          exists from, Memory.get loc to proms0 = Some (from, Message.reserve)
                                        end) dom).
      i. des. exists l'. split; i.
      - eapply COMPLETE. des. esplits; eauto.
      - eapply COMPLETE in H. des. esplits; eauto. }
    des. ginduction dom; ss; i.
    - exists proms0, mem0. esplits; eauto.
      ii. clarify. eapply COMPLETE. eauto.
    - destruct a as [loc to].
      exploit (proj2 (COMPLETE loc to)); eauto. i. des.
      destruct (classic (List.In (loc, to) dom)).
      { exploit IHdom; eauto. i. split; i.
        - des. exploit (proj1 (COMPLETE loc0 to0)); eauto.
          i. des; clarify.
        - exploit (proj2 (COMPLETE loc0 to0)); eauto. }
      exploit Memory.remove_exists; eauto.
      intros [prom1 REMOVE0].
      exploit Memory.remove_exists.
      { eapply MLE. eapply GET. }
      intros [mem1 REMOVE1]. hexploit IHdom.
      * instantiate (1:=prom1).
        eapply Memory.remove_finite; eauto.
      * instantiate (1:=mem1).
        ii. erewrite Memory.remove_o in LHS; eauto. des_ifs.
        eapply MLE in LHS. erewrite Memory.remove_o; eauto. des_ifs.
        ss. des; clarify.
      * i. split; i.
        { des. erewrite Memory.remove_o in GET0; eauto. des_ifs.
          exploit (proj1 (COMPLETE loc0 to0)); eauto. i. des; clarify. }
        { exploit (proj2 (COMPLETE loc0 to0)); eauto. i. des; clarify.
          exists from0. erewrite Memory.remove_o; eauto. des_ifs.
          ss. des; clarify. }
      * i. des. exists proms1, mem2. split; eauto.
        econs 2.
        { econs.
          - instantiate (2:=ThreadEvent.promise loc from to Message.reserve Memory.op_kind_cancel).
            econs; ss. econs. econs 1. econs; ss.
            econs; ss. econs; eauto.
          - eauto. }
        { eauto. }
  Qed.

  Lemma reserves_cancelable lang st vw proms0 sc mem0
        (FINITE: Memory.finite proms0)
        (MLE: Memory.le proms0 mem0)
    :
      exists proms1 mem1,
        (<<STEPS: rtc (tau (@PredStep.pred_step is_cancel lang))
                      (Thread.mk lang st (Local.mk vw proms0) sc mem0)
                      (Thread.mk lang st (Local.mk vw proms1) sc mem1)>>) /\
        (<<NORESERVES: no_reserves proms1>>).
  Proof.
    assert (exists dom,
               (<<COMPLETE: forall loc to,
                   (exists from, (<<GET: Memory.get loc to proms0 = Some (from, Message.reserve)>>))
                   <-> (<<IN: List.In (loc, to) dom>>)>>)).
    { unfold Memory.finite in *. des.
      generalize (list_filter_exists (fun locto =>
                                        match locto with
                                        | (loc, to) =>
                                          exists from, Memory.get loc to proms0 = Some (from, Message.reserve)
                                        end) dom).
      i. des. exists l'. split; i.
      - eapply COMPLETE. des. esplits; eauto.
      - eapply COMPLETE in H. des. esplits; eauto. }
    des. ginduction dom; ss; i.
    - exists proms0, mem0. esplits; eauto.
      ii. clarify. eapply COMPLETE. eauto.
    - destruct a as [loc to].
      exploit (proj2 (COMPLETE loc to)); eauto. i. des.
      destruct (classic (List.In (loc, to) dom)).
      { exploit IHdom; eauto. i. split; i.
        - des. exploit (proj1 (COMPLETE loc0 to0)); eauto.
          i. des; clarify.
        - exploit (proj2 (COMPLETE loc0 to0)); eauto. }
      exploit Memory.remove_exists; eauto.
      intros [prom1 REMOVE0].
      exploit Memory.remove_exists.
      { eapply MLE. eapply GET. }
      intros [mem1 REMOVE1]. hexploit IHdom.
      * instantiate (1:=prom1).
        eapply Memory.remove_finite; eauto.
      * instantiate (1:=mem1).
        ii. erewrite Memory.remove_o in LHS; eauto. des_ifs.
        eapply MLE in LHS. erewrite Memory.remove_o; eauto. des_ifs.
        ss. des; clarify.
      * i. split; i.
        { des. erewrite Memory.remove_o in GET0; eauto. des_ifs.
          exploit (proj1 (COMPLETE loc0 to0)); eauto. i. des; clarify. }
        { exploit (proj2 (COMPLETE loc0 to0)); eauto. i. des; clarify.
          exists from0. erewrite Memory.remove_o; eauto. des_ifs.
          ss. des; clarify. }
      * i. des. exists proms1, mem2. split; eauto.
        econs 2.
        { econs.
          - instantiate (2:=ThreadEvent.promise loc from to Message.reserve Memory.op_kind_cancel).
            econs; ss. econs. econs 1. econs; ss.
            econs; ss. econs; eauto.
          - eauto. }
        { eauto. }
  Qed.

  Lemma promise_not_cacncel_reserves_same prom0 mem0 loc from to msg prom1 mem1 kind
        (PROM: AMemory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
        (NOTCANCEL: kind <> Memory.op_kind_cancel)
        loc0 to0 from0
        (GET: Memory.get loc0 to0 prom0 = Some (from0, Message.reserve))
    :
      exists from1,
        Memory.get loc0 to0 prom1 = Some (from1, Message.reserve).
  Proof.
    inv PROM.
    - eapply Memory.add_get1 in GET; eauto.
    - des. clarify. erewrite Memory.split_o; eauto.
      dup PROMISES. eapply Memory.split_get0 in PROMISES0.
      eapply split_succeed_wf in PROMISES. des. des_ifs.
      + ss. des. clarify.
      + ss. guardH o. des. clarify.
        esplits; eauto.
      + esplits; eauto.
    - des. clarify. erewrite Memory.lower_o; eauto. des_ifs.
      + ss. des. clarify.
        eapply lower_succeed_wf in PROMISES. des. clarify.
      + esplits; eauto.
    - clarify.
  Qed.

  Lemma remove_not_cacncel_reserves_same prom0 loc from to val released prom1
        (REMOVE: Memory.remove prom0 loc from to (Message.full val released) prom1)
        loc0 to0 from0
        (GET: Memory.get loc0 to0 prom0 = Some (from0, Message.reserve))
    :
      exists from1,
        Memory.get loc0 to0 prom1 = Some (from1, Message.reserve).
  Proof.
    dup REMOVE. eapply Memory.remove_get0 in REMOVE. des.
    eapply Memory.remove_o in REMOVE0.
    instantiate (1:=to0) in REMOVE0.
    instantiate (1:=loc0) in REMOVE0. des_ifs.
    - ss. des. clarify.
    - esplits. etrans; eauto.
  Qed.

  Lemma step_not_cancel_reserves_same P lang e th0 th1
        (STEPS: (@pred_step P lang) e th0 th1)
        (PRED: P <1= (promise_free /1\ (fun e => ~ is_cancel e)))
        loc to from
        (GET: Memory.get loc to (Local.promises (Thread.local th0)) = Some (from, Message.reserve))
    :
      exists from',
        Memory.get loc to (Local.promises (Thread.local th1)) = Some (from', Message.reserve).
  Proof.
    inv STEPS. eapply PRED in SAT. inv STEP. inv STEP0.
    - inv STEP. des. ss. inv LOCAL.
      eapply promise_not_cacncel_reserves_same; eauto.
      ii. clarify.
    - inv STEP. inv LOCAL; ss.
      + esplits; eauto.
      + inv LOCAL0. esplits; eauto.
      + inv LOCAL0. inv WRITE. ss.
        eapply promise_not_cacncel_reserves_same in GET; cycle 1; eauto.
        { ii. clarify. inv PROMISE. clarify. } des.
        eapply remove_not_cacncel_reserves_same in GET; cycle 1; eauto.
      + inv LOCAL2. inv WRITE. ss. inv LOCAL1. ss.
        eapply promise_not_cacncel_reserves_same in GET; cycle 1; eauto.
        { ii. clarify. inv PROMISE. clarify. } des.
        eapply remove_not_cacncel_reserves_same in GET; cycle 1; eauto.
      + inv LOCAL0. esplits; eauto.
      + inv LOCAL0. esplits; eauto.
      + inv LOCAL0. esplits; eauto.
  Qed.

  Lemma steps_not_cancel_reserves_same P lang th0 th1
        (STEPS: rtc (tau (@pred_step P lang)) th0 th1)
        (PRED: P <1= (promise_free /1\ (fun e => ~ is_cancel e)))
        loc to from
        (GET: Memory.get loc to (Local.promises (Thread.local th0)) = Some (from, Message.reserve))
    :
      exists from',
        Memory.get loc to (Local.promises (Thread.local th1)) = Some (from', Message.reserve).
  Proof.
    ginduction STEPS; i.
    - esplits; eauto.
    - inv H. exploit step_not_cancel_reserves_same; eauto. i. des.
      exploit IHSTEPS; eauto.
  Qed.

  Lemma cancel_memory_decrease P lang e th0 th1
        (STEP: (@pred_step P lang) e th0 th1)
        (PRED: P <1= is_cancel)
    :
      Memory.le (Thread.memory th1) (Thread.memory th0).
  Proof.
    inv STEP. eapply PRED in SAT. unfold is_cancel in SAT. des_ifs.
    inv STEP0. inv STEP; inv STEP0; ss.
    - inv LOCAL. inv PROMISE; ss.
      ii. erewrite Memory.remove_o in LHS; eauto. des_ifs.
    - inv LOCAL.
  Qed.

  Lemma cancels_memory_decrease P lang th0 th1
        (STEP: rtc (tau (@pred_step P lang)) th0 th1)
        (PRED: P <1= is_cancel)
    :
      Memory.le (Thread.memory th1) (Thread.memory th0).
  Proof.
    ginduction STEP.
    - refl.
    - etrans; eauto. inv H.
      eapply cancel_memory_decrease; eauto.
  Qed.

  Lemma cancel_concrete_same P lang e th0 th1
        (STEP: (@pred_step P lang) e th0 th1)
        (PRED: P <1= is_cancel)
    :
      memory_concrete_le (Thread.memory th0) (Thread.memory th1).
  Proof.
    inv STEP. eapply PRED in SAT. unfold is_cancel in SAT. des_ifs.
    inv STEP0. inv STEP; inv STEP0; ss.
    - inv LOCAL. inv PROMISE; ss.
      ii. erewrite Memory.remove_o; eauto. des_ifs.
      ss. des. clarify.
      eapply Memory.remove_get0 in MEM. des. clarify.
    - inv LOCAL.
  Qed.

  Lemma cancels_concrete_same P lang th0 th1
        (STEP: rtc (tau (@pred_step P lang)) th0 th1)
        (PRED: P <1= is_cancel)
    :
      memory_concrete_le (Thread.memory th0) (Thread.memory th1).
  Proof.
    ginduction STEP.
    - refl.
    - etrans; eauto. inv H.
      eapply cancel_concrete_same; eauto.
  Qed.

  Lemma cancel_promises_decrease P lang e th0 th1
        (STEP: (@pred_step P lang) e th0 th1)
        (PRED: P <1= is_cancel)
    :
      Memory.le (Local.promises (Thread.local th1)) (Local.promises (Thread.local th0)).
  Proof.
    inv STEP. eapply PRED in SAT. unfold is_cancel in SAT. des_ifs.
    inv STEP0. inv STEP; inv STEP0; ss.
    - inv LOCAL. inv PROMISE; ss.
      ii. erewrite Memory.remove_o in LHS; eauto. des_ifs.
    - inv LOCAL.
  Qed.

  Lemma cancels_promises_decrease P lang th0 th1
        (STEP: rtc (tau (@pred_step P lang)) th0 th1)
        (PRED: P <1= is_cancel)
    :
      Memory.le (Local.promises (Thread.local th1)) (Local.promises (Thread.local th0)).
  Proof.
    ginduction STEP.
    - refl.
    - etrans; eauto. inv H.
      eapply cancel_promises_decrease; eauto.
  Qed.

  Lemma nacancel_promises_decrease P lang e th0 th1
        (STEP: (@PredStep.pred_step P lang) e th0 th1)
        (PRED: P <1= is_cancel)
    :
      Memory.le (Local.promises (Thread.local th1)) (Local.promises (Thread.local th0)).
  Proof.
    inv STEP. eapply PRED in SAT. unfold is_cancel in SAT. des_ifs.
    inv STEP0. inv STEP; inv STEP0; ss.
    - inv LOCAL. inv PROMISE; ss.
      ii. erewrite Memory.remove_o in LHS; eauto. des_ifs.
    - inv LOCAL.
  Qed.

  Lemma nacancels_promises_decrease P lang th0 th1
        (STEP: rtc (tau (@PredStep.pred_step P lang)) th0 th1)
        (PRED: P <1= is_cancel)
    :
      Memory.le (Local.promises (Thread.local th1)) (Local.promises (Thread.local th0)).
  Proof.
    ginduction STEP.
    - refl.
    - etrans; eauto. inv H.
      eapply nacancel_promises_decrease; eauto.
  Qed.

  Lemma cancel_remove_only P lang e th0 th1
        (STEP: (@pred_step P lang) e th0 th1)
        (PRED: P <1= is_cancel)
        loc from to msg
        (GET: Memory.get loc to (Local.promises (Thread.local th0)) = Some (from, msg))
        (NONE: Memory.get loc to (Local.promises (Thread.local th1)) = None)
    :
      (<<GET: Memory.get loc to (Thread.memory th0) = Some (from, msg)>>) /\
      (<<NONE: Memory.get loc to (Thread.memory th1) = None>>) /\
      (<<RESERVE: msg = Message.reserve>>).
  Proof.
    inv STEP. eapply PRED in SAT. unfold is_cancel in SAT. des_ifs.
    inv STEP0. inv STEP; inv STEP0; ss.
    - inv LOCAL. inv PROMISE; ss.
      dup NONE. erewrite Memory.remove_o in NONE; eauto. des_ifs. ss. clarify.
      dup MEM. eapply Memory.remove_get0 in MEM.
      dup PROMISES. eapply Memory.remove_get0 in PROMISES. des. clarify.
    - inv LOCAL.
  Qed.

  Lemma cancels_remove_only P lang th0 th1
        (STEP: rtc (tau (@pred_step P lang)) th0 th1)
        (PRED: P <1= is_cancel)
        loc from to msg
        (GET: Memory.get loc to (Local.promises (Thread.local th0)) = Some (from, msg))
        (NONE: Memory.get loc to (Local.promises (Thread.local th1)) = None)
    :
      (<<GET: Memory.get loc to (Thread.memory th0) = Some (from, msg)>>) /\
      (<<NONE: Memory.get loc to (Thread.memory th1) = None>>) /\
      (<<RESERVE: msg = Message.reserve>>).
  Proof.
    ginduction STEP.
    - i. clarify.
    - i. inv H.
      destruct (Memory.get loc to (Local.promises (Thread.local y))) eqn:GET0; auto.
      + destruct p. dup GET0.
        eapply cancel_promises_decrease in GET1; eauto.  clarify.
        exploit IHSTEP; eauto. i. des. splits; auto.
        eapply cancel_memory_decrease; eauto.
      + exploit cancel_remove_only; eauto. i. des.
        splits; auto.
        eapply cancels_memory_decrease in STEP; eauto.
        eapply memory_le_get_none; eauto.
  Qed.

End CANCEL.

Section CAP.

  Definition caps (mem0 mem1 : Memory.t) (l : Loc.t) (t from : Time.t) (msg : Message.t) :=
    (<<GET0: Memory.get l t mem0 = None>>) /\
    (<<GET1: Memory.get l t mem1 = Some (from, msg)>>).

  Definition caps_loc (mem0 mem1 : Memory.t) (l : Loc.t) (t : Time.t): Prop :=
    exists from msg, (<<CAPS: caps mem0 mem1 l t from msg>>).

  Lemma caps_unchangable mem0 prom mem1
        (MLE: Memory.le prom mem0)
        (CAP: Memory.cap prom mem0 mem1)
    :
      caps mem0 mem1 <4= unchangable mem1 prom.
  Proof.
    i. unfold caps in PR. des. inv CAP.
    econs; eauto. destruct (Memory.get x0 x1 prom) eqn:GET; auto.
    destruct p. exfalso. eapply MLE in GET. clarify.
  Qed.

  Lemma caps_concrete_last mem0 prom mem1 tm l t from val released
        (RESERVE: Memory.reserve_wf prom mem0)
        (INHABITED: Memory.inhabited mem0)
        (MAX: Memory.max_full_timemap mem0 tm)
        (CAP: Memory.cap prom mem0 mem1)
        (CAPS: caps mem0 mem1 l t from (Message.full val released))
    :
      from = Memory.max_ts l mem0.
  Proof.
    unfold caps in CAPS. des. inv CAP.
    exploit COMPLETE; eauto. i. des.
    destruct (classic (Memory.max_ts l mem0 = from)); eauto. exfalso.
    set (@cell_elements_least
           (mem0 l)
           (fun to => Time.lt from to)). des.
    + assert (TLE: Time.le from from0).
      { dup GET. eapply Memory.get_ts in GET. des; clarify.
        { exfalso. eapply Time.lt_strorder.
          eapply TimeFacts.lt_le_lt; eauto. eapply Time.bot_spec. }
        exploit memory_get_from_mon.
        - eapply x.
        - eapply GET2.
        - eauto.
        - i. des; clarify. }
      destruct TLE.
      * exploit MIDDLE; eauto.
        econs.
        { eapply x. }
        { eapply GET. }
        { eauto. }
        { i. destruct (Memory.get l ts mem0) eqn: GET2; auto.
          destruct p. exfalso. dup GET2. eapply LEAST in GET2; eauto.
          eapply Memory.get_ts in GET. des; clarify.
          - eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
            eapply SAT. eapply Time.bot_spec.
          - eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
            eapply GET. etrans; eauto. }
        { i. exploit memory_get_from_inj.
          - eapply x1.
          - eapply GET1.
          - i. des; clarify. eapply Time.lt_strorder; eauto. }
      * destruct H0.
        exploit memory_get_from_inj.
        { eapply GET1. }
        { eapply SOUND. eapply GET. }
        { i. des; clarify.
          - unfold Memory.get in GET0. clarify.
          - eapply Time.lt_strorder; eauto. }
    + exploit Memory.max_ts_spec.
      { eapply x. } i. des.
      eapply EMPTY; eauto. destruct MAX0; clarify.
      exfalso. eauto.
  Qed.

  Lemma caps_max_view mem0 prom mem1 tm l t from val released
        (RESERVE: Memory.reserve_wf prom mem0)
        (INHABITED: Memory.inhabited mem0)
        (MAX: Memory.max_full_timemap mem0 tm)
        (CAP: Memory.cap prom mem0 mem1)
        (CAPS: caps mem0 mem1 l t from (Message.full val released))
    :
      (<<FROM: from = Memory.max_ts l mem0>>) /\
      (<<RESERVE: Memory.latest_reserve l prom mem0>>) /\
      (<<VAL: Memory.latest_val l mem0 val >>) /\
      (<<RELEASED: released = Some (View.mk tm tm)>>) /\
      (<<TO: t = Time.incr (Memory.max_ts l mem0)>>).
  Proof.
    exploit caps_concrete_last; eauto. i. clarify.
    unfold caps in CAPS. des. inv CAP.
    exploit COMPLETE; eauto. i. des.
    exploit Memory.latest_val_exists; eauto. i. des.
    exploit BACK; eauto. i.
    exploit memory_get_from_inj.
    { eapply x1. }
    { eapply GET1. } i. des; clarify.
    - esplits; eauto.
    - exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
      + eapply Time.incr_spec.
      + erewrite BOT0. eapply Time.bot_spec.
    - erewrite INHABITED in GET0. clarify.
  Qed.

End CAP.

Section PROMISEFREE.

  Lemma promise_free_no_promise P lang (th0 th1: Thread.t lang) e
        (NOPROMISE: (Local.promises (Thread.local th0)) = Memory.bot)
        (STEP: pred_step P e th0 th1)
        (PRED: P <1= promise_free)
  :
    (<<STEP: pred_step P e th0 th1>>) /\
    (<<NOPROMISE: (Local.promises (Thread.local th1)) = Memory.bot>>).
  Proof.
    inv STEP. dup SAT. eapply PRED in SAT. inv STEP0. inv STEP.
    - inv STEP0. inv LOCAL. inv PROMISE; ss; des; clarify.
      + rewrite NOPROMISE in *.
        eapply Memory.lower_get0 in PROMISES. des.
        erewrite Memory.bot_get in *. clarify.
      + rewrite NOPROMISE in *.
        eapply Memory.remove_get0 in PROMISES. des.
        erewrite Memory.bot_get in *. clarify.
    - inv STEP0. inv LOCAL.
      + ss. esplits; eauto. econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
      + ss. esplits; eauto.
        * econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
        * inv LOCAL0. ss.
      + ss. esplits; eauto.
        * econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
        * inv LOCAL0. rewrite NOPROMISE in *.
          exploit memory_write_bot_add; eauto. i. clarify.
          inv WRITE. inv PROMISE. ss.
          symmetry. eapply MemoryMerge.MemoryMerge.add_remove; eauto.
      + ss. esplits; eauto.
        * econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
        * inv LOCAL1. inv LOCAL2. rewrite NOPROMISE in *.
          exploit memory_write_bot_add; eauto. i. clarify.
          inv WRITE. inv PROMISE. ss.
          symmetry. eapply MemoryMerge.MemoryMerge.add_remove; eauto.
      + ss. esplits; eauto.
        * econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
        * inv LOCAL0. ss.
      + ss. esplits; eauto.
        * econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
        * inv LOCAL0. ss.
      + ss. esplits; eauto.
        * econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
  Qed.

  Lemma write_promises_decrease prom0 mem0 loc from to val realeased prom1 mem1 kind
        (WRITE: AMemory.write prom0 mem0 loc from to val realeased prom1 mem1 kind)
    :
      concrete_promised prom1 <2= concrete_promised prom0.
  Proof.
    inv WRITE. inv PROMISE.
    - exploit MemoryMerge.MemoryMerge.add_remove.
      + eapply PROMISES.
      + eapply REMOVE.
      + i. clarify.
    - ii. inv PR.
      erewrite Memory.remove_o in GET; eauto. des_ifs.
      erewrite Memory.split_o in GET; eauto. des_ifs.
      + ss; des; clarify.
      + ss. des; clarify. eapply Memory.split_get0 in PROMISES.
        des. econs; eauto.
      + eapply Memory.split_get0 in PROMISES.
        guardH o. guardH o0. guardH o1. des. econs; eauto.
    - ii. inv PR.
      erewrite Memory.remove_o in GET; eauto. des_ifs.
      erewrite Memory.lower_o in GET; eauto. des_ifs.
      + ss; des; clarify.
      + econs; eauto.
    - clarify.
  Qed.

  Lemma pf_step_promises_decrease P lang e (th0 th1: Thread.t lang)
        (STEP: (@pred_step P lang) e th0 th1)
        (PRED: P <1= promise_free)
    :
      concrete_promised ((Local.promises (Thread.local th1))) <2=
      concrete_promised ((Local.promises (Thread.local th0))).
  Proof.
    i. inv STEP. eapply PRED in SAT. inv STEP0. des. inv STEP.
    - inv STEP0. ss. inv LOCAL. ss. inv PROMISE; clarify.
      + inv PR. erewrite Memory.lower_o in GET; eauto. des_ifs.
        * ss; des. clarify. eapply Memory.lower_get0 in PROMISES.
          des. econs; eauto.
        * econs; eauto.
      + inv PR. erewrite Memory.remove_o in GET; eauto. des_ifs.
        econs; eauto.
    - inv STEP0. ss. inv LOCAL; eauto.
      + inv LOCAL0. ss.
      + inv LOCAL0. ss. eapply write_promises_decrease; eauto.
      + inv LOCAL1. inv LOCAL2. ss. eapply write_promises_decrease; eauto.
      + inv LOCAL0. ss.
      + inv LOCAL0. ss.
  Qed.

  Lemma pf_step_rtc_promises_decrease P lang (th0 th1: Thread.t lang)
        (STEP: rtc (tau (@pred_step P lang)) th0 th1)
        (PRED: P <1= promise_free)
    :
      concrete_promised ((Local.promises (Thread.local th1))) <2=
      concrete_promised ((Local.promises (Thread.local th0))).
  Proof.
    ginduction STEP; ss.
    i. eapply IHSTEP in PR; eauto. inv H.
    eapply pf_step_promises_decrease; eauto.
  Qed.

End PROMISEFREE.


Section PFCONSISTENT.

  Definition pf_consistent_strong lang (e0:Thread.t lang): Prop :=
    forall mem1 sc1
           (CAP: Memory.cap (Local.promises (Thread.local e0)) (Thread.memory e0) mem1),
    exists e1,
      (<<STEPS0: rtc (tau (@pred_step is_cancel lang)) (Thread.mk _ (Thread.state e0) (Thread.local e0) sc1 mem1) e1>>) /\
      (<<NORESERVE: no_reserves (Local.promises (Thread.local e1))>>) /\
      exists e2,
        (<<STEPS1: rtc (tau (@pred_step ((promise_free /1\ (fun e => ~ is_cancel e) /1\ no_acq_read_msgs (caps_loc (Thread.memory e0) mem1)) /1\ no_sc) lang)) e1 e2>>) /\
        (__guard__((exists st',
                       (<<LOCAL: Local.failure_step (Thread.local e2)>>) /\
                       (<<FAILURE: Language.step lang ProgramEvent.failure (@Thread.state lang e2) st'>>)) \/
                   (<<PROMISES: (Local.promises (Thread.local e2)) = Memory.bot>>))).

  Lemma step_promise_consistent
        lang pf e th1 th2
        (STEP: @AThread.step lang pf e th1 th2)
        (CONS: Local.promise_consistent (Thread.local th2))
        (WF1: Local.wf (Thread.local th1) (Thread.memory th1))
        (SC1: Memory.closed_timemap (Thread.sc th1) (Thread.memory th1))
        (MEM1: Memory.closed (Thread.memory th1)):
    Local.promise_consistent (Thread.local th1).
  Proof.
    inv STEP; [inv STEP0|inv STEP0; inv LOCAL]; ss.
    - eapply promise_step_promise_consistent; eauto.
    - eapply read_step_promise_consistent; eauto.
    - eapply write_step_promise_consistent; eauto.
    - eapply read_step_promise_consistent; eauto.
      eapply write_step_promise_consistent; eauto.
    - eapply fence_step_promise_consistent; eauto.
    - eapply fence_step_promise_consistent; eauto.
  Qed.

  Lemma pf_consistent_pf_consistent_strong lang (th: Thread.t lang)
        (WF: Local.wf (Thread.local th) (Thread.memory th))
        (MEM: Memory.closed (Thread.memory th))
        (CONSISTENT: pf_consistent th)
    :
      pf_consistent_strong th.
  Proof.
    assert (INHABITED: Memory.inhabited (Thread.memory th)).
    { inv MEM. auto. }
    ii. exploit Memory.max_full_timemap_exists; eauto. intros MAX. des.
    ii. exploit Memory.max_full_timemap_exists.
    { eapply le_inhabited; eauto. eapply Memory.cap_le; eauto. refl. }
    i. des. exploit CONSISTENT; eauto. i.

    assert (exists e2,
               (<<STEPS: rtc (tau (Thread.step true))
                             (Thread.mk _ (Thread.state th) (Thread.local th)
                                        tm0 mem1) e2 >>) /\
               (<<NORESERVES: no_reserves (Local.promises (Thread.local e2))>>) /\
               (__guard__ ((exists e3, (<< FAILURE: Thread.step true ThreadEvent.failure e2 e3 >>)) \/
                           (<<PROMISES: Local.promises (Thread.local e2) = Memory.bot >>)))).
    { des.
      - exploit Thread.rtc_tau_step_future.
        + eapply rtc_implies; [|apply STEPS].
          i. inv H. econs; eauto. econs; eauto.
        + ss. eapply Local.cap_wf; eauto.
        + ss. eapply Memory.max_full_timemap_closed; eauto.
        + ss. eapply Memory.cap_closed; eauto.
        + i. des.
          destruct e2. destruct local. inv WF2. ss.
          exploit reserves_cancelable; eauto. i. des.
          esplits.
          * etrans.
            { eapply STEPS. }
            { eapply rtc_implies; [|apply STEPS0].
              i. inv H. inv TSTEP. inv STEP.
              unfold is_cancel in SAT. des_ifs.
              inv STEP0; inv STEP.
              - econs; eauto. econs; eauto. econs; eauto.
              - inv LOCAL. }
          * ss.
          * left. inv FAILURE; inv STEP. inv LOCAL. inv LOCAL0.
            exists (Thread.mk _ st2 (Local.mk tview proms1) sc2 mem0).
            ss. econs 2. econs; eauto. econs; eauto. econs; eauto.
            eapply nacancels_promises_decrease in STEPS0; auto. ss.
            ii. eapply CONSISTENT0; eauto.
      - unguard. esplits; eauto. rewrite PROMISES. ii.
        rewrite Memory.bot_get in GET. clarify. }

    clear x. des.
    eapply PredStep.pf_step_promise_free_step_rtc in STEPS.
    eapply pf_steps_cancels_not_cancels in STEPS; cycle 1.
    { ss. eapply Local.cap_wf; eauto. }
    { ss. eapply Memory.cap_closed; eauto. }
    { ss. eapply Memory.max_full_timemap_closed; eauto. } des.

    eapply pred_steps_apred_steps in STEPS1.
    eapply pred_steps_apred_steps in STEPS2.

    exploit AThread.rtc_tau_step_future.
    { eapply thread_steps_pred_steps. eapply STEPS1. }
    { ss. eapply Local.cap_wf; eauto. }
    { ss. eapply Memory.max_full_timemap_closed; eauto. }
    { ss. eapply Memory.cap_closed; eauto. }
    i. des. ss.

    destruct th1. exploit no_sc_any_sc_rtc; try apply STEPS1; ss.
    { i. unfold is_cancel in PR. des_ifs. }
    i. des. instantiate (1:=sc1) in STEP. clear STEPS1.

    eexists. splits.
    { eapply STEP. }
    { ss. ii. clarify.
      eapply steps_not_cancel_reserves_same in STEPS2; eauto.
      unguard. des.
      - eapply NORESERVES; eauto.
      - rewrite PROMISES in *. erewrite Memory.bot_get in STEPS2. clarify. }

    eapply hold_or_not with (Q := no_acq_read_msgs (caps_loc (Thread.memory th) mem1) /1\ no_sc) in STEPS2. des.

    - destruct e2. ss.
      exploit no_sc_any_sc_rtc; try eapply HOLD; eauto.
      { ss. i. des. auto. } i. des.
      esplits.
      + eapply pred_step_rtc_mon; try eapply STEP0.
        i. ss. des. splits; eauto.
      + ss. unguard. des.
        * left. ss. inv FAILURE; inv STEP1. inv LOCAL. eauto.
        * right. esplits; eauto.

    - exploit AThread.rtc_tau_step_future.
      { eapply thread_steps_pred_steps. eapply STEPS0. }
      { ss. }
      { ss. }
      { ss. } i. des.
      inv STEP0.
      exploit AThread.step_future; eauto. i. des.

      assert (PROMS: Local.promise_consistent (Thread.local e3)).
      { eapply rtc_tau_step_promise_consistent.
        - eapply thread_steps_pred_steps. eapply STEPS1.
        - unguard. des.
          + inv FAILURE; inv STEP0. inv LOCAL. inv LOCAL0. ss.
          + ii. rewrite PROMISES in PROMISE.
            rewrite Memory.bot_get in PROMISE. clarify.
        - eauto.
        - eauto.
        - eauto. }

      assert (NOPROMISE: (Local.promises (Thread.local e2')) = Memory.bot).
      { apply Memory.ext. i. rewrite Memory.bot_get.
        destruct (Memory.get loc ts (Local.promises (Thread.local e2')))
          as [[from [val released|]]|] eqn:GET; auto; cycle 1.
        - exfalso.
          eapply step_not_cancel_reserves_same in GET; cycle 1.
          + econs.
            * econs; eauto.
            * instantiate (1:=promise_free /1\ (fun e => ~ is_cancel e)). ss.
          + ss.
          + des. eapply steps_not_cancel_reserves_same in GET; eauto.
            des. eapply NORESERVES; eauto.
        - exfalso.
          exploit pf_step_rtc_promises_decrease.
          { eapply STEPS0. }
          { i. ss. des. auto. }
          { econs; eauto. } ss. i.
          exploit pf_step_rtc_promises_decrease.
          { eapply STEP. }
          { i. unfold is_cancel in *. des_ifs. }
          { ss. eauto. }
          ss. i. inv x2.
          ss. unfold no_sc, no_acq_read_msgs in BREAKQ. des_ifs; try by (exfalso; eauto).

          + apply not_and_or in BREAKQ. des; clarify.
            apply imply_to_and in BREAKQ. des. apply NNPP in BREAKQ0.
            unfold caps_loc in *. des. dup CAPS.
            eapply caps_unchangable in CAPS; eauto; cycle 1.
            { inv WF. eauto. }
            eapply unchangable_rtc_increase in STEP; eauto. ss.
            eapply unchangable_rtc_increase in STEPS0; eauto. inv STEPS0.
            inv STEP1; inv STEP0. ss. inv LOCAL.
            inv LOCAL0. clarify. eapply caps_max_view in CAPS0; eauto; cycle 1.
            { inv WF. eauto. } des.
            clarify. eapply PROMS in GET. ss. des_ifs. ss.
            exploit max_full_timemap_get.
            * apply MAX.
            * inv WF. eapply PROMISES. eauto.
            * i. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto.
              etrans; eauto. eapply TimeMap.join_r.
          + apply not_and_or in BREAKQ. des; clarify.
            apply imply_to_and in BREAKQ. des. apply NNPP in BREAKQ0.
            unfold caps_loc in *. des. dup CAPS.
            eapply caps_unchangable in CAPS; eauto; cycle 1.
            { inv WF. eauto. }
            eapply unchangable_rtc_increase in STEP; eauto. ss.
            eapply unchangable_rtc_increase in STEPS0; eauto. inv STEPS0.
            inv STEP1; inv STEP0. ss. inv LOCAL.
            eapply write_step_promise_consistent in LOCAL2; eauto.
            inv LOCAL1. clarify. eapply caps_max_view in CAPS0; eauto; cycle 1.
            { inv WF. eauto. } des.
            clarify. eapply LOCAL2 in GET. ss. des_ifs. ss.
            exploit max_full_timemap_get.
            * apply MAX.
            * inv WF. eapply PROMISES. eauto.
            * i. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto.
              etrans; eauto. eapply TimeMap.join_r.
          + apply not_and_or in BREAKQ. des; clarify. apply NNPP in BREAKQ.
            inv STEP1; inv STEP0. ss. inv LOCAL. inv LOCAL0. ss.
            eapply PROMS in GET. ss. des_ifs. ss.
            hexploit max_full_timemap_get; eauto.
            * inv WF. eapply Memory.cap_le; eauto.
            * i. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto.
          + inv STEP1; inv STEP0. ss. inv LOCAL. inv LOCAL0. ss.
            eapply PROMS in GET. ss. des_ifs. ss.
            hexploit max_full_timemap_get; eauto.
            * inv WF. eapply Memory.cap_le; eauto.
            * i. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto.
      }

      destruct e2'. destruct local. ss.
      eapply no_sc_any_sc_rtc in STEPS0; ss; cycle 1.
      { i. des; ss. } des.
      esplits.
      * eapply pred_step_rtc_mon; eauto.
        i. ss. des; auto.
      * unguard. ss. eauto.
  Qed.

End PFCONSISTENT.
