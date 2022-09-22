Require Import Lia.
Require Import RelationClasses.

From Paco Require Import paco.
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
Require Import Configuration.
Require Import Progress.
Require Import Behavior.

Require Import Coq.Logic.Classical.

Set Implicit Arguments.

Section Pred.

  Definition te_pred := ThreadEvent.t -> Prop.

  Definition promise_free (e: ThreadEvent.t): Prop :=
    match e with
    | ThreadEvent.promise loc from to msg kind =>
      (Memory.op_kind_is_lower_full kind && Message.is_released_none msg
       || Memory.op_kind_is_cancel kind)%bool
    | _ => True
    end.

  Definition no_acq_update_on (MSGS : Loc.t -> Time.t -> Prop)
             (e : ThreadEvent.t) : Prop :=
    match e with
    | ThreadEvent.update loc from _ _ _ _ _ ordr _ =>
      forall (SAT: MSGS loc from), ~ Ordering.le Ordering.acqrel ordr
    | _ => True
    end
  .

  Definition promise_not_in (MSGS : Loc.t -> Time.t -> Prop)
             (e : ThreadEvent.t) : Prop :=
    match e with
    | ThreadEvent.promise loc from to _ _ =>
      forall t (IN: Interval.mem (from, to) t), ~ (MSGS loc t)
    | _ => True
    end.

  Definition write_not_to (MSGS : Loc.t -> Time.t -> Prop)
             (e : ThreadEvent.t) : Prop :=
    match e with
    | ThreadEvent.write loc from to _ _ _ =>
      ~ MSGS loc to
    | ThreadEvent.update loc from to _ _ _ _ _ _ =>
      ~ MSGS loc to
    | ThreadEvent.promise loc from to _ kind =>
      if Memory.op_kind_is_cancel kind then True
      else ~ MSGS loc to
    | _ => True
    end.

  Definition wf_event (e: ThreadEvent.t): Prop :=
    match e with
    | ThreadEvent.write loc from to _ _ _ => Time.lt from to
    | ThreadEvent.update loc from to _ _ _ _ _ _ => Time.lt from to
    | ThreadEvent.promise loc from to _ _ => Time.lt from to
    | _ => True
    end.

  Definition wf_time_evt (P: Loc.t -> Time.t -> Prop) (e: ThreadEvent.t) : Prop :=
    match e with
    | ThreadEvent.promise loc from to msg kind =>
      (<<FROM: P loc from>>) /\ (<<TO: P loc to>>)
    | ThreadEvent.write loc from to val released ordw =>
      (<<FROM: P loc from>>) /\ (<<TO: P loc to>>)
    | ThreadEvent.update loc from to valr valw releasedr releasedw ordr ordw =>
      (<<TO: P loc to>>)
    | _ => True
    end.

  Lemma wf_time_evt_mon P0 P1
        (LE: P0 <2= P1)
    :
      wf_time_evt P0 <1= wf_time_evt P1.
  Proof.
    ii. unfold wf_time_evt in *. des_ifs; des; splits; eauto.
  Qed.

  Definition no_promise (e : ThreadEvent.t) : Prop :=
    match e with
    | ThreadEvent.promise _ _ _ _ _ => False
    | _ => True
    end.

  Definition no_read_msgs (MSGS : Loc.t -> Time.t -> Prop)
             (e : ThreadEvent.t) : Prop :=
    match e with
    | ThreadEvent.read loc to _ _ _ => ~ (MSGS loc to)
    | ThreadEvent.update loc from _ _ _ _ _ _ _ => ~ (MSGS loc from)
    | _ => True
    end.

  Definition write_not_in (MSGS : Loc.t -> Time.t -> Prop)
             (e : ThreadEvent.t) : Prop :=
    match e with
    | ThreadEvent.write loc from to _ _ _ =>
      forall t (IN: Interval.mem (from, to) t), ~ (MSGS loc t)
    | ThreadEvent.update loc from to _ _ _ _ _ _ =>
      forall t (IN: Interval.mem (from, to) t), ~ (MSGS loc t)
    | ThreadEvent.promise loc from to _ kind =>
      if Memory.op_kind_is_cancel kind then True
      else (forall t (IN: Interval.mem (from, to) t), ~ (MSGS loc t))
    | _ => True
    end.

  Definition no_update_on (MSGS : Loc.t -> Time.t -> Prop)
             (e : ThreadEvent.t) : Prop :=
    match e with
    | ThreadEvent.update loc from to _ _ _ _ _ _ =>
      ~ MSGS loc from
    | _ => True
    end.

  Definition no_sc (e : ThreadEvent.t) : Prop :=
    match e with
    | ThreadEvent.fence _ ordw => ~ Ordering.le Ordering.seqcst ordw
    | ThreadEvent.syscall _ => False
    | _ => True
    end
  .

  Definition write_in (MSGS : Loc.t -> Time.t -> Prop)
             (e : ThreadEvent.t) : Prop :=
    match e with
    | ThreadEvent.write loc from to _ _ _ =>
      forall t (IN: Interval.mem (from, to) t), (MSGS loc t)
    | ThreadEvent.update loc from to _ _ _ _ _ _ =>
      forall t (IN: Interval.mem (from, to) t), (MSGS loc t)
    | _ => True
    end.

  Lemma write_not_in_mon L0 L1
        e
        (NOTIN: write_not_in L1 e)
        (LE: L0 <2= L1)
    :
      write_not_in L0 e.
  Proof.
    i. unfold write_not_in in *. des_ifs.
    - ii. eapply NOTIN; eauto.
    - ii. eapply NOTIN; eauto.
    - ii. eapply NOTIN; eauto.
  Qed.

  Lemma no_read_msgs_mon L0 L1
        e
        (NOTIN: no_read_msgs L1 e)
        (LE: L0 <2= L1)
    :
      no_read_msgs L0 e.
  Proof.
    i. unfold no_read_msgs in *. des_ifs.
    - ii. eapply NOTIN; eauto.
    - ii. eapply NOTIN; eauto.
  Qed.

  Lemma no_update_on_mon L0 L1
        e
        (NOTIN: no_update_on L1 e)
        (LE: L0 <2= L1)
    :
      no_update_on L0 e.
  Proof.
    i. unfold no_update_on in *. des_ifs.
    ii. eapply NOTIN; eauto.
  Qed.

  Definition no_acq_read_msgs (MSGS : Loc.t -> Time.t -> Prop)
             (e : ThreadEvent.t) : Prop :=
    match e with
    | ThreadEvent.read loc to _ _ ord =>
      forall (SAT: MSGS loc to), ~ Ordering.le Ordering.acqrel ord
    | ThreadEvent.update loc from _ _ _ _ _ ordr _ =>
      forall (SAT: MSGS loc from), ~ Ordering.le Ordering.acqrel ordr
    | _ => True
    end
  .

  Definition is_cancel (e: ThreadEvent.t) : Prop :=
    match e with
    | ThreadEvent.promise _ _ _ _ Memory.op_kind_cancel => True
    | _ => False
    end.

End Pred.