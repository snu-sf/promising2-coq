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
Require Import Pred.
Require Import ReorderPromises2.

Require Import APredStep.
Require Import ALocal.
Require Import AThread.
Require Import AMemory.

Require Import PFConsistent.
Require Import ADRF_PF0.
Require Import ADRF_PF1.
Require Import ADRF_PF3.
Require Import AMapping.

(* Require Import PFConsistent. *)

Set Implicit Arguments.

Definition collapsing_latest_reserves (L: Loc.t -> Prop)
           (mem: Memory.t) (loc: Loc.t) (to: Time.t) (from: Time.t) :=
  (<<LATEST: to = Memory.max_ts loc mem>>) /\
  (<<RESERVE: Memory.get loc to mem = Some (from, Message.reserve)>>) /\
  (<<OTHER: L loc>>)
.

Definition collapsing_latest_reserves_times (L: Loc.t -> Prop)
           (mem: Memory.t) (loc: Loc.t) (to: Time.t): Prop :=
  exists from,
    (<<RESERVE: collapsing_latest_reserves L mem loc to from>>).

Definition collapsing_caps (L: Loc.t -> Prop)
           (mem0 mem1: Memory.t) (loc: Loc.t) (to: Time.t) (from: Time.t) :=
  (<<LATEST: exists val released,
      (<<CAP: caps mem0 mem1 loc to from (Message.full val released)>>)>>) /\
  (<<OTHER: L loc>>)
.

Definition collapsing_caps_times (L: Loc.t -> Prop)
           (mem0 mem1: Memory.t) (loc: Loc.t) (to: Time.t) :=
  exists from,
    (<<CAP: collapsing_caps L mem0 mem1 loc to from>>).

Inductive caps_collapsing (L: Loc.t -> Prop)
          (mem: Memory.t): Loc.t -> Time.t -> Time.t -> Prop :=
| caps_collapsing_not_in
    loc t
    (NSAT: ~ L loc)
  :
    caps_collapsing L mem loc t t
| caps_collapsing_in_memory
    loc t max
    (SAT: L loc)
    (FULL: Memory.max_full_ts mem loc max)
    (TLE: Time.le t max)
  :
    caps_collapsing L mem loc t t
| caps_collapsing_cap
    loc t max
    (SAT: L loc)
    (FULL: Memory.max_full_ts mem loc max)
    (TS0: Time.lt max t)
    (TS1: Time.le t (Time.incr (Memory.max_ts loc mem)))
  :
    caps_collapsing L mem loc t max
| caps_collapsing_outer_memory
    loc t
    (SAT: L loc)
    (TLE: Time.lt (Time.incr (Memory.max_ts loc mem)) t)
  :
    caps_collapsing L mem loc t t
.

Lemma caps_get_reserve mem0 prom mem1 loc to from
      (RESERVE: Memory.reserve_wf prom mem0)
      (CLOSED: Memory.closed mem0)
      (CAP: Memory.cap prom mem0 mem1)
      (CAPS: caps mem0 mem1 loc to from Message.reserve)
  :
    exists from0 to1 msg0 msg1,
      (<<GET0: Memory.get loc from mem0 = Some (from0, msg0)>>) /\
      (<<GET1: Memory.get loc to1 mem0 = Some (to, msg1)>>) /\
      (<<SPACE: forall t (ITV: Interval.mem (from, to) t), ~ covered loc t mem0>>)
.
Proof.
  unfold caps in CAPS. des. inv CAP.
  exploit COMPLETE; eauto. i. des.
  set (@cell_elements_least
         (mem0 loc)
         (fun t => Time.lt from t)). des.
  - hexploit (MIDDLE loc f from from0 to0).
    { econs; eauto. i.
      destruct (Memory.get loc ts mem0) eqn:GET2; auto. destruct p.
      exfalso. exploit LEAST.
      - eapply GET2.
      - eauto.
      - i. exploit Memory.get_ts; try apply GET.
        i. des; clarify.
        + eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          * eapply SAT.
          * eapply Time.bot_spec.
        + eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
          * etrans.
            { eapply x1. }
            { eapply TS2. }
          * eauto. }
    { exploit memory_get_from_mon.
      - eapply x.
      - eapply GET.
      - eauto.
      - i. destruct x2; auto. destruct H. exfalso.
        exploit memory_get_from_inj.
        { eapply SOUND. eapply GET. }
        { eapply GET1. }
        i. des; clarify.
        + setoid_rewrite GET0 in GET. clarify.
        + eapply Time.lt_strorder; eauto. }
    i. exploit memory_get_from_inj.
    { eapply H. }
    { eapply GET1. }
    i. des; clarify.
    + esplits; eauto. ii. inv H0.
      exploit Memory.get_disjoint.
      * eapply SOUND. eapply GET2.
      * eapply H.
      * i. des; clarify. eapply x2; eauto.
    + inv CLOSED. specialize (INHABITED loc).
      eapply SOUND in INHABITED. clarify.
  - exploit Memory.max_ts_spec.
    { eapply x. }
    i. des. destruct MAX.
    + exfalso. eapply EMPTY; eauto.
    + unfold Time.eq in *. subst. exploit x0; auto. intros LATEST.
      exploit Memory.latest_val_exists; eauto.
      { inv CLOSED. eauto. }
      i. des.
      exploit Memory.max_full_view_exists; eauto.
      { inv CLOSED. eauto. } i. des.
      exploit BACK; eauto. i.
      exploit memory_get_from_inj.
      * eapply x1.
      * eapply GET1.
      * i. des; clarify.
        { exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          - eapply Time.incr_spec.
          - rewrite BOT0. eapply Time.bot_spec. }
        { inv CLOSED. erewrite INHABITED in GET0. clarify. }
Qed.

Lemma max_full_ts_not_collapsed L prom mem0 mem1 loc max
      (INHABITED: Memory.inhabited mem0)
      (CAP: Memory.cap prom mem0 mem1)
      (MAX: Memory.max_full_ts mem0 loc max)
  :
    ~ (collapsing_latest_reserves_times L mem0 \2/ collapsing_caps_times L mem0 mem1) loc max.
Proof.
  ii. des.
  - inv H. inv H0. des. clarify.
    exploit Memory.max_full_ts_spec; eauto. i. des. clarify.
  - inv H. inv H0. des. inv CAP0.
    exploit Memory.max_full_ts_spec; eauto. i. des. clarify.
Qed.

Lemma partial_cap_closed prom mem0 mem1 mem2
      (MLE: Memory.le prom mem0)
      (CLOSED: Memory.closed mem0)
      (RESERVEWF: Memory.reserve_wf prom mem0)
      (CAP: Memory.cap prom mem0 mem2)
      (MLE0: Memory.le mem0 mem1)
      (MLE1: Memory.le mem1 mem2)
  :
    Memory.closed mem1.
Proof.
  exploit Memory.max_full_timemap_exists; eauto.
  { inv CLOSED. auto. }
  intros [tm MAX].
  inv CLOSED. econs; eauto.
  i. destruct (Memory.get loc to mem0) as [[from0 msg0]|] eqn:GET.
  - dup GET. eapply MLE0 in GET. clarify.
    eapply CLOSED0 in GET0. des. esplits; eauto.
    eapply memory_concrete_le_closed_msg; eauto.
  - destruct msg.
    + eapply MLE1 in MSG.
      exploit caps_max_view; eauto.
      * econs; eauto.
      * i. des; clarify. esplits; eauto.
        { econs; eauto. econs; eauto. econs. refl. }
        { econs; eauto. ss. transitivity (Memory.max_ts loc mem0).
          - specialize (MAX loc). inv MAX. des.
            eapply Memory.max_ts_spec in GET0. des. eauto.
          - left. eapply Time.incr_spec. }
        { eapply memory_concrete_le_closed_msg; eauto.
          econs. econs. econs.
          - eapply Memory.max_full_timemap_closed; eauto.
          - eapply Memory.max_full_timemap_closed; eauto. }
    + esplits; eauto. econs.
Qed.

Lemma collapsing_caps_forget_le
      mem0 mem1 mem2 prom (L: Loc.t -> Prop)
      (CAP: Memory.cap prom mem0 mem2)
      (FORGET: forget_memory (collapsing_latest_reserves_times L mem0 \2/ collapsing_caps_times L mem0 mem2) mem1 mem2)
  :
    memory_concrete_le mem0 mem1.
Proof.
  inv FORGET. ii.
  erewrite COMPLETE.
  - eapply Memory.cap_le in CAP; eauto. refl.
  - ii. des.
    + unfold collapsing_latest_reserves_times in *. des.
      inv RESERVE. des. clarify.
    + unfold collapsing_caps_times in *. des.
      inv CAP0. des. unfold caps in CAP0. des. clarify.
Qed.

Definition collapsable_cap (L: Loc.t -> Prop) (prom mem: Memory.t): Prop :=
  forall
    loc (SAT: L loc)
    from msg
    (GET: Memory.get loc (Memory.max_ts loc mem) prom = Some (from, msg)),
    msg <> Message.reserve.

Lemma collapsing_caps_forget_le2
      mem0 mem1 mem2 prom (L: Loc.t -> Prop)
      (CLOSED: Memory.closed mem0)
      (CAP: Memory.cap prom mem0 mem2)
      (FORGET: forget_memory (collapsing_latest_reserves_times L mem0 \2/ collapsing_caps_times L mem0 mem2) mem1 mem2)
      loc
      (SAT: L loc)
      from to val released
      (GET: Memory.get loc to mem1 = Some (from, Message.full val released))
  :
    Memory.get loc to mem0 = Some (from, Message.full val released).
Proof.
  dup GET. eapply forget_memory_get in GET; eauto. des.
  dup GET1. eapply Memory.cap_inv in GET1; eauto. des; eauto.
  - clarify.
  - clarify. exfalso. eapply NOT. right. econs; eauto. econs; eauto.
    esplits. econs; eauto.
Qed.

Lemma collapsing_caps_forget_prom_le
      mem0 mem1 mem2 prom (L: Loc.t -> Prop)
      (COLLAPSABLE: collapsable_cap L prom mem0)
      (MLE: Memory.le prom mem0)
      (CLOSED: Memory.closed mem0)
      (RESERVEWF: Memory.reserve_wf prom mem0)
      (CAP: Memory.cap prom mem0 mem2)
      (FORGET: forget_memory (collapsing_latest_reserves_times L mem0 \2/ collapsing_caps_times L mem0 mem2) mem1 mem2)
  :
    Memory.le prom mem1.
Proof.
  inv FORGET. ii.
  erewrite COMPLETE.
  - eapply Memory.cap_le in CAP; eauto.
  - ii. des.
    + unfold collapsing_latest_reserves_times in *. des.
      inv RESERVE. des. clarify.
      dup LHS. eapply MLE in LHS0. clarify.
      eapply COLLAPSABLE in OTHER. eapply OTHER in LHS. clarify.
    + unfold collapsing_caps_times in *. des.
      inv CAP0. des. unfold caps in CAP0. des.
      eapply MLE in LHS; eauto. clarify.
Qed.

Lemma identity_mapped_view tm maxmap (f: Loc.t -> Time.t -> Time.t -> Prop)
      (TM: TimeMap.le tm maxmap)
      (IDENT: forall loc ts (TS: Time.le ts (maxmap loc)), f loc ts ts)
  :
    timemap_map f tm tm.
Proof.
  ii. eapply IDENT; eauto.
Qed.

Lemma caps_collapsing_ident L mem loc maxts ts
      (MAX: Memory.max_full_ts mem loc maxts)
      (TS: Time.le ts maxts)
  :
    (caps_collapsing L mem) loc ts ts.
Proof.
  i. destruct (classic (L loc)).
  - econs 2; eauto.
  - econs 1; eauto.
Qed.

Lemma caps_collapsing_ident2 L mem maxts loc ts fts
      (MAX: Memory.max_full_ts mem loc maxts)
      (TS: Time.le ts maxts)
      (MAP: (caps_collapsing L mem) loc ts fts)
  :
    ts = fts.
Proof.
  inv MAP; eauto.
  exploit Memory.max_full_ts_inj.
  { eapply FULL. }
  { eapply MAX. } i. clarify.
  exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
  { eapply TS0. }
  { eapply TS. }
Qed.

Lemma caps_collapsing_ident3 L mem maxts loc ts fts
      (RESERVEWF : memory_reserve_wf mem)
      (INHABITED : Memory.inhabited mem)
      (MAX: Memory.max_full_ts mem loc maxts)
      (TS: Time.lt fts maxts)
      (MAP: (caps_collapsing L mem) loc ts fts)
  :
    ts = fts.
Proof.
  inv MAP; eauto.
  exploit Memory.max_full_ts_inj.
  { eapply FULL. }
  { eapply MAX. }
  i. clarify. exfalso. eapply Time.lt_strorder; eauto.
Qed.

Lemma caps_collapsing_timemap L mem tm
      (INHABITED: Memory.inhabited mem)
      (TM: Memory.closed_timemap tm mem)
  :
    timemap_map (caps_collapsing L mem) tm tm.
Proof.
  exploit Memory.max_full_timemap_exists; eauto. intros [maxmap MAX].
  eapply identity_mapped_view.
  - eapply Memory.max_full_timemap_spec; eauto.
  - i. eapply caps_collapsing_ident; eauto.
Qed.

Lemma caps_collapsing_view L mem vw
      (INHABITED: Memory.inhabited mem)
      (VW: Memory.closed_view vw mem)
  :
    view_map (caps_collapsing L mem) vw vw.
Proof.
  inv VW. econs.
  - eapply caps_collapsing_timemap; eauto.
  - eapply caps_collapsing_timemap; eauto.
Qed.

Lemma caps_collapsing_opt_view L mem vw
      (INHABITED: Memory.inhabited mem)
      (VW: Memory.closed_opt_view vw mem)
  :
    opt_view_map (caps_collapsing L mem) vw vw.
Proof.
  inv VW; econs.
  eapply caps_collapsing_view; eauto.
Qed.

Lemma caps_collapsing_message L mem msg
      (INHABITED: Memory.inhabited mem)
      (MSG: Memory.closed_message msg mem)
  :
    msg_map (caps_collapsing L mem) msg msg.
Proof.
  inv MSG; econs.
  eapply caps_collapsing_opt_view; eauto.
Qed.

Lemma caps_collapsing_tview L mem vw
      (INHABITED: Memory.inhabited mem)
      (VW: TView.closed vw mem)
  :
    tview_map (caps_collapsing L mem) vw vw.
Proof.
  inv VW. econs.
  - i. eapply caps_collapsing_view; eauto.
  - eapply caps_collapsing_view; eauto.
  - eapply caps_collapsing_view; eauto.
Qed.

Lemma memory_cap_message_closed prom mem0 mem1
      (CLOSED: Memory.closed mem0)
      (CAP: Memory.cap prom mem0 mem1)
      loc to from msg
      (GET: Memory.get loc to mem1 = Some (from, msg))
  :
    Memory.closed_message msg mem0.
Proof.
  eapply Memory.cap_inv in GET; eauto. des.
  - eapply CLOSED in GET. des; auto.
  - clarify.
  - clarify. econs. econs.
    eapply Memory.max_full_view_closed; eauto.
Qed.

Lemma caps_collapsing_promises (L: Loc.t -> Prop) mem prom
      (MLE: Memory.le prom mem)
      (CLOSED: Memory.closed mem)
      (RESERVEWF: memory_reserve_wf mem)
      (COLLAPSABLE: collapsable_cap L prom mem)
  :
    promises_map (caps_collapsing L mem) prom prom.
Proof.
  exploit Memory.max_full_timemap_exists; eauto.
  { inv CLOSED. eauto. }
  intros [tm MAX].
  dup CLOSED. inv CLOSED0. econs.
  - i. dup GET. eapply MLE in GET0. eapply CLOSED1 in GET0. des.
    exists to, from, msg.
    destruct (classic (L loc)).
    + dup GET. eapply MLE in GET0.
      eapply not_latest_reserve_le_max_full_ts in GET0; eauto.
      eapply or_strengthen in GET0. des; clarify.
      * esplits; eauto.
        { ii. unfold collapsed in *. des.
          eapply caps_collapsing_ident2 in MAP1; eauto; cycle 1.
          eapply caps_collapsing_ident2 in MAP0; eauto; cycle 1.
          { etrans; eauto. left. auto. } clarify.
          eapply Time.lt_strorder; eauto. }
        { econs 2; eauto. }
        { eapply caps_collapsing_message; eauto. }
      * exfalso. exploit COLLAPSABLE; eauto.
    + splits; auto.
      * ii. unfold collapsed in *. des.
        inv MAP0; clarify. inv MAP1; clarify.
        eapply Time.lt_strorder. eauto.
      * econs 1; eauto.
      * eapply caps_collapsing_message; eauto.
  - i. exists fto, ffrom, fmsg.
    destruct (classic (L loc)).
    + dup GET. eapply MLE in GET.
      eapply not_latest_reserve_le_max_full_ts in GET; eauto.
      des; clarify.
      * splits; auto.
        { eapply caps_collapsing_ident; eauto. }
        { eapply caps_collapsing_ident; eauto.
          etrans; eauto.
          eapply memory_get_ts_strong in GET0. des; clarify.
          { refl. }
          { left. auto. } }
      * exfalso. exploit COLLAPSABLE; eauto.
    + splits; auto.
      * econs 1; eauto.
      * econs 1; eauto.
Qed.

Lemma memory_reserve_wf_mon prom0 prom1 mem
      (RESERVEWF: Memory.reserve_wf prom1 mem)
      (MLE: Memory.le prom0 prom1)
  :
    Memory.reserve_wf prom0 mem.
Proof.
  ii. eauto.
Qed.

Lemma caps_collapsing_memory' (L0 L1: Loc.t -> Prop)
      mem0 mem1 mem2 mem3 prom
      (MLE: Memory.le prom mem0)
      (CLOSED: Memory.closed mem0)
      (RESERVEWF0: memory_reserve_wf mem0)
      (COLLAPSABLE0: collapsable_cap L0 prom mem0)
      (COLLAPSABLE1: collapsable_cap L1 prom mem0)
      (CAP: Memory.cap prom mem0 mem1)
      (FORGET0: forget_memory (collapsing_latest_reserves_times L0 mem0 \2/ collapsing_caps_times L0 mem0 mem1) mem2 mem1)
      (FORGET1: forget_memory (collapsing_latest_reserves_times L1 mem0 \2/ collapsing_caps_times L1 mem0 mem1) mem3 mem2)
  :
    memory_map (caps_collapsing L1 mem0) mem2 mem3.
Proof.
  assert (RESERVEWF1: Memory.reserve_wf prom mem0).
  { eapply memory_reserve_wf_mon; eauto. }
  apply memory_map2_memory_map.
  exploit Memory.max_full_timemap_exists; eauto.
  { inv CLOSED. eauto. }
  intros [tm MAX].
  dup FORGET0. inv FORGET0. dup FORGET1. inv FORGET1.
  dup CLOSED. inv CLOSED0. econs.
  - i. dup GET. eapply forget_memory_get in GET0; eauto. des.
    destruct (classic (L1 loc)).
    + destruct (classic ((collapsing_latest_reserves_times L1 mem0 \2/ collapsing_caps_times L1 mem0 mem1) loc to)).
      * des.
        { inv H0. inv H1. des. clarify.
          dup RESERVE. eapply Memory.cap_le in RESERVE0; eauto; [|refl]. clarify.
          replace from with (tm loc) in *; cycle 1.
          { eapply Memory.max_full_ts_inj; eauto.
            eapply max_ts_reserve_from_full_ts; eauto. }
          dup RESERVE0. eapply RESERVEWF0 in RESERVE. des.
          eapply Memory.cap_le in RESERVE; eauto. refl.
        }
        { inv H0. inv H1. des.
          dup CAP0. eapply caps_max_view in CAP0; eauto. des. clarify.
          unfold caps in CAP1. des. clarify.
          inv VAL.
          exploit Memory.max_full_ts_inj.
          { eapply MAX0. }
          { eapply MAX. } i. clarify.
          exploit Memory.max_full_ts_spec; eauto. i. des. clarify. right.
          exists (tm loc), from, (Message.full val (Some (View.mk tm tm))), (Message.full val released).
          splits.
          - econs 3; eauto.
            { eapply TimeFacts.le_lt_lt.
              - eapply max_full_ts_le_max_ts; eauto.
              - eapply Time.incr_spec. }
            { refl. }
          - eapply caps_collapsing_message; eauto. econs. econs.
            eapply Memory.max_full_view_closed. econs; eauto.
          - econs. eapply CLOSED1 in GET3. des. inv MSG_CLOSED.
            inv CLOSED0; eauto. inv CLOSED2. econs. econs; ss.
            + eapply Memory.max_full_timemap_spec; eauto.
            + eapply Memory.max_full_timemap_spec; eauto.
          - erewrite COMPLETE0; eauto.
            + erewrite COMPLETE; eauto.
              * eapply Memory.cap_le in GET3; eauto. refl.
              * eapply max_full_ts_not_collapsed; eauto.
            + eapply max_full_ts_not_collapsed; eauto. }
      * apply not_or_and in H0. des.
        assert (TS: Time.le to (tm loc)).
        { dup GET1. eapply Memory.cap_inv in GET1; eauto. des; clarify.
          - dup GET1. eapply not_latest_reserve_le_max_full_ts in GET1; eauto.
            des; clarify. exfalso. eapply H0. econs; eauto. econs; eauto.
          - inv GET2. dup GET5. eapply not_latest_reserve_le_max_full_ts in GET5; eauto.
            des; clarify.
            + eapply memory_get_ts_le in GET2. etrans; eauto.
            + refl.
          - exfalso. eapply H1. econs; eauto. econs; eauto.
            esplits; eauto. econs; eauto. }
        right. exists to, from, msg, msg. splits; auto.
        { econs 2; eauto. }
        { eapply caps_collapsing_message; eauto.
          eapply memory_cap_message_closed; eauto. }
        { refl. }
        { erewrite COMPLETE0; eauto. ii. des; clarify. }
    + right. exists to, from, msg, msg. esplits; eauto.
      * econs 1; eauto.
      * eapply caps_collapsing_message; eauto.
        eapply memory_cap_message_closed in GET1; eauto.
      * refl.
      * erewrite COMPLETE0; eauto. ii. des.
        { inv H0. inv H1. des. clarify. }
        { inv H0. inv H1. des. clarify. }
  - i. dup GET. eapply forget_memory_get in GET0; eauto. des.
    apply not_or_and in NOT. des.
    exists fto, ffrom, fmsg. destruct (classic (L1 loc)).
    + assert (TS: Time.le fto (tm loc)).
      { dup GET1. eapply forget_memory_get in GET1; eauto. des.
        dup GET2. eapply Memory.cap_inv in GET2; eauto. des; clarify.
        - dup GET2. eapply not_latest_reserve_le_max_full_ts in GET2; eauto.
          des; clarify. exfalso. eapply NOT. econs; eauto. econs; eauto.
        - inv GET3. dup GET6. eapply not_latest_reserve_le_max_full_ts in GET6; eauto.
          des; clarify.
          + eapply memory_get_ts_le in GET3. etrans; eauto.
          + refl.
        - exfalso. eapply NOT0. econs; eauto. econs; eauto.
          esplits; eauto. econs; eauto. }
      splits; auto.
      * econs 2; eauto.
      * econs 2; eauto. etrans; eauto.
        eapply memory_get_ts_le; eauto.
    + splits; auto.
      * econs 1; eauto.
      * econs 1; eauto.
Qed.

Definition earlier_times (tm: TimeMap.t) (loc: Loc.t) (to: Time.t): Prop :=
  Time.le to (tm loc).

Definition later_times (tm: TimeMap.t) (loc: Loc.t) (to: Time.t): Prop :=
  Time.lt (tm loc) to.

Lemma forget_covered L mem0 mem1
      (FORGET: forget_memory L mem1 mem0)
      loc ts
      (COVERED: covered loc ts mem0)
      (KEEP: forall to from msg (SAT: L loc to)
                    (GET: Memory.get loc to mem0 = Some (from, msg)),
          ~ Interval.mem (from, to) ts)
  :
    covered loc ts mem1.
Proof.
  inv COVERED. inv FORGET.
  erewrite <- COMPLETE in GET.
  - econs; eauto.
  - ii. eapply KEEP in H; eauto.
Qed.

Lemma caps_collapsing_memory
      mem0 mem1 mem2 prom (L: Loc.t -> Prop)
      (MLE: Memory.le prom mem0)
      (CLOSED: Memory.closed mem0)
      (RESERVEWF0: memory_reserve_wf mem0)
      (RESERVEWF1: Memory.reserve_wf prom mem0)
      (COLLAPSABLE: collapsable_cap L prom mem0)
      (CAP: Memory.cap prom mem0 mem1)
      (FORGET: forget_memory (collapsing_latest_reserves_times L mem0 \2/ collapsing_caps_times L mem0 mem1) mem2 mem1)
  :
    memory_map (caps_collapsing L mem0) mem1 mem2.
Proof.
  eapply (@caps_collapsing_memory' bot1); eauto.
  - ii. clarify.
  - eapply bot_forget. i.
    unfold collapsing_latest_reserves_times, collapsing_caps_times,
    collapsing_latest_reserves, collapsing_caps in PR. des; clarify.
Qed.

(* Definition memory_last_reserves (prom mem: Memory.t) := (fun loc => Memory.latest_reserve loc prom mem). *)

Definition pf_consistent_drf' lang (e0:Thread.t lang): Prop :=
  let L := (fun loc => Memory.latest_reserve loc (Local.promises (Thread.local e0)) (Thread.memory e0)) in
  forall mem1 mem2 max
         (CAP: Memory.cap (Local.promises (Thread.local e0)) (Thread.memory e0) mem1)
         (FORGET: forget_memory (collapsing_latest_reserves_times L (Thread.memory e0) \2/ collapsing_caps_times L (Thread.memory e0) mem1) mem2 mem1)
         (MAX: Memory.max_full_timemap (Thread.memory e0) max),
  exists e1,
    (<<STEPS0: rtc (tau (@pred_step is_cancel lang)) (Thread.mk _ (Thread.state e0) (Thread.local e0) TimeMap.bot mem2) e1>>) /\
    (<<NORESERVE: no_reserves (Local.promises (Thread.local e1))>>) /\
    (<<NOATTATCH: not_attatched (Memory.max_full_ts (Thread.memory e0)) (Thread.memory e1)>>) /\
    (<<MAXMAP: TimeMap.le (Memory.max_timemap (Thread.memory e1)) max>>) /\
    exists e2,
      (<<STEPS1: rtc (tau (@pred_step ((promise_free /1\ (fun e => ~ is_cancel e) /1\ no_acq_update_on ((fun loc to => L loc) /2\ Memory.max_full_ts (Thread.memory e0))) /1\ no_sc) lang)) e1 e2>>) /\
      (__guard__((exists st',
                     (<<LOCAL: Local.failure_step (Thread.local e2)>>) /\
                     (<<FAILURE: Language.step lang ProgramEvent.failure (@Thread.state lang e2) st'>>)) \/
                 (<<PROMISES: (Local.promises (Thread.local e2)) = Memory.bot>>))).

Lemma caps_collapsing_collapsable_unwritable L prom mem0 mem1
      (MLE: Memory.le prom mem0)
      (RESERVEWF : memory_reserve_wf mem0)
      (INHABITED : Memory.inhabited mem0)
      (COLLAPSABLE: collapsable_cap L prom mem0)
      (CAP: Memory.cap prom mem0 mem1)
  :
    collapsable_unwritable (caps_collapsing L mem0) prom mem1.
Proof.
  ii. des. unfold collapsed in *. des. inv ITV. ss.
  inv MAP0; inv MAP1; clarify.
  - exfalso; eapply Time.lt_strorder; eapply TimeFacts.lt_le_lt; eauto.
  - exfalso; eapply Time.lt_strorder; eapply TimeFacts.lt_le_lt; eauto.
  - exploit Memory.max_full_ts_inj; [apply FULL|apply FULL0|i; clarify].
    inv CAP. destruct (Time.le_lt_dec t (Memory.max_ts loc mem0)).
    + exploit max_full_ts_max_ts; eauto. i. des; clarify.
      * clear - FROM l.
        exfalso; eapply Time.lt_strorder; eapply TimeFacts.lt_le_lt; eauto.
      * econs; eauto.
        { econs; eauto.
          destruct (Memory.get loc (Memory.max_ts loc mem0) prom) eqn:GETPROM; eauto.
          exfalso. destruct p as [from []].
          - eapply MLE in GETPROM. clarify.
          - eapply COLLAPSABLE in GETPROM; eauto. }
        { econs; ss. }
    + exploit Memory.latest_val_exists; eauto. i. des.
      exploit Memory.max_full_view_exists; eauto. i. des.
      exploit BACK; eauto.
      { instantiate (1:=loc). unfold Memory.latest_reserve. des_ifs.
        eapply COLLAPSABLE in Heq; eauto. }
      i. econs; eauto.
      * econs; eauto.
        destruct (Memory.get loc (Time.incr (Memory.max_ts loc mem0)) prom) eqn:GETPROM; eauto.
        exfalso. destruct p as [from msg].
        eapply MLE in GETPROM.
        eapply Memory.max_ts_spec in GETPROM; eauto. des.
        exfalso; eapply Time.lt_strorder; eapply TimeFacts.lt_le_lt; eauto.
      * econs; eauto.
  - clear - FROM TO. exfalso; eapply Time.lt_strorder; eapply TimeFacts.lt_le_lt; eauto.
  - exploit Memory.max_full_ts_inj; [apply FULL|apply FULL0|i; clarify].
    exfalso; eapply Time.lt_strorder; eapply TimeFacts.le_lt_lt.
    { eapply TO. }
    etrans; eauto.
  - exploit Memory.max_full_ts_inj; [apply FULL|apply FULL0|i; clarify].
    inv CAP. destruct (Time.le_lt_dec t (Memory.max_ts loc mem0)).
    + exploit max_full_ts_max_ts; eauto. i. des; clarify.
      * clear - FROM TS0 l.
        exfalso; eapply Time.lt_strorder; eapply TimeFacts.lt_le_lt; eauto.
        etrans; eauto. left. auto.
      * econs; eauto.
        { econs; eauto.
          destruct (Memory.get loc (Memory.max_ts loc mem0) prom) eqn:GETPROM; eauto.
          exfalso. destruct p as [from []].
          - eapply MLE in GETPROM. clarify.
          - eapply COLLAPSABLE in GETPROM; eauto. }
        { econs; ss. clear - FROM TS0. etrans; eauto. }
    + exploit Memory.latest_val_exists; eauto. i. des.
      exploit Memory.max_full_view_exists; eauto. i. des.
      exploit BACK; eauto.
      { instantiate (1:=loc). unfold Memory.latest_reserve. des_ifs.
        eapply COLLAPSABLE in Heq; eauto. }
      i. econs; eauto.
      * econs; eauto.
        destruct (Memory.get loc (Time.incr (Memory.max_ts loc mem0)) prom) eqn:GETPROM; eauto.
        exfalso. destruct p as [from msg].
        eapply MLE in GETPROM.
        eapply Memory.max_ts_spec in GETPROM; eauto. des.
        exfalso; eapply Time.lt_strorder; eapply TimeFacts.lt_le_lt; eauto.
      * econs; eauto.
  - exfalso; eapply Time.lt_strorder; eapply TimeFacts.le_lt_lt; eauto.
  - clear - FROM TO. exfalso; eapply Time.lt_strorder; eapply TimeFacts.lt_le_lt; eauto.
  - exfalso; eapply Time.lt_strorder; eapply TimeFacts.le_lt_lt.
    { eapply TS1. }
    etrans; eauto.
  - clear - FROM TO. exfalso; eapply Time.lt_strorder; eapply TimeFacts.lt_le_lt; eauto.
Qed.

Lemma caps_collapsing_mapping_map_le L prom mem0 mem1
      (COLLAPSABLE: collapsable_cap L prom mem0)
      (CAP: Memory.cap prom mem0 mem1)
  :
    mapping_map_le (caps_collapsing L mem0).
Proof.
  ii. inv MAP0; inv MAP1; clarify.
  - exploit Memory.max_full_ts_inj; [apply FULL|apply FULL0|i; clarify].
  - etrans; eauto. left. auto.
  - exploit Memory.max_full_ts_inj; [apply FULL|apply FULL0|i; clarify]. refl.
  - etrans; eauto. left. auto.
  - exfalso; eapply Time.lt_strorder; eapply TimeFacts.lt_le_lt.
    { eapply TLE. }
    etrans; eauto.
Qed.

Lemma caps_collapsing_mapping_map_bot L prom mem0 mem1
      (COLLAPSABLE: collapsable_cap L prom mem0)
      (INHABITED: Memory.inhabited mem0)
      (CAP: Memory.cap prom mem0 mem1)
  :
    mapping_map_bot (caps_collapsing L mem0).
Proof.
  ii. destruct (classic (L loc)).
  - exploit Memory.max_full_ts_exists; eauto. i. des.
    econs 2; eauto. eapply Time.bot_spec.
  - econs 1; eauto.
Qed.

Lemma caps_collapsing_mapping_map_eq L prom mem0 mem1
      (COLLAPSABLE: collapsable_cap L prom mem0)
      (CAP: Memory.cap prom mem0 mem1)
  :
    mapping_map_eq (caps_collapsing L mem0).
Proof.
  ii. inv MAP0; inv MAP1; clarify.
  - exploit Memory.max_full_ts_inj; [apply FULL|apply FULL0|i; clarify].
    exfalso; eapply Time.lt_strorder; eapply TimeFacts.lt_le_lt; eauto.
  - exploit Memory.max_full_ts_inj; [apply FULL|apply FULL0|i; clarify].
    exfalso; eapply Time.lt_strorder; eapply TimeFacts.le_lt_lt; eauto.
  - exploit Memory.max_full_ts_inj; [apply FULL|apply FULL0|i; clarify].
  - exfalso; eapply Time.lt_strorder; eapply TimeFacts.lt_le_lt; eauto.
  - clear - TLE TS1. exfalso; eapply Time.lt_strorder; eapply TimeFacts.lt_le_lt; eauto.
Qed.

Lemma caps_collapsing_total L mem0 loc to
      (INHABITED: Memory.inhabited mem0)
  :
    exists fto,
      <<MAP: caps_collapsing L mem0 loc to fto >>.
Proof.
  destruct (classic (L loc)).
  - exploit Memory.max_full_ts_exists; eauto. i. des.
    destruct (Time.le_lt_dec to ts).
    { eexists. econs 2; eauto. }
    destruct (Time.le_lt_dec to (Time.incr (Memory.max_ts loc mem0))).
    { eexists. econs 3; eauto. }
    { eexists. econs 4; eauto. }
  - eexists. econs 1; eauto.
Qed.

Lemma caps_collapsing_mappable_time_always L mem0
      (INHABITED: Memory.inhabited mem0)
      loc to
  :
    mappable_time (caps_collapsing L mem0) loc to.
Proof.
  eapply caps_collapsing_total; eauto.
Qed.

Lemma caps_collapsing_mappable_event_always L mem0
      (INHABITED: Memory.inhabited mem0)
      e
  :
    mappable_evt (caps_collapsing L mem0) e.
Proof.
  destruct e; ss; split; (apply caps_collapsing_mappable_time_always; auto).
Qed.

Lemma collapsing_caps_forget_closed
      mem0 mem1 mem2 prom (L: Loc.t -> Prop)
      (CLOSED: Memory.closed mem0)
      (CAP: Memory.cap prom mem0 mem2)
      (FORGET: forget_memory (collapsing_latest_reserves_times L mem0 \2/ collapsing_caps_times L mem0 mem2) mem1 mem2)
  :
    Memory.closed mem1.
Proof.
  hexploit collapsing_caps_forget_le; eauto. intros MLE.
  inv CLOSED.
  econs.
  - ii. eapply forget_memory_get in MSG; eauto. des.
    eapply Memory.cap_inv in GET; try apply CAP; eauto. des; clarify.
    + eapply CLOSED0 in GET; eauto. des. splits; auto.
      eapply memory_concrete_le_closed_msg; eauto.
    + split; auto. econs.
    + splits; auto.
      * econs; eauto. econs. eapply Memory.max_full_view_wf; eauto.
      * econs; eauto. ss. inv GET4. ss. etrans.
        { eapply max_full_ts_le_max_ts; eauto. }
        { left. eapply Time.incr_spec. }
      * eapply memory_concrete_le_closed_msg; eauto.
        econs; eauto. econs.
        eapply Memory.max_full_view_closed; eauto.
  - ii. eauto.
Qed.

Lemma caps_collapsing_memory_max_other
      mem0 mem1 mem2 prom (L: Loc.t -> Prop)
      (MLE: Memory.le prom mem0)
      (CLOSED: Memory.closed mem0)
      (RESERVEWF0: memory_reserve_wf mem0)
      (RESERVEWF1: Memory.reserve_wf prom mem0)
      (COLLAPSABLE: collapsable_cap L prom mem0)
      (CAP: Memory.cap prom mem0 mem1)
      (FORGET: forget_memory (collapsing_latest_reserves_times L mem0 \2/ collapsing_caps_times L mem0 mem1) mem2 mem1)
      loc
      (SAT: L loc)
  :
    Memory.max_full_ts mem0 loc (Memory.max_ts loc mem2).
Proof.
  econs.
  - exploit Memory.max_ts_spec.
    { inv CLOSED. specialize (INHABITED loc).
      eapply collapsing_caps_forget_le in INHABITED; eauto. }
    i. des. clear MAX.
    dup GET. eapply forget_memory_get in GET; eauto. des.
    destruct (Memory.get loc (Memory.max_ts loc mem2) mem0) as [[to' []]|] eqn:GET2; eauto.
    + exfalso. dup GET2. eapply Memory.cap_le in GET3; eauto; [clarify|refl].
      dup GET2. apply RESERVEWF0 in GET2. des.
      dup GET2. eapply collapsing_caps_forget_le in GET2; eauto.
      exploit Memory.max_full_ts_exists; eauto.
      { inv CLOSED. eauto. } i. des.
      exploit Memory.max_full_ts_spec; eauto. i. des. destruct MAX.
      * dup GET.
        eapply collapsing_caps_forget_le in GET; eauto.
        dup GET. eapply Memory.max_ts_spec in GET. des.
        exploit Memory.get_disjoint.
        { eapply GET6. }
        { eapply GET0. }
        i. des; clarify. eapply x1.
        { instantiate (1:=ts). econs; ss.
          - eapply memory_get_ts_strong in GET5. des; clarify.
            exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
            + eapply H.
            + eapply Time.bot_spec.
          - refl. }
        { econs; eauto. }
      * inv H. dup GET.
        eapply collapsing_caps_forget_le in GET; eauto. clarify.
        dup x0. eapply max_full_ts_max_ts in x1; eauto; cycle 1.
        { inv CLOSED. auto. }
        des; clarify.
        { exploit Memory.cap_inv; eauto. i. des; clarify.
          dup x1. eapply Memory.max_ts_spec in x1. des.
          dup x2. eapply memory_get_ts_strong in x2. des; clarify.
          - rewrite x3 in *.
            inv CLOSED. rewrite (INHABITED loc) in x1. clarify.
          - eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
            + eapply TS.
            + eauto. }
        { exploit Memory.get_disjoint.
          { eapply GET2. }
          { eapply GET1. }
          i. apply or_strengthen in x1. des; clarify.
          - eapply NOT. left. econs; eauto. econs; eauto.
          - apply not_and_or in NOT0. des; cycle 1.
            { apply NOT0. split; auto. }
            dup GET2. eapply memory_get_ts_strong in GET2. des; clarify.
            + rewrite GET7 in *. eapply Time.lt_strorder; eauto.
            + dup GET1. eapply memory_get_ts_strong in GET1. des; clarify.
              * rewrite GET7 in *.
                inv CLOSED. rewrite (INHABITED loc) in GET2. clarify.
              * eapply SAT0.
                { instantiate (1:=Time.meet (Memory.max_ts loc mem0) (Memory.max_ts loc mem2)).
                  unfold Time.meet. des_ifs; econs; ss.
                  - refl.
                  - left. auto. }
                { unfold Time.meet. des_ifs; econs; ss. refl. } }
    + exploit Memory.cap_inv; eauto. i. des; clarify.
      * inv x1. destruct m2.
        { dup GET4. eapply collapsing_caps_forget_le in GET5; eauto.
          dup GET5. eapply Memory.max_ts_spec in GET5; eauto. des.
          dup GET6. eapply memory_get_ts_strong in GET6. des; clarify.
          - exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
            + eapply TS.
            + eapply Time.bot_spec.
          - exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
            + eapply TS0.
            + eauto. }
        { eapply RESERVEWF0 in GET4; eauto. }
      * exfalso. eapply NOT. right. econs; eauto. econs; eauto.
        esplits; eauto. econs; eauto.
  - i. eapply collapsing_caps_forget_le in GET; eauto.
    eapply Memory.max_ts_spec in GET. des. auto.
Qed.

Lemma caps_collapsing_memory_max_self
      mem0 mem1 mem2 prom (L: Loc.t -> Prop)
      (MLE: Memory.le prom mem0)
      (CLOSED: Memory.closed mem0)
      (RESERVEWF0: memory_reserve_wf mem0)
      (RESERVEWF1: Memory.reserve_wf prom mem0)
      (COLLAPSABLE: collapsable_cap L prom mem0)
      (CAP: Memory.cap prom mem0 mem1)
      (FORGET: forget_memory (collapsing_latest_reserves_times L mem0 \2/ collapsing_caps_times L mem0 mem1) mem2 mem1)
      loc
      (NSAT: ~ Memory.latest_reserve loc prom mem0)
  :
    Memory.max_ts loc mem0 = Memory.max_ts loc mem2.
Proof.
  assert (NLOC: ~ L loc).
  { ii. apply COLLAPSABLE in H.
    unfold Memory.latest_reserve in NSAT. des_ifs. eapply H; eauto. }
  dup CLOSED. inv CLOSED.
  exploit Memory.max_ts_spec.
  { eapply (INHABITED loc). }
  i. des.
  exploit Memory.max_ts_spec.
  { specialize (INHABITED loc). eapply collapsing_caps_forget_le in INHABITED; eauto. }
  i. des.
  apply TimeFacts.antisym.
  - eapply Memory.cap_le in GET; eauto; [|refl].
    inv FORGET. erewrite <- COMPLETE in GET.
    + eapply Memory.max_ts_spec in GET. des; eauto.
    + unfold collapsing_latest_reserves_times, collapsing_latest_reserves,
      collapsing_caps_times, collapsing_caps.
      ii. des; clarify.
  - dup GET0. eapply forget_memory_get in GET1; eauto. des.
    dup GET2. eapply Memory.cap_inv in GET2; eauto. des; clarify.
    + eapply Memory.max_ts_spec in GET2. des; eauto.
    + inv GET3. dup GET6. eapply Memory.max_ts_spec in GET6. des.
      etrans.
      { eapply memory_get_ts_le; eauto. }
      { eauto. }
Qed.

Lemma caps_collapsing_memory_full_max_self
      mem0 mem1 mem2 prom (L: Loc.t -> Prop)
      (MLE: Memory.le prom mem0)
      (CLOSED: Memory.closed mem0)
      (RESERVEWF0: memory_reserve_wf mem0)
      (RESERVEWF1: Memory.reserve_wf prom mem0)
      (COLLAPSABLE: collapsable_cap L prom mem0)
      (CAP: Memory.cap prom mem0 mem1)
      (FORGET: forget_memory (collapsing_latest_reserves_times L mem0 \2/ collapsing_caps_times L mem0 mem1) mem2 mem1)
      loc
      (NSAT: ~ Memory.latest_reserve loc prom mem0)
  :
    exists max,
      (<<MAX: Memory.max_full_ts mem0 loc max>>) /\
      (<<LATEST: Memory.get loc (Memory.max_ts loc mem0) mem0 = Some (max, Message.reserve)>>) /\
      (<<GET: Memory.get loc (Memory.max_ts loc mem0) mem2 = Some (max, Message.reserve)>>).
Proof.
  assert (NLOC: ~ L loc).
  { ii. apply COLLAPSABLE in H.
    unfold Memory.latest_reserve in NSAT. des_ifs. eapply H; eauto. }
  unfold Memory.latest_reserve in NSAT. des_ifs.
  dup Heq. eapply MLE in Heq0.
  exploit Memory.max_full_ts_exists; eauto.
  { inv CLOSED. auto. } i. des.
  exploit max_full_ts_max_ts; eauto.
  { inv CLOSED. auto. }
  instantiate (1:=loc). i. des; clarify.
  - dup x0. inv x0. des.
    setoid_rewrite GET in Heq0. clarify.
  - esplits; eauto.
    dup GET. eapply Memory.cap_le in GET; try apply CAP; eauto; [|refl].
    inv FORGET. erewrite COMPLETE; eauto.
    unfold collapsing_latest_reserves_times, collapsing_caps_times,
    collapsing_latest_reserves, collapsing_caps. ii. des; clarify.
Qed.

Lemma caps_collapsing_memory_full_max_other
      mem0 mem1 mem2 prom (L: Loc.t -> Prop)
      (MLE: Memory.le prom mem0)
      (CLOSED: Memory.closed mem0)
      (RESERVEWF0: memory_reserve_wf mem0)
      (RESERVEWF1: Memory.reserve_wf prom mem0)
      (COLLAPSABLE: collapsable_cap L prom mem0)
      (CAP: Memory.cap prom mem0 mem1)
      (FORGET: forget_memory (collapsing_latest_reserves_times L mem0 \2/ collapsing_caps_times L mem0 mem1) mem2 mem1)
      loc
      (SAT: L loc)
  :
    Memory.max_full_ts mem2 loc (Memory.max_ts loc mem2).
Proof.
  exploit Memory.max_full_ts_exists.
  { ii. eapply collapsing_caps_forget_le; eauto. inv CLOSED. auto. }
  instantiate (1:=loc). i. des.
  replace ts with (Memory.max_ts loc mem2) in *; eauto.
  apply TimeFacts.antisym.
  - exploit caps_collapsing_memory_max_other; eauto. i.
    dup x1. inv x1. des. eapply collapsing_caps_forget_le in GET; eauto.
    eapply Memory.max_full_ts_spec in GET; eauto. des. eauto.
  - eapply max_full_ts_le_max_ts; eauto.
Qed.

Lemma caps_collapsing_memory_not_attatched
      mem0 mem1 mem2 prom (L: Loc.t -> Prop)
      (MLE: Memory.le prom mem0)
      (CLOSED: Memory.closed mem0)
      (RESERVEWF0: memory_reserve_wf mem0)
      (RESERVEWF1: Memory.reserve_wf prom mem0)
      (COLLAPSABLE: collapsable_cap L prom mem0)
      (CAP: Memory.cap prom mem0 mem1)
      (FORGET: forget_memory (collapsing_latest_reserves_times L mem0 \2/ collapsing_caps_times L mem0 mem1) mem2 mem1)
  :
    not_attatched (fun loc to => <<SAT: L loc>> /\ Memory.max_full_ts mem0 loc to) mem2.
Proof.
  ii. des. split.
  - assert (CONCRETE: concrete_promised mem0 loc to).
    { inv CLOSED. specialize (INHABITED loc).
      eapply Memory.max_full_ts_spec in INHABITED; eauto.
      des. econs; eauto. }
    inv CONCRETE. eapply collapsing_caps_forget_le in GET; eauto.
    econs; eauto.
  - exists (Time.incr to). splits.
    + apply Time.incr_spec.
    + ii. inv H. inv ITV0. inv ITV. ss.
      dup GET. eapply Memory.max_ts_spec in GET0; auto. des.
      exploit caps_collapsing_memory_max_other; eauto. intros MAX0.
      exploit Memory.max_full_ts_inj.
      { eapply SAT1. }
      { eapply MAX0. } i. clarify.
      eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
      { eapply FROM0. }
      etrans.
      { eapply TO. }
      { eauto. }
Qed.

Lemma concrete_le_le_not_attatched L mem0 mem1
      (CONCRETE: memory_concrete_le mem0 mem1)
      (MLE: Memory.le mem1 mem0)
      (ATTATCHED: not_attatched L mem0)
  :
    not_attatched L mem1.
Proof.
  ii. exploit ATTATCHED; eauto. i. des. split.
  - inv CONCRETE0. eapply CONCRETE in GET. econs; eauto.
  - exists to'. splits; eauto. ii. eapply EMPTY; eauto.
    eapply memory_le_covered; eauto.
Qed.

Lemma remove_msg_not_attatched mem0 mem1
      (MLE: Memory.le mem1 mem0)
      loc from0 to0 to1 val released msg1
      (TS: Time.lt to0 to1)
      (GET1: Memory.get loc to0 mem1 = Some (from0, Message.full val released))
      (GET0: Memory.get loc to1 mem0 = Some (to0, msg1))
      (NONE: Memory.get loc to1 mem1 = None)
  :
    (<<CONCRETE: concrete_promised mem1 loc to0>>) /\
    (<<NOATTATCH: exists to',
        (<<TLE: Time.lt to0 to'>>) /\
        (<<EMPTY: forall t (ITV: Interval.mem (to0, to') t), ~ covered loc t mem1>>)>>).
Proof.
  split.
  - econs; eauto.
  - esplits; eauto. ii. inv H.
    exploit Memory.get_disjoint.
    { eapply GET0. }
    { eapply MLE. eapply GET. }
    i. des; clarify. eapply x0; eauto.
Qed.

Lemma memory_le_max_ts mem0 mem1
      (MLE: Memory.le mem0 mem1)
      (INHABITED: Memory.inhabited mem0)
      loc
  :
    Time.le (Memory.max_ts loc mem0) (Memory.max_ts loc mem1).
Proof.
  exploit Memory.max_ts_spec.
  { eapply (INHABITED loc). } i. des.
  eapply MLE in GET.
  eapply Memory.max_ts_spec in GET. des. auto.
Qed.

Lemma concrete_le_max_full_ts mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      loc max0 max1
      (MAX0: Memory.max_full_ts mem0 loc max0)
      (MAX1: Memory.max_full_ts mem1 loc max1)
  :
    Time.le max0 max1.
Proof.
  inv MAX0. inv MAX1. des.
  eapply MLE in GET. eapply MAX0; eauto.
Qed.

Lemma pf_consistent_pf_consistent_drf' lang (th: Thread.t lang)
      (WF: Local.wf (Thread.local th) (Thread.memory th))
      (MEM: Memory.closed (Thread.memory th))
      (CONSISTENT: pf_consistent_strong th)
      (RESERVEWF: memory_reserve_wf (Thread.memory th))
  :
    pf_consistent_drf' th.
Proof.
  assert (INHABITED: Memory.inhabited (Thread.memory th)).
  { inv MEM. auto. }
  ii.
  set (L:=fun loc : Loc.t =>
            Memory.latest_reserve loc (Local.promises (Thread.local th)) (Thread.memory th)).
  assert (COLLAPSABLE: collapsable_cap L (Local.promises (Thread.local th)) (Thread.memory th)).
  { ii. clarify. unfold L, Memory.latest_reserve in SAT.
    rewrite GET in SAT. clarify. }
  assert (MAPLE: mapping_map_le (caps_collapsing L (Thread.memory th))).
  { eapply caps_collapsing_mapping_map_le; eauto. }
  assert (MAPBOT: mapping_map_bot (caps_collapsing L (Thread.memory th))).
  { eapply caps_collapsing_mapping_map_bot; eauto. }
  assert (MAPEQ: mapping_map_eq (caps_collapsing L (Thread.memory th))).
  { eapply caps_collapsing_mapping_map_eq; eauto. }
  assert (CONCRETELE: memory_concrete_le (Thread.memory th) mem2).
  { eapply collapsing_caps_forget_le; eauto. }

  exploit CONSISTENT; eauto. i. des.

  assert (WFTGT: Local.wf (Thread.local th) mem1).
  { eapply Local.cap_wf; eauto. }
  assert (CLOSEDTGT: Memory.closed mem1).
  { eapply Memory.cap_closed; eauto. }
  assert (CLOSEDSRC: Memory.closed mem2).
  { eapply collapsing_caps_forget_closed; cycle 1; eauto. }
  assert (LCWFSRC: Local.wf (Thread.local th) mem2).
  { eapply memory_concrete_le_local_wf; eauto. inv WF.
    eapply collapsing_caps_forget_prom_le; eauto. }

  assert (SCSRC: Memory.closed_timemap TimeMap.bot mem2).
  { eapply Memory.closed_timemap_bot; eauto. }
  assert (SCTGT: Memory.closed_timemap TimeMap.bot mem1).
  { eapply Memory.closed_timemap_bot; eauto.
    ii. eapply Memory.cap_le; eauto. refl. }
  assert (UNWRITABLE: collapsable_unwritable
                        (caps_collapsing L (Thread.memory th))
                        (Local.promises (Thread.local th)) mem1).
  { inv WF. eapply caps_collapsing_collapsable_unwritable; eauto. }

  destruct e1.
  hexploit (@steps_map (caps_collapsing L (Thread.memory th))); try apply STEPS0; auto; eauto.
  { i. eapply caps_collapsing_mappable_event_always; eauto. }
  { econs.
    - refl.
    - eapply caps_collapsing_tview; eauto. inv WF. eauto.
    - eapply caps_collapsing_promises; eauto. inv WF. eauto. }
  { inv WF. eapply caps_collapsing_memory; try apply FORGET; eauto. }
  { eapply timemap_bot_map; eauto. }
  { refl. }
  { instantiate (1:=is_cancel). ii. inv REL; ss. inv KIND; ss. }
  i. des.

  exploit AThread.rtc_tau_step_future.
  { eapply thread_steps_pred_steps. eapply STEPS0. } all: eauto. i. des. ss.
  exploit AThread.rtc_tau_step_future.
  { eapply thread_steps_pred_steps. eapply STEP. } all: eauto. i. des. ss.

  destruct e2.
  eapply steps_write_not_in in STEPS1; cycle 1.
  { inv WF2. ss. }
  eapply steps_wf_event in STEPS1; cycle 1.
  { inv CLOSED2. ss. }

  hexploit (@steps_map (caps_collapsing L (Thread.memory th))); try apply STEPS1; auto; eauto.
  { i. eapply caps_collapsing_mappable_event_always; eauto. }
  { eapply collapsable_unwritable_steps in STEPS0; eauto. }
  { instantiate (1:=(promise_free /1\ (fun e => ~ is_cancel e) /1\ no_acq_update_on ((fun loc to => L loc) /2\ Memory.max_full_ts (Thread.memory th))) /1\ no_sc).
    ss. ii. des. inv REL; splits; ss; eauto.
    - inv KIND; ss. inv MSG0; ss. inv MSG; ss. inv MAP0; ss.
    - inv KIND; ss.
    - ii. des.
      specialize (SAT1 (Time.meet to (Time.incr (Memory.max_ts loc (Thread.memory th))))).
      inv FROM.
      + clarify.
      + exploit Memory.max_full_ts_inj; [apply SAT6|apply FULL|i; clarify].
        assert (TS: Time.lt max0 (Time.incr (Memory.max_ts loc (Thread.memory th)))).
        { eapply TimeFacts.le_lt_lt.
          { eapply max_full_ts_le_max_ts; eauto. }
          { eapply Time.incr_spec. } }
        assert (UNWRITABLE0: unwritable memory (Local.promises local) loc (Time.meet to (Time.incr (Memory.max_ts loc (Thread.memory th))))).
        { exploit rtc_unwritable_increase; [| |].
          - eapply thread_steps_pred_steps. eapply STEPS0.
          - ss. eapply UNWRITABLE.
            eexists max0, (Time.incr (Memory.max_ts loc (Thread.memory th))). splits; eauto.
            + eexists. splits.
              * econs 2; eauto.
              * econs 3; eauto. refl.
            + instantiate (1:=Time.meet to (Time.incr (Memory.max_ts loc (Thread.memory th)))).
              unfold Time.meet. des_ifs; econs; ss. refl.
          - ss. }
        eapply SAT1; eauto. unfold Time.meet. des_ifs; econs; ss.
        * refl.
        * left. auto.
      + destruct TS1.
        { assert (TS: Time.lt ffrom (Time.incr (Memory.max_ts loc (Thread.memory th)))).
          { eapply TimeFacts.le_lt_lt.
            { eapply max_full_ts_le_max_ts; eauto. }
            { eapply Time.incr_spec. } }
          assert (UNWRITABLE0: unwritable memory (Local.promises local) loc (Time.meet to (Time.incr (Memory.max_ts loc (Thread.memory th))))).
          { exploit rtc_unwritable_increase; [| |].
            - eapply thread_steps_pred_steps. eapply STEPS0.
            - ss. eapply UNWRITABLE.
              eexists ffrom, (Time.incr (Memory.max_ts loc (Thread.memory th))). splits; eauto.
              + eexists. splits.
                * econs 2; eauto. refl.
                * econs 3; eauto. refl.
              + instantiate (1:=Time.meet to (Time.incr (Memory.max_ts loc (Thread.memory th)))).
                unfold Time.meet. des_ifs; econs; ss.
                * transitivity from; auto.
                * refl.
            - ss. }
          eapply SAT1; eauto. unfold Time.meet. des_ifs; econs; ss.
          * refl.
          * left. auto. }
        { unfold Time.eq in *. subst.
          eapply SAT3; eauto. econs; eauto. inv CAP.
          hexploit (@Memory.latest_val_exists loc (Thread.memory th)); eauto. i. des.
          hexploit (@Memory.max_full_view_exists (Thread.memory th)); eauto. i. des.
          exploit BACK; eauto. i.
          esplits; eauto. econs; eauto.
          destruct (Memory.get loc (Time.incr (Memory.max_ts loc (Thread.memory th))) (Thread.memory th)) eqn: GET; auto.
          exfalso. destruct p.
          eapply Memory.max_ts_spec in GET. des.
          eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
          - eapply MAX0.
          - eapply Time.incr_spec. }
      + exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
        { eapply TLE. }
        etrans.
        { eapply max_full_ts_le_max_ts; eauto. }
        { left. eapply Time.incr_spec. }
  }
  i. des.
  assert (NORESERVES: no_reserves (Local.promises flc1)).
  { ss. inv LOCAL. eapply no_reserves_map; eauto. }
  esplits; eauto.
  - eapply not_attatched_mon with
        (L0 :=
           (fun loc to => <<SAT: L loc>> /\ Memory.max_full_ts (Thread.memory th) loc to)
             \2/
             (fun loc to => <<SAT: ~ L loc>> /\ Memory.max_full_ts (Thread.memory th) loc to)); cycle 1.
    { i. destruct (classic (L x1)).
      - left. split; auto.
      - right. split; auto. }
    eapply not_attatched_sum.
    + eapply concrete_le_le_not_attatched.
      * eapply cancels_concrete_same in STEP; eauto.
      * eapply cancels_memory_decrease in STEP; eauto.
      * inv WF. eapply caps_collapsing_memory_not_attatched; try apply CAP; eauto.
    + ii. ss. des. inv WF.
      exploit caps_collapsing_memory_full_max_self; try apply COLLAPSABLE; try apply CAP; eauto.
      i. des.
      exploit Memory.max_full_ts_inj.
      { eapply SAT1. }
      { eapply MAX0. } i. clarify.
      unfold L, Memory.latest_reserve in SAT0. des_ifs.

      dup SAT1. inv SAT2. des.
      eapply collapsing_caps_forget_le in GET0; eauto.
      hexploit cancels_concrete_same; try apply STEP; eauto. intros CONCRETE.
      apply CONCRETE in GET0. ss.
      eapply remove_msg_not_attatched.
      * eapply cancels_memory_decrease in STEP; eauto.
      * instantiate (1:=Memory.max_ts loc (Thread.memory th)).
        dup GET. eapply memory_get_ts_strong in GET. des; clarify.
        erewrite GET2 in *. erewrite BOT in Heq. clarify.
      * eauto.
      * eauto.
      * eapply cancels_remove_only in STEP; eauto; ss.
        { des. auto. }
        { destruct (Memory.get loc (Memory.max_ts loc (Thread.memory th)) (Local.promises flc1)) eqn:NONE; auto.
          destruct p.
          dup NONE. eapply cancels_promises_decrease in STEP; eauto. ss.
          eapply STEP in NONE0. clarify.
          eapply NORESERVES in NONE. clarify. }

  - ss. ii. destruct (classic (L loc)).
    + etrans.
      { eapply memory_le_max_ts.
        - eapply cancels_memory_decrease in STEP; eauto.
        - inv CLOSED0. auto. }
      { ss. inv WF.
        exploit caps_collapsing_memory_max_other; try apply COLLAPSABLE; try apply CAP; eauto.
        i. exploit Memory.max_full_ts_inj.
        { eapply x1. }
        { eapply MAX. }
        i. right. auto. }

    + destruct (Time.le_lt_dec (Memory.max_timemap fmem1 loc) (max loc)); auto. exfalso.
      inv WF.
      exploit caps_collapsing_memory_full_max_self; try apply COLLAPSABLE; try apply CAP; eauto.
      i. des.
      unfold L in H. dup H. unfold Memory.latest_reserve in H. des_ifs.
      dup Heq. eapply PROMISES in Heq0. clarify.
      exploit Memory.max_ts_spec.
      { eapply cancels_concrete_same; try apply STEP; eauto. }
      instantiate (1:=loc). i. des. ss.
      clarify. dup GET0.
      exploit cancels_memory_decrease; try apply STEP; eauto. i. ss.
      dup x1. eapply Memory.max_ts_spec in x1. des.
      erewrite <- (@caps_collapsing_memory_max_self _ mem1 mem2) in MAX2; eauto; cycle 1.
      exploit Memory.max_full_ts_inj.
      { eapply MAX0. }
      { eapply MAX. } i. clarify.
      destruct MAX2.
      * exploit Memory.get_disjoint.
        { eapply x2. }
        { inv FORGET. erewrite COMPLETE.
          - eapply Memory.cap_le; [eauto|refl|].
            eapply Heq0.
          - unfold collapsing_latest_reserves_times, collapsing_caps_times,
            collapsing_latest_reserves, collapsing_caps. ii. des; clarify. }
        i. des; clarify.
        { erewrite x1 in *. eapply Time.lt_strorder; eauto. }
        { eapply x1.
          - econs; [|refl]. ss.
            eapply memory_get_ts_strong in GET1. des; clarify.
            erewrite GET3 in *. exfalso. eapply Time.lt_strorder.
            eapply TimeFacts.lt_le_lt.
            + eapply l.
            + unfold Memory.max_timemap. erewrite GET3. eapply Time.bot_spec.
          - econs; ss. left. auto. }
      * inv H1.
        exploit cancels_remove_only; try apply STEP; eauto.
        { ss.
          destruct (Memory.get loc (Memory.max_ts loc (Thread.memory th)) (Local.promises flc1)) eqn:GET3; auto.
          exfalso. destruct p.
          exploit cancels_promises_decrease; try apply STEP; eauto.
          ss. i. clarify. eapply NORESERVES in GET3. clarify. }
        { i. ss. des. rewrite H3 in *. clarify. }
  - ss. unguard. des.
    + left. esplits; eauto. econs. inv LOCAL1. inv LOCAL0.
      eapply promise_consistent_mon.
      { eapply promise_consistent_map; eauto. }
      { ss. }
      { ss. }
    + right. inv LOCAL0. rewrite PROMISES in *.
      eapply bot_promises_map; eauto.
Qed.

Inductive shorter_thread lang: (Thread.t lang) -> (Thread.t lang) -> Prop :=
| shorter_thread_intro
    st lc sc mem0 mem1
    (MEM: shorter_memory mem0 mem1)
  :
    shorter_thread
      (Thread.mk lang st lc sc mem0)
      (Thread.mk lang st lc sc mem1)
.

Global Program Instance shorter_thread_PreOrder lang: PreOrder (@shorter_thread lang).
Next Obligation. ii. destruct x. econs. refl. Qed.
Next Obligation.
  ii. inv H. inv H0. econs. etrans; eauto.
Qed.

Lemma shorter_thread_shorter_memory lang (th_src th_tgt: Thread.t lang)
      (THREAD: shorter_thread th_src th_tgt)
  :
    shorter_memory (Thread.memory th_src) (Thread.memory th_tgt).
Proof. inv THREAD; eauto. Qed.

Lemma no_update_on_step2
      L lang e_tgt (th_src th_tgt th_tgt': Thread.t lang)
      (LCWF: Memory.le (Local.promises (Thread.local th_src)) (Thread.memory th_src))
      (PRED: (no_update_on L /1\ promise_free) e_tgt)
      (STEPS: AThread.step_allpf e_tgt th_tgt th_tgt')
      (SHORTER: shorter_thread th_src th_tgt)
      (NOATTATCH: not_attatched L (Thread.memory th_src))
  :
    exists e_src th_src',
      (<<STEPS: AThread.step_allpf e_src th_src th_src'>>) /\
      (<<SHORTER: shorter_thread th_src' th_tgt'>>) /\
      (<<EVENT: shorter_event e_src e_tgt>>) /\
      (<<NOATTATCH: not_attatched L (Thread.memory th_src')>>).
Proof.
  assert (TSTEP0: pred_step (no_update_on L /1\ promise_free) e_tgt th_tgt th_tgt').
  { econs; eauto. }
  destruct th_src, th_tgt, th_tgt'. destruct local0, local1. inv SHORTER. ss.
  exploit no_update_on_step; try apply STEPS; eauto; ss. i. des.
  esplits; eauto. econs; eauto.
Qed.

Lemma list_Forall_app A P (l0 l1: list A)
  :
    List.Forall P (l0 ++ l1) <-> (<<FORALL0: List.Forall P l0>> /\ <<FORALL1: List.Forall P l1>>).
Proof.
  induction l0; split; i; ss.
  - split; auto.
  - des. auto.
  - inv H. apply IHl0 in H3. des. split; auto.
  - des. inv FORALL0. econs; eauto.
Qed.

Lemma list_Forall2_app A B P (lhd0 ltl0: list A) (lhd1 ltl1: list B)
      (FORALL0: List.Forall2 P lhd0 lhd1)
      (FORALL1: List.Forall2 P ltl0 ltl1)
  :
    List.Forall2 P (lhd0 ++ ltl0) (lhd1 ++ ltl1).
Proof.
  ginduction FORALL0; eauto. i. ss. econs; eauto.
Qed.

Lemma list_Forall2_in A B P (l0: list A) (l1: list B)
      (FORALL: List.Forall2 P l0 l1)
      b
      (IN: List.In b l1)
  :
    exists a,
      (<<IN: List.In a l0>>) /\ (<<SAT: P a b>>).
Proof.
  ginduction FORALL; eauto; i; ss. des; clarify.
  - esplits; eauto.
  - eapply IHFORALL in IN; eauto. des. esplits; eauto.
Qed.

Lemma list_Forall_sum A (P Q R: A -> Prop) (l: list A)
      (FORALL0: List.Forall P l)
      (FORALL1: List.Forall Q l)
      (SUM: forall a (SAT0: P a) (SAT1: Q a), R a)
  :
    List.Forall R l.
Proof.
  ginduction l; eauto. i. inv FORALL0. inv FORALL1. econs; eauto.
Qed.

Lemma updates_list_exists L
      lang (th0 th1: Thread.t lang) tr
      (PRED: List.Forall (fun em => promise_free (fst em)) tr)
      (LCWF: Memory.le (Local.promises (Thread.local th0)) (Thread.memory th0))
      (STEPS: traced_step tr th0 th1)
      (ATTATCHED: not_attatched L (Thread.memory th0))
  :
    exists (updates: list (Loc.t * Time.t)) th1' tr',
      (<<UPDATESWF: List.Forall (fun locto => L (fst locto) (snd locto)) updates>>) /\
      (<<STEPS: traced_step tr' th0 th1'>>) /\
      (<<SHORTER: shorter_thread th1' th1>>) /\
      (<<ATTATCHED: not_attatched (fun loc to => L loc to /\ ~ List.In (loc, to) updates) (Thread.memory th1')>>) /\
      (<<TRACE: List.Forall2 (fun em em' => <<EVENT: shorter_event (fst em') (fst em)>> /\ <<MEM: shorter_memory (snd em') (snd em)>>) tr tr'>>) /\
      (<<MEMORY: List.Forall (fun em => not_attatched (fun loc to => L loc to /\ ~ List.In (loc, to) updates) (snd em)) tr'>>) /\
      (<<COMPLETE:
         forall loc from (SAT: List.In (loc, from) updates),
         exists to valr valw releasedr releasedw ordr ordw mem,
           <<IN: List.In (ThreadEvent.update loc from to valr valw releasedr releasedw ordr ordw, mem) tr'>> >>).
Proof.
  apply traced_step_equivalent in STEPS.
  setoid_rewrite traced_step_equivalent. ginduction STEPS; i.
  - exists [], th0, []. esplits; eauto.
    + econs.
    + refl.
    + eapply not_attatched_mon; eauto. i. des. auto.
    + i. ss.
  - rewrite list_Forall_app in PRED. des. inv FORALL1. ss.
    exploit IHSTEPS; eauto. i. des. clear IHSTEPS.
    destruct (classic (no_update_on (fun loc to => L loc to /\ ~ List.In (loc, to) updates) tle)).
    + exploit no_update_on_step2; try apply SHORTER; eauto.
      { eapply traced_step_promises_le; eauto.
        apply traced_step_equivalent; eauto. }
      i. des. exists updates, th_src', (tr'++[(e_src, (Thread.memory th1'))]).
      esplits; eauto.
      * econs; eauto.
      * eapply list_Forall2_app; eauto. econs; eauto. ss. split; auto.
        apply shorter_thread_shorter_memory; auto.
      * eapply list_Forall_app; eauto.
      * i. exploit COMPLETE; eauto. i. des.
        esplits. eapply List.in_or_app; eauto.

    + unfold no_update_on in H. des_ifs. apply NNPP in H. des.
      hexploit (@no_update_on_step2 (fun loc0 to => L loc0 to /\ ~ List.In (loc0, to) ((loc, tsr) :: updates))); try apply TL; try apply SHORTER; eauto.
      { eapply traced_step_promises_le; eauto.
        apply traced_step_equivalent; eauto. }
      { ss. split; auto. ii. des; auto. }
      { eapply not_attatched_mon; [eauto|]. i. ss. des; auto. }
      i. des. exists ((loc, tsr) :: updates), th_src', (tr'++[(e_src, (Thread.memory th1'))]).
      esplits; eauto.
      * econs; eauto.
      * eapply list_Forall2_app; eauto. econs; eauto. ss. split; auto.
        apply shorter_thread_shorter_memory; auto.
      * eapply List.Forall_impl; cycle 1.
        { eapply list_Forall_app; eauto. }
        { i. ss. eapply not_attatched_mon; eauto. i. ss. des. split; auto. }
      * i. inv SAT; clarify.
        { inv EVENT. esplits. apply List.in_or_app. right. econs; eauto. }
        { exploit COMPLETE; eauto. i. des.
          esplits. apply List.in_or_app. left. eauto. }
Qed.

Lemma after_promise_covered
      prom0 mem0 loc from to msg prom1 mem1 kind
      (CANCEL: Memory.op_kind_is_cancel kind = false)
      (PROMISE: AMemory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
      ts (ITV: Interval.mem (from, to) ts)
  :
    covered loc ts mem1.
Proof.
  dup PROMISE. eapply AMemory.promise_get2 in PROMISE0; auto. des.
  econs; eauto.
Qed.

Lemma after_write_covered
      prom0 mem0 loc from to val released prom1 mem1 kind
      (WRITE: AMemory.write prom0 mem0 loc from to val released prom1 mem1 kind)
      ts (ITV: Interval.mem (from, to) ts)
  :
    covered loc ts mem1.
Proof.
  inv WRITE. eapply after_promise_covered; eauto.
  inv PROMISE; clarify.
Qed.

Lemma blank_write_write_not_in (L: Loc.t -> Time.t -> Prop)
      prom0 mem0 loc from to val released prom1 mem1 kind
      (WRITE: AMemory.write prom0 mem0 loc from to val released prom1 mem1 kind)
      (COVERED: forall loc' ts' (SAT: L loc' ts'), ~ covered loc' ts' mem1)
      ts (ITV: Interval.mem (from, to) ts)
  :
    ~ L loc ts.
Proof.
  ii. eapply COVERED; eauto. eapply after_write_covered; eauto.
Qed.

Lemma not_cancel_promise_covered
      prom0 mem0 loc from to msg prom1 mem1 kind
      (CANCEL: Memory.op_kind_is_cancel kind = false)
      (PROMISE: AMemory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
  :
    forall loc to (COVERED: covered loc to mem0),
      covered loc to mem1.
Proof.
  inv PROMISE; i; clarify.
  - eapply add_covered; eauto.
  - eapply split_covered; eauto.
  - eapply lower_covered; eauto.
Qed.

Lemma write_covered
      prom0 mem0 loc from to val released prom1 mem1 kind
      (WRITE: AMemory.write prom0 mem0 loc from to val released prom1 mem1 kind)
  :
    forall loc to (COVERED: covered loc to mem0),
      covered loc to mem1.
Proof.
  inv WRITE. eapply not_cancel_promise_covered; eauto.
  inv PROMISE; clarify.
Qed.

Lemma not_cancel_step_covered
      lang (th0 th1: Thread.t lang) e
      (STEP: AThread.step_allpf e th0 th1)
      (CANCEL: ~ is_cancel e)
  :
    forall loc to (COVERED: covered loc to (Thread.memory th0)),
      covered loc to (Thread.memory th1).
Proof.
  inv STEP. inv STEP0.
  - inv STEP. inv LOCAL. ss.
    eapply not_cancel_promise_covered; eauto. des_ifs.
  - inv STEP. inv LOCAL; ss.
    + inv LOCAL0. eapply write_covered; eauto.
    + inv LOCAL2. eapply write_covered; eauto.
Qed.

Lemma not_cancel_steps_covered
      lang (th0 th1: Thread.t lang) tr
      (STEP: traced_step tr th0 th1)
      (CANCEL: List.Forall (fun em => ~ is_cancel (fst em)) tr)
  :
    forall loc to (COVERED: covered loc to (Thread.memory th0)),
      covered loc to (Thread.memory th1).
Proof.
  ginduction STEP; auto. i. inv CANCEL.
  eapply IHSTEP; eauto. eapply not_cancel_step_covered; eauto.
Qed.

Lemma blank_promise_write_not_in (L: Loc.t -> Time.t -> Prop)
      prom0 mem0 loc from to msg prom1 mem1 kind
      (CANCEL: Memory.op_kind_is_cancel kind = false)
      (PROMISE: AMemory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
      (COVERED: forall loc' ts' (SAT: L loc' ts'), ~ covered loc' ts' mem1)
      ts (ITV: Interval.mem (from, to) ts)
  :
    ~ L loc ts.
Proof.
  ii. eapply COVERED; eauto. eapply after_promise_covered; eauto.
Qed.

Lemma blank_step_write_not_in (L: Loc.t -> Time.t -> Prop)
      lang (th0 th1: Thread.t lang) e
      (STEP: AThread.step_allpf e th0 th1)
      (COVERED: forall loc' ts' (SAT: L loc' ts'), ~ covered loc' ts' (Thread.memory th1))
  :
    write_not_in L e.
Proof.
  inv STEP. inv STEP0; inv STEP; ss.
  - inv LOCAL. des_ifs.
    eapply blank_promise_write_not_in; eauto.
  - inv LOCAL; ss.
    + inv LOCAL0. eapply blank_write_write_not_in; eauto.
    + inv LOCAL2. eapply blank_write_write_not_in; eauto.
Qed.

Lemma blank_steps_write_not_in (L: Loc.t -> Time.t -> Prop)
      lang (th0 th1: Thread.t lang) tr
      (STEP: traced_step tr th0 th1)
      (CANCEL: List.Forall (fun em => ~ is_cancel (fst em)) tr)
      (COVERED: forall loc' ts' (SAT: L loc' ts'), ~ covered loc' ts' (Thread.memory th1))
  :
    List.Forall (fun em => write_not_in L (fst em)) tr.
Proof.
  ginduction STEP; auto. i. inv CANCEL. econs; eauto.
  eapply blank_step_write_not_in; eauto.
  ii. eapply COVERED; eauto.
  eapply not_cancel_steps_covered; eauto.
Qed.

Lemma promise_should_be_written_promise
      prom0 mem0 loc from to msg prom1 mem1 kind
      (PROMISE: AMemory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
      loc0 to0
      (PROMISED: concrete_promised prom0 loc0 to0)
  :
    concrete_promised prom1 loc0 to0.
Proof.
  inv PROMISED. inv PROMISE.
  - eapply Memory.add_get1 in PROMISES; eauto. econs; eauto.
  - eapply Memory.split_get1 in PROMISES; eauto. des. econs; eauto.
  - eapply Memory.lower_get1 in PROMISES; eauto. des.
    clarify. inv MSG_LE. econs; eauto.
  - dup PROMISES. eapply Memory.remove_get1 in PROMISES; eauto. des.
    + clarify. eapply Memory.remove_get0 in PROMISES0. des. clarify.
    + econs; eauto.
Qed.

Lemma promise_should_be_written_write
      prom0 mem0 loc from to val released prom1 mem1 kind
      (WRITE: AMemory.write prom0 mem0 loc from to val released prom1 mem1 kind)
      loc0 to0
      (NEQ: (loc0, to0) <> (loc, to))
      (PROMISED: concrete_promised prom0 loc0 to0)
  :
    concrete_promised prom1 loc0 to0.
Proof.
  inv WRITE. eapply promise_should_be_written_promise in PROMISE; eauto.
  inv PROMISE. eapply Memory.remove_get1 in GET; eauto. des; clarify.
  econs; eauto.
Qed.

Lemma promise_should_be_written_write_step
      lc0 sc0 mem0 loc from to val releasedm released ord lc1 sc1 mem kind
      (WRITE: ALocal.write_step lc0 sc0 mem0 loc from to val releasedm released ord lc1 sc1 mem kind)
      loc0 to0
      (NEQ: ~ ((loc0, to0) = (loc, to) /\ Ordering.le ord Ordering.relaxed))
      (PROMISED: concrete_promised (Local.promises lc0) loc0 to0)
  :
    concrete_promised (Local.promises lc1) loc0 to0.
Proof.
  inv WRITE. ss. apply not_and_or in NEQ. apply or_strengthen in NEQ. des.
  - eapply promise_should_be_written_write in PROMISED; eauto.
  - apply NNPP in NOT. clarify.
    exfalso. inv PROMISED. dup GET. eapply RELEASE in GET; cycle 1.
    { destruct ord; ss. }
    inv WRITE0. inv PROMISE; ss.
    + apply Memory.add_get0 in PROMISES. des. clarify.
    + apply Memory.split_get0 in PROMISES. des. clarify.
    + apply Memory.lower_get0 in PROMISES. des. clarify.
      inv MSG_LE. inv RELEASED. unfold TView.write_released in *. des_ifs.
      destruct ord; ss.
Qed.

Lemma promise_should_be_written_step
      lang (th0 th1: Thread.t lang) e
      (STEP: AThread.step_allpf e th0 th1)
      loc0 to0
      (NEQ: match e with
            | ThreadEvent.write loc _ to _ _ ordw
            | ThreadEvent.update loc _ to _ _ _ _ _ ordw =>
              ~ ((loc0, to0) = (loc, to) /\ Ordering.le ordw Ordering.relaxed)
            | _ => True
            end)
      (PROMISED: concrete_promised (Local.promises (Thread.local th0)) loc0 to0)
  :
    concrete_promised (Local.promises (Thread.local th1)) loc0 to0.
Proof.
  inv STEP. inv STEP0.
  - inv STEP. inv LOCAL. eapply promise_should_be_written_promise; eauto.
  - inv STEP. inv LOCAL; ss; try by (inv LOCAL0; auto).
    + inv LOCAL0. eapply promise_should_be_written_write_step; eauto.
    + inv LOCAL1. inv LOCAL2. eapply promise_should_be_written_write_step; eauto.
Qed.

Definition rlx_write_to (loc: Loc.t) (to: Time.t) (e: ThreadEvent.t): Prop :=
  match e with
  | ThreadEvent.write loc0 _ to0 _ _ ordw
  | ThreadEvent.update loc0 _ to0 _ _ _ _ _ ordw =>
    (loc, to) = (loc0, to0) /\ Ordering.le ordw Ordering.relaxed
  | _ => False
  end.

Lemma promise_should_be_written_steps
      lang (th0 th1: Thread.t lang) tr
      (STEP: traced_step tr th0 th1)
      loc to
      (PROMISED: concrete_promised (Local.promises (Thread.local th0)) loc to)
      (NPROMISED: ~ concrete_promised (Local.promises (Thread.local th1)) loc to)
  :
    exists e m,
      (<<IN: List.In (e, m) tr>>) /\
      (<<WRITETO: rlx_write_to loc to e>>).
Proof.
  ginduction STEP; i.
  - exfalso. clarify.
  - destruct (classic (concrete_promised (Local.promises (Thread.local th1)) loc to)).
    + exploit IHSTEP; eauto. i. des.
      esplits; eauto. ss. eauto.
    + esplits.
      * ss. left. auto.
      * apply NNPP. intros WRITETO. apply H.
        eapply promise_should_be_written_step; eauto.
        unfold rlx_write_to in *. des_ifs.
Qed.

Lemma cancel_concrete_promises_same P lang e th0 th1
      (STEP: (@pred_step P lang) e th0 th1)
      (PRED: P <1= is_cancel)
  :
    concrete_promised (Local.promises (Thread.local th0)) <2=
    concrete_promised (Local.promises (Thread.local th1)).
Proof.
  inv STEP. eapply PRED in SAT. unfold is_cancel in SAT. des_ifs.
  inv STEP0. inv STEP; inv STEP0; ss.
  - inv LOCAL. inv PROMISE; ss.
    ii. inv PR. econs.
    erewrite Memory.remove_o; eauto.
    des_ifs; eauto. ss. des. clarify.
    eapply Memory.remove_get0 in PROMISES. des. clarify.
  - inv LOCAL.
Qed.

Lemma cancels_concrete_promises_same P lang th0 th1
      (STEP: rtc (tau (@pred_step P lang)) th0 th1)
      (PRED: P <1= is_cancel)
  :
    concrete_promised (Local.promises (Thread.local th0)) <2=
    concrete_promised (Local.promises (Thread.local th1)).
Proof.
  ginduction STEP; ss. i. eapply IHSTEP; eauto.
  inv H. eapply cancel_concrete_promises_same; eauto.
Qed.

Lemma not_attatched_write_not_in_gap L lang (th0 th1: Thread.t lang) tr
      (STEP: traced_step tr th0 th1)
      (CANCEL: List.Forall (fun em => ~ is_cancel (fst em)) tr)
      (ATTATCH: not_attatched L (Thread.memory th1))
  :
    forall loc to (SAT: L loc to),
    exists to',
      (<<TS: Time.lt to to'>>) /\
      (<<EVENT: List.Forall (fun em => write_not_in (fun loc0 to0 => loc0 = loc /\ <<ITV: Interval.mem (to, to') to0>>) (fst em)) tr>>).
Proof.
  i. exploit ATTATCH; eauto. i. des. esplits; eauto.
  eapply blank_steps_write_not_in; eauto. i. des; clarify. eauto.
Qed.

Lemma memory_cap_covered prom mem0 mem1
      (CAP: Memory.cap prom mem0 mem1)
      (INHABITED: Memory.inhabited mem0)
      loc to
      (TS0: Time.lt Time.bot to)
      (TS1: Time.le to (Memory.max_ts loc mem0))
  :
    covered loc to mem1.
Proof.
  inv CAP.
  set (@cell_elements_least
         (mem0 loc)
         (fun to' => Time.le to to')). des; cycle 1.
  { exfalso. exploit Memory.max_ts_spec.
    - eapply INHABITED.
    - i. des. exploit EMPTY; eauto. }
  set (@cell_elements_greatest
         (mem0 loc)
         (fun to' => Time.lt to' to)). des; cycle 1.
  { exfalso. exploit EMPTY.
    - eapply INHABITED.
    - eauto.
    - ss. }
  destruct (Time.le_lt_dec to from).
  - exploit MIDDLE.
    + econs.
      * eapply GET0.
      * eapply GET.
      * eapply TimeFacts.lt_le_lt; eauto.
      * i. destruct (Memory.get loc ts mem0) eqn:GET1; auto.
        exfalso. destruct p.
        destruct (Time.le_lt_dec to ts).
        { exploit LEAST; eauto. i.
          eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
          { eapply x. }
          eapply TimeFacts.le_lt_lt.
          { eapply TS3. }
          { eapply memory_get_ts_strong in GET. des; clarify; ss.
            exfalso. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
            - eapply l.
            - eauto. } }
        { exploit GREATEST; eauto. i.
          eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
          { eapply x. }
          { eauto. } }
    + eapply TimeFacts.lt_le_lt; eauto.
    + i. econs; eauto. econs; eauto.
  - econs.
    + eapply Memory.cap_le; try apply GET; eauto. refl.
    + econs; eauto.
Qed.

Lemma collapsing_last_reserves_promise_or_later
      L prom mem0 mem1 mem2 max
      (LOC: L = (fun loc => Memory.latest_reserve loc prom mem0))
      (MLE: Memory.le prom mem0)
      (RESERVEWF: memory_reserve_wf mem0)
      (CLOSED: Memory.closed mem0)
      (CAP: Memory.cap prom mem0 mem1)
      (MAX: Memory.max_full_timemap mem0 max)
      (FORGET: forget_memory (collapsing_latest_reserves_times L mem0 \2/ collapsing_caps_times L mem0 mem1) mem2 mem1)
      loc to
      (UNWRITABLE: ~ unwritable mem2 prom loc to)
  :
    <<COVERED: concrete_covered prom mem0 loc to>> \/ <<LATER: later_times max loc to>> \/ <<BOT: to = Time.bot>>.
Proof.
  clarify.
  assert (RESERVEWF0: Memory.reserve_wf prom mem0).
  { eapply memory_reserve_wf_mon; eauto. }
  assert (INHABITED: Memory.inhabited mem0).
  { inv CLOSED. eauto. }
  assert (MLE0: Memory.le prom mem2).
  { eapply collapsing_caps_forget_prom_le; eauto.
    ii. clarify. unfold Memory.latest_reserve in SAT. des_ifs. }
  erewrite unwritable_eq in UNWRITABLE; eauto.
  eapply not_and_or in UNWRITABLE. des.
  - destruct (Time.le_lt_dec to Time.bot).
    { right. right. destruct l; auto. exfalso.
      eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto.
      eapply Time.bot_spec. }
    right. left.
    destruct (Time.le_lt_dec to (max loc)); auto. exfalso.
    eapply UNWRITABLE. red.
    eapply forget_covered; eauto.
    + eapply memory_cap_covered; eauto.
      etrans; eauto. specialize (MAX loc).
      eapply max_full_ts_le_max_ts; eauto.
    + ii. inv H. ss. des.
      * unfold collapsing_latest_reserves_times, collapsing_latest_reserves in SAT.
        des. clarify. specialize (MAX loc). des; clarify.
        dup RESERVE. eapply Memory.cap_le in RESERVE0; eauto; [|refl]. clarify.
        eapply max_ts_reserve_from_full_ts in RESERVE; eauto.
        exploit Memory.max_full_ts_inj.
        { eapply RESERVE. }
        { eapply MAX. }
        i. clarify. eapply Time.lt_strorder.
        eapply TimeFacts.lt_le_lt; eauto.
      * unfold collapsing_caps_times, collapsing_caps, caps in SAT. des. clarify.
        exploit Memory.cap_inv; eauto. i. des; clarify.
        eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
        { eapply FROM. }
        etrans.
        { eapply l0. }
        { specialize (MAX loc). des; clarify.
          eapply max_full_ts_le_max_ts; eauto. }
  - apply NNPP in UNWRITABLE.
    destruct (Time.le_lt_dec to (max loc)).
    + left. econs; eauto.
    + right. left. ss.
Qed.

Lemma write_not_in_write_in L0 L1
      (LOCS: forall loc to (NSAT: ~ L0 loc to),
          <<SAT: L1 loc to>> \/ <<BOT: to = Time.bot>>)
  :
    write_not_in L0 <1= write_in L1.
Proof.
  i. destruct x0; ss.
  - i. dup IN. eapply PR in IN. eapply LOCS in IN. des; auto.
    clarify. inv IN0. ss. exfalso.
    eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
    + eapply FROM.
    + eapply Time.bot_spec.
  - i. dup IN. eapply PR in IN. eapply LOCS in IN. des; auto.
    clarify. inv IN0. ss. exfalso.
    eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
    + eapply FROM.
    + eapply Time.bot_spec.
Qed.


Definition pf_consistent_drf'' lang (e0:Thread.t lang): Prop :=
  let L := (fun loc => Memory.latest_reserve loc (Local.promises (Thread.local e0)) (Thread.memory e0)) in
  forall mem1 mem2 max
         (CAP: Memory.cap (Local.promises (Thread.local e0)) (Thread.memory e0) mem1)
         (FORGET: forget_memory (collapsing_latest_reserves_times L (Thread.memory e0) \2/ collapsing_caps_times L (Thread.memory e0) mem1) mem2 mem1)
         (MAX: Memory.max_full_timemap (Thread.memory e0) max),
  exists e1 (U: list Loc.t) (AU: list Loc.t),
    (<<DISJOINT: forall loc (INU: List.In loc U) (INAU: List.In loc AU), False>>) /\
    (<<AUPDATES: forall loc (INAU: List.In loc AU), ~ L loc>>) /\

    (<<STEPS0: rtc (tau (@pred_step is_cancel lang)) (Thread.mk _ (Thread.state e0) (Thread.local e0) TimeMap.bot mem2) e1>>) /\
    (<<NORESERVE: no_reserves (Local.promises (Thread.local e1))>>) /\
    (<<NOATTATCH: not_attatched (Memory.max_full_ts (Thread.memory e0)) (Thread.memory e1)>>) /\
    (<<MAXMAP: TimeMap.le (Memory.max_timemap (Thread.memory e1)) max>>) /\
    exists e2 tr max',
      (<<STEPS1: traced_step tr e1 e2>>) /\

      (<<TIMEMAP: TimeMap.le max max'>>) /\
      (<<GAP: forall loc (NUPDATES: ~ List.In loc (U ++ AU)),
          Time.lt (max loc) (max' loc)>>) /\

      (<<ATTATCHED: not_attatched (fun loc to => (<<MAX: Memory.max_full_ts (Thread.memory e0) loc to>>) /\
                                                 (<<NUPDATES: ~ List.In loc (U ++ AU)>>))
                                  (Thread.memory e2)>>) /\
      (<<TRACE: List.Forall (fun em => <<EVENT: (promise_free /1\ (fun e => ~ is_cancel e) /1\ no_sc
                                                              /1\ no_acq_update_on ((fun loc to => L loc) /2\ Memory.max_full_ts (Thread.memory e0))
                                                              /1\
                                                              (write_in (later_times max' \2/ (concrete_covered (Local.promises (Thread.local e0)) (Thread.memory e0) /2\ earlier_times max)))
                                                              /1\
                                                              (fun e => ThreadEvent.get_machine_event e = MachineEvent.silent)

                                                ) (fst em)>> /\ <<MEMORY: not_attatched (fun loc to => (<<MAX: Memory.max_full_ts (Thread.memory e0) loc to>>) /\
                                                                                                       (<<NUPDATES: ~ List.In loc (U ++ AU)>>)) (snd em)>>) tr>>) /\
      (<<COMPLETEU:
         forall loc (SAT: List.In loc U),
         exists to valr valw releasedr releasedw ordr ordw mem,
           <<IN: List.In (ThreadEvent.update loc (max loc) to valr valw releasedr releasedw ordr ordw, mem) tr>> /\ <<ORDR: Ordering.le ordr Ordering.strong_relaxed>> >>) /\
      (<<COMPLETEAU:
         forall loc (SAT: List.In loc AU),
         exists to valr valw releasedr releasedw ordr ordw mem,
           <<IN: List.In (ThreadEvent.update loc (max loc) to valr valw releasedr releasedw ordr ordw, mem) tr>> >>) /\
      (__guard__((exists st',
                     (<<LOCAL: Local.failure_step (Thread.local e2)>>) /\
                     (<<FAILURE: Language.step lang ProgramEvent.failure (@Thread.state lang e2) st'>>)) \/
                 ((<<PROMISES: (Local.promises (Thread.local e2)) = Memory.bot>>) /\
                  (<<COMPLETEW:
                     forall loc to (PROMISED: concrete_promised (Local.promises (Thread.local e0)) loc to),
                     exists e m,
                       (<<IN: List.In (e, m) tr>>) /\
                       (<<WRITETO: rlx_write_to loc to e>>)>>))))
.

Lemma traced_steps_unwritable_increase lang (th0 th1: Thread.t lang) tr
      (STEP: traced_step tr th0 th1)
  :
    unwritable (Thread.memory th0) (Local.promises (Thread.local th0)) <2=
    unwritable (Thread.memory th1) (Local.promises (Thread.local th1)).
Proof.
  ginduction STEP; eauto.
  i. eapply IHSTEP. inv HD. eapply unwritable_increase; eauto.
Qed.

Lemma traced_step_write_not_in lang (th_tgt th_tgt': Thread.t lang) tr
      (MLE: Memory.le (Local.promises (Thread.local th_tgt)) (Thread.memory th_tgt))
      (STEP: traced_step tr th_tgt th_tgt')
  :
    List.Forall (fun em => write_not_in (unwritable (Thread.memory th_tgt) (Local.promises (Thread.local th_tgt))) (fst em)) tr.
Proof.
  ginduction STEP; i; ss. econs.
  - ss. inv HD. eapply step_write_not_in; eauto.
  - eapply List.Forall_impl; cycle 1.
    + eapply IHSTEP. eapply step_promises_le; eauto.
    + i. ss. eapply write_not_in_mon; eauto.
      i. inv HD. eapply unwritable_increase; eauto.
Qed.

Lemma traced_step_wf_event lang (th0 th1: Thread.t lang) tr
      (INHABITED: Memory.inhabited (Thread.memory th0))
      (STEP: traced_step tr th0 th1)
  :
    List.Forall (fun em => wf_event (fst em)) tr.
Proof.
  ginduction STEP; i; ss. econs.
  - eapply step_wf_event; eauto.
    econs; eauto. instantiate (1:=fun _ => True). ss.
  - eapply IHSTEP; eauto. inv HD. eapply AThread.step_inhabited; eauto.
Qed.

Lemma write_not_in_sum L0 L1 e
      (NOTIN0: write_not_in L0 e)
      (NOTIN1: write_not_in L1 e)
  :
    write_not_in (L0 \2/ L1) e.
Proof.
  destruct e; ss; des_ifs; ii; des.
  - eapply NOTIN0; eauto.
  - eapply NOTIN1; eauto.
  - eapply NOTIN0; eauto.
  - eapply NOTIN1; eauto.
  - eapply NOTIN0; eauto.
  - eapply NOTIN1; eauto.
Qed.

Lemma write_not_in_sum2 A (L: A -> Loc.t -> Time.t -> Prop) e
      (NOTIN: forall a, write_not_in (L a) e)
  :
    write_not_in (fun loc to => exists a, (L a) loc to) e.
Proof.
  destruct e; ss; des_ifs; ii; des.
  - eapply NOTIN; eauto.
  - eapply NOTIN; eauto.
  - eapply NOTIN; eauto.
Qed.

Lemma pf_consistent_pf_consistent_drf'' lang (th: Thread.t lang)
      (WF: Local.wf (Thread.local th) (Thread.memory th))
      (MEM: Memory.closed (Thread.memory th))
      (CONSISTENT: pf_consistent_drf' th)
      (RESERVEWF: memory_reserve_wf (Thread.memory th))
  :
    pf_consistent_drf'' th.
Proof.
  set (L := (fun loc => Memory.latest_reserve loc (Local.promises (Thread.local th)) (Thread.memory th))).
  ii. exploit CONSISTENT; eauto. i. des.

  assert (LCWFSRC: Local.wf (Thread.local th) mem2).
  { dup WF. inv WF.
    eapply memory_concrete_le_local_wf; eauto.
    - eapply collapsing_caps_forget_le; eauto.
    - eapply collapsing_caps_forget_prom_le; eauto.
      ii. clarify. unfold Memory.latest_reserve in SAT.
      rewrite GET in SAT. clarify. }

  eapply pred_steps_traced_step in STEPS1. des.

  exploit updates_list_exists; try apply STEPS.
  { eapply List.Forall_impl; eauto. i. ss. des; auto. }
  { eapply steps_promises_le in STEPS0; eauto. ss.
    inv LCWFSRC. auto. }
  { eauto. }
  i. des.

  exploit traced_step_write_not_in; try apply STEPS1.
  { eapply steps_promises_le; eauto. inv LCWFSRC. auto. } intros WRITENOTIN.
  exploit traced_step_wf_event; try apply STEPS1.
  { ii. eapply cancels_concrete_same; eauto. ss.
    exploit collapsing_caps_forget_closed; eauto. i. inv x1. auto. } intros WFEVT.

  hexploit (list_filter_exists (fun locto => L (fst locto)) updates). i. des.
  hexploit (list_filter_exists (fun locto => ~ L (fst locto)) updates). i. des.

  assert (LOCS: forall loc to
                       (NUPDATES: Memory.max_full_ts (Thread.memory th) loc to /\
                                  ~ List.In loc (List.map fst l' ++ List.map fst l'0)),
             Memory.max_full_ts (Thread.memory th) loc to /\ ~ List.In (loc, to) updates).
  { i. des. split; auto.
    intros IN. apply NUPDATES0. apply List.in_or_app.
    dup IN. eapply List.Forall_forall in UPDATESWF; eauto.
    destruct (classic (L loc)).
    - left. hexploit (proj1 (@COMPLETE0 (loc, to))); auto.
      i. eapply (List.in_map fst) in H0. ss.
    - right. hexploit (proj1 (@COMPLETE1 (loc, to))); auto.
      i. eapply (List.in_map fst) in H0. ss. }

  exists e1, (List.map fst l'), (List.map fst l'0). splits; auto.
  { i. apply List.in_map_iff in INAU. apply List.in_map_iff in INU. des. clarify.
    apply (proj2 (@COMPLETE0 x1)) in INU0.
    apply (proj2 (@COMPLETE1 x)) in INAU0. des.
    rewrite INAU in *. clarify. }
  { i. apply List.in_map_iff in INAU. des. clarify.
    apply (proj2 (@COMPLETE1 x)) in INAU0. des. auto. }

  hexploit (choice (fun loc to =>
                      (<<NOGAP: forall (IN: List.In loc (List.map fst l' ++ List.map fst l'0)),
                          to = max loc>>) /\
                      (<<GAP: forall (NIN: ~ List.In loc (List.map fst l' ++ List.map fst l'0)),
                          Time.lt (max loc) to>>) /\
                      (<<EVENT: List.Forall (fun em => write_not_in (fun loc0 to0 => loc0 = loc /\ <<ITV: Interval.mem ((max loc), to) to0>>) (fst em)) tr'>>))).
  { intros loc. destruct (classic (List.In loc (List.map fst l' ++ List.map fst l'0))).
    - exists (max loc). splits; auto.
      + i. clarify.
      + eapply List.Forall_impl; try apply WFEVT. i. destruct a. ss.
        destruct t; ss; des_ifs; ii; des.
        * inv H2. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto.
        * inv H2. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto.
        * inv H2. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto.
    - exploit not_attatched_write_not_in_gap; eauto.
      + eapply List.Forall_forall. i.
        exploit list_Forall2_in; eauto. i. des.
        eapply List.Forall_forall in IN; eauto. ss. des.
        destruct a, x. ss. inv EVENT; ss.
      + ss. splits; eauto. ii. eapply H. eapply List.in_or_app.
        destruct (classic (L loc)).
        * left. exploit (proj1 (@COMPLETE0 (loc, max loc))).
          { splits; eauto. }
          i. eapply (List.in_map fst) in x1; eauto.
        * right. exploit (proj1 (@COMPLETE1 (loc, max loc))).
          { splits; eauto. }
          i. eapply (List.in_map fst) in x1; eauto.
      + i. des. exists to'. splits.
        * i. clarify.
        * i. splits; auto.
        * ss. }
  intros [max' MAX'].

  exists th1', tr', max'. esplits; eauto.
  - ii. destruct (classic (List.In loc (List.map fst l' ++ List.map fst l'0))).
    + right. specialize (MAX' loc). des. symmetry. eapply NOGAP. auto.
    + left. specialize (MAX' loc). des. exploit GAP; eauto.
  - i. specialize (MAX' loc). des. exploit GAP; eauto.

  - eapply not_attatched_mon; eauto.
  - eapply list_Forall_sum.
    + eapply MEMORY.
    + instantiate (1:=fun em => (write_in (later_times max' \2/ (concrete_covered (Local.promises (Thread.local th)) (Thread.memory th) /2\ earlier_times max)) /1\ (promise_free /1\ (fun e => ~ is_cancel e) /1\ no_sc /1\ no_acq_update_on ((fun loc to => L loc) /2\ Memory.max_full_ts (Thread.memory th)) /1\ (fun e => ThreadEvent.get_machine_event e = MachineEvent.silent))) (fst em)).
      eapply List.Forall_forall. i. ss. dup H.
      eapply list_Forall2_in in H; eauto. des.
      eapply List.Forall_forall in IN; eauto. destruct a, x. ss. des.
      split.

      * exploit write_not_in_sum.
        { eapply List.Forall_forall in WRITENOTIN; eauto. }
        { eapply write_not_in_sum2 with
              (L:= fun loc =>
                     (fun loc0 to0 =>
                        loc0 = loc /\ <<ITV: Interval.mem (max loc, max' loc) to0 >>)).
          i. ss. specialize (MAX' a). des.
          eapply List.Forall_forall in EVENT0; eauto. ss. }
        intros NOTIN. ss.
        eapply write_not_in_write_in; [|apply NOTIN]. i.
        apply not_or_and in NSAT. des.
        hexploit collapsing_last_reserves_promise_or_later; eauto; ss.
        { inv WF. auto. }
        { ii. eapply thread_steps_pred_steps in STEPS0.
          eapply rtc_unwritable_increase in STEPS0; eauto. }
        i. destruct (Time.le_lt_dec to (max' loc)).
        { des; auto.
          - left. right. split; auto.
            destruct (Time.le_lt_dec to (max loc)); auto.
            exfalso. eapply NSAT0. esplits; eauto. econs; eauto.
          - left. left. exfalso. eapply NSAT0. esplits; eauto. econs; eauto. }
        { left. left. auto. }
      * inv EVENT; split; ss.
    + i. ss. des. splits; auto.
      eapply not_attatched_mon; eauto.

  - i. eapply List.in_map_iff in SAT. des. clarify.
    apply COMPLETE0 in SAT0. des. destruct x as [loc to]. ss.
    exploit COMPLETE; eauto.
    i. des. eapply List.Forall_forall in UPDATESWF; eauto.
    exploit Memory.max_full_ts_inj.
    { eapply UPDATESWF. }
    { eapply MAX. } i. ss. clarify.
    esplits; eauto.
    exploit list_Forall2_in; eauto. i. des. ss. inv EVENT.
    eapply List.Forall_forall in IN1; eauto. ss. des.
    rewrite <- H in *. ss. hexploit SAT2; eauto.
    destruct ordr; ss.
  - i. eapply List.in_map_iff in SAT. des. clarify.
    apply COMPLETE1 in SAT0. des. destruct x as [loc to]. ss.
    exploit COMPLETE; eauto.
    i. des. eapply List.Forall_forall in UPDATESWF; eauto.
    exploit Memory.max_full_ts_inj.
    { eapply UPDATESWF. }
    { eapply MAX. } i. ss. clarify.
    esplits; eauto.

  - inv SHORTER. unguard. des.
    + left. esplits; eauto.
    + right. split; auto. i.
      eapply cancels_concrete_promises_same in STEPS0; ss.
      * eapply promise_should_be_written_steps in STEPS0; eauto.
        i. ss. rewrite PROMISES. ii. inv H.
        erewrite Memory.bot_get in GET. clarify.
      * ss.
Qed.

Inductive latest_other_reserves (prom mem: Memory.t) (loc: Loc.t) (to: Time.t): Prop :=
| latest_other_reserves_intro
    from
    (MAX: to = Memory.max_ts loc mem)
    (GET: Memory.get loc to mem = Some (from, Message.reserve))
    (NONE: Memory.get loc to prom = None)
.

Definition mapping_map_lt_loc (f: Time.t -> Time.t -> Prop):=
  forall t0 t1 ft0 ft1
         (MAP0: f t0 ft0)
         (MAP1: f t1 ft1),
    Time.lt t0 t1 <-> Time.lt ft0 ft1.

Definition mapping_map_lt (f: Loc.t -> Time.t -> Time.t -> Prop): Prop :=
  forall loc t0 t1 ft0 ft1
         (MAP0: f loc t0 ft0)
         (MAP1: f loc t1 ft1),
    Time.lt t0 t1 <-> Time.lt ft0 ft1.

Lemma mapping_map_lt_locwise f
      (MAPLT: forall loc, mapping_map_lt_loc (f loc))
  :
    mapping_map_lt f.
Proof.
  eauto.
Qed.

Lemma mapping_map_lt_map_eq f
      (MAPLT: mapping_map_lt f)
  :
    mapping_map_eq f.
Proof.
  ii. destruct (Time.le_lt_dec ft0 ft1).
  - inv l; auto.
    erewrite <- (@MAPLT loc to to) in H; eauto.
    exfalso. eapply Time.lt_strorder; eauto.
  - erewrite <- (@MAPLT loc to to) in l; eauto.
    exfalso. eapply Time.lt_strorder; eauto.
Qed.

Lemma mapping_map_lt_map_le f
      (MAPLT: mapping_map_lt f)
  :
    mapping_map_le f.
Proof.
  ii. inv H.
  - left. erewrite (@MAPLT loc t0 t1) in H0; eauto.
  - right. inv H0.
    eapply mapping_map_lt_map_eq; eauto.
Qed.


Definition ident_map (loc: Loc.t) := @eq Time.t.

Lemma ident_map_lt
  :
    mapping_map_lt ident_map.
Proof.
  unfold ident_map in *. ii. clarify.
Qed.

Lemma ident_map_le
  :
    mapping_map_le ident_map.
Proof.
  apply mapping_map_lt_map_le, ident_map_lt.
Qed.

Lemma ident_map_bot
  :
    mapping_map_bot ident_map.
Proof.
  unfold ident_map in *. ii. clarify.
Qed.

Lemma ident_map_eq
  :
    mapping_map_eq ident_map.
Proof.
  apply mapping_map_lt_map_eq, ident_map_lt.
Qed.

Lemma ident_map_total
      loc to
  :
    exists fto,
      <<MAP: ident_map loc to fto >>.
Proof.
  esplits; eauto. refl.
Qed.

Lemma mapping_map_lt_non_collapsable f
      (MAPLT: mapping_map_lt f)
      loc to
  :
    non_collapsable f loc to.
Proof.
  ii. unfold collapsed in *. des.
  erewrite (MAPLT loc to' to) in TLE; eauto. eapply Time.lt_strorder; eauto.
Qed.

Lemma ident_map_timemap
      tm
  :
    timemap_map ident_map tm tm.
Proof.
  ii. refl.
Qed.

Lemma ident_map_view
      vw
  :
    view_map ident_map vw vw.
Proof.
  econs; eapply ident_map_timemap.
Qed.

Lemma ident_map_message
      msg
  :
    msg_map ident_map msg msg.
Proof.
  destruct msg; econs. destruct released; econs.
  apply ident_map_view.
Qed.

Lemma ident_map_promises
      prom
  :
    promises_map ident_map prom prom.
Proof.
  econs; i.
  - esplits; eauto.
    + eapply mapping_map_lt_non_collapsable.
      eapply ident_map_lt.
    + refl.
    + eapply ident_map_message.
  - esplits; eauto; refl.
Qed.

Lemma ident_map_local
      lc
  :
    local_map ident_map lc lc.
Proof.
  econs; i.
  - refl.
  - econs; i; eapply ident_map_view.
  - eapply ident_map_promises.
Qed.

Lemma mapping_map_lt_collapsable_unwritable f prom mem
      (MAPLT: mapping_map_lt f)
  :
    collapsable_unwritable f prom mem.
Proof.
  ii. exfalso. des.
  eapply mapping_map_lt_non_collapsable; try eassumption.
  inv ITV. eapply TimeFacts.lt_le_lt; eauto.
Qed.

Lemma ident_map_collapsing_latest_memory L prom mem0 mem1 mem2 mem3
      (MLE: Memory.le prom mem0)
      (CLOSED: Memory.closed mem0)
      (LOCS: L = (fun loc => Memory.latest_reserve loc prom mem0))
      (CAP: Memory.cap prom mem0 mem1)
      (FORGET0: forget_memory (collapsing_latest_reserves_times L mem0 \2/ collapsing_caps_times L mem0 mem1) mem2 mem1)
      (FORGET1: forget_memory (latest_other_reserves prom mem0) mem3 mem0)
  :
    memory_map ident_map mem2 mem3.
Proof.
  eapply memory_map2_memory_map.
  econs.
  - i. dup GET. eapply forget_memory_get in GET0; eauto. des.
    apply not_or_and in NOT. des.
    dup GET1. eapply Memory.cap_inv in GET0; eauto. des.
    + inv FORGET1.
      erewrite <- COMPLETE in GET0.
      * right. esplits.
        { refl. }
        { eapply ident_map_message. }
        { refl. }
        { eauto. }
      * intros LATEST. inv LATEST.
        eapply NOT. eexists. econs; eauto. splits; eauto.
        unfold Memory.latest_reserve. des_ifs.
    + clarify. left. auto.
    + clarify. exfalso. eapply NOT0.
      eexists. econs; eauto. esplits. econs; eauto.
  - i. dup GET. eapply forget_memory_get in GET0; eauto. des.
    dup GET1. eapply Memory.cap_le in GET0; eauto; [|refl].
    inv FORGET0.
    dup GET0. erewrite <- COMPLETE in GET2.
    + esplits.
      * refl.
      * eauto.
      * refl.
    + ii. des.
      * unfold collapsing_latest_reserves_times, collapsing_latest_reserves, Memory.latest_reserve in H.
        des. clarify. apply NOT. econs; eauto. des_ifs.
        eapply MLE in Heq. clarify.
      * unfold collapsing_caps_times, collapsing_caps, Memory.latest_reserve in H.
        des. inv CAP0. des. clarify.
Qed.

Lemma collapsing_latest_memory_concrete_le L prom mem0 mem1 mem2 mem3
      (MLE: Memory.le prom mem0)
      (CLOSED: Memory.closed mem0)
      (LOCS: L = (fun loc => Memory.latest_reserve loc prom mem0))
      (CAP: Memory.cap prom mem0 mem1)
      (FORGET0: forget_memory (collapsing_latest_reserves_times L mem0 \2/ collapsing_caps_times L mem0 mem1) mem2 mem1)
      (FORGET1: forget_memory (latest_other_reserves prom mem0) mem3 mem0)
  :
    memory_concrete_le mem2 mem3.
Proof.
  ii. dup GET. eapply forget_memory_get in GET0; eauto. des.
  apply not_or_and in NOT. des.
  dup GET1. eapply Memory.cap_inv in GET0; eauto. des; clarify.
  - inv FORGET1.
    erewrite <- COMPLETE in GET0; eauto.
    ii. inv H. clarify.
  - exfalso. eapply NOT0.
    eexists. econs; eauto. esplits. econs; eauto.
Qed.

Lemma forget_latest_other_reserves_promises_le prom mem0 mem1
      (MLE: Memory.le prom mem0)
      (FORGET: forget_memory (latest_other_reserves prom mem0) mem1 mem0)
  :
    Memory.le prom mem1.
Proof.
  ii. inv FORGET. erewrite COMPLETE; eauto.
  ii. inv H. clarify.
Qed.

Lemma forget_latest_other_reserves_concrete_le prom mem0 mem1
      (FORGET: forget_memory (latest_other_reserves prom mem0) mem1 mem0)
  :
    memory_concrete_le mem0 mem1.
Proof.
  ii. inv FORGET. erewrite COMPLETE; eauto.
  ii. inv H. clarify.
Qed.

Lemma concrete_le_inhabited mem0 mem1
      (INHABITED: Memory.inhabited mem0)
      (MLE: memory_concrete_le mem0 mem1)
  :
    Memory.inhabited mem1.
Proof.
  ii. eapply MLE; eauto.
Qed.

Lemma forget_latest_other_reserves_closed prom mem0 mem1
      (CLOSED: Memory.closed mem0)
      (MLE: Memory.le prom mem0)
      (FORGET: forget_memory (latest_other_reserves prom mem0) mem1 mem0)
  :
    Memory.closed mem1.
Proof.
  inv CLOSED. econs; eauto.
  - i. dup MSG. eapply forget_memory_get in MSG; eauto. des.
    dup GET. eapply CLOSED0 in GET0. des. splits; auto.
    eapply memory_concrete_le_closed_msg; eauto.
    eapply forget_latest_other_reserves_concrete_le; eauto.
  - eapply concrete_le_inhabited; eauto.
    eapply forget_latest_other_reserves_concrete_le; eauto.
Qed.

Lemma ident_map_mappable_any_event e
  :
    mappable_evt ident_map e.
Proof.
  destruct e; ss; split; eapply ident_map_total.
Qed.

Lemma ident_map_event_write_not_in L e0 e1
      (EVENT: tevent_map ident_map e1 e0)
      (NOTIN: write_not_in L e0)
  :
    write_not_in L e1.
Proof.
  inv EVENT; ss.
  - des_ifs.
    + inv KIND; ss.
    + ii. eapply NOTIN; eauto. inv IN. ss.
      inv FROM. inv TO. econs; eauto.
  - ii. eapply NOTIN; eauto. inv IN. ss.
    inv FROM. inv TO. econs; eauto.
  - ii. eapply NOTIN; eauto. inv IN. ss.
    inv FROM. inv TO. econs; eauto.
Qed.

Lemma ident_map_event_no_acq_update_on L e0 e1
      (EVENT: tevent_map ident_map e1 e0)
      (ACQU: no_acq_update_on L e0)
  :
    no_acq_update_on L e1.
Proof.
  inv EVENT; ss. inv FROM. inv TO. auto.
Qed.

Lemma ident_map_event_write_in L e0 e1
      (EVENT: tevent_map ident_map e1 e0)
      (IN: write_in L e0)
  :
    write_in L e1.
Proof.
  inv EVENT; ss.
  - ii. eapply IN; eauto. inv IN0. ss.
    inv FROM. inv TO. econs; eauto.
  - ii. eapply IN; eauto. inv IN0. ss.
    inv FROM. inv TO. econs; eauto.
Qed.

Lemma map_event_promise_free f e0 e1
      (EVENT: tevent_map f e1 e0)
      (PROMISEFREE: promise_free e0)
  :
    promise_free e1.
Proof.
  inv EVENT; ss. inv KIND; ss.
  inv MSG0; ss. inv MSG; ss. inv MAP0; ss.
Qed.

Lemma map_event_no_sc f e0 e1
      (EVENT: tevent_map f e1 e0)
      (NOSC: no_sc e0)
  :
    no_sc e1.
Proof.
  inv EVENT; ss.
Qed.

Lemma ident_map_memory_not_attatched L mem0 mem1
      (MEMORY: memory_map ident_map mem0 mem1)
      (ATTATCHED: not_attatched L mem0)
  :
    not_attatched L mem1.
Proof.
  inv MEMORY. ii. exploit ATTATCHED; eauto. i. des.
  inv CONCRETE. exploit MAPPED; eauto. i. des; clarify.
  inv MSG. inv MSGLE. inv TO. splits.
  - econs; eauto.
  - esplits; eauto. ii.
    inv H. eapply ONLY in GET1; eauto. des; cycle 1.
    { exfalso. eapply Time.lt_strorder. eapply OUT; eauto. refl. }
    inv TO. inv FROM. eapply EMPTY.
    + eauto.
    + eapply COVERED. inv ITV0. econs; ss.
      * eapply TimeFacts.le_lt_lt; eauto.
      * etrans; eauto.
Qed.

Lemma ident_map_memory_max_ts mem0 mem1
      (INHABIED: Memory.inhabited mem1)
      (MEMORY: memory_map ident_map mem0 mem1)
      loc
  :
    Time.le (Memory.max_ts loc mem1) (Memory.max_ts loc mem0).
Proof.
  inv MEMORY.
  exploit Memory.max_ts_spec; eauto. i. des.
  instantiate (1:=loc) in MAX.
  dup GET. eapply ONLY in GET. des.
  - destruct (Time.le_lt_dec to from0).
    + inv TO. inv FROM.
      eapply memory_get_ts_strong in GET0. des; clarify.
      * rewrite GET1. eapply Time.bot_spec.
      * exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
        { eapply TS. }
        etrans; eauto.
    + exploit COVERED.
      * econs; eauto. refl.
      * i. inv x. eapply Memory.max_ts_spec in GET. des.
        etrans; eauto. inv TO. inv ITV. ss. etrans; eauto.
  - exfalso. eapply Time.lt_strorder. eapply OUT; eauto. refl.
Qed.

Lemma list_Forall2_in2 A B P (l0: list A) (l1: list B)
      (FORALL: List.Forall2 P l0 l1)
      a
      (IN: List.In a l0)
  :
    exists b,
      (<<IN: List.In b l1>>) /\ (<<SAT: P a b>>).
Proof.
  ginduction FORALL; eauto; i; ss. des; clarify.
  - esplits; eauto.
  - eapply IHFORALL in IN; eauto. des. esplits; eauto.
Qed.

Lemma write_not_cross_concrete_promise
      prom0 mem0 loc from to msg prom1 mem1 kind
      to0
      (CONCRETE: concrete_promised mem0 loc to0)
      (PROMISE: AMemory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
  :
    Time.le to to0 \/ Time.le to0 from.
Proof.
  inv CONCRETE. dup GET. eapply memory_get_ts_strong in GET0. des; clarify.
  { right. apply Time.bot_spec. }
  inv PROMISE.
  - eapply add_succeed_wf in MEM. des.
    hexploit DISJOINT; eauto. i.
    eapply disjoint_equivalent2 in H. des; auto; clarify.
    unfold Time.meet, Time.join in *. des_ifs; eauto.
    exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
    { eapply TS. }
    { eapply TS2. }

  - eapply split_succeed_wf in MEM. des.
    exploit Memory.get_disjoint.
    { eapply GET. }
    { eapply GET2. } i. des; clarify.
    + left. left. auto.
    + eapply disjoint_equivalent2 in x0. des; auto; clarify.
      { eapply memory_get_ts_strong in GET2. des; clarify.
        exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
        - eapply TS23.
        - eapply Time.bot_spec. }
      unfold Time.meet, Time.join in *. des_ifs; eauto.
      * exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
        { eapply TS. }
        { eapply TS2. }
      * left. left. etrans; eauto.
      * left. left. etrans; eauto.

  - eapply lower_succeed_wf in MEM. des.
    exploit Memory.get_disjoint.
    { eapply GET. }
    { eapply GET0. } i. des; clarify.
    + left. refl.
    + eapply disjoint_equivalent2 in x0. des; auto; clarify.
      unfold Time.meet, Time.join in *. des_ifs; eauto.
      * exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
        { eapply TS. }
        { eapply TS3. }
      * left. left. auto.
      * left. left. auto.

  - eapply Memory.remove_get0 in MEM. des.
    exploit Memory.get_disjoint.
    { eapply GET. }
    { eapply GET0. } i. des; clarify.
    eapply disjoint_equivalent2 in x0. des; auto; clarify.
    + eapply memory_get_ts_strong in GET0. des; clarify.
      left. apply Time.bot_spec.
    + unfold Time.meet, Time.join in *. des_ifs; eauto.
      * exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
        { eapply TS. }
        { eapply TS0. }
      * left. left. auto.
      * left. left. auto.
Qed.

Lemma write_not_cross_concrete_write
      prom0 mem0 loc from to val released prom1 mem1 kind
      to0
      (CONCRETE: concrete_promised mem0 loc to0)
      (WRITE: AMemory.write prom0 mem0 loc from to val released prom1 mem1 kind)
  :
    Time.le to to0 \/ Time.le to0 from.
Proof.
  inv WRITE. eapply write_not_cross_concrete_promise; eauto.
Qed.

Lemma write_not_cross_concrete_step (tm: TimeMap.t)
      lang (th0 th1: Thread.t lang) e
      (CONCRETE: forall loc, concrete_promised (Thread.memory th0) loc (tm loc))
      (STEP: AThread.step_allpf e th0 th1)
  :
    (write_in (earlier_times tm) \1/ write_in (later_times tm)) e.
Proof.
  inv STEP. inv STEP0.
  - inv STEP. inv LOCAL. ss. auto.
  - inv STEP. inv LOCAL; ss; auto.
    + inv LOCAL0. eapply write_not_cross_concrete_write in WRITE; eauto. des.
      * left. i. inv IN; ss. unfold earlier_times. etrans; eauto.
      * right. i. inv IN; ss. unfold later_times.
        eapply TimeFacts.le_lt_lt; eauto.
    + inv LOCAL1. inv LOCAL2. eapply write_not_cross_concrete_write in WRITE; eauto. des.
      * left. i. inv IN; ss. unfold earlier_times. etrans; eauto.
      * right. i. inv IN; ss. unfold later_times.
        eapply TimeFacts.le_lt_lt; eauto.
Qed.

Definition pf_consistent_drf_complete lang (e0:Thread.t lang): Prop :=
  let L := (fun loc => Memory.latest_reserve loc (Local.promises (Thread.local e0)) (Thread.memory e0)) in
  forall mem2 max
         (FORGET: forget_memory (latest_other_reserves (Local.promises (Thread.local e0)) (Thread.memory e0)) mem2 (Thread.memory e0))
         (MAX: Memory.max_full_timemap (Thread.memory e0) max),
  exists e1 (U: list Loc.t) (AU: list Loc.t),
    (<<DISJOINT: forall loc (INU: List.In loc U) (INAU: List.In loc AU), False>>) /\
    (<<AUPDATES: forall loc (INAU: List.In loc AU), ~ L loc>>) /\
    (<<STEPS0: rtc (tau (@pred_step is_cancel lang)) (Thread.mk _ (Thread.state e0) (Thread.local e0) TimeMap.bot mem2) e1>>) /\
    (<<NORESERVE: no_reserves (Local.promises (Thread.local e1))>>) /\
    (* (<<NOATTATCH: not_attatched (Memory.max_full_ts (Thread.memory e0)) (Thread.memory e1)>>) /\ *)
    (<<MAXMAP: TimeMap.le (Memory.max_timemap (Thread.memory e1)) max>>) /\
    exists e2 tr max',
      (<<STEPS1: traced_step tr e1 e2>>) /\
      (<<TIMEMAP: TimeMap.le max max'>>) /\
      (<<GAP: forall loc (NUPDATES: ~ List.In loc (U ++ AU)),
          Time.lt (max loc) (max' loc)>>) /\
      (<<ATTATCHED: not_attatched (fun loc to => (<<MAX: Memory.max_full_ts (Thread.memory e0) loc to>>) /\
                                                 (<<NUPDATES: ~ List.In loc (U ++ AU)>>))
                                  (Thread.memory e2)>>) /\
      (<<TRACE: List.Forall (fun em => <<EVENT: (promise_free /1\ (fun e => ~ is_cancel e) /1\ no_sc
                                                              /1\
                                                              (no_acq_update_on ((fun loc to => L loc) /2\ Memory.max_full_ts (Thread.memory e0)))
                                                              /1\
                                                              (write_in (later_times max' \2/ (concrete_covered (Local.promises (Thread.local e0)) (Thread.memory e0) /2\ earlier_times max)))
                                                              /1\
                                                              (fun e => ThreadEvent.get_machine_event e = MachineEvent.silent)
                                                ) (fst em)>> /\ <<MEMORY: not_attatched (fun loc to => (<<MAX: Memory.max_full_ts (Thread.memory e0) loc to>>) /\
                                                                                                       (<<NUPDATES: ~ List.In loc (U ++ AU)>>)) (snd em)>>) tr>>) /\
      (<<COMPLETEU:
         forall loc (SAT: List.In loc U),
         exists to valr valw releasedr releasedw ordr ordw mem,
           <<IN: List.In (ThreadEvent.update loc (max loc) to valr valw releasedr releasedw ordr ordw, mem) tr>> /\ <<ORDR: Ordering.le ordr Ordering.strong_relaxed>> >>) /\
      (<<COMPLETEAU:
         forall loc (SAT: List.In loc AU),
         exists to valr valw releasedr releasedw ordr ordw mem,
           <<IN: List.In (ThreadEvent.update loc (max loc) to valr valw releasedr releasedw ordr ordw, mem) tr>> >>) /\
      (__guard__((exists st',
                     (<<LOCAL: Local.failure_step (Thread.local e2)>>) /\
                     (<<FAILURE: Language.step lang ProgramEvent.failure (@Thread.state lang e2) st'>>)) \/
                 ((<<PROMISES: (Local.promises (Thread.local e2)) = Memory.bot>>) /\
                  (<<COMPLETEW:
                     forall loc to (PROMISED: concrete_promised (Local.promises (Thread.local e0)) loc to),
                     exists e m,
                       (<<IN: List.In (e, m) tr>>) /\
                       (<<WRITETO: rlx_write_to loc to e>>)>>))))
.

Lemma pf_consistent_pf_consistent_drf_complete lang (th: Thread.t lang)
      (WF: Local.wf (Thread.local th) (Thread.memory th))
      (MEM: Memory.closed (Thread.memory th))
      (CONSISTENT: pf_consistent th)
      (RESERVEWF: memory_reserve_wf (Thread.memory th))
  :
    pf_consistent_drf_complete th.
Proof.
  eapply pf_consistent_pf_consistent_strong in CONSISTENT; eauto.
  eapply pf_consistent_pf_consistent_drf' in CONSISTENT; eauto.
  eapply pf_consistent_pf_consistent_drf'' in CONSISTENT; eauto.

  set ident_map_le.
  set ident_map_bot.
  set ident_map_eq.

  set (L:=fun loc : Loc.t =>
            Memory.latest_reserve loc (Local.promises (Thread.local th)) (Thread.memory th)).
  exploit Memory.cap_exists; eauto. i. des.
  exploit forget_exists; eauto. i. des.
  ii. exploit CONSISTENT; eauto. i. des.
  assert (MLE0: Memory.le (Local.promises (Thread.local th)) (Thread.memory th)).
  { inv WF. auto. }
  assert (COLLAPSABLE: collapsable_cap L (Local.promises (Thread.local th)) (Thread.memory th)).
  { ii. clarify. unfold L, Memory.latest_reserve in SAT.
    rewrite GET in SAT. clarify. }
  assert (MEMORY: memory_map ident_map mem_src mem0).
  { eapply ident_map_collapsing_latest_memory; cycle 3; eauto. }
  assert (MLE1: memory_concrete_le mem_src mem0).
  { eapply collapsing_latest_memory_concrete_le; cycle 3; eauto. }
  assert (CONCRETELE: memory_concrete_le (Thread.memory th) mem_src).
  { eapply collapsing_caps_forget_le; eauto. }
  assert (LCWFTGT: Local.wf (Thread.local th) mem_src).
  { eapply memory_concrete_le_local_wf; eauto. inv WF.
    eapply collapsing_caps_forget_prom_le; eauto. }
  assert (LCWFSRC: Local.wf (Thread.local th) mem0).
  { eapply memory_concrete_le_local_wf; eauto. inv WF.
    eapply forget_latest_other_reserves_promises_le; eauto. }
  assert (CLOSEDSRC: Memory.closed mem0).
  { eapply forget_latest_other_reserves_closed; cycle 1; eauto. }
  assert (CLOSEDTGT: Memory.closed mem_src).
  { eapply collapsing_caps_forget_closed; cycle 1; eauto. }

  destruct e1.
  hexploit (@steps_map ident_map).
  { eapply ident_map_le. }
  { eapply ident_map_bot. }
  { eapply ident_map_eq. }
  { ss. i. eapply ident_map_mappable_any_event. }
  { eapply STEPS0. }
  { ss. }
  { ss. }
  { ss. }
  { ss. }
  { eauto. }
  { eauto. }
  { eauto. }
  { eapply Memory.closed_timemap_bot; eauto. inv CLOSEDSRC. auto. }
  { eapply Memory.closed_timemap_bot; eauto. inv CLOSEDTGT. auto. }
  { eapply ident_map_local; eauto. }
  { eauto. }
  { eapply mapping_map_lt_collapsable_unwritable. eapply ident_map_lt. }
  { eapply ident_map_timemap. }
  { refl. }
  { instantiate (1:=is_cancel). ii. inv REL; ss. inv KIND; ss. }
  i. des.

  exploit AThread.rtc_tau_step_future.
  { eapply thread_steps_pred_steps. eapply STEPS0. } all: eauto.
  { eapply Memory.closed_timemap_bot; eauto. ss. inv CLOSEDTGT. auto. } i. des. ss.
  exploit AThread.rtc_tau_step_future.
  { eapply thread_steps_pred_steps. eapply STEP. } all: eauto.
  { eapply Memory.closed_timemap_bot; eauto. ss. inv CLOSEDSRC. auto. } i. des. ss.

  destruct e2. hexploit traced_steps_map.
  { eauto. }
  { eauto. }
  { eauto. }
  { eapply List.Forall_forall. i.
    eapply ident_map_mappable_any_event. }
  { eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  { eapply WF0. }
  { eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  { ii. unfold collapsed in *. des. inv MAP0. inv MAP1. inv ITV.
    exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto. }
  { eauto. }
  { eauto. } i. des.
  esplits; eauto; ss.
  { inv LOCAL. eapply no_reserves_map in PROMISES; eauto. }
  { etrans; eauto. ii. eapply ident_map_memory_max_ts; eauto.
    inv CLOSED0. ss. }
  { eapply ident_map_memory_not_attatched; eauto. }
  { eapply List.Forall_forall. i.
    eapply list_Forall2_in in H; eauto. des. destruct a, x. ss.
    eapply List.Forall_forall in TRACE; eauto. ss. des. splits.
    - eapply map_event_promise_free; eauto.
    - inv EVENT; ss. inv KIND; ss.
    - eapply map_event_no_sc; eauto.
    - eapply ident_map_event_no_acq_update_on; eauto.
    - eapply ident_map_event_write_in; eauto.
    - inv EVENT; ss.
    - eapply ident_map_memory_not_attatched; eauto. }
  { i. exploit COMPLETEU; eauto. i. des.
    eapply list_Forall2_in2 in IN; eauto. des. destruct b. ss. inv EVENT.
    inv FROM. esplits; eauto. }
  { i. exploit COMPLETEAU; eauto. i. des.
    eapply list_Forall2_in2 in IN; eauto. des. destruct b. ss. inv EVENT.
    inv FROM. esplits; eauto. }
  { unguard. des.
    - left. esplits; eauto. inv LOCAL1. inv LOCAL0. destruct local0. ss. econs.
      hexploit promise_consistent_map; try apply PROMISES; eauto.
      i. destruct flc0. eapply promise_consistent_mon; eauto. ss.
    - right. split.
      + inv LOCAL0. rewrite PROMISES in *.
        eapply bot_promises_map in PROMISES0; eauto.
      + i. exploit COMPLETEW; eauto. i. des.
        eapply list_Forall2_in2 in IN; eauto. des. destruct b. ss.
        inv EVENT; ss.
        * inv TO. esplits; eauto.
        * inv TO. esplits; eauto.
  }
Qed.

Definition times_in_memory (mem: Memory.t) (L: Loc.t -> list Time.t): Prop :=
  forall loc t,
    (<<SAT: List.In t (L loc)>>) <->
    (<<INMEMORY:
       (exists from msg, (<<GET: Memory.get loc t mem = Some (from, msg)>>)) \/
       (exists to msg, (<<GET: Memory.get loc to mem = Some (t, msg)>>))>>).

Lemma times_in_memory_exists mem
  :
    exists l, times_in_memory mem l.
Proof.
  hexploit (choice
              (fun loc tl =>
                 forall t,
                   (<<SAT: List.In t tl>>) <->
                   (<<INMEMORY:
                      (exists from msg, (<<GET: Memory.get loc t mem = Some (from, msg)>>)) \/
                      (exists to msg, (<<GET: Memory.get loc to mem = Some (t, msg)>>))>>))); auto.
  intros loc.
  hexploit (wf_cell_msgs_exists (mem loc)). i. des.
  exists ((List.map (fun ftm =>
                       match ftm with
                       | (from, _, _) => from
                       end) l)
            ++
            (List.map (fun ftm =>
                         match ftm with
                         | (_, to, _) => to
                         end) l)).
  i. split; i.
  - red in H. eapply List.in_app_or in H. des.
    + eapply List.in_map_iff in H. des.
      destruct x as [[from to] msg]. clarify.
      eapply COMPLETE in H0. right. eauto.
    + eapply List.in_map_iff in H. des.
      destruct x as [[from to] msg]. clarify.
      eapply COMPLETE in H0. left. eauto.
  - eapply List.in_or_app.  des.
    + right. eapply COMPLETE in GET.
      eapply List.in_map_iff. esplits; eauto. ss.
    + left. eapply COMPLETE in GET.
      eapply List.in_map_iff. esplits; eauto. ss.
Qed.

Lemma concrete_promised_increase_steps
      lang (th0 th1: Thread.t lang) tr
      (STEPS: traced_step tr th0 th1)
  :
    concrete_promised (Thread.memory th0) <2= concrete_promised (Thread.memory th1).
Proof.
  ginduction STEPS; i; auto.
  eapply IHSTEPS. inv HD.  eapply concrete_promised_increase; eauto.
Qed.


Lemma write_not_cross_concrete_steps (tm: TimeMap.t)
      lang (th0 th1: Thread.t lang) tr
      (CONCRETE: forall loc, concrete_promised (Thread.memory th0) loc (tm loc))
      (STEPS: traced_step tr th0 th1)
  :
    List.Forall (fun em => (write_in (earlier_times tm) \1/ write_in (later_times tm)) (fst em)) tr.
Proof.
  ginduction STEPS.
  - i. econs.
  - i. econs.
    + eapply write_not_cross_concrete_step; eauto.
    + eapply IHSTEPS. i. inv HD.
      eapply concrete_promised_increase; eauto.
Qed.

Definition pf_consistent_drf lang (e0:Thread.t lang): Prop :=
  let L := (fun loc => Memory.latest_reserve loc (Local.promises (Thread.local e0)) (Thread.memory e0)) in
  forall mem2 max sc
         (FORGET: forget_memory (latest_other_reserves (Local.promises (Thread.local e0)) (Thread.memory e0)) mem2 (Thread.memory e0))
         (MAX: Memory.max_full_timemap (Thread.memory e0) max),
  exists e2 (U: list Loc.t) (AU: list Loc.t) tr max',
    (<<DISJOINT: forall loc (INU: List.In loc U) (INAU: List.In loc AU), False>>) /\
    (<<AUPDATES: forall loc (INAU: List.In loc AU), ~ L loc>>) /\
    (<<STEPS: traced_step tr (Thread.mk _ (Thread.state e0) (Thread.local e0) sc mem2) e2>>) /\
    (<<TIMEMAP: TimeMap.le max max'>>) /\
    (<<GAP: forall loc (NUPDATES: ~ List.In loc (U ++ AU)),
        Time.lt (max loc) (max' loc)>>) /\
    (<<ATTATCHED: not_attatched (fun loc to => (<<MAX: Memory.max_full_ts (Thread.memory e0) loc to>>) /\
                                               (<<NUPDATES: ~ List.In loc (U ++ AU)>>))
                                (Thread.memory e2)>>) /\
    (<<TRACE: List.Forall (fun em => (no_sc /1\
                                            (fun e => ThreadEvent.get_machine_event e = MachineEvent.silent) /1\
                                            (no_acq_update_on ((fun loc to => L loc) /2\ Memory.max_full_ts (Thread.memory e0)))
                                            /1\
                                            __guard__((write_in (later_times max')) \1/ (write_in (concrete_covered (Local.promises (Thread.local e0)) (Thread.memory e0) /2\ earlier_times max)))
                                            (* (write_in (later_times max' \2/ (concrete_covered (Local.promises (Thread.local e0)) (Thread.memory e0) /2\ earlier_times max))) *)
                                            /1\
                                            (fun e => ThreadEvent.get_machine_event e = MachineEvent.silent)
                                     ) (fst em)) tr>>) /\
    (<<COMPLETEU:
       forall loc (SAT: List.In loc U),
       exists to valr valw releasedr releasedw ordr ordw mem,
         <<IN: List.In (ThreadEvent.update loc (max loc) to valr valw releasedr releasedw ordr ordw, mem) tr>> /\ <<ORDR: Ordering.le ordr Ordering.strong_relaxed>> >>) /\
    (<<COMPLETEAU:
       forall loc (SAT: List.In loc AU),
       exists to valr valw releasedr releasedw ordr ordw mem,
         <<IN: List.In (ThreadEvent.update loc (max loc) to valr valw releasedr releasedw ordr ordw, mem) tr>> >>) /\
    (__guard__((exists st',
                     (<<LOCAL: Local.failure_step (Thread.local e2)>>) /\
                     (<<FAILURE: Language.step lang ProgramEvent.failure (@Thread.state lang e2) st'>>)) \/
               ((<<PROMISES: (Local.promises (Thread.local e2)) = Memory.bot>>) /\
                (<<COMPLETEW:
                   forall loc to (PROMISED: concrete_promised (Local.promises (Thread.local e0)) loc to),
                   exists e m,
                     (<<IN: List.In (e, m) tr>>) /\
                     (<<WRITETO: rlx_write_to loc to e>>)>>))))
.


Lemma write_in_sum L0 L1 L2
      e
      (WRITEIN0: write_in L0 e)
      (WRITEIN1: write_in L1 e)
      (IMPL: (L0 /2\ L1) <2= L2)
  :
    write_in L2 e.
Proof.
  i. unfold write_in in *. des_ifs.
  - ii. eapply IMPL; eauto.
  - ii. eapply IMPL; eauto.
Qed.

Lemma write_in_mon L0 L1
      e
      (NOTIN: write_in L1 e)
      (LE: L1 <2= L0)
  :
    write_in L0 e.
Proof.
  i. unfold write_in in *. des_ifs.
  - ii. eapply LE. eapply NOTIN; eauto.
  - ii. eapply LE. eapply NOTIN; eauto.
Qed.

Lemma pf_consistent_pf_consistent_drf lang (th: Thread.t lang)
      (WF: Local.wf (Thread.local th) (Thread.memory th))
      (MEM: Memory.closed (Thread.memory th))
      (CONSISTENT: pf_consistent th)
      (RESERVEWF: memory_reserve_wf (Thread.memory th))
  :
    pf_consistent_drf th.
Proof.
  eapply pf_consistent_pf_consistent_drf_complete in CONSISTENT; eauto.
  ii. exploit CONSISTENT; eauto. i. des.
  eapply pred_steps_traced_step in STEPS0. des.

  destruct e1. eapply no_sc_any_sc_traced in STEPS; ss; cycle 1.
  { ii. eapply List.Forall_forall in IN; eauto. ss. des.
    destruct e. ss. destruct t; ss. } des.

  destruct e2. eapply no_sc_any_sc_traced in STEPS1; ss; cycle 1.
  { ii. eapply List.Forall_forall in IN; eauto. ss. des. ss. } des.

  exploit write_not_cross_concrete_steps; try apply STEPS; eauto.
  { ss. instantiate (1:=max). i.
    eapply concrete_promised_increase_steps in STEPS0; eauto. ss.
    inv FORGET. specialize (MAX loc). inv MAX. des.
    unfold Memory.get in COMPLETE. erewrite <- COMPLETE in GET.
    - econs; eauto.
    - intros LATEST. inv LATEST. unfold Memory.get in GET0. clarify. }
  intros NOTCROSS.

  exists (Thread.mk _ state0 local0 sc_src'0 memory0), U, AU, (tr0 ++ tr), max'.
  esplits; auto.
  - eapply traced_step_trans; eauto.
  - eapply Forall_app.
    + eapply List.Forall_impl; try apply EVENTS; eauto. i. ss. des; auto. destruct a. ss.
      unfold is_cancel in SAT. des_ifs; ss. unguard. splits; auto.
    + eapply List.Forall_forall. i.
      eapply List.Forall_forall in NOTCROSS; eauto.
      eapply List.Forall_forall in TRACE; eauto.
      ss. des; splits; auto.
      * right. eapply write_in_sum.
        { eapply EVENT1. }
        { eapply NOTCROSS. }
        i. ss. des; auto.
        exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
        { eapply PR. }
        etrans.
        { eapply PR0. }
        { eauto. }
      * left. eapply write_in_sum.
        { eapply EVENT1. }
        { eapply NOTCROSS. }
        i. ss. des; auto.
        exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
        { eapply PR0. }
        eauto.
  - i. exploit COMPLETEU; eauto. i. des. esplits; eauto.
    eapply List.in_or_app; eauto.
  - i. exploit COMPLETEAU; eauto. i. des. esplits; eauto.
    eapply List.in_or_app; eauto.
  - unguard. des.
    + left. esplits; eauto.
    + right. splits; auto.
      i. exploit COMPLETEW; eauto. i. des.
      esplits; eauto. eapply List.in_or_app; eauto.
Qed.
