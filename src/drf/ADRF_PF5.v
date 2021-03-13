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
Require Import PredStep.
Require Import ReorderPromises2.

Require Import Pred.
Require Import AMemory.
Require Import ALocal.
Require Import AThread.
Require Import APredStep.
Require Import ADRF_PF0.
Require Import ADRF_PF1.
Require Import ADRF_PF2.
Require Import ADRF_PF3.
Require Import ADRF_PF4.
Require Import AMapping.

Set Implicit Arguments.


Definition map_ident_in_memory (f: Loc.t -> Time.t -> Time.t -> Prop)
           (mem: Memory.t): Prop :=
  forall loc to
         (TS: Time.le to (Memory.max_ts loc mem)),
    f loc to to.

Definition map_ident_in_memory_bot
           f mem
           (MAP: map_ident_in_memory f mem)
  :
    mapping_map_bot f.
Proof.
  ii. eapply MAP. eapply Time.bot_spec.
Qed.

Lemma map_ident_in_memory_closed_timemap
      f mem tm
      (MAP: map_ident_in_memory f mem)
      (CLOSED: Memory.closed_timemap tm mem)
  :
    timemap_map f tm tm.
Proof.
  ii. eapply MAP; eauto.
  exploit CLOSED; eauto. i. des.
  eapply Memory.max_ts_spec in x. des. eauto.
Qed.

Lemma map_ident_in_memory_closed_view
      f mem vw
      (MAP: map_ident_in_memory f mem)
      (CLOSED: Memory.closed_view vw mem)
  :
    view_map f vw vw.
Proof.
  inv CLOSED. econs.
  - eapply map_ident_in_memory_closed_timemap; eauto.
  - eapply map_ident_in_memory_closed_timemap; eauto.
Qed.

Lemma map_ident_in_memory_closed_tview
      f mem tvw
      (MAP: map_ident_in_memory f mem)
      (CLOSED: TView.closed tvw mem)
  :
    tview_map f tvw tvw.
Proof.
  inv CLOSED. econs.
  - i. eapply map_ident_in_memory_closed_view; eauto.
  - eapply map_ident_in_memory_closed_view; eauto.
  - eapply map_ident_in_memory_closed_view; eauto.
Qed.

Lemma map_ident_in_memory_closed_opt_view
      f mem vw
      (MAP: map_ident_in_memory f mem)
      (CLOSED: Memory.closed_opt_view vw mem)
  :
    opt_view_map f vw vw.
Proof.
  inv CLOSED; econs.
  eapply map_ident_in_memory_closed_view; eauto.
Qed.

Lemma map_ident_in_memory_closed_message
      f mem msg
      (MAP: map_ident_in_memory f mem)
      (CLOSED: Memory.closed_message msg mem)
  :
    msg_map f msg msg.
Proof.
  inv CLOSED; econs.
  eapply map_ident_in_memory_closed_opt_view; eauto.
Qed.

Lemma map_ident_in_memory_promises
      f mem0 mem
      (MAP: map_ident_in_memory f mem)
      (MAPLT: mapping_map_lt f)
      (CLOSED: Memory.closed mem)
      (MLE: Memory.le mem0 mem)
  :
    promises_map f mem0 mem0.
Proof.
  inv CLOSED. econs.
  - i. esplits; eauto.
    + eapply mapping_map_lt_non_collapsable; auto.
    + eapply MLE in GET. eapply Memory.max_ts_spec in GET. des.
      eapply MAP; eauto.
    + eapply MLE in GET. eapply CLOSED0 in GET. des.
      eapply map_ident_in_memory_closed_message; eauto.
  - i. esplits; eauto.
    + eapply MLE in GET. eapply Memory.max_ts_spec in GET. des.
      eapply MAP; eauto.
    + eapply MLE in GET. eapply MAP. etrans.
      * eapply memory_get_ts_le; eauto.
      * eapply Memory.max_ts_spec in GET. des. auto.
Qed.

Lemma map_ident_in_memory_memory
      f mem
      (MAP: map_ident_in_memory f mem)
      (MAPLT: mapping_map_lt f)
      (CLOSED: Memory.closed mem)
  :
    memory_map f mem mem.
Proof.
  eapply promises_map_memory_map.
  eapply map_ident_in_memory_promises; eauto. refl.
Qed.

Lemma map_ident_in_memory_local
      f mem lc
      (MAP: map_ident_in_memory f mem)
      (MAPLT: mapping_map_lt f)
      (LOCAL: Local.wf lc mem)
      (CLOSED: Memory.closed mem)
  :
    local_map f lc lc.
Proof.
  inv LOCAL. econs.
  - refl.
  - eapply map_ident_in_memory_closed_tview; eauto.
  - eapply map_ident_in_memory_promises; eauto.
Qed.

Lemma update_map_lt (f: Time.t -> Time.t -> Prop) to fto
      (MAPLT: mapping_map_lt_loc f)
      (NOMAPPED: forall fts (MAPPED: f to fts), False)
      (LEFT: forall ts fts (TS: Time.lt ts to) (MAPPED: f ts fts),
          Time.lt fts fto)
      (RIGHT: forall ts fts (TS: Time.lt to ts) (MAPPED: f ts fts),
          Time.lt fto fts)
  :
    mapping_map_lt_loc (fun ts fts => <<ORIG: f ts fts>> \/ <<NEW: to = ts /\ fto = fts>>).
Proof.
  ii. des; clarify.
  - eapply MAPLT; eauto.
  - split; i.
    + eapply RIGHT; eauto.
    + destruct (Time.le_lt_dec t1 t0); auto. destruct l.
      * eapply LEFT in H0; eauto.
        exfalso. eapply Time.lt_strorder. etrans; eauto.
      * inv H0. exfalso. eapply NOMAPPED; eauto.
  - split; i.
    + eapply LEFT; eauto.
    + destruct (Time.le_lt_dec t1 t0); auto. destruct l.
      * eapply RIGHT in H0; eauto.
        exfalso. eapply Time.lt_strorder. etrans; eauto.
      * inv H0. exfalso. eapply NOMAPPED; eauto.
  - split; i.
    + exfalso. eapply Time.lt_strorder; eauto.
    + exfalso. eapply Time.lt_strorder; eauto.
Qed.

Fixpoint compressing_map (ts0 ts1: Time.t) (T: list Time.t) :=
  match T with
  | [] => bot2
  | hd :: tl => (fun ts fts => ts = hd /\ fts = Time.middle ts0 ts1)
                  \2/ compressing_map (Time.middle ts0 ts1) ts1 tl
  end.

Lemma compressing_map_spec ts0 ts1 T
      (TS: Time.lt ts0 ts1)
      (SORTED: times_sorted T)
  :
    (<<MAPLT: mapping_map_lt_loc (compressing_map ts0 ts1 T)>>) /\
    (<<COMPLETE: forall to (IN: List.In to T), exists fto, (<<MAPPED: (compressing_map ts0 ts1 T) to fto>>)>>) /\
    (<<BOUND: forall to fto (MAPPED: (compressing_map ts0 ts1 T) to fto),
        (<<IN: List.In to T>>) /\ (<<TS0: Time.lt ts0 fto>>) /\ (<<TS1: Time.lt fto ts1>>)>>).
Proof.
  i. ginduction T.
  - i. ss. splits.
    + ii. clarify.
    + i. clarify.
    + i. clarify.
  - i. ss. inv SORTED. exploit IHT.
    { instantiate (1:=ts1). instantiate (1:=Time.middle ts0 ts1).
      eapply Time.middle_spec; eauto. }
    { eauto. }
    i. des. clear IHT. splits.
    + ii. des; clarify.
      * split; i.
        { exfalso. eapply Time.lt_strorder; eauto. }
        { exfalso. eapply Time.lt_strorder; eauto. }
      * eapply BOUND in MAP0. des.
        eapply List.Forall_forall in HD; eauto. split; i.
        { exfalso. eapply Time.lt_strorder; eauto. }
        { exfalso. eapply Time.lt_strorder; eauto. }
      * eapply BOUND in MAP1. des. split; i; auto.
        eapply List.Forall_forall in HD; eauto.
      * eapply MAPLT; eauto.
    + i. des; clarify.
      * esplits; eauto.
      * eapply COMPLETE in IN. des. esplits; eauto.
    + i. des; clarify.
      * split; auto. eapply Time.middle_spec; auto.
      * eapply BOUND in MAPPED. des. splits; auto.
        etrans.
        { eapply Time.middle_spec; eauto. }
        { eauto. }
Qed.

Lemma shift_map_exists max ts0 ts1 (T: list Time.t)
      (MAX: Time.le max ts0)
      (TS: Time.lt ts0 ts1)
  :
    exists (f: Time.t -> Time.t -> Prop),
      (<<COMPLETE: forall to (IN: List.In to T), exists fto, (<<MAPPED: f to fto>>)>>) /\
      (<<SAME: forall ts (TS: Time.le ts max), f ts ts>>) /\
      (<<BOUND: forall to fto (MAPPED: f to fto) (TS: Time.lt max to),
          (Time.lt ts0 fto /\ Time.lt fto ts1)>>) /\
      (<<MAPLT: mapping_map_lt_loc f>>)
.
Proof.
  hexploit (list_filter_exists (fun ts => Time.lt max ts) T). i. des.
  hexploit (sorting_sorted l'). i. des.
  hexploit (@compressing_map_spec ts0 ts1 (sorting l')); eauto. i. des.
  exists ((fun ts fts => Time.le ts max /\ ts = fts) \2/ (compressing_map ts0 ts1 (sorting l'))).
  splits.

  - i. destruct (Time.le_lt_dec to max).
    + esplits; eauto.
    + hexploit (proj1 (COMPLETE to)).
      { split; auto. } intros IN'. des.
      eapply COMPLETE0 in IN'.
      eapply COMPLETE1 in IN'. des. esplits; eauto.
  - i. eauto.
  - i. apply or_strengthen in MAPPED. des; clarify; eauto.
    + exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto.
    + eapply BOUND in SAT. des. auto.

  - ii. des; clarify.
    + apply BOUND in MAP0. des.
      eapply COMPLETE0 in IN. eapply COMPLETE in IN. des.
      split; i.
      * exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
        { eapply H. } etrans.
        { eapply MAP1. }
        { left. auto. }
      * exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
        { eapply H. } etrans.
        { eapply MAP1. } etrans.
        { eapply MAX. }
        { left. auto. }

    + apply BOUND in MAP1. des.
      apply COMPLETE0 in IN. eapply COMPLETE in IN. des.
      split; i.
      * eapply TimeFacts.le_lt_lt.
        { eapply MAP0. }
        eapply TimeFacts.le_lt_lt; eauto.
      * eapply TimeFacts.le_lt_lt; eauto.

    + eapply MAPLT; eauto.
Qed.


Definition pf_consistent_drf_shift lang (e0:Thread.t lang)
           (spaces: Loc.t -> Time.t -> Prop)
           (promises: Loc.t -> Time.t -> Prop)
           (max: TimeMap.t)
           (U AU: Loc.t -> Prop): Prop :=
  (<<UPDATESMAX: forall loc (UPDATES: (U \1/ AU) loc), max loc = Memory.max_ts loc (Thread.memory e0)>>) /\
  (<<CONSISTENT:
     forall (gap newmax: TimeMap.t)
            (GAP: forall loc (UPDATES: U loc \/ AU loc),
                Time.lt (max loc) (gap loc))
            (NEWMAX: TimeMap.le max newmax),
     exists e2 tr,
       (<<STEPS: traced_step tr e0 e2>>) /\

       (<<TRACE: List.Forall (fun em => (no_sc /1\ no_promise /1\ (fun e => ThreadEvent.get_machine_event e = MachineEvent.silent)/1\ (write_in (spaces \2/ (fun loc to => (__guard__(U loc \/ AU loc) /\ Time.lt (max loc) to /\ Time.lt to (gap loc))) \2/                 (fun loc to => ~ U loc /\ ~ AU loc /\ Time.lt (newmax loc) to)))) (fst em)) tr>>) /\

       (<<COMPLETEU:
          forall loc (SAT: U loc),
          exists to from valr valw releasedr releasedw ordr ordw mem,
            <<IN: List.In (ThreadEvent.update loc from to valr valw releasedr releasedw ordr ordw, mem) tr>> /\ <<ORDR: Ordering.le ordr Ordering.strong_relaxed>> >>) /\

       (<<COMPLETEAU:
          forall loc (SAT: AU loc),
          exists to from valr valw releasedr releasedw ordr ordw mem,
            <<IN: List.In (ThreadEvent.update loc from to valr valw releasedr releasedw ordr ordw, mem) tr>> >>) /\

       (<<COMPLETEW: forall loc to (PROMISED: promises loc to),
           exists e m,
             (<<IN: List.In (e, m) tr>>) /\
             (<<WRITETO: rlx_write_loc loc e>>)>>)
         >>)
.

Definition wf_time_evt (P: Loc.t -> Time.t -> Prop) (e: ThreadEvent.t) : Prop :=
  match e with
  | ThreadEvent.promise loc from to msg kind =>
    (<<FROM: P loc from>>) /\ (<<TO: P loc to>>)
  | ThreadEvent.write loc from to val released ordw =>
    (<<FROM: P loc from>>) /\ (<<TO: P loc to>>)
  | ThreadEvent.update loc from to valr valw releasedr releasedw ordr ordw =>
    (<<FROM: P loc from>>) /\ (<<TO: P loc to>>)
  | _ => True
  end.

Lemma wf_time_evt_mon P0 P1
      (LE: P0 <2= P1)
  :
    wf_time_evt P0 <1= wf_time_evt P1.
Proof.
  ii. unfold wf_time_evt in *. des_ifs; des; splits; eauto.
Qed.

Lemma step_times_list_exists lang (th0 th1: Thread.t lang) e
      (STEP: AThread.step_allpf e th0 th1)
  :
    exists (times: Loc.t -> list Time.t),
      (<<WFTIME: wf_time_evt (fun loc to => List.In to (times loc)) e>>).
Proof.
  destruct e.
  - exists (fun l => if Loc.eq_dec l loc then
                       [from; to] else []).
    econs; eauto.
    + ss. splits; auto; des_ifs; ss; eauto.
    + ss. splits; auto; des_ifs; ss; eauto.
  - exists (fun _ => []). econs; eauto.
  - exists (fun _ => []). econs; eauto.
  - exists (fun l => if Loc.eq_dec l loc then
                       [from; to] else []).
    econs; eauto.
    + ss. splits; auto; des_ifs; ss; eauto.
    + ss. splits; auto; des_ifs; ss; eauto.
  - exists (fun l => if Loc.eq_dec l loc then
                       [tsr; tsw] else []).
    econs; eauto.
    + ss. splits; auto; des_ifs; ss; eauto.
    + ss. splits; auto; des_ifs; ss; eauto.
  - exists (fun _ => []). econs; eauto.
  - exists (fun _ => []). econs; eauto.
  - exists (fun _ => []). econs; eauto.
Qed.

Lemma traced_times_list_exists lang (th0 th1: Thread.t lang) tr
      (STEPS: traced_step tr th0 th1)
  :
    exists (times: Loc.t -> list Time.t),
      (<<WFTIME: List.Forall (fun em => wf_time_evt (fun loc to => List.In to (times loc)) (fst em)) tr>>).
Proof.
  ginduction STEPS.
  - exists (fun _ => []). econs.
  - des. eapply step_times_list_exists in HD. des.
    exists (fun loc => (times0 loc ++ times loc)). econs.
    + eapply wf_time_evt_mon; eauto.
      i. ss. eapply List.in_or_app; eauto.
    + eapply List.Forall_impl; eauto.
      i. ss. eapply wf_time_evt_mon; eauto.
      i. ss. eapply List.in_or_app; eauto.
Qed.

Lemma wf_time_mapped_mappable (tr: list (ThreadEvent.t * Memory.t)) times f
      (WFTIME: List.Forall (fun em => wf_time_evt (fun loc to => List.In to (times loc)) (fst em)) tr)
      (COMPLETE: forall loc to (IN: List.In to (times loc)),
          exists fto, (<<MAPPED: f loc to fto>>))
  :
    List.Forall (fun em => mappable_evt f (fst em)) tr.
Proof.
  eapply List.Forall_impl; eauto. i. ss. destruct a. destruct t; ss.
  - des. split.
    + apply COMPLETE in FROM. des. esplit. eauto.
    + apply COMPLETE in TO. des. esplit. eauto.
  - des. split.
    + apply COMPLETE in FROM. des. esplit. eauto.
    + apply COMPLETE in TO. des. esplit. eauto.
  - des. split.
    + apply COMPLETE in FROM. des. esplit. eauto.
    + apply COMPLETE in TO. des. esplit. eauto.
Qed.

Lemma step_wf_event lang (th0 th1: Thread.t lang) e
      (INHABITED: Memory.inhabited (Thread.memory th0))
      (STEP: AThread.step_allpf e th0 th1)
  :
    wf_event e.
Proof.
  inv STEP. inv STEP0.
  - inv STEP. inv LOCAL. ss.
    eapply promise_wf_event; eauto.
  - inv STEP. inv LOCAL; ss.
    + inv LOCAL0. eapply write_wf_event; eauto.
    + inv LOCAL1. inv LOCAL2. eapply write_wf_event; eauto.
Qed.

Lemma traced_step_wf_event lang (th0 th1: Thread.t lang) tr
      (INHABITED: Memory.inhabited (Thread.memory th0))
      (STEPS: traced_step tr th0 th1)
  :
    List.Forall (fun em => wf_event (fst em)) tr.
Proof.
  ginduction STEPS; i.
  - econs.
  - econs.
    + eapply step_wf_event; eauto.
    + eapply IHSTEPS. inv HD. eapply AThread.step_inhabited; eauto.
Qed.


Lemma pf_consistent_drf_src_shift lang (e0: Thread.t lang) spaces promises max U AU
      (LOCAL: Local.wf (Thread.local e0) (Thread.memory e0))
      (SC: Memory.closed_timemap (Thread.sc e0) (Thread.memory e0))
      (CLOSED: Memory.closed (Thread.memory e0))
      (CONSISTENT: pf_consistent_drf_src e0 spaces promises max U AU)
  :
    pf_consistent_drf_shift e0 spaces promises max U AU.
Proof.
  ii. unfold pf_consistent_drf_src in CONSISTENT. des.
  split.
  { auto. } red.
  exploit (choice
             (fun loc to =>
                forall (SAT: MU loc),
                  (<<NOTUPDATES: ~ U loc /\ ~ AU loc>>) /\
                  (<<TS0: Time.le (Memory.max_ts loc (Thread.memory e0)) to>>) /\
                  (<<TS1: Time.lt to (max loc)>>) /\
                  (<<BLANK: Interval.mem (to, (max loc)) <1= spaces loc>>))).
  { intros loc. destruct (classic (MU loc)).
    - eapply MYUPDATES in H. des. exists to. esplits; eauto.
    - exists Time.bot. i. clarify. }
  i. clear MYUPDATES. destruct x0 as [mu MYUPDATES].

  exploit traced_times_list_exists; eauto. i. des.
  exploit (choice
             (fun loc (floc: Time.t -> Time.t -> Prop) =>
                (<<COMPLETE: forall to (IN: List.In to (times loc)),
                    exists fto, (<<MAPPED: floc to fto>>)>>) /\
                (<<NUS: forall (SAT: ~ U loc /\ ~ AU loc /\ ~ MU loc),
                    (<<SAME: forall ts (TS: Time.le ts (max loc)), floc ts ts>>) /\
                    (<<MAPGAP: exists fts, <<MAPPED: floc (max' loc) fts>> /\ Time.lt (newmax loc) fts>>) /\
                    (<<RANGE: forall ts fts (MAPPED: floc ts fts) (TS: Time.lt (max loc) ts),
                        Time.lt (newmax loc) fts>>)>>) /\
                (<<UAUS: forall (SAT: __guard__(U loc \/ AU loc)),
                    (<<SAME: forall ts (TS: Time.le ts (max loc)), floc ts ts>>) /\
                    (<<RANGE: forall ts fts (MAPPED: floc ts fts) (TS: Time.lt (max loc) ts),
                        Time.lt (max loc) fts /\ Time.lt fts (gap loc)>>)>>) /\
                (<<MUS: forall (SAT: MU loc),
                    (<<SAME: forall ts (TS: Time.le ts (mu loc)), floc ts ts>>) /\
                    (<<RANGE: forall ts fts (MAPPED: floc ts fts) (TS: Time.lt (mu loc) ts),
                        Time.lt (mu loc) fts /\ Time.lt fts (max loc)>>)>>) /\
                (<<MAPLT: mapping_map_lt_loc floc>>)
          )).
  { intros loc. destruct (classic (MU loc)).
    { exploit MYUPDATES; eauto. i. des.
      exploit (@shift_map_exists (mu loc) (mu loc) (max loc)); auto.
      { refl. }
      i. des. esplits; eauto; i; des; clarify.
      exfalso. unguard. des; clarify.
    }
    destruct (classic (__guard__(U loc \/ AU loc))).
    { exploit (@shift_map_exists (max loc) (max loc) (gap loc)); auto.
      { refl. }
      i. des. esplits; eauto; i.
      - clarify. unguard. exfalso. des; eauto.
      - exploit MYUPDATES; eauto. i. des. unguard. des; clarify. }
    { exploit (@shift_map_exists (max loc) (newmax loc) (Time.incr (newmax loc)) ((max' loc)::(times loc))); auto.
      { apply Time.incr_spec. }
      i. des. esplits; eauto; i; clarify.
      { eapply COMPLETE; eauto. ss. auto. } splits; auto.
      { ss. exploit COMPLETE; eauto. i. des. esplits; eauto.
        exploit BOUND; eauto. i. des. auto. }
      i. exploit BOUND; eauto. i. des; auto.
    }
  }
  intros [f FSPEC].

  assert (MAPLT: mapping_map_lt f).
  { eapply mapping_map_lt_locwise. i. specialize (FSPEC loc). des. auto. }
  assert (IDENTINMAP: map_ident_in_memory f (Thread.memory e0)).
  { ii. specialize (FSPEC loc). des.
    destruct (classic (MU loc)).
    { exploit MUS; eauto. i. des.
      exploit MYUPDATES; eauto. i. des.
      eapply SAME. etrans; eauto. }
    destruct (classic (__guard__(U loc \/ AU loc))).
    { exploit UAUS; eauto. i. des.
      eapply SAME. etrans; eauto. }
    { exploit NUS; eauto.
      { unguard. apply not_or_and in H0. des. split; auto. }
      i. des.
      eapply SAME. etrans; eauto. }
  }
  assert (MAPEQ: mapping_map_eq f).
  { eapply mapping_map_lt_map_eq; eauto. }
  assert (MAPLE: mapping_map_le f).
  { eapply mapping_map_lt_map_le; eauto. }

  assert (MAPPABLE: List.Forall (fun em => mappable_evt f (fst em)) tr).
  { eapply wf_time_mapped_mappable; eauto. i.
    specialize (FSPEC loc). des.
    destruct (classic (MU loc)).
    { exploit MUS; eauto. }
    destruct (classic (__guard__(U loc \/ AU loc))).
    { exploit UAUS; eauto. }
    { exploit NUS; eauto.
      unguard. apply not_or_and in H0. des. split; auto. }
  }

  exploit traced_step_wf_event; eauto.
  { inv CLOSED. auto. } intros WFEVT.

  destruct e0 as [st0 lc0 sc0 mem0].
  destruct e2 as [st1 lc1 sc1 mem1]. ss.
  hexploit traced_steps_map; try apply STEPS; eauto.
  { eapply map_ident_in_memory_bot; eauto. }
  { eapply map_ident_in_memory_local; eauto. }
  { eapply map_ident_in_memory_memory; eauto. }
  { eapply mapping_map_lt_collapsable_unwritable; eauto. }
  { eapply map_ident_in_memory_closed_timemap; eauto. }
  { refl. }
  i. des. esplits; eauto.

  - eapply List.Forall_forall. i.
    eapply list_Forall2_in in H; eauto. des. destruct a, x. ss.
    eapply List.Forall_forall in TRACE; eauto. ss. des.
    eapply List.Forall_forall in WFEVT; eauto. ss.
    inv EVENT; ss.

    + splits; auto.
      specialize (FSPEC loc). des.
      destruct (classic (MU loc)).
      { exploit MUS; eauto. i. des.
        exploit MYUPDATES; eauto. i. des. unguard. des.
        - left. left. eapply BLANK. inv IN0. ss.
          assert (TS: Time.le (mu loc) from).
          { destruct (Time.le_lt_dec (mu loc) from); auto. exfalso.
            exploit (TRACE1 (Time.meet (mu loc) to)).
            - unfold Time.meet. des_ifs; econs; ss. refl.
            - unfold later_times. i. eapply Time.lt_strorder.
              eapply TimeFacts.lt_le_lt.
              { eapply x0. } etrans.
              { eapply Time.meet_l. } etrans.
              { left. eauto. }
              eauto.
          }
          econs; ss.
          + eapply TimeFacts.le_lt_lt; [|eapply FROM0].
            eapply MAPLE.
            * eapply SAME; eauto. refl.
            * eauto.
            * eauto.
          + etrans; eauto.
            left. eapply RANGE.
            * eauto.
            * eapply TimeFacts.le_lt_lt; eauto.
        - ss. inv IN0. destruct (Time.le_lt_dec t (mu loc)).
          + dup l. eapply SAME in l; eauto.
            exploit (TRACE1 t).
            { econs; ss.
              - eapply MAPLT; eauto.
              - destruct (Time.le_lt_dec t to); auto.
                erewrite (MAPLT loc) in l1; try eassumption.
                exfalso. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
                { eapply TO0. }
                { auto. }
            }
            i. des. auto.
          + dup l. left. left. eapply BLANK. econs; ss.
            exploit RANGE.
            * eapply TO.
            * eapply MAPLT.
              { eapply SAME. refl. }
              { eauto. }
              eapply TimeFacts.lt_le_lt; eauto.
            * i. des. etrans.
              { eapply TO0. }
              { left. auto. }
      }
      destruct (classic (__guard__(U loc \/ AU loc))).
      { exploit UAUS; eauto. i. des. unguard. guardH H0. des.
        - left. right. split; auto. ss.
          assert (TS: Time.le (max loc) from).
          { destruct (Time.le_lt_dec (max loc) from); eauto. exfalso.
            exploit (TRACE1 (Time.meet to (max loc))).
            { unfold Time.meet. des_ifs; econs; ss.
              - refl.
              - left. auto. }
            unfold later_times. i.
            eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
            { eapply x0. } etrans.
            { eapply Time.meet_r. }
            eauto. }
          exploit RANGE; try apply TO.
          { eapply TimeFacts.le_lt_lt.
            - eapply TS.
            - eauto. } i. des. inv IN0. split.
          + eapply TimeFacts.le_lt_lt; [|eapply FROM0]. ss.
            eapply MAPLE.
            * eapply SAME. refl.
            * eauto.
            * eauto.
          + eapply TimeFacts.le_lt_lt; eauto.
        - left. left. ss. exploit (TRACE1 to).
          { econs; ss. refl. } i. des.
          exploit (SAME to); eauto. i.
          hexploit (MAPEQ _ _ _ _ x2 TO). i. subst.
          exploit (SAME from); eauto.
          { etrans; eauto. left. auto. } i.
          hexploit (MAPEQ _ _ _ _ x3 FROM). i. subst.
          eapply TRACE1; eauto. }
      { exploit NUS; eauto.
        { unguard. guardH TRACE1. apply not_or_and in H0. des. split; auto. }
        i. des. unguard. apply not_or_and in H0. des.
        - right. splits; auto. inv IN0. ss.
          transitivity ffrom; auto. eapply RANGE; eauto.
          destruct (Time.le_lt_dec from (max loc)); auto. exfalso.
          exploit (TRACE1 (Time.middle (max loc) (max' loc))).
          { econs; ss.
            - eapply TimeFacts.le_lt_lt; eauto.
              eapply Time.middle_spec; eauto.
            - etrans.
              + left. eapply Time.middle_spec; eauto.
              + left. eapply TRACE1; eauto. econs; ss. refl. }
          unfold later_times. i.
          eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          { eapply x0. }
          { left. eapply Time.middle_spec; eauto. }
        - left. left. ss. exploit (TRACE1 to).
          { econs; ss. refl. } i. des.
          exploit (SAME to); eauto. i.
          hexploit (MAPEQ _ _ _ _ x2 TO). i. subst.
          exploit (SAME from); eauto.
          { etrans; eauto. left. auto. } i.
          hexploit (MAPEQ _ _ _ _ x3 FROM). i. subst.
          eapply TRACE1; eauto. }


    + splits; auto.
      specialize (FSPEC loc). des.
      destruct (classic (MU loc)).
      { exploit MUS; eauto. i. des.
        exploit MYUPDATES; eauto. i. des. unguard. des.
        - left. left. eapply BLANK. inv IN0. ss.
          assert (TS: Time.le (mu loc) from).
          { destruct (Time.le_lt_dec (mu loc) from); auto. exfalso.
            exploit (TRACE1 (Time.meet (mu loc) to)).
            - unfold Time.meet. des_ifs; econs; ss. refl.
            - unfold later_times. i. eapply Time.lt_strorder.
              eapply TimeFacts.lt_le_lt.
              { eapply x0. } etrans.
              { eapply Time.meet_l. } etrans.
              { left. eauto. }
              eauto.
          }
          econs; ss.
          + eapply TimeFacts.le_lt_lt; [|eapply FROM0].
            eapply MAPLE.
            * eapply SAME; eauto. refl.
            * eauto.
            * eauto.
          + etrans; eauto.
            left. eapply RANGE.
            * eauto.
            * eapply TimeFacts.le_lt_lt; eauto.
        - ss. inv IN0. destruct (Time.le_lt_dec t (mu loc)).
          + dup l. eapply SAME in l; eauto.
            exploit (TRACE1 t).
            { econs; ss.
              - eapply MAPLT; eauto.
              - destruct (Time.le_lt_dec t to); auto.
                erewrite (MAPLT loc) in l1; try eassumption.
                exfalso. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
                { eapply TO0. }
                { auto. }
            }
            i. des. auto.
          + dup l. left. left. eapply BLANK. econs; ss.
            exploit RANGE.
            * eapply TO.
            * eapply MAPLT.
              { eapply SAME. refl. }
              { eauto. }
              eapply TimeFacts.lt_le_lt; eauto.
            * i. des. etrans.
              { eapply TO0. }
              { left. auto. }
      }
      destruct (classic (__guard__(U loc \/ AU loc))).
      { exploit UAUS; eauto. i. des. unguard. guardH H0. des.
        - left. right. split; auto. ss.
          assert (TS: Time.le (max loc) from).
          { destruct (Time.le_lt_dec (max loc) from); eauto. exfalso.
            exploit (TRACE1 (Time.meet to (max loc))).
            { unfold Time.meet. des_ifs; econs; ss.
              - refl.
              - left. auto. }
            unfold later_times. i.
            eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
            { eapply x0. } etrans.
            { eapply Time.meet_r. }
            eauto. }
          exploit RANGE; try apply TO.
          { eapply TimeFacts.le_lt_lt.
            - eapply TS.
            - eauto. } i. des. inv IN0. split.
          + eapply TimeFacts.le_lt_lt; [|eapply FROM0]. ss.
            eapply MAPLE.
            * eapply SAME. refl.
            * eauto.
            * eauto.
          + eapply TimeFacts.le_lt_lt; eauto.
        - left. left. ss. exploit (TRACE1 to).
          { econs; ss. refl. } i. des.
          exploit (SAME to); eauto. i.
          hexploit (MAPEQ _ _ _ _ x2 TO). i. subst.
          exploit (SAME from); eauto.
          { etrans; eauto. left. auto. } i.
          hexploit (MAPEQ _ _ _ _ x3 FROM). i. subst.
          eapply TRACE1; eauto. }
      { exploit NUS; eauto.
        { unguard. guardH TRACE1. apply not_or_and in H0. des. split; auto. }
        i. des. unguard. apply not_or_and in H0. des.
        - right. splits; auto. inv IN0. ss.
          transitivity ffrom; auto. eapply RANGE; eauto.
          destruct (Time.le_lt_dec from (max loc)); auto. exfalso.
          exploit (TRACE1 (Time.middle (max loc) (max' loc))).
          { econs; ss.
            - eapply TimeFacts.le_lt_lt; eauto.
              eapply Time.middle_spec; eauto.
            - etrans.
              + left. eapply Time.middle_spec; eauto.
              + left. eapply TRACE1; eauto. econs; ss. refl. }
          unfold later_times. i.
          eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          { eapply x0. }
          { left. eapply Time.middle_spec; eauto. }
        - left. left. ss. exploit (TRACE1 to).
          { econs; ss. refl. } i. des.
          exploit (SAME to); eauto. i.
          hexploit (MAPEQ _ _ _ _ x2 TO). i. subst.
          exploit (SAME from); eauto.
          { etrans; eauto. left. auto. } i.
          hexploit (MAPEQ _ _ _ _ x3 FROM). i. subst.
          eapply TRACE1; eauto. }

  - i. eapply COMPLETEU in SAT. des.
    eapply list_Forall2_in2 in IN; eauto. des. ss. destruct b. ss.
    inv EVENT. esplits; eauto.

  - i. eapply COMPLETEAU in SAT. des.
    eapply list_Forall2_in2 in IN; eauto. des. ss. destruct b. ss.
    inv EVENT. esplits; eauto.

  - i. eapply COMPLETEW in PROMISED. des.
    eapply list_Forall2_in2 in IN; eauto. des. ss. destruct b. ss.
    inv EVENT; ss.
    + esplits; eauto.
    + esplits; eauto.

Qed.



Definition pf_consistent_drf_future lang (e0:Thread.t lang)
           (spaces: Loc.t -> Time.t -> Prop)
           (promises: Loc.t -> Time.t -> Prop)
           (U AU: Loc.t -> Prop): Prop :=
  forall mem_future sc_future
         (UNCH: unchanged_on spaces (Thread.memory e0) mem_future)
         (ATTATCH: not_attatched (fun loc to => (<<UPDATES: (U \1/ AU) loc>>) /\ (<<MAX: Memory.max_ts loc (Thread.memory e0) = to>>)) mem_future),
  exists e2 tr,
    (<<STEPS: traced_step tr (Thread.mk _ (Thread.state e0) (Thread.local e0) sc_future mem_future) e2>>) /\

    (<<TRACE: List.Forall (fun em => no_promise (fst em) /\ ThreadEvent.get_machine_event (fst em) = MachineEvent.silent) tr>>) /\

    (<<COMPLETEU:
       forall loc (SAT: U loc),
       exists to from valr valw releasedr releasedw ordr ordw mem,
         <<IN: List.In (ThreadEvent.update loc from to valr valw releasedr releasedw ordr ordw, mem) tr>> /\ <<ORDR: Ordering.le ordr Ordering.strong_relaxed>> >>) /\

    (<<COMPLETEAU:
       forall loc (SAT: AU loc),
       exists to from valr valw releasedr releasedw ordr ordw mem,
         <<IN: List.In (ThreadEvent.update loc from to valr valw releasedr releasedw ordr ordw, mem) tr>> >>) /\

    (<<COMPLETEW: forall loc to (PROMISED: promises loc to),
        exists e m,
          (<<IN: List.In (e, m) tr>>) /\
          (<<WRITETO: rlx_write_loc loc e>>)>>)
.


Lemma unchanged_on_traced_step
      L lang th_src th_tgt th_tgt' st st' v v' prom' sc sc'
      mem_src mem_tgt mem_tgt' tr_tgt
      (PRED: List.Forall (fun em => (write_in L /1\ no_promise) (fst em)) tr_tgt)
      (STEPS: traced_step tr_tgt th_tgt th_tgt')
      (TH_SRC: th_src = Thread.mk lang st (Local.mk v Memory.bot) sc mem_src)
      (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v Memory.bot) sc mem_tgt)
      (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
      (MEM: unchanged_on L mem_tgt mem_src)
  :
    exists tr_src mem_src',
      (<<STEP: traced_step
                 tr_src
                 th_src
                 (Thread.mk lang st' (Local.mk v' Memory.bot) sc' mem_src')>>) /\
      (<<TRACE: List.map fst tr_src = List.map fst tr_tgt>>) /\
      (<<MEM: unchanged_on L mem_tgt' mem_src'>>).
Proof.
  ginduction STEPS; i; clarify.
  - esplits.
    + econs 1.
    + ss.
    + auto.
  - inv PRED. destruct th1. destruct local.
    exploit unchanged_on_step; eauto.
    { instantiate (1:=write_in L /1\ no_promise). ss. }
    { econs; eauto. } i. des. inv STEP.
    exploit IHSTEPS; ss.
    + eauto.
    + f_equal. f_equal.
      exploit promise_bot_no_promise.
      * econs.
        { eapply HD. }
        { apply SAT. }
      * i. auto.
      * ss.
      * ss.
    + eauto.
    + i. des. esplits; eauto.
      * econs; eauto.
      * ss. f_equal. auto.
Qed.


Lemma pf_consistent_shift_future lang (e0: Thread.t lang)
      spaces promises max U AU
      (CONSISTENT: pf_consistent_drf_shift e0 spaces promises max U AU)
      (BOT: (Local.promises (Thread.local e0)) = Memory.bot)
  :
    pf_consistent_drf_future e0 spaces promises U AU.
Proof.
  ii.
  unfold pf_consistent_drf_shift in CONSISTENT. des.
  exploit (choice (fun loc ts =>
                     forall (UPDATES: U loc \/ AU loc),
                       (<<TS: Time.lt (max loc) ts>>) /\
                       (<<NCOVER: forall to (TS0: Time.lt (max loc) to) (TS1: Time.le to ts),
                           ~ covered loc to mem_future>>))).
  { intros loc. destruct (classic (__guard__(U loc \/ AU loc))).
    - exploit ATTATCH.
      { splits; eauto. } i. des.
      exists to'. i. rewrite UPDATESMAX in *; auto. splits; auto.
      i. eapply EMPTY. econs; ss.
    - exists Time.bot. i. clarify. }
  intros [gap GAP].

  set (newmax := TimeMap.join (Memory.max_timemap mem_future) max).
  set (L := (spaces \2/ (fun loc to => (__guard__(U loc \/ AU loc) /\ Time.lt (max loc) to /\ Time.lt to (gap loc))) \2/                 (fun loc to => ~ U loc /\ ~ AU loc /\ Time.lt (newmax loc) to))).
  assert (NEWMAX: TimeMap.le (Memory.max_timemap mem_future) newmax).
  { unfold newmax. eapply TimeMap.join_l. }

  hexploit (CONSISTENT0 gap newmax).
  { i. eapply GAP in UPDATES. des. auto. }
  { unfold newmax. eapply TimeMap.join_r. }
  i. des.
  destruct e0, e2. destruct local, local0. ss. clarify.
  hexploit (@unchanged_on_traced_step L); try apply STEPS; eauto.
  { eapply List.Forall_impl; eauto. i. ss. des. auto. }
  { instantiate (1:=mem_future). inv UNCH. econs; eauto. unfold L. i. des.
    - eauto.
    - exploit GAP; eauto. i. des.
      exfalso. eapply NCOVER in COV; eauto. left. auto.
    - inv COV. eapply Memory.max_ts_spec in GET. des. inv ITV. ss.
      exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
      { eapply IN1. } etrans.
      { eapply TO. } etrans.
      { eapply MAX. }
      { eapply NEWMAX. }
  }
  i. des. eapply no_sc_any_sc_traced in STEP; eauto; cycle 1.
  { i. eapply List.in_map in IN; eauto.
    erewrite TRACE0 in IN.
    eapply List.in_map_iff in IN; eauto. des. destruct x, e. ss. clarify.
    eapply List.Forall_forall in IN0; eauto. ss. des; auto. }
  des. esplits; eauto.
  - eapply List.Forall_forall. i.
    eapply List.in_map in H; eauto.
    erewrite TRACE0 in H.
    eapply List.in_map_iff in H; eauto. des. destruct x0, x. ss. clarify.
    eapply List.Forall_forall in H0; eauto. ss. des; auto.
  - i. eapply COMPLETEU in SAT. des.
    eapply List.in_map in IN. erewrite <- TRACE0 in IN.
    eapply List.in_map_iff in IN; eauto. des. destruct x. ss. subst.
    esplits; eauto.
  - i. eapply COMPLETEAU in SAT. des.
    eapply List.in_map in IN. erewrite <- TRACE0 in IN.
    eapply List.in_map_iff in IN; eauto. des. destruct x. ss. subst.
    esplits; eauto.
  - i. eapply COMPLETEW in PROMISED. des.
    eapply List.in_map in IN. erewrite <- TRACE0 in IN.
    eapply List.in_map_iff in IN; eauto. des. destruct x. ss. subst.
    esplits; eauto.
Qed.

Lemma sim_pf_impl tids0 tids1 mlast spaces updates aupdates c_src c_tgt
      (SIM: sim_pf tids1 mlast spaces updates aupdates c_src c_tgt)
      (IMPL: tids0 <1= tids1)
  :
    sim_pf tids0 mlast spaces updates aupdates c_src c_tgt.
Proof.
  inv SIM. econs; eauto.
Qed.

Lemma sim_pf_minus_plus_one
      tid mlast spaces updates aupdates c_src c_tgt
      (SIM: sim_pf_minus_one tid mlast spaces updates aupdates c_src c_tgt)
      mlast_one spaces_one updates_one aupdates_one
      (ONE: sim_pf_one tid mlast_one spaces_one updates_one aupdates_one c_src c_tgt)
  :
    sim_pf
      (fun _ => True)
      (fun tid' => if Ident.eq_dec tid tid' then mlast_one else mlast tid')
      (fun tid' => if Ident.eq_dec tid tid' then spaces_one else spaces tid')
      (fun tid' => if Ident.eq_dec tid tid' then updates_one else updates tid')
      (fun tid' => if Ident.eq_dec tid tid' then aupdates_one else aupdates tid')
      c_src c_tgt.
Proof.
  inv SIM. econs; eauto. i. des_ifs. eapply THREADS; eauto.
Qed.


Lemma no_promise_traces_step_program_step lang (th0 th1: Thread.t lang) tr
      (STEPS: traced_step tr th0 th1)
      (NOPROMISE: List.Forall (fun em => no_promise (fst em) /\ ThreadEvent.get_machine_event (fst em) = MachineEvent.silent) tr)
  :
    rtc (tau (@AThread.program_step lang)) th0 th1.
Proof.
  ginduction STEPS; auto. i. inv NOPROMISE. inv HD. des. inv STEP.
  { inv STEP0; ss. }
  econs.
  - econs; eauto.
  - eapply IHSTEPS; eauto.
Qed.

Lemma sim_pf_step
      c_src0 c_tgt0 c_tgt1 tid e
      (SIM: sim_pf_all c_src0 c_tgt0)
      (STEP: Configuration.step e tid c_tgt0 c_tgt1)
  :
    exists c_src1,
      (<<STEP: APFConfiguration.opt_step e tid c_src0 c_src1>>) /\
      ((<<FAIL: e = MachineEvent.failure>>) \/
       (exists c_src2,
           (<<FAIL: APFConfiguration.step MachineEvent.failure tid c_src1 c_src2>>)) \/
       (<<SIM: sim_pf_all c_src1 c_tgt1>>)).
Proof.
  inv SIM.
  eapply sim_pf_impl with (tids0 := fun tid0 => tid <> tid0) in SIM0; ss.
  exploit sim_pf_step_minus_full; eauto. i. des.
  unguard. des; cycle 1.
  { exists c_src1. esplits; eauto. }
  exploit sim_pf_step_pf_consistent; eauto. i. des; cycle 1.
  { esplits; eauto. }
  dup SIM. inv SIM1. inv WFSRC. inv WF. exploit THREADS0; eauto. intros LCWF.
  exploit pf_consistent_drf_src_shift; eauto; ss.
  intros CONSISTENTSHIFT.
  hexploit pf_consistent_shift_future; eauto.
  { inv FORGET. specialize (THS tid).
    rewrite FIND in *. rewrite FIND0 in *. inv THS. ss. }
  intros CONSISTENTFUTURE.

  esplits; eauto. right. right. econs.
  eapply sim_pf_minus_plus_one; [eauto|].

  instantiate (1:=fun loc to => (<<UPDATES: AU loc>>) /\ (<<MAX: Memory.max_ts loc (Configuration.memory c_src1) = to>>)).
  instantiate (1:=fun loc to => (<<UPDATES: U loc>>) /\ (<<MAX: Memory.max_ts loc (Configuration.memory c_src1) = to>>)).
  instantiate (1:=concrete_covered (Local.promises lc_tgt) (Configuration.memory c_tgt1)).
  instantiate (1:=Configuration.memory c_src1). econs.

  - refl.
  - ii. assert (MAXTS: to = Memory.max_ts loc (Configuration.memory c_src1)).
    { des; auto. } clear SAT. clarify. split.
    + inv MEM. specialize (INHABITED loc).
      eapply Memory.max_ts_spec in INHABITED. des. destruct msg.
      * econs; eauto.
      * exfalso. eapply sim_pf_src_no_reserve; eauto.
    + esplits.
      * eapply Time.incr_spec.
      * ii. inv H. inv ITV. inv ITV0. ss.
        eapply Memory.max_ts_spec in GET. des.
        eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
        { eapply FROM. } etrans; eauto.
  - i. clarify. dependent destruction H0. dependent destruction H1. econs; eauto.
    + i. des. dup UPDATES. eapply AUPDATES in UPDATES.
      unfold Memory.latest_reserve in UPDATES.
      des_ifs. inv WFTGT. inv WF. exploit THREADS1; eauto. intros LCWFTGT.
      inv LCWFTGT. dup Heq. eapply PROMISES in Heq0.
      exploit max_full_ts_max_ts; eauto.
      { inv MEM0. auto. }
      i. des.
      * destruct (MAX loc). des. unfold Memory.get in Heq0.
        rewrite FULL in GET. clarify .
      * clarify. unfold pf_consistent_drf_shift in *. des.
        exploit UPDATESMAX; eauto. i. ss. rewrite x in *. esplits; eauto.

    + i. hexploit (CONSISTENTFUTURE m sc); eauto.
      { eapply not_attatched_mon; eauto. i. des; ss; auto. }
      i. des. ss.
      exploit COMPLETEW; eauto. i. des.
      exploit traced_step_in; eauto. i. des. clarify.
      eapply no_promise_traces_step_program_step in STEPS0.
      * destruct th'. destruct local. ss. esplits; eauto.
        clear - STEP1 WRITETO. inv STEP1. inv STEP; inv STEP0; ss.
        unfold is_writing. inv LOCAL; ss; des; subst.
        { esplits; eauto.
          - econs; eauto.
          - ss. }
        { esplits; eauto.
          - econs; eauto.
          - ss. }
      * eapply Forall_app_inv in TRACE. des. auto.

    + i. hexploit (CONSISTENTFUTURE m sc); eauto.
      { eapply not_attatched_mon; eauto. i. des; ss; auto. }
      i. des. ss.
      exploit COMPLETEU; eauto. i. des.
      exploit traced_step_in; eauto. i. des. subst.
      eapply no_promise_traces_step_program_step in STEPS0.
      * destruct th'. destruct local. ss. esplits; eauto.
        clear - STEP1 ORDR. inv STEP1. inv STEP; inv STEP0; ss.
        unfold is_updating. inv LOCAL; ss; des; subst.
        esplits; eauto.
        { econs; eauto. }
        { ss. }
      * eapply Forall_app_inv in TRACE. des. auto.

    + i. hexploit (CONSISTENTFUTURE m sc); eauto.
      { eapply not_attatched_mon; eauto. i. des; ss; auto. }
      i. des. ss.
      exploit COMPLETEAU; eauto. i. des.
      exploit traced_step_in; eauto. i. des. subst.
      eapply no_promise_traces_step_program_step in STEPS0.
      * destruct th'. destruct local. ss. esplits; eauto.
        clear - STEP1. inv STEP1. inv STEP; inv STEP0; ss.
        unfold is_updating. inv LOCAL; ss; des; subst.
        esplits; eauto.
        { econs; eauto. }
        { instantiate (1:=ordr). destruct ordr; ss. }
        { ss. }
      * eapply Forall_app_inv in TRACE. des. auto.

  - i. clarify.
Qed.