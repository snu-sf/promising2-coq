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
Require Import PromiseConsistent.
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
Require Import APredStep.

Require Import ALocal.
Require Import AThread.
Require Import AMemory.

Require Import ADRF_PF0.


Set Implicit Arguments.

Section MAPPED.

  Variable f: Loc.t -> Time.t -> Time.t -> Prop.

  Definition mapping_map_le:=
    forall loc t0 t1 ft0 ft1
           (MAP0: f loc t0 ft0)
           (MAP1: f loc t1 ft1),
      Time.le t0 t1 -> Time.le ft0 ft1.

  Definition mapping_map_bot :=
    forall loc,
      f loc Time.bot Time.bot.

  Definition mapping_map_eq :=
    forall loc to ft0 ft1
           (MAP0: f loc to ft0)
           (MAP1: f loc to ft1),
      ft0 = ft1.

  Hypothesis map_le: mapping_map_le.
  Hypothesis map_bot: mapping_map_bot.
  Hypothesis map_eq: mapping_map_eq.

  Definition dom loc to: Prop :=
    exists fto, f loc to fto.

  Definition collapsed (loc: Loc.t) (t0 t1: Time.t): Prop :=
    exists ft,
      (<<MAP0: f loc t0 ft>>) /\ (<<MAP1: f loc t1 ft>>).

  Global Program Instance collapsed_Symmetric (loc: Loc.t): Symmetric (collapsed loc).
  Next Obligation.
    destruct H. eexists. des. splits; eauto.
  Qed.

  Lemma collapsed_inside
        loc
        t0 t1 t2 t3
        ft0 ft1 ft2 ft3
        (MAP0: f loc t0 ft0)
        (MAP1: f loc t1 ft1)
        (MAP2: f loc t2 ft2)
        (MAP3: f loc t3 ft3)
        (CLPS: collapsed loc t0 t3)
        (TLE0: Time.le t0 t1)
        (TLE1: Time.le t1 t2)
        (TLE2: Time.le t2 t3)
    :
      collapsed loc t1 t2.
  Proof.
    eapply map_le in TLE0; eauto.
    eapply map_le in TLE1; eauto.
    eapply map_le in TLE2; eauto.
    unfold collapsed in *. des.
    hexploit (map_eq MAP0 MAP4). i. subst.
    hexploit (map_eq MAP3 MAP5). i. subst.
    exploit TimeFacts.antisym; eauto. i. subst.
    exploit TimeFacts.antisym; eauto. i. subst.
    esplits; eauto.
  Qed.

  Lemma not_collapsed_outside
        loc
        t0 t1 t2 t3
        ft0 ft1 ft2 ft3
        (MAP0: f loc t0 ft0)
        (MAP1: f loc t1 ft1)
        (MAP2: f loc t2 ft2)
        (MAP3: f loc t3 ft3)
        (NCLPS: ~ collapsed loc t1 t2)
        (TLE0: Time.le t0 t1)
        (TLE1: Time.le t1 t2)
        (TLE2: Time.le t2 t3)
    :
      ~ collapsed loc t0 t3.
  Proof.
    ii. apply NCLPS. eapply collapsed_inside.
    - apply MAP0.
    - apply MAP1.
    - apply MAP2.
    - apply MAP3.
    - auto.
    - auto.
    - auto.
    - auto.
  Qed.

  Lemma map_lt_only_if
        loc t0 t1 ft0 ft1
        (MAP0: f loc t0 ft0)
        (MAP1: f loc t1 ft1)
    :
      Time.lt ft0 ft1 -> Time.lt t0 t1.
  Proof.
    set (TimeFacts.OrderTac.TO.lt_total t0 t1). des; eauto.
    - clarify. i.
      hexploit (map_eq MAP0 MAP1). i. subst.
      timetac.
    - exploit map_le.
      + eapply MAP1.
      + eapply MAP0.
      + left. eauto.
      + i. timetac.
  Qed.
  #[local]
  Hint Resolve map_lt_only_if: core.

  Definition map_eq_iff
             loc t0 t1 ft0 ft1
             (MAP0: f loc t0 ft0)
             (MAP1: f loc t1 ft1)
             (CLPS: ~ collapsed loc t0 t1)
    :
      t0 = t1 <-> ft0 = ft1.
  Proof.
    split; i; clarify; eauto.
    exfalso. apply CLPS. eexists. eauto.
  Qed.
  #[local]
  Hint Resolve map_eq_iff: core.

  Definition map_lt_iff
             loc t0 t1 ft0 ft1
             (MAP0: f loc t0 ft0)
             (MAP1: f loc t1 ft1)
             (CLPS: ~ collapsed loc t0 t1)
    :
      Time.lt t0 t1 <-> Time.lt ft0 ft1.
  Proof.
    split; i; cycle 1.
    { eapply map_lt_only_if; eauto. }
    exploit map_le.
    - eapply MAP0.
    - eapply MAP1.
    - left. eauto.
    - i. destruct x; auto. exfalso. apply CLPS.
      destruct H0. eexists. eauto.
  Qed.
  #[local]
  Hint Resolve map_lt_iff: core.

  Definition map_le_iff
             loc t0 t1 ft0 ft1
             (MAP0: f loc t0 ft0)
             (MAP1: f loc t1 ft1)
             (CLPS: ~ collapsed loc t0 t1)
    :
      Time.le t0 t1 <-> Time.le ft0 ft1.
  Proof.
    repeat rewrite Time.le_lteq.
    split; i; des; clarify; eauto.
    - left. erewrite <- map_lt_iff; eauto.
    - right. eapply map_eq_iff; eauto.
  Qed.
  #[local]
  Hint Resolve map_le_iff: core.

  Definition timemap_map (tm ftm: TimeMap.t): Prop :=
    forall loc, f loc (tm loc) (ftm loc).


  Record view_map (vw fvw: View.t): Prop :=
    view_map_intro
      { map_pln: timemap_map (View.pln vw) (View.pln fvw);
        map_rlx: timemap_map (View.rlx vw) (View.rlx fvw);
      }.

  Inductive opt_view_map: option View.t -> option View.t -> Prop :=
  | opt_view_map_some
      vw fvw
      (MAP: view_map vw fvw)
    :
      opt_view_map (Some vw) (Some fvw)
  | opt_view_map_none
    :
      opt_view_map None None
  .

  Record tview_map (vw fvw: TView.t): Prop :=
    tview_map_intro
      { map_rel: forall loc, view_map ((TView.rel vw) loc) ((TView.rel fvw) loc);
        map_cur: view_map (TView.cur vw) (TView.cur fvw);
        map_acq: view_map (TView.acq vw) (TView.acq fvw);
      }.

  Inductive msg_map: Message.t -> Message.t -> Prop :=
  | msg_map_reserve
    :
      msg_map Message.reserve Message.reserve
  | msg_map_full
      val released freleased
      (MAP: opt_view_map released freleased)
    :
      msg_map (Message.full val released) (Message.full val freleased)
  .

  Inductive memory_op_kind_map (loc: Loc.t) : Memory.op_kind -> Memory.op_kind -> Prop :=
  | memory_op_kind_map_add
    :
      memory_op_kind_map loc (Memory.op_kind_add) (Memory.op_kind_add)
  | memory_op_kind_map_split
      to fto msg fmsg
      (MSG: msg_map msg fmsg)
      (TO: f loc to fto)
    :
      memory_op_kind_map loc (Memory.op_kind_split to msg) (Memory.op_kind_split fto fmsg)
  | memory_op_kind_map_lower
      msg fmsg
      (MSG: msg_map msg fmsg)
    :
      memory_op_kind_map loc (Memory.op_kind_lower msg) (Memory.op_kind_lower fmsg)
  | memory_op_kind_map_cancel
    :
      memory_op_kind_map loc (Memory.op_kind_cancel) (Memory.op_kind_cancel)
  .
  #[local]
  Hint Constructors memory_op_kind_map: core.

  Inductive tevent_map: ThreadEvent.t -> ThreadEvent.t -> Prop :=
  | tevent_map_promise
      loc from ffrom to fto msg fmsg kind fkind
      (FROM: f loc from ffrom)
      (TO: f loc to fto)
      (MSG: msg_map msg fmsg)
      (KIND: memory_op_kind_map loc kind fkind)
    :
      tevent_map
        (ThreadEvent.promise loc ffrom fto fmsg fkind)
        (ThreadEvent.promise loc from to msg kind)
  | tevent_map_read
      loc to fto val released freleased freleased' ordr
      (TO: f loc to fto)
      (RELEASED: opt_view_map released freleased')
      (RELEASEDLE: View.opt_le freleased freleased')
    :
      tevent_map
        (ThreadEvent.read loc fto val freleased ordr)
        (ThreadEvent.read loc to val released ordr)
  | tevent_map_write
      loc from ffrom to fto val released freleased freleased' ordw
      (FROM: f loc from ffrom)
      (TO: f loc to fto)
      (RELEASED: opt_view_map released freleased')
      (RELEASEDLE: View.opt_le freleased freleased')
    :
      tevent_map
        (ThreadEvent.write loc ffrom fto val freleased ordw)
        (ThreadEvent.write loc from to val released ordw)
  | tevent_map_update
      loc from ffrom to fto valr valw releasedr freleasedr freleasedr'
      releasedw freleasedw freleasedw' ordr ordw
      (FROM: f loc from ffrom)
      (TO: f loc to fto)
      (RELEASEDR: opt_view_map releasedr freleasedr')
      (RELEASEDW: opt_view_map releasedw freleasedw')
      (RELEASEDRLE: View.opt_le freleasedr freleasedr')
      (RELEASEDWLE: View.opt_le freleasedw freleasedw')
    :
      tevent_map
        (ThreadEvent.update loc ffrom fto valr valw freleasedr freleasedw ordr ordw)
        (ThreadEvent.update loc from to valr valw releasedr releasedw ordr ordw)
  | tevent_map_fence
      or ow
    :
      tevent_map
        (ThreadEvent.fence or ow)
        (ThreadEvent.fence or ow)
  | tevent_map_syscall
      e
    :
      tevent_map
        (ThreadEvent.syscall e)
        (ThreadEvent.syscall e)
  | tevent_map_silent
    :
      tevent_map
        (ThreadEvent.silent)
        (ThreadEvent.silent)
  | tevent_map_failure
    :
      tevent_map
        (ThreadEvent.failure)
        (ThreadEvent.failure)
  .

  Definition non_collapsable (loc: Loc.t) (to: Time.t): Prop :=
    forall to' (TLE: Time.lt to' to),
      ~ collapsed loc to' to.

  Lemma map_lt_non_collapsable
        loc t0 t1 ft0 ft1
        (MAP0: f loc t0 ft0)
        (MAP1: f loc t1 ft1)
        (NCLPS: non_collapsable loc t1)
    :
      Time.lt t0 t1 <-> Time.lt ft0 ft1.
  Proof.
    split; i.
    - erewrite <- map_lt_iff; eauto.
    - eapply map_lt_only_if; eauto.
  Qed.

  Lemma time_join_map loc t0 t1 ft0 ft1
        (MAP0: f loc t0 ft0)
        (MAP1: f loc t1 ft1)
    :
      f loc (Time.join t0 t1) (Time.join ft0 ft1).
  Proof.
    unfold Time.join. des_ifs.
    - eapply map_le in l; eauto. timetac.
    - destruct l0; auto.
      + eapply map_lt_only_if in H; eauto.
        exfalso. eapply Time.lt_strorder. etrans; eauto.
      + destruct H. auto.
  Qed.

  Lemma timemap_bot_map
    :
      timemap_map TimeMap.bot TimeMap.bot.
  Proof.
    ii. eapply map_bot.
  Qed.

  Lemma view_bot_map
    :
      view_map View.bot View.bot.
  Proof.
    econs.
    - eapply timemap_bot_map; eauto.
    - eapply timemap_bot_map; eauto.
  Qed.

  Lemma timemap_singleton_map loc to fto
        (MAP: f loc to fto)
    :
      timemap_map (TimeMap.singleton loc to) (TimeMap.singleton loc fto).
  Proof.
    ii. unfold TimeMap.singleton.
    setoid_rewrite LocFun.add_spec. des_ifs.
  Qed.

  Lemma singleton_ur_map loc to fto
        (MAP: f loc to fto)
    :
      view_map (View.singleton_ur loc to) (View.singleton_ur loc fto).
  Proof.
    unfold View.singleton_ur. econs; ss.
    - eapply timemap_singleton_map; eauto.
    - eapply timemap_singleton_map; eauto.
  Qed.

  Lemma singleton_rw_map loc to fto
        (MAP: f loc to fto)
    :
      view_map (View.singleton_rw loc to) (View.singleton_rw loc fto).
  Proof.
    unfold View.singleton_ur. econs; ss.
    eapply timemap_singleton_map; eauto.
  Qed.

  Lemma singleton_ur_if_map loc to fto cond
        (MAP: f loc to fto)
    :
      view_map (View.singleton_ur_if cond loc to) (View.singleton_ur_if cond loc fto).
  Proof.
    unfold View.singleton_ur_if. des_ifs.
    - eapply singleton_ur_map; eauto.
    - eapply singleton_rw_map; eauto.
  Qed.

  Lemma timemap_join_map tm0 tm1 ftm0 ftm1
        (TM0: timemap_map tm0 ftm0)
        (TM1: timemap_map tm1 ftm1)
    :
      timemap_map (TimeMap.join tm0 tm1) (TimeMap.join ftm0 ftm1).
  Proof.
    ii. unfold TimeMap.join.
    eapply time_join_map; eauto.
  Qed.

  Lemma timemap_le_map tm0 tm1 ftm0 ftm1
        (TM0: timemap_map tm0 ftm0)
        (TM1: timemap_map tm1 ftm1)
        (TMLE: TimeMap.le tm0 tm1)
    :
      TimeMap.le ftm0 ftm1.
  Proof.
    ii. eapply map_le; eauto.
  Qed.

  Inductive memory_map2 m fm: Prop :=
  | memory_map2_intro
      (MAPPED: forall loc to from msg (GET: Memory.get loc to m = Some (from, msg)),
          msg = Message.reserve \/
          exists fto ffrom fmsg' fmsg,
            (<<TO: f loc to fto>>) /\
            (<<MSG: msg_map msg fmsg'>>) /\
            (<<MSGLE: Message.le fmsg fmsg'>>) /\
            (<<GET: Memory.get loc fto fm = Some (ffrom, fmsg)>>))
      (ONLY: forall loc fto ffrom fmsg
                    (GET: Memory.get loc fto fm = Some (ffrom, fmsg)),
          exists to from msg,
            (<<TO: f loc to fto>>) /\
            (<<GET: Memory.get loc to m = Some (from, msg)>>) /\
            (<<FROM: f loc from ffrom>>))
  .

  Inductive memory_map m fm: Prop :=
  | memory_map_intro
      (MAPPED: forall loc to from msg (GET: Memory.get loc to m = Some (from, msg)),
          msg = Message.reserve \/
          exists fto ffrom fmsg' fmsg,
            (<<TO: f loc to fto>>) /\
            (<<MSG: msg_map msg fmsg'>>) /\
            (<<MSGLE: Message.le fmsg fmsg'>>) /\
            (<<GET: Memory.get loc fto fm = Some (ffrom, fmsg)>>))
      (ONLY: forall loc fto ffrom fmsg
                    (GET: Memory.get loc fto fm = Some (ffrom, fmsg)),
          (exists to from fto' ffrom',
              (<<TO: f loc to fto'>>) /\
              (<<TS0: Time.le ffrom' ffrom>>) /\
              (<<TS1: Time.le fto fto'>>) /\
              (<<FROM: f loc from ffrom'>>) /\
              (<<COVERED: forall ts (ITV: Interval.mem (from, to) ts),
                  covered loc ts m>>)) \/
          (<<OUT: forall ts fts (MAP: f loc ts fts), Time.lt fts ffrom>>))
  .

  Lemma memory_map2_memory_map
    :
      memory_map2 <2= memory_map.
  Proof.
    ii. inv PR. econs; eauto.
    i. exploit ONLY; eauto. i. des.
    left. esplits.
    - eapply TO.
    - refl.
    - refl.
    - eapply FROM.
    - i. econs; eauto.
  Qed.

  Inductive promises_map m fm: Prop :=
  | promises_map_intro
      (MAPPED: forall loc to from msg (GET: Memory.get loc to m = Some (from, msg)),
          exists fto ffrom fmsg,
            (<<NCLPS: non_collapsable loc to>>) /\
            (<<TO: f loc to fto>>) /\
            (<<MSG: msg_map msg fmsg>>) /\
            (<<GET: Memory.get loc fto fm = Some (ffrom, fmsg)>>))
      (ONLY: forall loc fto ffrom fmsg
                    (GET: Memory.get loc fto fm = Some (ffrom, fmsg)),
          exists to from msg,
            (<<TO: f loc to fto>>) /\
            (<<GET: Memory.get loc to m = Some (from, msg)>>) /\
            (<<FROM: f loc from ffrom>>))
  .

  Definition collapsable_unwritable prom mem: Prop :=
    forall loc t
           (SAT: (fun loc' t' => exists ts0 ts1,
                      (<<CLPS: collapsed loc' ts0 ts1>>) /\
                      (<<ITV: Interval.mem (ts0, ts1) t'>>)) loc t),
      unwritable mem prom loc t.

  Lemma collapsable_unwritable_step pf e lang (th0 th1: Thread.t lang)
        (STEP: AThread.step pf e th0 th1)
        (WFMEM: collapsable_unwritable (Local.promises (Thread.local th0)) (Thread.memory th0))
    :
      collapsable_unwritable (Local.promises (Thread.local th1)) (Thread.memory th1) .
  Proof.
    ii. eapply unwritable_increase; eauto.
  Qed.

  Lemma collapsable_unwritable_steps P lang (th0 th1: Thread.t lang)
        (STEP: rtc (tau (@pred_step P lang)) th0 th1)
        (WFMEM: collapsable_unwritable (Local.promises (Thread.local th0)) (Thread.memory th0))
    :
      collapsable_unwritable (Local.promises (Thread.local th1)) (Thread.memory th1) .
  Proof.
    revert WFMEM. induction STEP; auto.
    i. eapply IHSTEP. inv H. inv TSTEP. inv STEP0.
    eapply collapsable_unwritable_step; eauto.
  Qed.

  Lemma promises_map_memory_map2 m fm
        (PROMISES: promises_map m fm)
    :
      memory_map2 m fm.
  Proof.
    inv PROMISES. econs; eauto.
    i. exploit MAPPED; eauto. i. des.
    right. esplits; eauto. refl.
  Qed.

  Lemma promises_map_memory_map m fm
        (PROMISES: promises_map m fm)
    :
      memory_map m fm.
  Proof.
    eapply memory_map2_memory_map.
    eapply promises_map_memory_map2; eauto.
  Qed.
  #[local]
  Hint Resolve promises_map_memory_map: core.

  Lemma closed_timemap_map m fm tm ftm
        (MEM: memory_map m fm)
        (TM: timemap_map tm ftm)
        (CLOSED: Memory.closed_timemap tm m)
    :
      Memory.closed_timemap ftm fm.
  Proof.
    inv MEM. ii. specialize (CLOSED loc). des.
    eapply MAPPED in CLOSED. des; clarify. inv MSG.
    specialize (TM loc).
    hexploit (map_eq TM TO). i. subst.
    inv MSGLE. esplits; eauto.
  Qed.

  Lemma closed_view_map m fm vw fvw
        (MEM: memory_map m fm)
        (VIEW: view_map vw fvw)
        (CLOSED: Memory.closed_view vw m)
    :
      Memory.closed_view fvw fm.
  Proof.
    inv CLOSED. inv VIEW. econs.
    - eapply closed_timemap_map; eauto.
    - eapply closed_timemap_map; eauto.
  Qed.

  Lemma closed_opt_view_map m fm vw fvw
        (MEM: memory_map m fm)
        (VIEW: opt_view_map vw fvw)
        (CLOSED: Memory.closed_opt_view vw m)
    :
      Memory.closed_opt_view fvw fm.
  Proof.
    inv CLOSED.
    - inv VIEW. econs. eapply closed_view_map; eauto.
    - inv VIEW. econs.
  Qed.

  Lemma view_join_map v0 v1 fv0 fv1
        (VIEW0: view_map v0 fv0)
        (VIEW1: view_map v1 fv1)
    :
      view_map (View.join v0 v1) (View.join fv0 fv1).
  Proof.
    inv VIEW0. inv VIEW1.
    unfold View.join. econs; ss.
    - eapply timemap_join_map; eauto.
    - eapply timemap_join_map; eauto.
  Qed.

  Lemma tviewjoin_map tv0 tv1 ftv0 ftv1
        (TVIEW0: tview_map tv0 ftv0)
        (TVIEW1: tview_map tv1 ftv1)
    :
      tview_map (TView.join tv0 tv1) (TView.join ftv0 ftv1).
  Proof.
    inv TVIEW0. inv TVIEW1.
    unfold TView.join. econs; ss.
    - i. eapply view_join_map; eauto.
    - eapply view_join_map; eauto.
    - eapply view_join_map; eauto.
  Qed.

  Lemma unwrap_map released freleased
        (VIEW: opt_view_map released freleased)
    :
      view_map (View.unwrap released) (View.unwrap freleased).
  Proof.
    inv VIEW; ss.
  Qed.

  Lemma readable_map vw fvw loc to fto released freleased ordr
        (VIEW: view_map vw fvw)
        (TO: f loc to fto)
        (RELEASED: opt_view_map released freleased)
        (READABLE: TView.readable vw loc to released ordr)
    :
      TView.readable fvw loc fto freleased ordr.
  Proof.
    inv READABLE. econs.
    - eapply map_le; eauto.
      inv VIEW. eauto.
    - intros ORD. specialize (RLX ORD).
      eapply map_le; eauto.
      inv VIEW. eauto.
  Qed.

  Lemma read_tview_map tvw ftvw loc to fto released freleased ord
        (TVIEW: tview_map tvw ftvw)
        (TO: f loc to fto)
        (RELEASED: opt_view_map released freleased)
    :
      tview_map
        (TView.read_tview tvw loc to released ord)
        (TView.read_tview ftvw loc fto freleased ord).
  Proof.
    unfold TView.read_tview. econs; ss.
    - i. eapply map_rel; eauto.
    - eapply view_join_map.
      + eapply view_join_map.
        * eapply map_cur; eauto.
        * eapply singleton_ur_if_map; eauto.
      + des_ifs. eapply unwrap_map; eauto.
    - eapply view_join_map.
      + eapply view_join_map.
        * eapply map_acq; eauto.
        * eapply singleton_ur_if_map; eauto.
      + des_ifs. eapply unwrap_map; eauto.
  Qed.

  Lemma write_tview_map tvw ftvw sc fsc loc to fto ord
        (TVIEW: tview_map tvw ftvw)
        (TO: f loc to fto)
    :
      tview_map
        (TView.write_tview tvw sc loc to ord)
        (TView.write_tview ftvw fsc loc fto ord).
  Proof.
    unfold TView.write_tview. econs; ss.
    - i. setoid_rewrite LocFun.add_spec. des_ifs.
      + eapply view_join_map.
        * eapply map_cur; eauto.
        * eapply singleton_ur_map; eauto.
      + eapply view_join_map.
        * eapply map_rel; eauto.
        * eapply singleton_ur_map; eauto.
      + eapply map_rel in TVIEW. eauto.
    - eapply view_join_map.
      + eapply map_cur; eauto.
      + eapply singleton_ur_map; eauto.
    - eapply view_join_map.
      + eapply map_acq; eauto.
      + eapply singleton_ur_map; eauto.
  Qed.

  Lemma read_fence_tview_map tvw ftvw ord
        (TVIEW: tview_map tvw ftvw)
    :
      tview_map
        (TView.read_fence_tview tvw ord)
        (TView.read_fence_tview ftvw ord).
  Proof.
    unfold TView.read_fence_tview. econs; ss.
    - i. eapply map_rel; eauto.
    - des_ifs.
      + eapply map_acq; eauto.
      + eapply map_cur; eauto.
    - eapply map_acq; eauto.
  Qed.

  Lemma write_fence_sc_map tvw ftvw sc fsc ord
        (TVIEW: tview_map tvw ftvw)
        (SC: timemap_map sc fsc)
    :
      timemap_map
        (TView.write_fence_sc tvw sc ord)
        (TView.write_fence_sc ftvw fsc ord).
  Proof.
    unfold TView.write_fence_sc. des_ifs.
    eapply timemap_join_map; eauto.
    eapply map_rlx; eauto. eapply map_cur; eauto.
  Qed.

  Lemma write_fence_tview_map tvw ftvw sc fsc ord
        (TVIEW: tview_map tvw ftvw)
        (SC: timemap_map sc fsc)
    :
      tview_map
        (TView.write_fence_tview tvw sc ord)
        (TView.write_fence_tview ftvw fsc ord).
  Proof.
    unfold TView.write_fence_tview. econs; ss.
    - i. des_ifs.
      + econs; ss.
        * eapply write_fence_sc_map; eauto.
        * eapply write_fence_sc_map; eauto.
      + eapply map_cur; eauto.
      + eapply map_rel; eauto.
    - des_ifs.
      + econs; ss.
        * eapply write_fence_sc_map; eauto.
        * eapply write_fence_sc_map; eauto.
      + eapply map_cur; eauto.
    - eapply view_join_map.
      + eapply map_acq; eauto.
      + des_ifs. econs; ss.
        * eapply write_fence_sc_map; eauto.
        * eapply write_fence_sc_map; eauto.
  Qed.

  Lemma write_released_map tvw ftvw sc fsc loc to fto released freleased ord
        (TVIEW: tview_map tvw ftvw)
        (SC: timemap_map sc fsc)
        (TO: f loc to fto)
        (VIEW: opt_view_map released freleased)
    :
      opt_view_map
        (TView.write_released tvw sc loc to released ord)
        (TView.write_released ftvw fsc loc fto freleased ord).
  Proof.
    unfold TView.write_released. des_ifs; econs.
    eapply view_join_map; eauto.
    - eapply unwrap_map; eauto.
    - eapply map_rel; eauto. eapply write_tview_map; eauto.
  Qed.

  Lemma bot_promises_map fprom
        (MEM: promises_map Memory.bot fprom)
    :
      fprom = Memory.bot.
  Proof.
    inv MEM. eapply Memory.ext. i.
    rewrite Memory.bot_get.
    destruct (Memory.get loc ts fprom) eqn:GET; auto.
    destruct p. eapply ONLY in GET. des.
    rewrite Memory.bot_get in GET; eauto. clarify.
  Qed.

  Lemma no_reserves_map prom fprom
        (RESERVES: no_reserves prom)
        (MEM: promises_map prom fprom)
    :
      no_reserves fprom.
  Proof.
    inv MEM. ii. clarify. dup GET.
    eapply ONLY in GET0. des.
    dup GET0. eapply MAPPED in GET1. des.
    hexploit (map_eq TO TO0). i. clarify. inv MSG.
    eapply RESERVES in GET0. clarify.
  Qed.

  Lemma msg_get_map m fm loc to from msg
        (MEM: memory_map m fm)
        (GET: Memory.get loc to m = Some (from, msg))
    :
      msg = Message.reserve \/
      exists ffrom fto fmsg fmsg',
        (<<GET: Memory.get loc fto fm = Some (ffrom, fmsg)>>) /\
        (<<TO: f loc to fto>>) /\
        (<<MSG: msg_map msg fmsg'>>) /\
        (<<MSGLE: Message.le fmsg fmsg'>>).
  Proof.
    inv MEM. eapply MAPPED in GET. des; auto.
    right. esplits; eauto.
  Qed.

  Lemma msg_get_map_if m fm loc to fto from msg
        (MEM: memory_map m fm)
        (TO: f loc to fto)
        (GET: Memory.get loc to m = Some (from, msg))
    :
      msg = Message.reserve \/
      exists ffrom fmsg fmsg',
        (<<GET: Memory.get loc fto fm = Some (ffrom, fmsg)>>) /\
        (<<MSG: msg_map msg fmsg'>>) /\
        (<<MSGLE: Message.le fmsg fmsg'>>).
  Proof.
    inv MEM. eapply MAPPED in GET. des; auto. right.
    hexploit (map_eq TO TO0). i. subst.
    esplits; eauto.
  Qed.

  (* Lemma msg_get_map_only_if m fm *)
  (*       (MEM: memory_map m fm) *)
  (*       loc fto ffrom fmsg *)
  (*       (GET: Memory.get loc fto fm = Some (ffrom, fmsg)) *)
  (*   : *)
  (*     exists to from msg fmsg', *)
  (*       (<<TO: f loc to fto>>) /\ *)
  (*       (<<GET: Memory.get loc to m = Some (from, msg)>>) /\ *)
  (*       (<<FROM: f loc from ffrom>>) /\ *)
  (*       (<<MSG: msg_map msg fmsg'>>) /\ *)
  (*       (<<MSGLE: Message.le fmsg fmsg' >>) *)
  (* . *)
  (* Proof. *)
  (*   inv MEM. *)
  (*   dup GET. eapply ONLY in GET. des. *)
  (*   dup GET. eapply MAPPED in GET1. des. *)
  (*   - clarify. esplits; eauto. econs. *)
  (*   - hexploit (map_eq TO TO0). i. clarify. *)
  (*     esplits; eauto. *)
  (* Qed. *)

  Lemma promise_consistent_map tvw ftvw prom fprom
        (TVIEW: tview_map tvw ftvw)
        (PROMS: promises_map prom fprom)
        (CONSISTENT: Local.promise_consistent (Local.mk tvw prom))
    :
      Local.promise_consistent (Local.mk ftvw fprom).
  Proof.
    ii. ss.
    inv PROMS. exploit ONLY; eauto. i. des.
    exploit MAPPED; eauto. i. des.
    hexploit (map_eq TO TO0). i. clarify.
    inv MSG. exploit CONSISTENT; ss; eauto.
    i. erewrite <- map_lt_iff; eauto.
    eapply map_rlx. eapply map_cur. auto.
  Qed.

  Lemma nonsynch_loc_map loc prom fprom
        (PROMS: promises_map prom fprom)
        (NONSYNCH: Memory.nonsynch_loc loc prom)
    :
      Memory.nonsynch_loc loc fprom.
  Proof.
    ii. dup GET.
    inv PROMS. exploit ONLY; eauto. i. des.
    exploit MAPPED; eauto. i. des.
    hexploit (map_eq TO TO0). i. clarify.
    eapply NONSYNCH in GET1. des_ifs.
    - inv MSG. inv MAP. ss.
    - inv MSG.
  Qed.

  Lemma writable_map vw fvw sc fsc loc to fto released freleased ordw
        (VIEW: view_map vw fvw)
        (TO: f loc to fto)
        (RELEASED: opt_view_map released freleased)
        (NCLPS: non_collapsable loc to)
        (WRITABLE: TView.writable vw sc loc to ordw)
    :
      TView.writable fvw fsc loc fto ordw.
  Proof.
    inv WRITABLE. econs.
    erewrite <- map_lt_non_collapsable; eauto.
    eapply map_rlx. eauto.
  Qed.

  Lemma timemap_map_exists mem fmem tm
        (MEM: memory_map mem fmem)
        (CLOSED: Memory.closed_timemap tm mem)
    :
      exists ftm,
        (<<TM: timemap_map tm ftm>>) /\
        (<<CLOSED: Memory.closed_timemap ftm fmem>>).
  Proof.
    hexploit (choice (fun loc to =>
                        (<<MAP: f loc (tm loc) to>>) /\
                        exists from val released,
                          Memory.get loc to fmem = Some (from, Message.full val released))).
    { intros loc. specialize (CLOSED loc). des.
      inv MEM. eapply MAPPED in CLOSED. des; clarify.
      inv MSG. inv MSGLE.
      esplits; eauto. }
    i. des. esplits; eauto.
    - ii. specialize (H loc). des. eauto.
    - ii. specialize (H loc). des. eauto.
  Qed.

  Lemma opt_view_map_exists mem fmem vw
        (MEM: memory_map mem fmem)
        (CLOSED: Memory.closed_opt_view vw mem)
    :
      exists fvw,
        (<<VIEW: opt_view_map vw fvw>>) /\
        (<<CLOSED: Memory.closed_opt_view fvw fmem>>).
  Proof.
    inv CLOSED.
    - inv CLOSED0.
      hexploit (timemap_map_exists MEM PLN). i. des.
      hexploit (timemap_map_exists MEM RLX). i. des.
      exists (Some (View.mk ftm ftm0)). esplits; eauto.
      econs. econs; eauto.
    - exists None. esplits; eauto. econs.
  Qed.

  Lemma view_wf_map vw fvw
        (VIEW: view_map vw fvw)
        (VIEWWF: View.wf vw)
    :
      View.wf fvw.
  Proof.
    inv VIEWWF. inv VIEW.
    econs. eapply timemap_le_map; eauto.
  Qed.

  Lemma opt_view_wf_map vw fvw
        (VIEW: opt_view_map vw fvw)
        (VIEWWF: View.opt_wf vw)
    :
      View.opt_wf fvw.
  Proof.
    inv VIEWWF; inv VIEW; econs.
    eapply view_wf_map; eauto.
  Qed.

  Lemma msg_wf_map msg fmsg
        (MSG: msg_map msg fmsg)
        (MSGWF: Message.wf msg)
    :
      Message.wf fmsg.
  Proof.
    inv MSGWF.
    - inv MSG. econs; ss. eapply opt_view_wf_map; eauto.
    - inv MSG. econs.
  Qed.

  Lemma time_meet_map loc t0 t1 ft0 ft1
        (MAP0: f loc t0 ft0)
        (MAP1: f loc t1 ft1)
    :
      f loc (Time.meet t0 t1) (Time.meet ft0 ft1).
  Proof.
    unfold Time.meet. des_ifs.
    - eapply map_le in l; eauto. timetac.
    - destruct l0; auto.
      + eapply map_lt_only_if in H; eauto.
        exfalso. eapply Time.lt_strorder. etrans; eauto.
      + destruct H. auto.
  Qed.

  Lemma disjoint_map loc from0 ffrom0 to0 fto0 from1 ffrom1 to1 fto1
        (FROM0: f loc from0 ffrom0)
        (TO0: f loc to0 fto0)
        (FROM1: f loc from1 ffrom1)
        (TO1: f loc to1 fto1)
        (DISJOINT: Interval.disjoint (from0, to0) (from1, to1))
    :
      Interval.disjoint (ffrom0, fto0) (ffrom1, fto1).
  Proof.
    apply NNPP. ii. revert DISJOINT.
    apply disjoint_equivalent. apply disjoint_equivalent in H. des.
    splits.
    - eapply map_lt_only_if; eauto.
    - eapply map_lt_only_if; eauto.
    - eapply map_lt_only_if; eauto.
      + eapply time_join_map; eauto.
      + eapply time_meet_map; eauto.
  Qed.

  Lemma view_le_map vw0 vw1 fvw0 fvw1
        (VIEW0: view_map vw0 fvw0)
        (VIEW1: view_map vw1 fvw1)
        (VIEWLE: View.le vw0 vw1)
    :
      View.le fvw0 fvw1.
  Proof.
    inv VIEWLE. econs; eauto.
    - eapply timemap_le_map.
      + eapply map_pln; eauto.
      + eapply map_pln; eauto.
      + eauto.
    - eapply timemap_le_map.
      + eapply map_rlx; eauto.
      + eapply map_rlx; eauto.
      + eauto.
  Qed.

  Lemma opt_view_le_map vw0 vw1 fvw0 fvw1
        (VIEW0: opt_view_map vw0 fvw0)
        (VIEW1: opt_view_map vw1 fvw1)
        (VIEWLE: View.opt_le vw0 vw1)
    :
      View.opt_le fvw0 fvw1.
  Proof.
    inv VIEWLE.
    - inv VIEW0. econs.
    - inv VIEW0. inv VIEW1. econs.
      eapply view_le_map; eauto.
  Qed.

  Lemma msg_le_map msg0 msg1 fmsg0 fmsg1
        (MSG0: msg_map msg0 fmsg0)
        (MSG1: msg_map msg1 fmsg1)
        (MSGLE: Message.le msg1 msg0)
    :
      Message.le fmsg1 fmsg0.
  Proof.
    inv MSGLE.
    - inv MSG0. inv MSG1. econs; eauto.
      eapply opt_view_le_map; eauto.
    - inv MSG0. econs; eauto.
  Qed.

  Lemma msg_get_promises_map m fm loc to from msg
        (MEM: promises_map m fm)
        (GET: Memory.get loc to m = Some (from, msg))
    :
      exists ffrom fto fmsg,
        (<<NCLPS: non_collapsable loc to>>) /\
        (<<GET: Memory.get loc fto fm = Some (ffrom, fmsg)>>) /\
        (<<FROM: f loc from ffrom>>) /\
        (<<TO: f loc to fto>>) /\
        (<<MSG: msg_map msg fmsg>>) /\
        (<<UNIQUE:
           forall to' (TO: f loc to' fto) frommsg
                  (GET: Memory.get loc to' m = Some frommsg),
             to = to'>>).
  Proof.
    inv MEM.
    exploit MAPPED; eauto. i. des.
    exploit ONLY; eauto. i. des.
    exploit MAPPED; try apply GET1; eauto. i. des.
    hexploit (map_eq TO0 TO1). i. subst.
    destruct (Time.le_lt_dec to to0); [destruct l|].
    - exfalso. exploit NCLPS0; eauto. econs; eauto.
    - destruct H. clarify. esplits; eauto.
      i. destruct frommsg. eapply MAPPED in GET. des.
      destruct (Time.le_lt_dec to to'); [destruct l|]; auto.
      + exfalso. exploit NCLPS1; eauto. econs; eauto.
      + exfalso. exploit NCLPS; eauto. econs; eauto.
    - exfalso. exploit NCLPS; eauto. econs; eauto.
  Qed.

  Lemma add_promises_map0 mem0 fmem0 loc from ffrom to fto msg fmsg mem1 fmem1
        (ADD0: Memory.add mem0 loc from to msg mem1)
        (PROMS: promises_map mem0 fmem0)
        (FROM: f loc from ffrom)
        (TO: f loc to fto)
        (NCLPS: non_collapsable loc to)
        (MSG: msg_map msg fmsg)
        (ADD1: Memory.add fmem0 loc ffrom fto fmsg fmem1)
    :
      promises_map mem1 fmem1.
  Proof.
    econs.
    - i. erewrite Memory.add_o in GET; eauto. des_ifs.
      + ss. des; clarify.
        esplits; eauto.
        eapply Memory.add_get0; eauto.
      + eapply msg_get_promises_map in GET; eauto.
        guardH o. des. unguard.
        esplits; eauto.
        eapply Memory.add_get1; eauto.
    - i. erewrite Memory.add_o in GET; eauto. des_ifs.
      + ss. des; clarify. exists to. esplits; eauto.
        eapply Memory.add_get0; eauto.
      + inv PROMS. eapply ONLY in GET; eauto.
        guardH o. des. esplits; eauto.
        eapply Memory.add_get1; eauto.
  Qed.

  Lemma add_promises_map mem0 fmem0 loc from ffrom to fto msg fmsg mem1
        (ADD: Memory.add mem0 loc from to msg mem1)
        (PROMS: promises_map mem0 fmem0)
        (FROM: f loc from ffrom)
        (TO: f loc to fto)
        (NCLPS: non_collapsable loc to)
        (MSG: msg_map msg fmsg)
    :
      exists fmem1,
        (<<PROMS: promises_map mem1 fmem1>>) /\
        (<<ADD: Memory.add fmem0 loc ffrom fto fmsg fmem1>>).
  Proof.
    hexploit add_succeed_wf; eauto. i. des.
    hexploit (@Memory.add_exists fmem0 loc ffrom fto fmsg).
    { i. dup GET2. dup PROMS. inv PROMS. eapply ONLY in GET2; eauto. des.
      eapply disjoint_map; eauto. }
    { erewrite <- map_lt_non_collapsable; eauto. }
    { eapply msg_wf_map; eauto. }
    i. des. esplits; eauto.
    eapply add_promises_map0; eauto.
  Qed.

  Lemma lower_promises_map mem0 fmem0 loc from to msg0 msg1 fmsg1 mem1
        (LOWER: Memory.lower mem0 loc from to msg0 msg1 mem1)
        (MEM: promises_map mem0 fmem0)
        (MSG: msg_map msg1 fmsg1)
    :
      exists ffrom fto fmsg0 fmem1,
        (<<FROM: f loc from ffrom>>) /\
        (<<TO: f loc to fto>>) /\
        (<<MSG: msg_map msg0 fmsg0>>) /\
        (<<MEM: promises_map mem1 fmem1>>) /\
        (<<LOWER: Memory.lower fmem0 loc ffrom fto fmsg0 fmsg1 fmem1>>).
  Proof.
    exploit Memory.lower_get0; eauto. i. des.
    hexploit lower_succeed_wf; eauto. i. des.
    eapply msg_get_promises_map in GET; eauto. des.
    hexploit (@Memory.lower_exists fmem0 loc ffrom fto fmsg fmsg1); eauto.
    { erewrite <- map_lt_non_collapsable; eauto. }
    { eapply msg_wf_map; eauto. }
    { eapply msg_le_map; eauto. }
    i. des. esplits; eauto.
    econs.
    - i. erewrite Memory.lower_o in GET2; eauto. des_ifs.
      + ss. des; clarify.
        esplits; eauto.
        eapply Memory.lower_get0; eauto.
      + eapply msg_get_promises_map in GET2; eauto.
        guardH o. des. unguard.
        exists fto0, ffrom0, fmsg0. esplits; eauto.
        erewrite Memory.lower_o; eauto. des_ifs.
        ss. des; clarify. exfalso. eauto.
    - i. erewrite Memory.lower_o in GET2; eauto. des_ifs.
      + ss. des; clarify.
        esplits; eauto.
      + dup MEM. inv MEM. eapply ONLY in GET2.
        guardH o. des. unguard.
        exists to0, from0, msg.
        esplits; eauto. erewrite Memory.lower_o; eauto.
        des_ifs. ss; des; clarify.
        hexploit (map_eq TO0 TO). i. clarify.
  Qed.

  Lemma split_promises_map mem0 fmem0 loc ts1 ts2 ts3 msg0 msg1 fmsg0 mem1 fts2
        (SPLIT: Memory.split mem0 loc ts1 ts2 ts3 msg0 msg1 mem1)
        (MEM: promises_map mem0 fmem0)
        (TS2: f loc ts2 fts2)
        (MSG: msg_map msg0 fmsg0)
        (NCLPS: non_collapsable loc ts2)
    :
      exists fts1 fts3 fmsg1 fmem1,
        (<<TS1: f loc ts1 fts1>>) /\
        (<<TS3: f loc ts3 fts3>>) /\
        (<<MSG: msg_map msg1 fmsg1>>) /\
        (<<MEM: promises_map mem1 fmem1>>) /\
        (<<SPLIT: Memory.split fmem0 loc fts1 fts2 fts3 fmsg0 fmsg1 fmem1>>).
  Proof.
    exploit Memory.split_get0; eauto. i. des.
    hexploit split_succeed_wf; eauto. i. des.
    eapply msg_get_promises_map in GET3; eauto. des.
    hexploit (@Memory.split_exists fmem0 loc ffrom fts2 fto fmsg0 fmsg); eauto.
    { erewrite <- map_lt_non_collapsable; try apply TS12; eauto. }
    { erewrite <- map_lt_non_collapsable; try apply TS23; eauto. }
    { eapply msg_wf_map; eauto. }
    i. des. esplits; eauto.
    econs.
    - i. erewrite Memory.split_o in GET4; eauto. des_ifs.
      + ss. des; clarify.
        exploit Memory.split_get0; eauto. i. des.
        esplits; eauto.
      + ss. des; clarify.
        exploit Memory.split_get0; eauto. i. des.
        esplits; eauto.
      + eapply msg_get_promises_map in GET4; eauto.
        guardH o. guardH o0. des. unguard.
        exists fto0, ffrom0, fmsg1. esplits; eauto.
        erewrite Memory.split_o; eauto.
        des_ifs; ss; des; clarify.
        * exploit Memory.split_get0; eauto. i. des. clarify.
        * ss. des; clarify.
          hexploit UNIQUE0; try apply TO; eauto.
          i. clarify.
    - i. erewrite Memory.split_o in GET4; eauto. des_ifs.
      + ss. des; clarify.
        esplits; eauto.
      + ss. des; clarify.
        esplits; eauto.
      + dup MEM. inv MEM. eapply ONLY in GET4.
        guardH o. guardH o0. des.
        esplits; eauto.
        erewrite Memory.split_o; eauto.
        unguard. ss. des_ifs; ss; eauto.
        * ss; des; clarify.
        * ss; des; clarify. exfalso.
          hexploit (map_eq TO0 TO). i. clarify.
  Qed.

  Lemma remove_promises_map mem0 fmem0 loc from to msg mem1
        (REMOVE: Memory.remove mem0 loc from to msg mem1)
        (MEM: promises_map mem0 fmem0)
    :
      exists ffrom fto fmsg fmem1,
        (<<TO: f loc to fto>>) /\
        (<<FROM: f loc from ffrom>>) /\
        (<<MSG: msg_map msg fmsg>>) /\
        (<<MEM: promises_map mem1 fmem1>>) /\
        (<<REMOVE: Memory.remove fmem0 loc ffrom fto fmsg fmem1>>).
  Proof.
    exploit Memory.remove_get0; eauto. i. des.
    eapply msg_get_promises_map in GET; eauto. des.
    hexploit (@Memory.remove_exists fmem0 loc ffrom fto fmsg); eauto.
    i. des. esplits; eauto.
    econs.
    - i. erewrite Memory.remove_o in GET1; eauto. des_ifs. ss.
      dup GET1. eapply msg_get_promises_map in GET1; eauto.
      guardH o. des. unguard.
      exists fto0, ffrom0, fmsg0. esplits; eauto.
      erewrite Memory.remove_o; eauto. des_ifs; ss. des; clarify.
      exploit UNIQUE; eauto. i. clarify.
    - i. erewrite Memory.remove_o in GET1; eauto. des_ifs.
      dup MEM. inv MEM. eapply ONLY in GET1.
      guardH o. des.
      esplits; eauto.
      erewrite Memory.remove_o; eauto.
      unguard. ss. des_ifs; ss; eauto.
      des; clarify. exfalso.
      hexploit (map_eq TO0 TO). i. clarify.
  Qed.

  Lemma remove_memory_map mem0 fmem0 loc from to mem1
        fto ffrom
        (REMOVE: Memory.remove mem0 loc from to Message.reserve mem1)
        (TO: f loc to fto)
        (NCLPS: non_collapsable loc to)
        (FROM: f loc from ffrom)
        (SRCGET: Memory.get loc fto fmem0 = Some (ffrom, Message.reserve))
        (MEM: memory_map mem0 fmem0)
    :
      exists fmem1,
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<REMOVE: Memory.remove fmem0 loc ffrom fto Message.reserve fmem1>>).
  Proof.
    exploit Memory.remove_get0; eauto. i. des.
    hexploit (@Memory.remove_exists fmem0 loc ffrom fto Message.reserve); eauto.
    i. des. esplits; eauto.
    econs.
    - i. erewrite Memory.remove_o in GET1; eauto. des_ifs. ss.
      dup GET1. eapply msg_get_map in GET1; eauto.
      guardH o. des;auto. unguard.
      destruct msg; auto. right.
      exists fto0, ffrom0, fmsg', fmsg. esplits; eauto.
      erewrite Memory.remove_o; eauto. des_ifs; ss. des; clarify.
      exfalso. inv MSGLE. inv MSG.
    - i. erewrite Memory.remove_o in GET1; eauto. des_ifs.
      apply or_strengthen in o. ss. des.
      { dup MEM. inv MEM. dup GET1. eapply ONLY in GET1.
        des; auto. left.
        exists to0, from0, fto', ffrom'. splits; auto.
        i. erewrite remove_covered; eauto. }
      apply NNPP in NOT. clarify.
      dup MEM. inv MEM. dup GET1. eapply ONLY in GET1.
      des; auto. left.
      destruct (Time.le_lt_dec to from0).
      { exists to0, from0, fto', ffrom'. splits; auto.
        i. erewrite remove_covered; [|eauto]. splits; auto.
        right. ii. inv ITV. inv H0. ss.
        eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
        { eapply FROM1. }
        etrans; eauto. }
      destruct (Time.le_lt_dec to0 from).
      { exists to0, from0, fto', ffrom'. splits; auto.
        i. erewrite remove_covered; [|eauto]. splits; auto.
        right. ii. inv ITV. inv H0. ss.
        eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
        { eapply FROM2. }
        etrans.
        { eapply TO1. }
        { eauto. } }
      dup GET2. apply memory_get_ts_strong in GET1. des; clarify.
      { exists Time.bot, Time.bot, Time.bot, Time.bot. splits; auto.
        - refl.
        - refl.
        - i. inv ITV. ss. exfalso. eapply Time.lt_strorder.
          eapply TimeFacts.lt_le_lt; eauto. }
      dup SRCGET. apply memory_get_ts_strong in SRCGET0. des; clarify.
      { assert (BOT: to = Time.bot).
        { destruct (Time.le_lt_dec to Time.bot).
          - destruct l1; auto. exfalso. eapply Time.lt_strorder.
            eapply TimeFacts.lt_le_lt.
            + apply H0.
            + apply Time.bot_spec.
          - exfalso. eapply NCLPS; eauto. econs; eauto. }
        clarify. exfalso. eapply Time.lt_strorder.
        eapply TimeFacts.lt_le_lt.
        - eapply l.
        - eapply Time.bot_spec. }
      assert (DISJOINT: Time.le fto ffrom0 \/ Time.le fto0 ffrom).
      { destruct (Time.le_lt_dec fto ffrom0); auto.
        destruct (Time.le_lt_dec fto0 ffrom); auto.
        exfalso. exploit Memory.get_disjoint.
        { eapply GET2. }
        { eapply SRCGET. }
        i. des; clarify.
        revert x0. eapply disjoint_equivalent. splits; auto.
        unfold Time.join, Time.meet. des_ifs. }
      des.
      + exists to0, to, fto', fto. splits; auto.
        i. erewrite remove_covered; [|eauto]. splits; auto.
        * eapply COVERED. inv ITV. econs; ss. etrans; eauto.
        * right. ii. inv ITV. inv H0. ss.
          eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          { eapply FROM1. }
          { eapply TO4. }
      + exists from, from0, ffrom, ffrom'. splits; auto.
        i. erewrite remove_covered; [|eauto]. splits; auto.
        * eapply COVERED. inv ITV. econs; ss. etrans; eauto.
          left. auto.
        * right. ii. inv ITV. inv H0. ss.
          eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          { eapply FROM2. }
          { eapply TO3. }
  Qed.

  Lemma add_memory_map mem0 fmem0 loc from ffrom to fto msg fmsg' fmsg mem1
        (ADD: Memory.add mem0 loc from to msg mem1)
        (MEM: memory_map mem0 fmem0)
        (FROM: f loc from ffrom)
        (TO: f loc to fto)
        (NCLPS: non_collapsable loc to)
        (MSG: msg_map msg fmsg')
        (MSGLE: Message.le fmsg fmsg')
        (MSGWF: Message.wf fmsg)
    :
      exists fmem1,
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<ADD: Memory.add fmem0 loc ffrom fto fmsg fmem1>>).
  Proof.
    hexploit add_succeed_wf; eauto. i. des.
    hexploit (@Memory.add_exists fmem0 loc ffrom fto fmsg).
    { i. dup GET2. dup MEM. inv MEM0. eapply ONLY in GET2. des.
      - hexploit disjoint_map.
        + eapply FROM.
        + eapply TO.
        + eapply FROM0.
        + eapply TO0.
        + ii. eapply COVERED in RHS. inv RHS.
          eapply DISJOINT in GET. eapply GET; eauto.
        + ii. eapply H; eauto. inv RHS. econs; ss.
          * eapply TimeFacts.le_lt_lt; eauto.
          * etrans; eauto.
      - eapply OUT in TO. ii. inv LHS. inv RHS. ss.
        eapply Time.lt_strorder. etrans.
        { eapply TO. }
        eapply TimeFacts.lt_le_lt; eauto. }
    { erewrite <- map_lt_non_collapsable; eauto. }
    { auto. }
    i. des. esplits; eauto.
    econs.
    - i. erewrite Memory.add_o in GET; eauto. des_ifs.
      + ss. des; clarify. right.
        esplits; eauto.
        eapply Memory.add_get0; eauto.
      + eapply msg_get_map in GET; eauto.
        guardH o. des; auto. right. unguard.
        esplits; eauto.
        eapply Memory.add_get1; eauto.
    - i. erewrite Memory.add_o in GET; eauto. des_ifs.
      + ss. des; clarify. left.
        exists to, from, fto, ffrom0. splits; auto.
        * refl.
        * refl.
        * i. econs; eauto.
          eapply Memory.add_get0; eauto.
      + guardH o. inv MEM. eapply ONLY in GET. des; auto.
        left. exists to0, from0, fto', ffrom'. splits; auto.
        i. eapply add_covered; eauto.
  Qed.

  Lemma lower_memory_map mem0 fmem0 loc from to ffrom fto msg0 fmsg0 msg1 fmsg1 fmsg1' mem1
        (LOWER: Memory.lower mem0 loc from to msg0 msg1 mem1)
        (MEM: memory_map mem0 fmem0)
        (SRCGET: Memory.get loc fto fmem0 = Some (ffrom, fmsg0))
        (MSG0: msg_map msg0 fmsg0)
        (MSG1: msg_map msg1 fmsg1')
        (MSGLE: Message.le fmsg1 fmsg1')
        (MSGWF: Message.wf fmsg1)
        (FROM: f loc from ffrom)
        (TO: f loc to fto)
        (NCLPS: non_collapsable loc to)
    :
      exists fmem1,
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<LOWER: Memory.lower fmem0 loc ffrom fto fmsg0 fmsg1 fmem1>>).
  Proof.
    exploit Memory.lower_get0; eauto. i. des.
    hexploit lower_succeed_wf; eauto. i. des.
    hexploit (@Memory.lower_exists fmem0 loc ffrom fto fmsg0 fmsg1); eauto.
    { erewrite <- map_lt_non_collapsable; eauto. }
    { etrans; eauto.
      eapply msg_le_map; eauto. }
    i. des. esplits; eauto.
    econs.
    - i. erewrite Memory.lower_o in GET2; eauto. des_ifs.
      + ss. des; clarify. right.
        esplits; eauto.
        eapply Memory.lower_get0; eauto.
      + eapply msg_get_map in GET2; eauto.
        guardH o. ss. des; auto. right.
        eapply Memory.lower_get1 in GET3; eauto. des.
        exists fto0, ffrom0, fmsg', m'. esplits; eauto.
        etrans; eauto.
    - i. erewrite Memory.lower_o in GET2; eauto. des_ifs.
      + ss. des; clarify. left.
        exists to, from, fto, ffrom0. splits; auto.
        * refl.
        * refl.
        * i. erewrite lower_covered; eauto.
          econs; eauto.
      + guardH o. inv MEM. eapply ONLY in GET2. des; auto.
        left.  exists to0, from0, fto', ffrom'. splits; auto.
        i. erewrite lower_covered; eauto.
  Qed.

  Lemma no_attatch_map prom mem fmem from ffrom loc
        (NBOT: Time.lt Time.bot ffrom)
        (EMPTY: ~ covered loc from mem)
        (MEM: memory_map mem fmem)
        (FROM: f loc from ffrom)
        (UNWRITABLE: collapsable_unwritable prom mem)
        (NOATTATCH: forall to msg (GET: Memory.get loc to mem = Some (from, msg)), False)
    :
      forall to msg (GET: Memory.get loc to fmem = Some (ffrom, msg)), False.
  Proof.
    i. inv MEM. dup GET. eapply ONLY in GET. des.
    - destruct (Time.le_lt_dec to0 from).
      + dup l. eapply map_le in l; eauto.
        dup GET0. eapply memory_get_ts_strong in GET1. des; clarify.
        * eapply Time.lt_strorder; eauto.
        * eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          { apply TS. }
          etrans; eauto.
      + hexploit (@closed_point mem loc from to0); auto.
        { destruct (Time.le_lt_dec from0 from).
          - i. eapply COVERED; eauto. inv ITV. econs; ss.
            eapply TimeFacts.le_lt_lt; eauto.
          - i. destruct (Time.le_lt_dec t from0).
            + exploit UNWRITABLE.
              * exists from, from0. splits.
                { apply NNPP. ii.
                  erewrite <- map_le_iff in TS0; eauto.
                  - eapply Time.lt_strorder.
                    eapply TimeFacts.lt_le_lt; eauto.
                  - ii. symmetry in H0. eauto. }
                { inv ITV. econs; eauto. }
              * i. eapply unwritable_covered; eauto.
            + eapply COVERED; eauto. inv ITV. econs; ss. }
        i. des. destruct TS2.
        { eapply EMPTY. econs; eauto. econs; ss.
          left. auto. }
        { inv H. eauto. }
    - eapply OUT in FROM. eapply Time.lt_strorder; eauto.
  Qed.

  Lemma write_add_map mem0 fmem0 prom0 fprom0 loc from ffrom to fto val released freleased' freleased mem1 prom1
        (MLE: Memory.le fprom0 fmem0)
        (ADD: AMemory.write prom0 mem0 loc from to val released prom1 mem1 Memory.op_kind_add)
        (MEM: memory_map mem0 fmem0)
        (UNWRITABLE: collapsable_unwritable prom0 mem0)
        (PROM: promises_map prom0 fprom0)
        (FROM: f loc from ffrom)
        (TO: f loc to fto)
        (NCLPS: non_collapsable loc to)
        (VIEW: opt_view_map released freleased')
        (VIEWLE: View.opt_le freleased freleased')
        (VIEWWF: View.opt_wf freleased)
    :
      exists fprom1 fmem1,
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<PROM: promises_map prom1 fprom1>>) /\
        (<<ADD: AMemory.write fprom0 fmem0 loc ffrom fto val freleased fprom1 fmem1 Memory.op_kind_add>>).
  Proof.
    inv ADD. inv PROMISE.
    exploit add_memory_map; try apply MEM0; try eassumption.
    { econs. eauto. }
    { econs 1. eauto. }
    { econs; eauto. }
    i. des.
    exploit Memory.add_exists_le.
    { eapply MLE. }
    { eapply ADD. }
    i. des.
    exploit Memory.remove_exists.
    { eapply Memory.add_get0 in x0. des. apply GET0. }
    i. des.
    exploit (@MemoryFacts.MemoryFacts.add_remove_eq fprom0 promises0 mem2); eauto. i. clarify.
    exploit (@MemoryFacts.MemoryFacts.add_remove_eq prom0 promises2 prom1); eauto. i. clarify.
    esplits; eauto. econs; eauto. econs; eauto.
    - inv TS. econs.
      eapply View.unwrap_opt_le in VIEWLE.
      eapply unwrap_map in VIEW.
      eapply map_rlx in VIEW. specialize (VIEW loc).
      eapply map_le in TS0; cycle 1; eauto.
      etrans; eauto. inv VIEWLE. eauto.
    - i. clarify.
  (*   - i. clarify. *)
  (*     assert (TS0: Time.lt Time.bot fto). *)
  (*     { inv ADD. inv ADD0. eapply TimeFacts.le_lt_lt; eauto. *)
  (*       eapply Time.bot_spec. } *)
  (*     exploit no_attatch_map; try apply MEM; eauto. *)
  (*     ii. inv H. eapply add_succeed_wf in MEM0. des. *)
  (*     eapply DISJOINT. *)
  (*     + eapply GET0. *)
  (*     + instantiate (1:=to). econs; ss. refl. *)
  (*     + eauto. *)
  Qed.

  Lemma write_lower_map mem0 fmem0 prom0 fprom0 loc from ffrom to fto val released freleased' freleased msg mem1 prom1
        (MLE: Memory.le fprom0 fmem0)
        (LOWER: AMemory.write prom0 mem0 loc from to val released prom1 mem1 (Memory.op_kind_lower msg))
        (MEM: memory_map mem0 fmem0)
        (PROM: promises_map prom0 fprom0)
        (FROM: f loc from ffrom)
        (TO: f loc to fto)
        (VIEW: opt_view_map released freleased')
        (VIEWLE: View.opt_le freleased freleased')
        (VIEWWF: View.opt_wf freleased)
    :
      exists fmsg fprom1 fmem1,
        (<<MSG: msg_map msg fmsg>>) /\
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<PROM: promises_map prom1 fprom1>>) /\
        (<<LOWER: AMemory.write fprom0 fmem0 loc ffrom fto val freleased fprom1 fmem1 (Memory.op_kind_lower fmsg)>>).
  Proof.
    inv LOWER. inv PROMISE.
    dup PROMISES. eapply Memory.lower_get0 in PROMISES0. des. clarify.
    eapply msg_get_promises_map in GET; eauto. des.

    exploit lower_memory_map.
    { apply MEM0. }
    { apply MEM. }
    { apply MLE. apply GET. }
    { apply MSG. }
    { econs. eapply VIEW. }
    { econs. apply VIEWLE. }
    { econs; eauto. }
    { apply FROM0. }
    { apply TO0. }
    { apply NCLPS. }
    i. des.

    exploit lower_succeed_wf; try eapply LOWER. i. des.
    exploit Memory.lower_exists; try apply GET; eauto. i. des.
    exploit Memory.remove_exists.
    { eapply Memory.lower_get0 in x0. des. eapply GET3. } i. des.
    exploit lower_remove_remove.
    { eapply PROMISES. }
    { eapply REMOVE. } intros REMOVETGT.
    exploit lower_remove_remove.
    { eapply x0. }
    { eapply x1. } intros REMOVESRC.
    exploit remove_promises_map; try apply REMOVETGT; eauto.
    i. des.
    hexploit (map_eq TO1 TO0). i. clarify.
    hexploit (map_eq FROM1 FROM0). i. clarify.
    hexploit (map_eq TO0 TO). i. clarify.
    hexploit (map_eq FROM0 FROM). i. clarify.
    exploit Memory.remove_inj.
    { eapply REMOVESRC. }
    { eapply REMOVE0. } i. clarify.

    inv MSG.
    esplits; cycle 1.
    { eauto. }
    { eauto. }
    { econs; eauto.  econs; eauto. econs.
      inv TS. eapply View.unwrap_opt_le in VIEWLE.
      eapply unwrap_map in VIEW.
      eapply map_rlx in VIEW. specialize (VIEW loc).
      eapply map_le in TS1; cycle 1; eauto.
      etrans; eauto. inv VIEWLE. eauto. }
    { econs; eauto. }
  Qed.

  Lemma split_memory_map mem0 fmem0 loc ts1 ts2 ts3 msg0 msg1 fmsg0 mem1 fts2
        fts1 fts3 fmsg0' fmsg1
        (SPLIT: Memory.split mem0 loc ts1 ts2 ts3 msg0 msg1 mem1)
        (MEM: memory_map mem0 fmem0)
        (SRCGET: Memory.get loc fts3 fmem0 = Some (fts1, fmsg1))
        (TS1: f loc ts1 fts1)
        (TS2: f loc ts2 fts2)
        (TS3: f loc ts3 fts3)
        (MSG: msg_map msg0 fmsg0')
        (MSGLE: Message.le fmsg0 fmsg0')
        (MSGWF: Message.wf fmsg0)
        (NCLPS2: non_collapsable loc ts2)
        (NCLPS3: non_collapsable loc ts3)
    :
      exists fmem1,
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<SPLIT: Memory.split fmem0 loc fts1 fts2 fts3 fmsg0 fmsg1 fmem1>>).
  Proof.
    exploit Memory.split_get0; eauto. i. des.
    hexploit split_succeed_wf; eauto. i. des.
    hexploit (@Memory.split_exists fmem0 loc fts1 fts2 fts3 fmsg0 fmsg1); eauto.
    { erewrite <- map_lt_non_collapsable; try apply TS12; eauto. }
    { erewrite <- map_lt_non_collapsable; try apply TS23; eauto. }
    i. des. esplits; eauto.
    econs.
    - i. erewrite Memory.split_o in GET4; eauto. des_ifs.
      + ss. des; clarify.
        exploit Memory.split_get0; eauto. i. des.
        right. esplits; eauto.
      + guardH o. eapply msg_get_map in GET3; eauto.
        des; auto. right.
        eapply Memory.split_get1 in GET4; eauto. des.
        ss. des; clarify. esplits; eauto.
      + guardH o. guardH o0. eapply msg_get_map in GET4; eauto.
        des; auto. right.
        eapply Memory.split_get1 in GET5; eauto. des.
        ss. esplits; eauto.


    - i. erewrite Memory.split_o in GET4; eauto. des_ifs.
      + ss. des; clarify. left.
        exists ts2, ts1, fts2, ffrom. esplits; eauto.
        * refl.
        * refl.
        * i. econs; cycle 1; eauto.
      + ss. guardH o. des; clarify. left.
        exists ts3, ts2, fts3, ffrom. esplits; eauto.
        * refl.
        * refl.
        * i. econs; cycle 1; eauto.
      + guardH o. guardH o0. inv MEM. eapply ONLY in GET4. des; auto.
        left. exists to, from, fto', ffrom'. splits; auto.
        i. eapply split_covered; eauto.
  Qed.

  Lemma shorten_promises_map mem0 fmem0 loc from from' ffrom ffrom' to fto mem1 msg fmsg fmem1
        (GET0: Memory.get loc to mem0 = Some (from, msg))
        (GET1: Memory.get loc fto fmem0 = Some (ffrom, fmsg))
        (SHORTEN0:
           forall l t,
             Memory.get l t fmem1 =
             if loc_ts_eq_dec (l, t) (loc, fto) then Some (ffrom', fmsg) else Memory.get l t fmem0)
        (SHORTEN1:
           forall l t,
             Memory.get l t mem1 =
             if loc_ts_eq_dec (l, t) (loc, to) then Some (from', msg) else Memory.get l t mem0)
        (MEM: promises_map mem0 fmem0)
        (TO: f loc to fto)
        (FROM': f loc from' ffrom')
    :
      promises_map mem1 fmem1.
  Proof.
    dup GET0. eapply msg_get_promises_map in GET0; eauto. des.
    hexploit (map_eq TO0 TO). i. clarify.
    inv MEM. econs.
    - i. erewrite SHORTEN1 in GET0. des_ifs.
      + ss. des; clarify.
        esplits; cycle 1; eauto.
        erewrite SHORTEN0. des_ifs. ss. des; clarify.
      + guardH o. apply MAPPED in GET0. des.
        esplits; eauto.
        rewrite SHORTEN0. des_ifs; eauto.
        unguard. ss; des; clarify. exfalso.
        destruct (Time.le_lt_dec to0 to).
        { destruct l; clarify.
          erewrite map_lt_non_collapsable in H; eauto.
          eapply Time.lt_strorder; eauto. }
        { erewrite map_lt_non_collapsable in l; eauto.
          eapply Time.lt_strorder; eauto. }
    - i. erewrite SHORTEN0 in GET0. des_ifs.
      + ss. des; clarify. esplits; eauto.
        erewrite SHORTEN1. des_ifs. ss. des; clarify.
      + guardH o. eapply ONLY in GET0. des.
        esplits; eauto. erewrite SHORTEN1; eauto.
        des_ifs; eauto. unguard. ss; des; clarify.
        hexploit (map_eq TO TO1). i. clarify.
  Qed.

  Lemma write_split_map mem0 fmem0 prom0 fprom0 loc from ffrom to fto val released freleased' freleased msg mem1 prom1 ts3
        (MLE: Memory.le fprom0 fmem0)
        (SPLIT: AMemory.write prom0 mem0 loc from to val released prom1 mem1 (Memory.op_kind_split ts3 msg))
        (MEM: memory_map mem0 fmem0)
        (PROM: promises_map prom0 fprom0)
        (FROM: f loc from ffrom)
        (TO: f loc to fto)
        (VIEW: opt_view_map released freleased')
        (VIEWLE: View.opt_le freleased freleased')
        (VIEWWF: View.opt_wf freleased)
        (NCLPS: non_collapsable loc to)
    :
      exists fmsg fts3 fprom1 fmem1,
        (<<MSG: msg_map msg fmsg>>) /\
        (<<SPLIT: memory_map mem1 fmem1>>) /\
        (<<TS3: f loc ts3 fts3>>) /\
        (<<PROM: promises_map prom1 fprom1>>) /\
        (<<LOWER: AMemory.write fprom0 fmem0 loc ffrom fto val freleased fprom1 fmem1 (Memory.op_kind_split fts3 fmsg)>>).
  Proof.
    inv SPLIT. inv PROMISE.
    dup PROMISES. eapply Memory.split_get0 in PROMISES0. des. clarify.
    eapply msg_get_promises_map in GET0; eauto. des.
    hexploit (map_eq FROM0 FROM). i. clarify.
    exploit split_memory_map.
    { apply MEM0. }
    { apply MEM. }
    { apply MLE. apply GET0. }
    { apply FROM. }
    { apply TO. }
    { apply TO0. }
    { econs. apply VIEW. }
    { econs. apply VIEWLE. }
    { econs; eauto. }
    { auto. }
    { auto. }
    i. des.
    exploit split_succeed_wf; try eapply SPLIT. i. des.
    exploit split_remove_exists.
    { apply GET0. }
    { eapply TS12. }
    { eapply TS23. }
    { eapply MSG_WF. }
    i. des.
    exists fmsg, fto0, mem3, fmem1. esplits; eauto.
    - eapply shorten_promises_map; cycle 2.
      + eapply split_remove_shorten; eauto.
      + eapply split_remove_shorten; eauto.
      + eauto.
      + eauto.
      + eauto.
      + eapply Memory.split_get0 in PROMISES. des. eauto.
      + eapply Memory.split_get0 in SPLIT0. des. eauto.
    - econs; eauto. econs; eauto. econs.
      inv TS. eapply View.unwrap_opt_le in VIEWLE.
      eapply unwrap_map in VIEW.
      eapply map_rlx in VIEW. specialize (VIEW loc).
      eapply map_le in TS0; cycle 1; eauto.
      etrans; eauto. inv VIEWLE. eauto.
  Qed.

  Lemma promise_add_map mem0 fmem0 prom0 fprom0 loc from ffrom to fto msg fmsg mem1 prom1
        (MLE: Memory.le fprom0 fmem0)
        (ADD: AMemory.promise prom0 mem0 loc from to msg prom1 mem1 Memory.op_kind_add)
        (MEM: memory_map mem0 fmem0)
        (PROM: promises_map prom0 fprom0)
        (UNWRITABLE: collapsable_unwritable prom0 mem0)
        (FROM: f loc from ffrom)
        (TO: f loc to fto)
        (NCLPS: non_collapsable loc to)
        (MSG: msg_map msg fmsg)
    :
      exists fprom1 fmem1,
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<PROM: promises_map prom1 fprom1>>) /\
        (<<ADD: AMemory.promise fprom0 fmem0 loc ffrom fto fmsg fprom1 fmem1 Memory.op_kind_add>>).
  Proof.
    inv ADD.
    exploit add_memory_map; try apply MEM0; try eassumption.
    { refl. }
    { eapply msg_wf_map; eauto.
      exploit add_succeed_wf; try apply MEM0. i. des. auto. }
    i. des.
    exploit add_promises_map; try apply PROMISES; try eassumption.
    i. des.
    esplits; eauto. econs; eauto.
    - inv TS.
      + inv MSG. econs.
        eapply map_le; eauto. eapply map_rlx. eapply unwrap_map; eauto.
      + inv MSG. econs.
    - i. clarify. inv MSG.
      inv MEM0. exploit RESERVE; eauto. i. des.
      eapply msg_get_map in x; eauto. des; clarify.
      inv MSG. inv MSGLE.
      hexploit (map_eq TO0 FROM). i. clarify.
      esplits; eauto.
    (* - i. clarify. inv MSG. *)
    (*   assert (TS0: Time.lt Time.bot fto). *)
    (*   { inv ADD. inv ADD1. eapply TimeFacts.le_lt_lt; eauto. *)
    (*     eapply Time.bot_spec. } *)
    (*   exploit no_attatch_map; try apply MEM; eauto. *)
    (*   ii. inv H. eapply add_succeed_wf in MEM0. des. *)
    (*   eapply DISJOINT. *)
    (*   + eapply GET0. *)
    (*   + instantiate (1:=to). econs; ss. refl. *)
    (*   + eauto. *)
  Qed.

  Lemma promise_lower_map mem0 fmem0 prom0 fprom0 loc from ffrom to fto msg fmsg mem1 prom1 msg0
        (MLE: Memory.le fprom0 fmem0)
        (LOWER: AMemory.promise prom0 mem0 loc from to msg prom1 mem1 (Memory.op_kind_lower msg0))
        (MEM: memory_map mem0 fmem0)
        (PROM: promises_map prom0 fprom0)
        (FROM: f loc from ffrom)
        (TO: f loc to fto)
        (NCLPS: non_collapsable loc to)
        (MSG: msg_map msg fmsg)
    :
      exists fmsg0 fprom1 fmem1,
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<MSG: msg_map msg0 fmsg0>>) /\
        (<<PROM: promises_map prom1 fprom1>>) /\
        (<<LOWER: AMemory.promise fprom0 fmem0 loc ffrom fto fmsg fprom1 fmem1 (Memory.op_kind_lower fmsg0)>>).
  Proof.
    inv LOWER.
    exploit lower_promises_map; try apply PROMISES; try eassumption.
    i. des.
    exploit lower_succeed_wf; try apply LOWER; eauto. i. des. clarify.
    hexploit (map_eq TO TO0). i. clarify.
    hexploit (map_eq FROM FROM0). i. clarify.
    exploit lower_memory_map; try apply MEM0; try eassumption.
    { eapply MLE. eauto. }
    { refl. }
    i. des. esplits; eauto.
    inv MSG0. inv MSG_LE. inv MSG.
    econs; eauto. econs; eauto.
    inv TS. eapply map_le; eauto. eapply map_rlx. eapply unwrap_map; eauto.
  Qed.

  Lemma promise_split_map mem0 fmem0 prom0 fprom0 loc from ffrom to fto msg fmsg mem1 prom1 ts3 msg0
        (MLE: Memory.le fprom0 fmem0)
        (SPLIT: AMemory.promise prom0 mem0 loc from to msg prom1 mem1 (Memory.op_kind_split ts3 msg0))
        (MEM: memory_map mem0 fmem0)
        (PROM: promises_map prom0 fprom0)
        (FROM: f loc from ffrom)
        (TO: f loc to fto)
        (NCLPS: non_collapsable loc to)
        (MSG: msg_map msg fmsg)
    :
      exists fmsg0 fts3 fprom1 fmem1,
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<TS3: f loc ts3 fts3>>) /\
        (<<MSG: msg_map msg0 fmsg0>>) /\
        (<<PROM: promises_map prom1 fprom1>>) /\
        (<<SPLIT: AMemory.promise fprom0 fmem0 loc ffrom fto fmsg fprom1 fmem1 (Memory.op_kind_split fts3 fmsg0)>>).
  Proof.
    inv SPLIT.
    exploit split_promises_map; try apply PROMISES; try eassumption.
    i. des.
    exploit split_succeed_wf; try apply SPLIT; eauto. i. des. clarify.
    hexploit (map_eq FROM TS1). i. clarify.
    exploit split_memory_map; try apply MEM0; try eassumption.
    { eapply MLE. eauto. }
    { refl. }
    { eapply Memory.split_get0 in PROMISES. des.
      inv PROM. eapply MAPPED in GET0. des. auto. }
    i. des. esplits; eauto. inv MSG. econs; eauto.
    econs. inv TS. eapply map_le; eauto.
    eapply map_rlx. eapply unwrap_map; eauto.
  Qed.

  Lemma promise_cancel_map mem0 fmem0 prom0 fprom0 loc from ffrom to fto msg fmsg mem1 prom1
        (MLE: Memory.le fprom0 fmem0)
        (CANCEL: AMemory.promise prom0 mem0 loc from to msg prom1 mem1 Memory.op_kind_cancel)
        (MEM: memory_map mem0 fmem0)
        (PROM: promises_map prom0 fprom0)
        (FROM: f loc from ffrom)
        (TO: f loc to fto)
        (NCLPS: non_collapsable loc to)
        (MSG: msg_map msg fmsg)
    :
      exists fprom1 fmem1,
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<PROM: promises_map prom1 fprom1>>) /\
        (<<CANCEL: AMemory.promise fprom0 fmem0 loc ffrom fto fmsg fprom1 fmem1 Memory.op_kind_cancel>>).
  Proof.
    inv CANCEL.
    exploit remove_promises_map; try apply PROMISES; try eassumption.
    i. des.
    hexploit (map_eq FROM FROM0). i. clarify.
    hexploit (map_eq TO TO0). i. clarify.
    inv MSG. inv MSG0.
    exploit remove_memory_map; try apply MEM0; try eassumption.
    { eapply MLE. eapply Memory.remove_get0 in REMOVE. des. auto. }
    i. des. esplits; eauto.
  Qed.

  Lemma promise_map mem0 fmem0 prom0 fprom0 loc from ffrom to fto msg fmsg mem1 prom1 kind
        (MLE: Memory.le fprom0 fmem0)
        (PROMISE: AMemory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
        (MEM: memory_map mem0 fmem0)
        (PROM: promises_map prom0 fprom0)
        (UNWRITABLE: collapsable_unwritable prom0 mem0)
        (FROM: f loc from ffrom)
        (TO: f loc to fto)
        (NCLPS: non_collapsable loc to)
        (MSG: msg_map msg fmsg)
    :
      exists fkind fprom1 fmem1,
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<KIND: memory_op_kind_map loc kind fkind>>) /\
        (<<PROM: promises_map prom1 fprom1>>) /\
        (<<PROMISE: AMemory.promise fprom0 fmem0 loc ffrom fto fmsg fprom1 fmem1 fkind>>).
  Proof.
    inv PROMISE.
    - exploit promise_add_map; try apply PROM; eauto. i. des.
      esplits; eauto.
    - exploit promise_split_map; try apply PROM; eauto. i. des.
      esplits; eauto.
    - exploit promise_lower_map; try apply PROM; eauto. i. des.
      esplits; eauto.
    - exploit promise_cancel_map; try apply PROM; try apply MEM; eauto. i. des.
      esplits; eauto.
  Qed.

  Lemma write_map mem0 fmem0 prom0 fprom0 loc from ffrom to fto mem1 prom1 kind
        val released freleased' freleased
        (MLE: Memory.le fprom0 fmem0)
        (WRITE: AMemory.write prom0 mem0 loc from to val released prom1 mem1 kind)
        (MEM: memory_map mem0 fmem0)
        (PROM: promises_map prom0 fprom0)
        (UNWRITABLE: collapsable_unwritable prom0 mem0)
        (FROM: f loc from ffrom)
        (TO: f loc to fto)
        (NCLPS: non_collapsable loc to)
        (RELEASED: opt_view_map released freleased')
        (RELEASEDLE: View.opt_le freleased freleased')
        (RELEASEDWF: View.opt_wf freleased)
    :
      exists fkind fprom1 fmem1,
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<KIND: memory_op_kind_map loc kind fkind>>) /\
        (<<PROM: promises_map prom1 fprom1>>) /\
        (<<WRITE: AMemory.write fprom0 fmem0 loc ffrom fto val freleased fprom1 fmem1 fkind>>).
  Proof.
    destruct kind.
    - exploit write_add_map; try apply WRITE; eauto. i. des.
      esplits; eauto.
    - exploit write_split_map; try apply WRITE; eauto. i. des.
      esplits; eauto.
    - exploit write_lower_map; try apply WRITE; eauto. i. des.
      esplits; eauto.
    - inv WRITE. inv PROMISE. clarify.
  Qed.

  Inductive local_map (lc flc: Local.t): Prop :=
  | local_map_intro
      ftv'
      (TVIEWLE: TView.le (Local.tview flc) ftv')
      (TVIEW: tview_map (Local.tview lc) ftv')
      (* (TVWF: TView.wf ftv') *)
      (PROMISES: promises_map (Local.promises lc) (Local.promises flc))
  .

  Lemma read_step_map lc0 flc0 mem0 fmem0 loc to val released ord lc1
        (LOCAL: local_map lc0 flc0)
        (TVWF: TView.wf (Local.tview flc0))
        (MEM: memory_map mem0 fmem0)
        (READ: Local.read_step lc0 mem0 loc to val released ord lc1)
    :
      exists fto freleased' freleased flc1,
        (<<READ: Local.read_step flc0 fmem0 loc fto val freleased ord flc1>>) /\
        (<<TO: f loc to fto>>) /\
        (<<RELEASED: opt_view_map released freleased'>>) /\
        (<<RELEASEDLE: View.opt_le freleased freleased'>>) /\
        (<<LOCAL: local_map lc1 flc1>>).
  Proof.
    inv LOCAL. inv READ. exploit msg_get_map; eauto. i. des; clarify.
    inv MSG. inv MSGLE.
    eapply readable_map in READABLE; eauto; cycle 1.
    { eapply map_cur; eauto. }
    esplits.
    - econs; eauto. eapply TViewFacts.readable_mon; eauto.
      + inv TVIEWLE. auto.
      + refl.
    - auto.
    - eauto.
    - eauto.
    - econs; ss.
      + eapply read_tview_mon.
        * eapply TVIEWLE.
        * eauto.
        * refl.
      + eapply read_tview_map; eauto.
  Qed.

  Lemma write_released_mon_same_ord
        tview1 tview2 ord loc to sc1 sc2 released1 released2
        (SC: TimeMap.le sc1 sc2)
        (TVIEW: TView.le tview1 tview2)
        (RELEASED: View.opt_le released1 released2)
    :
      View.opt_le
        (TView.write_released tview1 sc1 loc to released1 ord)
        (TView.write_released tview2 sc2 loc to released2 ord).
  Proof.
    unfold TView.write_released.
    dup TVIEW. inv TVIEW. des_ifs. econs.
    eapply view_join_mon; eauto.
    - eapply View.unwrap_opt_le; eauto.
    - exploit write_tview_mon_same_ord; eauto. i.
      inv x0. eauto.
  Qed.

  Lemma write_step_map lc0 flc0 mem0 mem1 fmem0 loc from to val releasedr releasedw ord lc1
        kind ffrom fto freleasedr freleasedr' sc0 sc1 fsc0 fsc0'
        (LOCAL: local_map lc0 flc0)
        (MLE: Memory.le (Local.promises flc0) fmem0)
        (TVWF: TView.wf (Local.tview flc0))
        (MEM: memory_map mem0 fmem0)
        (UNWRITABLE: collapsable_unwritable (Local.promises lc0) mem0)
        (RELEASEDR: opt_view_map releasedr freleasedr')
        (RELEASEDRLE: View.opt_le freleasedr freleasedr')
        (RELEASEDRWF: View.opt_wf freleasedr)
        (FROM: f loc from ffrom)
        (TO: f loc to fto)
        (NCLPS: non_collapsable loc to)
        (SC: timemap_map sc0 fsc0')
        (SCLE: TimeMap.le fsc0 fsc0')
        (WRITE: ALocal.write_step lc0 sc0 mem0 loc from to val releasedr releasedw ord lc1 sc1 mem1 kind)
    :
      exists flc1 fmem1 fsc1' fsc1 freleasedw' freleasedw fkind,
        (<<WRITE: ALocal.write_step flc0 fsc0 fmem0 loc ffrom fto val freleasedr freleasedw ord flc1 fsc1 fmem1 fkind>>) /\
        (<<RELEASEDW: opt_view_map releasedw freleasedw'>>) /\
        (<<RELEASEDWLE: View.opt_le freleasedw freleasedw'>>) /\
        (<<LOCAL: local_map lc1 flc1>>) /\
        (<<SC: timemap_map sc1 fsc1'>>) /\
        (<<SCLE: TimeMap.le fsc1 fsc1'>>) /\
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<KIND: memory_op_kind_map loc kind fkind>>)
  .
  Proof.
    inv LOCAL. inv WRITE.
    exploit write_released_map; eauto. intros RELEASEDW.
    exploit write_released_mon_same_ord.
    { eapply SCLE. }
    { eapply TVIEWLE. }
    { eapply RELEASEDRLE. } intros VIEWLE.
    exploit write_map; try apply VIEWLE; eauto.
    { eapply TViewFacts.write_future0; eauto. }
    i. des.
    esplits; eauto.
    - econs; eauto.
      + eapply TViewFacts.writable_mon.
        * eapply TVIEWLE.
        * eapply SCLE.
        * refl.
        * eapply writable_map; eauto. eapply TVIEW.
      + i. eapply nonsynch_loc_map; eauto.
    - econs; ss.
      + eapply write_tview_mon_same_ord.
        { eapply TVIEWLE. }
        { eapply SCLE. }
      + eapply write_tview_map; eauto.
  Qed.

  Lemma nonsynch_map prom fprom
        (PROMS: promises_map prom fprom)
        (NONSYNCH: Memory.nonsynch prom)
    :
      Memory.nonsynch fprom.
  Proof.
    ii. dup GET.
    inv PROMS. exploit ONLY; eauto. i. des.
    exploit MAPPED; eauto. i. des.
    hexploit (map_eq TO TO0). i. clarify.
    eapply NONSYNCH in GET1. des_ifs.
    - inv MSG. inv MAP. ss.
    - inv MSG.
  Qed.

  Lemma fence_step_map lc0 flc0 sc0 sc1 fsc0' fsc0 ordr ordw lc1
        (LOCAL: local_map lc0 flc0)
        (SC: timemap_map sc0 fsc0')
        (SCLE: TimeMap.le fsc0 fsc0')
        (TVWF: TView.wf (Local.tview flc0))
        (FENCE: Local.fence_step lc0 sc0 ordr ordw lc1 sc1)
    :
      exists flc1 fsc1 fsc1',
        (<<FENCE: Local.fence_step flc0 fsc0 ordr ordw flc1 fsc1>>) /\
        (<<LOCAL: local_map lc1 flc1>>) /\
        (<<SC: timemap_map sc1 fsc1'>>) /\
        (<<SCLE: TimeMap.le fsc1 fsc1'>>)
  .
  Proof.
    inv LOCAL. inv FENCE.
    exploit read_fence_tview_map; eauto. intros READVIEW.
    exploit read_fence_tview_mon_same_ord; eauto. intros READVIEWLE.
    exploit write_fence_tview_map; eauto. intros WRITEVIEW.
    exploit write_fence_tview_mon_same_ord; eauto. intros WRITEVIEWLE.
    esplits.
    - econs; ss. i. eapply nonsynch_map; eauto.
    - econs; eauto.
    - eapply write_fence_sc_map; eauto.
    - eapply write_fence_fc_mon_same_ord; eauto.
  Qed.


  Definition mappable_time loc to :=
    exists fto, (<<MAPPED: f loc to fto>>).

  Definition mappable_memory mem :=
    forall loc to from val released (GET: Memory.get loc to mem = Some (from, Message.full val released)),
      mappable_time loc to.

  Lemma mappable_memory_op mem0 loc from to msg mem1 kind
        (OP: Memory.op mem0 loc from to msg mem1 kind)
        (FROM: mappable_time loc from)
        (TO: mappable_time loc to)
        (MEM: mappable_memory mem0)
    :
      mappable_memory mem1.
  Proof.
    ii. inv OP.
    - erewrite Memory.add_o in GET; eauto. des_ifs; eauto.
      ss. des; clarify.
    - erewrite Memory.split_o in GET; eauto. des_ifs; eauto.
      + ss. des; clarify.
      + ss. des; clarify.
        eapply Memory.split_get0 in SPLIT. des. eauto.
    - erewrite Memory.lower_o in GET; eauto. des_ifs; eauto.
      ss. des; clarify.
    - erewrite Memory.remove_o in GET; eauto. des_ifs; eauto.
  Qed.

  Lemma memory_map_mappable mem fmem
        (MEM: memory_map mem fmem)
    :
      mappable_memory mem.
  Proof.
    inv MEM. ii.
    eapply MAPPED in GET. des; clarify.
    eexists. eauto.
  Qed.

  Lemma mappable_memory_closed_timemap_exists
        tm mem
        (CLOSED: Memory.closed_timemap tm mem)
        (MEM: mappable_memory mem)
    :
      exists ftm, (<<TM: timemap_map tm ftm>>).
  Proof.
    unfold timemap_map.
    exploit (choice (fun loc t => f loc (tm loc) t)).
    - intros loc. specialize (CLOSED loc). des.
      eapply MEM in CLOSED. eauto.
    - i. des. eauto.
  Qed.

  Lemma mappable_memory_closed_view_exists
        vw mem
        (CLOSED: Memory.closed_view vw mem)
        (MEM: mappable_memory mem)
    :
      exists fvw, (<<VW: view_map vw fvw>>).
  Proof.
    inv CLOSED.
    eapply mappable_memory_closed_timemap_exists in PLN; eauto.
    eapply mappable_memory_closed_timemap_exists in RLX; eauto.
    des. exists (View.mk ftm0 ftm). econs; eauto.
  Qed.

  Lemma mappable_memory_closed_opt_view_exists
        vw mem
        (CLOSED: Memory.closed_opt_view vw mem)
        (MEM: mappable_memory mem)
    :
      exists fvw, (<<VW: opt_view_map vw fvw>>).
  Proof.
    inv CLOSED.
    - eapply mappable_memory_closed_view_exists in CLOSED0; eauto.
      des. esplits. econs; eauto.
    - esplits. econs.
  Qed.

  Lemma mappable_memory_closed_msg_exists
        msg mem
        (CLOSED: Memory.closed_message msg mem)
        (MEM: mappable_memory mem)
    :
      exists fmsg, (<<MSG: msg_map msg fmsg>>).
  Proof.
    inv CLOSED.
    - eapply mappable_memory_closed_opt_view_exists in CLOSED0; eauto.
      des. esplits. econs; eauto.
    - esplits. econs.
  Qed.

  Lemma msg_map_exists mem fmem msg
        (MEM: memory_map mem fmem)
        (CLOSED: Memory.closed_message msg mem)
    :
      exists fmsg,
        (<<MSG: msg_map msg fmsg>>) /\
        (<<CLOSED: Memory.closed_message fmsg fmem>>).
  Proof.
    inv CLOSED.
    - exploit opt_view_map_exists; eauto. i. des.
      exists (Message.full val fvw).
      esplits; eauto. econs; eauto.
    - exists Message.reserve.
      esplits; eauto. econs; eauto.
  Qed.

  Lemma closed_message_map mem fmem msg fmsg
        (MEM: memory_map mem fmem)
        (MSG: msg_map msg fmsg)
        (CLOSED: Memory.closed_message msg mem)
    :
      Memory.closed_message fmsg fmem.
  Proof.
    inv CLOSED.
    - inv MSG. econs.
      eapply closed_opt_view_map; eauto.
    - inv MSG. econs.
  Qed.

  Lemma promise_consistent_mon vw0 vw1 prom0 prom1
        (CONSISTENT: Local.promise_consistent (Local.mk vw1 prom1))
        (VIEW: TView.le vw0 vw1)
        (MLE: Memory.le prom0 prom1)
    :
      Local.promise_consistent (Local.mk vw0 prom0).
  Proof.
    ii. eapply MLE in PROMISE. eapply CONSISTENT in PROMISE.
    eapply TimeFacts.le_lt_lt; eauto. inv VIEW. inv CUR. ss.
  Qed.

  Definition mappable_evt (e: ThreadEvent.t) : Prop :=
    match e with
    | ThreadEvent.promise loc from to msg kind =>
      (<<FROM: mappable_time loc from>>) /\
      (<<TO: mappable_time loc to>>)
    | ThreadEvent.write loc from to val released ordw =>
      (<<FROM: mappable_time loc from>>) /\
      (<<TO: mappable_time loc to>>)
    | ThreadEvent.update loc from to valr valw releasedr releasedw ordr ordw =>
      (<<FROM: mappable_time loc from>>) /\
      (<<TO: mappable_time loc to>>)
    | _ => True
    end.

  Lemma step_map
        P lang th0 th1 fth0 st0 st1 lc0 lc1 flc0
        sc0 sc1 fsc0 fsc0' mem0 mem1 fmem0 e
        (MAPPABLE: P <1= mappable_evt)
        (STEP: (@pred_step P lang) e th0 th1)
        (TH_TGT0: th0 = Thread.mk lang st0 lc0 sc0 mem0)
        (TH_TGT1: th1 = Thread.mk lang st1 lc1 sc1 mem1)
        (TH_SRC: fth0 = Thread.mk lang st0 flc0 fsc0 fmem0)
        (LCWF0: Local.wf lc0 mem0)
        (LCWF1: Local.wf flc0 fmem0)
        (CLOSED: Memory.closed fmem0)
        (LOCAL: local_map lc0 flc0)
        (MEM: memory_map mem0 fmem0)
        (UNWRITABLE: collapsable_unwritable (Local.promises lc0) mem0)
        (SC: timemap_map sc0 fsc0')
        (SCLE: TimeMap.le fsc0 fsc0')
    :
      exists flc1 fmem1 fsc1 fsc1' fe,
        (<<EVT: tevent_map fe e>>) /\
        (<<STEP: AThread.step_allpf
                   fe fth0
                   (Thread.mk lang st1 flc1 fsc1 fmem1)>>) /\
        (<<SC: timemap_map sc1 fsc1'>>) /\
        (<<SCLE: TimeMap.le fsc1 fsc1'>>) /\
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<LOCAL: local_map lc1 flc1>>)
  .
  Proof.
    clarify. inv STEP. eapply MAPPABLE in SAT. inv STEP0.
    exploit step_write_not_in; eauto.
    { inv LCWF0. auto. } intros WRITENOTIN. ss.

    eapply write_not_in_mon in WRITENOTIN; cycle 1.
    { apply UNWRITABLE. }
    eapply step_write_not_in_boundary in WRITENOTIN; eauto.

    inv STEP.
    - inv STEP0. ss. inv LOCAL. inv LOCAL0. inv LCWF1. des.
      exploit mappable_memory_closed_msg_exists; eauto.
      { eapply mappable_memory_op.
        - eapply AMemory.promise_op; eauto.
        - eauto.
        - eauto.
        - eapply memory_map_mappable; eauto. }
      i. des. unfold mappable_time in FROM, TO. des.
      exploit promise_map; eauto.
      { ii. unfold collapsed in H. des. des_ifs.
        - destruct kind; ss. exploit UNWRITABLE.
          + exists to', to. unfold collapsed. esplits; eauto.
            instantiate (1:=to). econs; ss. refl.
          + ii. inv x. inv UNCH. inv PROMISE.
            eapply Memory.remove_get0 in MEM0.
            eapply Memory.remove_get0 in PROMISES1. des.
            exploit Memory.get_disjoint.
            { eapply GET2. }
            { eapply GET. } i. des; clarify.
            eapply x0; eauto. econs; ss.
            * eapply Memory.get_ts in GET2. des; clarify.
              exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
              { eapply TLE. }
              { eapply Time.bot_spec. }
            * refl.
        - apply WRITENOTIN.
          exists to', to. esplits; ss; econs; eauto. refl. }
      i. des.
      exists (Local.mk (Local.tview flc0) fprom1). esplits; eauto.
      + econs; eauto.
      + econs; eauto. econs; eauto. econs; eauto. econs; eauto.
        eapply closed_message_map; eauto.
      + ss. econs; eauto.
    - inv LCWF1. inv STEP0. inv LOCAL0; ss.
      + esplits; eauto.
        * econs; eauto.
        * econs; eauto. econs 2; eauto. econs; eauto.
      + exploit read_step_map; eauto. i. des.
        esplits; eauto.
        * econs; eauto.
        * econs; eauto. econs 2; eauto. econs; eauto.
      + unfold mappable_time in SAT. des.
        hexploit write_step_map; try apply LOCAL1; try eassumption.
        { econs. }
        { econs. }
        { econs. }
        { ii. unfold collapsed in H. des. apply WRITENOTIN.
          exists to', to. esplits; ss; econs; eauto. refl. }
        i. des. esplits; eauto.
        * econs; eauto.
        * econs; eauto. econs 2; eauto. econs; eauto.
      + unfold mappable_time in SAT. des.
        hexploit read_step_map; try apply LOCAL1; try eassumption. i. des.
        exploit Local.read_step_future; eauto. i. des.
        hexploit write_step_map; try apply LOCAL2; try eassumption.
        { inv READ. ss. }
        { inv WF2. auto. }
        { inv LOCAL1. auto. }
        { ii. unfold collapsed in H. des. apply WRITENOTIN.
          exists to', tsw. esplits; ss; econs; eauto. refl. }
        i. des. esplits; eauto.
        * econs; eauto.
        * econs; eauto. econs 2; eauto. econs; eauto.
      + hexploit fence_step_map; try apply LOCAL1; try eassumption. i. des.
        esplits; eauto.
        * econs; eauto.
        * econs; eauto. econs 2; eauto. econs; eauto.
      + hexploit fence_step_map; try apply LOCAL1; try eassumption. i. des.
        esplits; eauto.
        * econs; eauto.
        * econs; eauto. econs 2; eauto. econs; eauto.
      + inv LOCAL1. esplits; eauto.
        * econs; eauto.
        * econs; eauto. econs 2; eauto. econs; eauto.
          econs; eauto. econs; eauto. inv LOCAL.
          eapply promise_consistent_mon.
          { eapply promise_consistent_map; eauto. }
          { ss. }
          { refl. }
  Qed.

  Lemma tevent_map_same_machine_event e fe
        (TEVENT: tevent_map e fe)
    :
      same_machine_event e fe.
  Proof.
    inv TEVENT; ss; eauto.
  Qed.

  Lemma steps_map
        P0 P1 lang th0 th1 fth0 st0 st1 lc0 lc1 flc0
        sc0 sc1 fsc0 fsc0' mem0 mem1 fmem0
        (MAPPABLE: P0 <1= mappable_evt)
        (STEP: rtc (tau (@pred_step P0 lang)) th0 th1)
        (TH_TGT0: th0 = Thread.mk lang st0 lc0 sc0 mem0)
        (TH_TGT1: th1 = Thread.mk lang st1 lc1 sc1 mem1)
        (TH_SRC: fth0 = Thread.mk lang st0 flc0 fsc0 fmem0)
        (LCWF0: Local.wf lc0 mem0)
        (LCWF1: Local.wf flc0 fmem0)
        (CLOSED0: Memory.closed fmem0)
        (CLOSED1: Memory.closed mem0)
        (CLOSEDSC0: Memory.closed_timemap fsc0 fmem0)
        (CLOSEDSC1: Memory.closed_timemap sc0 mem0)
        (LOCAL: local_map lc0 flc0)
        (MEM: memory_map mem0 fmem0)
        (UNWRITABLE: collapsable_unwritable (Local.promises lc0) mem0)
        (SC: timemap_map sc0 fsc0')
        (SCLE: TimeMap.le fsc0 fsc0')
        (SHIFT: te_pred_shift P1 P0 tevent_map)
    :
      exists flc1 fmem1 fsc1 fsc1',
        (<<STEP: rtc (tau (@pred_step P1 lang))
                     fth0
                     (Thread.mk lang st1 flc1 fsc1 fmem1)>>) /\
        (<<SC: timemap_map sc1 fsc1'>>) /\
        (<<SCLE: TimeMap.le fsc1 fsc1'>>) /\
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<LOCAL: local_map lc1 flc1>>)
  .
  Proof.
    ginduction STEP; i; ss; clarify.
    - esplits; eauto.
    - inv H. destruct y. exploit step_map; try apply TSTEP; ss; eauto.
      i. des.
      dup TSTEP. inv TSTEP0. inv STEP1.
      exploit AThread.step_future; try apply STEP2; ss. i. des.
      dup STEP0. inv STEP1.
      exploit AThread.step_future; try apply STEP3; ss. i. des.
      exploit IHSTEP; try apply MEM0; eauto.
      { eapply collapsable_unwritable_step in STEP2; eauto. }
      i. des.
      esplits; eauto. econs 2; eauto. econs.
      + econs; eauto.
      + erewrite tevent_map_same_machine_event; eauto.
  Qed.

  Lemma traced_steps_map
        lang (th0 th1 fth0: Thread.t lang) st0 st1 lc0 lc1 flc0
        sc0 sc1 fsc0 fsc0' mem0 mem1 fmem0 tr
        (PRED: List.Forall (fun em => mappable_evt (fst em)) tr)
        (STEPS: traced_step tr th0 th1)
        (TH_TGT0: th0 = Thread.mk lang st0 lc0 sc0 mem0)
        (TH_TGT1: th1 = Thread.mk lang st1 lc1 sc1 mem1)
        (TH_SRC: fth0 = Thread.mk lang st0 flc0 fsc0 fmem0)
        (LCWF0: Local.wf lc0 mem0)
        (LCWF1: Local.wf flc0 fmem0)
        (CLOSED0: Memory.closed fmem0)
        (CLOSED1: Memory.closed mem0)
        (CLOSEDSC0: Memory.closed_timemap fsc0 fmem0)
        (CLOSEDSC1: Memory.closed_timemap sc0 mem0)
        (LOCAL: local_map lc0 flc0)
        (MEM: memory_map mem0 fmem0)
        (UNWRITABLE: collapsable_unwritable (Local.promises lc0) mem0)
        (SC: timemap_map sc0 fsc0')
        (SCLE: TimeMap.le fsc0 fsc0')
    :
      exists ftr flc1 fmem1 fsc1 fsc1',
        (<<STEPS: traced_step ftr fth0 (Thread.mk lang st1 flc1 fsc1 fmem1)>>) /\
        (<<SC: timemap_map sc1 fsc1'>>) /\
        (<<SCLE: TimeMap.le fsc1 fsc1'>>) /\
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<LOCAL: local_map lc1 flc1>>) /\
        (<<TRACE: List.Forall2 (fun em fem => <<EVENT: tevent_map (fst fem) (fst em)>> /\ <<MEM: memory_map (snd em) (snd fem)>>) tr ftr>>)
  .
  Proof.
    ginduction STEPS; i; ss; clarify.
    - esplits; eauto. econs.
    - ss. destruct th1. inv PRED. exploit step_map; ss.
      { instantiate (1:=mappable_evt). ss. }
      { econs; eauto. }
      { eauto. }
      { eapply LCWF1. }
      { eauto. }
      { eauto. }
      { eauto. }
      { eauto. }
      i. des.
      dup HD. inv HD.
      exploit AThread.step_future; try apply STEP0; ss. i. des.
      dup STEP. inv STEP1.
      exploit AThread.step_future; try apply STEP2; ss. i. des.
      exploit IHSTEPS; try apply STEPS; eauto.
      { eapply collapsable_unwritable_step in STEP0; eauto. }
      i. des. esplits; eauto.
      + econs; eauto.
      + econs; eauto.
  Qed.

End MAPPED.
