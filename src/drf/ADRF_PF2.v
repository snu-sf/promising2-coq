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
Require Import AMemory.
Require Import ALocal.
Require Import AThread.
Require Import APredStep.
Require Import ADRF_PF0.
Require Import ADRF_PF1.
Require Import ADRF_PF4.

Set Implicit Arguments.

Lemma forget_event_no_promise e_src e_tgt
      (FORGET: forget_event e_src e_tgt)
  :
    no_promise e_src.
Proof.
  unfold forget_event in *. des_ifs.
Qed.

Lemma forget_event_write_not_in L e_src e_tgt
      (FORGET: forget_event e_src e_tgt)
      (WRITENOTIN: write_not_in L e_tgt)
  :
    write_not_in L e_src.
Proof.
  unfold forget_event in *. des_ifs.
Qed.

Lemma pred_step_pred P lang th0 th1 e
      (STEP: @pred_step P lang e th0 th1)
  :
    P e.
Proof.
  inv STEP; auto.
Qed.


Inductive drf_sim_event: ThreadEvent.t -> ThreadEvent.t -> Prop :=
| drf_sim_event_read
    loc to val released ordr
  :
    drf_sim_event
      (ThreadEvent.read loc to val released ordr)
      (ThreadEvent.read loc to val released ordr)
| drf_sim_event_write
    loc from ffrom to val released ordw
    (FROM: Time.le from ffrom)
  :
    drf_sim_event
      (ThreadEvent.write loc ffrom to val released ordw)
      (ThreadEvent.write loc from to val released ordw)
| drf_sim_event_update
    loc from to valr valw releasedr releasedw ordr ordw
  :
    drf_sim_event
      (ThreadEvent.update loc from to valr valw releasedr releasedw ordr ordw)
      (ThreadEvent.update loc from to valr valw releasedr releasedw ordr ordw)
| drf_sim_event_fence
    or ow
  :
    drf_sim_event
      (ThreadEvent.fence or ow)
      (ThreadEvent.fence or ow)
| drf_sim_event_syscall
    e
  :
    drf_sim_event
      (ThreadEvent.syscall e)
      (ThreadEvent.syscall e)
| drf_sim_event_silent
  :
    drf_sim_event
      (ThreadEvent.silent)
      (ThreadEvent.silent)
| drf_sim_event_failure
  :
    drf_sim_event
      (ThreadEvent.failure)
      (ThreadEvent.failure)
| drf_sim_event_promise
    loc from to msg kind
  :
    drf_sim_event
      (ThreadEvent.silent)
      (ThreadEvent.promise loc from to msg kind)
.

Lemma drf_sim_event_same_machine_event e_src e_tgt
      (EVENT: drf_sim_event e_src e_tgt)
  :
    same_machine_event e_src e_tgt.
Proof.
  inv EVENT; ss.
Qed.

Lemma drf_sim_event_no_promise
      e_src e_tgt
      (EVT: drf_sim_event e_src e_tgt)
  :
    no_promise e_src.
Proof.
  inv EVT; ss.
Qed.

Lemma drf_sim_event_write_not_in L
      e_src e_tgt
      (SAT: write_not_in L e_tgt)
      (EVT: drf_sim_event e_src e_tgt)
  :
    write_not_in L e_src.
Proof.
  inv EVT; ss. i. apply SAT. inv IN. econs; ss.
  eapply TimeFacts.le_lt_lt; eauto.
Qed.

Inductive drf_sim_trace : list ThreadEvent.t -> list ThreadEvent.t -> Prop :=
| drf_sim_trace_nil
  :
    drf_sim_trace [] []
| drf_sim_trace_promise
    tl_src tl_tgt
    hd_tgt
    (TL: drf_sim_trace tl_src tl_tgt)
    (HD: drf_sim_event ThreadEvent.silent hd_tgt)
  :
    drf_sim_trace tl_src (hd_tgt :: tl_tgt)
| drf_sim_trace_cons
    tl_src tl_tgt
    hd_src hd_tgt
    (TL: drf_sim_trace tl_src tl_tgt)
    (HD: drf_sim_event hd_src hd_tgt)
  :
    drf_sim_trace (hd_src :: tl_src) (hd_tgt :: tl_tgt)
.

Lemma drf_sim_trace_in tr_src tr_tgt
      (EVENT: drf_sim_trace tr_src tr_tgt)
      e_src
      (IN: List.In e_src tr_src)
  :
    exists e_tgt,
      (<<IN: List.In e_tgt tr_tgt>>) /\
      (<<EVENT: drf_sim_event e_src e_tgt>>).
Proof.
  ginduction EVENT; ss; i.
  - apply IHEVENT in IN. des. esplits; eauto.
  - des; clarify.
    + esplits; eauto.
    + apply IHEVENT in IN. des. esplits; eauto.
Qed.

Lemma drf_sim_trace_in2 tr_src tr_tgt
      (EVENT: drf_sim_trace tr_src tr_tgt)
      e_tgt
      (IN: List.In e_tgt tr_tgt)
      (NOTPROMISE: ~ drf_sim_event ThreadEvent.silent e_tgt)
  :
    exists e_src,
      (<<IN: List.In e_src tr_src>>) /\
      (<<EVENT: drf_sim_event e_src e_tgt>>).
Proof.
  ginduction EVENT; ss; i.
  - des; clarify. apply IHEVENT in IN; eauto.
  - des; clarify.
    + esplits; eauto.
    + apply IHEVENT in IN; eauto. des. esplits; eauto.
Qed.


Lemma unchangables_not_promises_covered
      prom0 mem0
      (MLE: Memory.le prom0 mem0)
      loc to from msg
      (UNCH: unchangable mem0 prom0 loc to from msg)
  :
    ~ covered loc to prom0.
Proof.
  intros COVERED. inv UNCH. inv COVERED.
  exploit Memory.get_disjoint.
  { eapply GET. }
  { eapply MLE. eapply GET0. }
  i. des; clarify.
  eapply memory_get_ts_strong in GET. des; clarify.
  { inv ITV. ss. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
    - eapply FROM.
    - eapply Time.bot_spec. }
  eapply x0; eauto. econs; ss. refl.
Qed.

Lemma promise_write_not_in_unchangable (L: Loc.t -> Time.t -> Prop)
      prom0 mem0 loc from to msg prom1 mem1 kind
      (MLE: Memory.le prom0 mem0)
      (PROMISE: AMemory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
      (UNCH: forall loc to (SAT: L loc to),
          exists from msg, <<UNCH: unchangable mem0 prom0 loc to from msg>>)
  :
    forall ts (ITV: Interval.mem (from, to) ts), ~ L loc ts.
Proof.
  ii. eapply UNCH in H. des.
  hexploit unchangables_not_promises_covered; eauto. intros NCOVERED.
  inv UNCH0.
  dup GET. eapply memory_get_ts_strong in GET0. des; clarify.
  { inv ITV. ss. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
    - eapply FROM.
    - eapply Time.bot_spec. }
  dup ITV. inv ITV. inv PROMISE.
  - dup PROMISES. apply Memory.add_get0 in PROMISES. des.
    eapply add_succeed_wf in MEM. des. eapply DISJOINT; eauto.
    econs; ss. refl.
  - dup PROMISES. eapply Memory.split_get0 in PROMISES; eauto. des. clarify.
    eapply split_succeed_wf in PROMISES0. des. eapply NCOVERED.
    econs; eauto. econs; ss.
    etrans; eauto. left. auto.
  - dup PROMISES. eapply Memory.lower_get0 in PROMISES; eauto. des. clarify.
    eapply lower_succeed_wf in PROMISES0. des. eapply NCOVERED.
    econs; eauto.
  - dup PROMISES. eapply Memory.remove_get0 in PROMISES; eauto. des. clarify.
    eapply NCOVERED. econs; eauto.
Qed.

Lemma write_write_not_in_unchangable (L: Loc.t -> Time.t -> Prop)
      prom0 mem0 loc from to val released prom1 mem1 kind
      (MLE: Memory.le prom0 mem0)
      (WRITE: AMemory.write prom0 mem0 loc from to val released prom1 mem1 kind)
      (UNCH: forall loc to (SAT: L loc to),
          exists from msg, <<UNCH: unchangable mem0 prom0 loc to from msg>>)
  :
    forall ts (ITV: Interval.mem (from, to) ts), ~ L loc ts.
Proof.
  inv WRITE. eapply promise_write_not_in_unchangable; eauto.
Qed.

Lemma write_not_in_unchangable (L: Loc.t -> Time.t -> Prop) lang(th0 th1: Thread.t lang) e
      (MLE: Memory.le (Local.promises (Thread.local th0)) (Thread.memory th0))
      (STEP: AThread.step_allpf e th0 th1)
      (UNCH: forall loc to (SAT: L loc to),
          exists from msg, <<UNCH: unchangable (Thread.memory th0) (Local.promises (Thread.local th0)) loc to from msg>>)
  :
    write_not_in L e.
Proof.
  inv STEP; inv STEP0.
  - inv STEP. inv LOCAL; ss. des_ifs. ii.
    eapply promise_write_not_in_unchangable in PROMISE; eauto.
  - inv STEP. inv LOCAL; ss.
    + inv LOCAL0. ii. eapply write_write_not_in_unchangable in WRITE; eauto.
    + inv LOCAL1. inv LOCAL2. ii. eapply write_write_not_in_unchangable in WRITE; eauto.
Qed.

Lemma step_lifting_raw
      lang th_src th_tgt th_tgt' st st' v v' prom prom' sc sc'
      mem_src mem_tgt mem_tgt' e_tgt others updates otherspace
      (STEP: AThread.step_allpf e_tgt th_tgt th_tgt')
      (PRED: ((write_not_in otherspace)
                /1\ (no_update_on updates)
                /1\ (no_read_msgs others)
                /1\ (no_read_msgs (promised prom))) e_tgt)
      (OTHERS: forall loc to (SAT: others loc to),
          exists from msg, <<UNCH: unchangable mem_tgt prom loc to from msg>>)
      (TH_SRC: th_src = Thread.mk lang st (Local.mk v Memory.bot) sc mem_src)
      (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem_tgt)
      (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
      (MEM: pf_sim_memory (others \2/ promised prom) mem_src mem_tgt)
      (NOATTATCH: not_attatched updates mem_src)
      (SC: Memory.closed_timemap sc mem_tgt)
      (CLOSED: Memory.closed mem_tgt)
      (LCWF: Local.wf (Local.mk v prom) mem_tgt)
  :
    exists mem_src' e_src,
      (<<STEP: AThread.opt_step
                 e_src th_src
                 (Thread.mk lang st' (Local.mk v' Memory.bot) sc' mem_src')>>) /\
      (<<EVT: drf_sim_event e_src e_tgt>>) /\
      (<<MEM: pf_sim_memory (others \2/ promised prom') mem_src' mem_tgt'>>) /\
      (<<NOATTATCH: not_attatched updates mem_src'>>) /\
      (<<UNCHANGED: unchanged_on otherspace mem_src mem_src'>>).
Proof.
  ss. des.
  assert (PSTEP: pred_step ((write_not_in otherspace)
                              /1\ (write_not_in others)
                              /1\ (no_update_on updates)
                              /1\ (no_read_msgs others)
                              /1\ (no_read_msgs (promised prom))) e_tgt th_tgt th_tgt').
  { econs; eauto. splits; auto.
    eapply write_not_in_unchangable; eauto.
    - inv LCWF. ss.
    - clarify. }
  hexploit (forget_exists (promised prom) mem_tgt); eauto. i. des.
  exploit self_promise_remove; try apply FORGET; try apply PSTEP; eauto.
  { i. ss. des. auto. }
  i. des.

  inv MEM.
  assert (FORGET1: forget_memory others mem_inter mem_src0).
  { eapply forget_compose_middle; eauto. }

  inv STEP0.
  { exists mem_src, ThreadEvent.silent. esplits; eauto.
    - econs 1.
    - unfold forget_event in EVT. des_ifs; econs.
    - econs; eauto. eapply forget_compose; eauto.
    - refl. }

  exploit other_promise_remove; try eapply STEP1; eauto.
  { i. ss. des. splits; auto. }
  i. des.

  exploit shorter_memory_step; try apply STEP0; eauto.
  { ii. erewrite Memory.bot_get in LHS. clarify. }
  i. des.

  exploit no_update_on_step; try apply STEP2; eauto.
  { ii. erewrite Memory.bot_get in LHS. clarify. }
  { i. ss. des. splits; auto. destruct x0; ss. }
  { refl. }
  i. des.

  exists mem_src'2, e_src0. esplits.
  - inv STEP3. econs 2. eapply pred_step_mon; cycle 1; eauto.
  - unfold forget_event in EVT. des_ifs; inv EVT0; econs. auto.
  - econs.
    + eapply forget_compose; eauto.
    + etrans; eauto.
  - eauto.
  - exploit write_not_in_unchanged_on.
    + econs; try apply STEP3.
      instantiate (1:=write_not_in otherspace /1\ no_promise).
      eapply shorter_event_shift; eauto. split.
      * eapply forget_event_write_not_in; eauto.
      * eapply forget_event_no_promise; eauto.
    + i. apply PR.
    + ss.
    + ss.
Qed.

Lemma step_lifting
      lang (th_src th_tgt th_tgt': Thread.t lang)
      e_tgt others updates otherspace
      (STEP: AThread.step_allpf e_tgt th_tgt th_tgt')
      (PRED: ((no_update_on updates)
                /1\ (no_read_msgs others)) e_tgt)
      (FORGET: forget_thread others th_src th_tgt)
      (OTHERS: forall loc to (SAT: others loc to),
          exists from msg, <<UNCH: unchangable (Thread.memory th_tgt) (Local.promises (Thread.local th_tgt)) loc to from msg>>)
      (OTHERSPACE: otherspace <2= unwritable (Thread.memory th_tgt) (Local.promises (Thread.local th_tgt)))
      (CONSISTENT: Local.promise_consistent (Thread.local th_tgt'))
      (NOATTATCH: not_attatched updates (Thread.memory th_src))
      (SC: Memory.closed_timemap (Thread.sc th_tgt) (Thread.memory th_tgt))
      (CLOSED: Memory.closed (Thread.memory th_tgt))
      (LCWF: Local.wf (Thread.local th_tgt) (Thread.memory th_tgt))
  :
    exists th_src' e_src,
      (<<STEP: AThread.opt_step e_src th_src th_src'>>) /\
      (<<FORGET: forget_thread others th_src' th_tgt'>>) /\
      (<<EVT: drf_sim_event e_src e_tgt>>) /\
      (<<NOATTATCH: not_attatched updates (Thread.memory th_src')>>) /\
      (<<UNCHANGED: unchanged_on otherspace (Thread.memory th_src) (Thread.memory th_src')>>).
Proof.
  destruct th_tgt, th_tgt', th_src. destruct local, local0, local1. ss.
  exploit step_lifting_raw; eauto.
  { des. splits; auto.
    - inv STEP. eapply step_write_not_in in STEP0; ss.
      + eapply write_not_in_mon; eauto.
      + inv LCWF. auto.
    - inv STEP. eapply consistent_read_no_self_promise in STEP0; eauto. }
  { inv FORGET. auto. }
  i. des. inv FORGET. esplits; eauto. econs; eauto.
Qed.

Lemma all_steps_traced_step lang
      th0 th1
  :
    rtc (@AThread.all_step lang) th0 th1 <->
    exists tr,
      (<<STEPS: traced_step tr th0 th1>>)
.
Proof.
  split; i.
  - ginduction H; i.
    + exists []. splits; eauto. econs 1.
    + des. inv H. exists ((e, (Thread.memory x))::tr). splits.
      econs; eauto.
  - des. ginduction STEPS; i.
    + refl.
    + econs; eauto. econs; eauto.
Qed.

Lemma traced_step_lifting
      lang (th_src th_tgt th_tgt': Thread.t lang)
      tr_tgt others updates otherspace
      (STEPS: traced_step tr_tgt th_tgt th_tgt')
      (PRED: List.Forall (fun em => ((no_update_on updates)
                                       /1\ (no_read_msgs others)) (fst em)) tr_tgt)
      (FORGET: forget_thread others th_src th_tgt)
      (OTHERS: forall loc to (SAT: others loc to),
          exists from msg, <<UNCH: unchangable (Thread.memory th_tgt) (Local.promises (Thread.local th_tgt)) loc to from msg>>)
      (OTHERSPACE: otherspace <2= unwritable (Thread.memory th_tgt) (Local.promises (Thread.local th_tgt)))
      (CONSISTENT: Local.promise_consistent (Thread.local th_tgt'))
      (NOATTATCH: not_attatched updates (Thread.memory th_src))
      (SC: Memory.closed_timemap (Thread.sc th_tgt) (Thread.memory th_tgt))
      (CLOSED: Memory.closed (Thread.memory th_tgt))
      (LCWF: Local.wf (Thread.local th_tgt) (Thread.memory th_tgt))
  :
    exists th_src' tr_src,
      (<<FORGET: forget_thread others th_src' th_tgt'>>) /\
      (<<STEP: traced_step tr_src th_src th_src'>>) /\
      (<<EVT: drf_sim_trace (List.map fst tr_src) (List.map fst tr_tgt)>>) /\
      (<<NOATTATCH: not_attatched updates (Thread.memory th_src')>>) /\
      (<<UNCHANGED: unchanged_on otherspace (Thread.memory th_src) (Thread.memory th_src')>>).
Proof.
  ginduction STEPS; i.
  - esplits; eauto.
    + econs 1.
    + econs 1.
    + refl.
  - clarify. inv PRED. ss.
    dup HD. inv HD0.
    exploit AThread.step_future; eauto. i. des. ss. clear STEP.

    assert (OTHERS': forall loc to (SAT: others loc to),
               exists from msg, <<UNCH: unchangable (Thread.memory th1) (Local.promises (Thread.local th1)) loc to from msg>>).
    { i. exploit OTHERS; eauto. i. des.
      inv HD. eapply unchangable_increase in STEP; eauto. }

    exploit step_lifting; ss; eauto.
    { hexploit rtc_all_step_promise_consistent.
      { eapply all_steps_traced_step. esplits; eauto. }
      all: auto. }
    i. des.

    exploit IHSTEPS; try eassumption.
    { instantiate (1:=otherspace). i.
      eapply OTHERSPACE in PR. inv HD.
      eapply unwritable_increase in STEP0; eauto. }
    i. des.

    inv STEP.
    + esplits; eauto. econs 2; eauto.
    + esplits; eauto.
      * econs; eauto. econs; eauto.
      * econs 3; eauto.
      * etrans; eauto.
Qed.

Lemma drf_sim_trace_tau tr_src tr_tgt
      (TRACE: drf_sim_trace tr_src tr_tgt)
      (TAU: List.Forall
              (fun em => ThreadEvent.get_machine_event em = MachineEvent.silent) tr_tgt)
  :
    List.Forall
      (fun em => ThreadEvent.get_machine_event em = MachineEvent.silent) tr_src.
Proof.
  ginduction TRACE; i; ss.
  - inv TAU. eauto.
  - inv TAU. econs; eauto. inv HD; eauto.
Qed.

Lemma drf_sim_trace_no_promise tr_src tr_tgt
      (TRACE: drf_sim_trace tr_src tr_tgt)
  :
    List.Forall no_promise tr_src.
Proof.
  ginduction TRACE; i; ss. econs; eauto. inv HD; ss.
Qed.

Lemma pred_steps_traced_step2 P lang
      th0 th1 tr
      (STEPS: traced_step tr th0 th1)
      (EVENTS: List.Forall (fun em => <<SAT: P (fst em)>> /\ <<TAU: ThreadEvent.get_machine_event (fst em) = MachineEvent.silent>>) tr)
  :
    rtc (tau (@pred_step P lang)) th0 th1.
Proof.
  eapply pred_steps_traced_step; eauto.
Qed.

Lemma rtc_tau_step_lifting
      P lang (th_src th_tgt th_tgt': Thread.t lang)
      others updates otherspace
      (STEPS: rtc (tau (@pred_step P lang)) th_tgt th_tgt')
      (PRED: P <1= ((no_update_on updates)
                      /1\ (no_read_msgs others)))
      (FORGET: forget_thread others th_src th_tgt)
      (OTHERS: forall loc to (SAT: others loc to),
          exists from msg, <<UNCH: unchangable (Thread.memory th_tgt) (Local.promises (Thread.local th_tgt)) loc to from msg>>)
      (OTHERSPACE: otherspace <2= unwritable (Thread.memory th_tgt) (Local.promises (Thread.local th_tgt)))
      (CONSISTENT: Local.promise_consistent (Thread.local th_tgt'))
      (NOATTATCH: not_attatched updates (Thread.memory th_src))
      (SC: Memory.closed_timemap (Thread.sc th_tgt) (Thread.memory th_tgt))
      (CLOSED: Memory.closed (Thread.memory th_tgt))
      (LCWF: Local.wf (Thread.local th_tgt) (Thread.memory th_tgt))
  :
    exists th_src',
      (<<FORGET: forget_thread others th_src' th_tgt'>>) /\
      (<<STEP: rtc (tau (@AThread.program_step lang)) th_src th_src'>>) /\
      (<<NOATTATCH: not_attatched updates (Thread.memory th_src')>>) /\
      (<<UNCHANGED: unchanged_on otherspace (Thread.memory th_src) (Thread.memory th_src')>>).
Proof.
  eapply pred_steps_traced_step in STEPS. des.
  hexploit traced_step_lifting; eauto.
  { eapply List.Forall_impl; eauto.
    i. ss. des. eapply PRED in SAT. des. split; auto. }
  i. des.
  esplits; eauto. eapply pred_steps_traced_step2 in STEP.
  - eapply no_promise_program_step_rtc; eauto.
  - eapply List.Forall_forall. i.
    eapply List.in_map in H.
    split.
    + eapply drf_sim_trace_no_promise in EVT.
      eapply List.Forall_forall in EVT; eauto.
    + eapply drf_sim_trace_tau in EVT; eauto.
      * eapply List.Forall_forall in EVT; eauto.
      * eapply List.Forall_forall. i.
        eapply List.in_map_iff in H0. des. clarify.
        eapply List.Forall_forall in EVENTS; eauto. des. auto.
Qed.

Lemma future_max_full_ts mem0 mem1
      (FUTURE: Memory.future mem0 mem1)
      loc max0 max1
      (MAX0: Memory.max_full_ts mem0 loc max0)
      (MAX1: Memory.max_full_ts mem1 loc max1)
  :
    Time.le max0 max1.
Proof.
  inv MAX0. des.
  eapply Memory.future_get1 in GET; eauto. des. inv MSG_LE.
  eapply Memory.max_full_ts_spec in GET0; eauto.
  des; eauto.
Qed.

Lemma max_full_ts_exists mem0
      loc to from val released
      (GET: Memory.get loc to mem0 = Some (from, Message.full val released))
  :
    exists max, <<MAX: Memory.max_full_ts mem0 loc max>>.
Proof.
  hexploit (@cell_elements_greatest
              (mem0 loc)
              (fun ts => exists from' val' released',
                   Memory.get loc ts mem0 = Some (from', Message.full val' released'))).
  i. des.
  - exists to0. econs; eauto.
  - exfalso. eapply EMPTY; eauto.
Qed.

Lemma concrete_covered_same prom mem0 mem1
      (FUTURE: Memory.future mem0 mem1)
  :
    concrete_covered prom mem0 <2= concrete_covered prom mem1.
Proof.
  i. inv PR. dup MAX. inv MAX0. des.
  eapply Memory.future_get1 in GET; eauto. des. inv MSG_LE.
  eapply max_full_ts_exists in GET0; eauto. des.
  econs; eauto. etrans; eauto.
  eapply future_max_full_ts; eauto.
Qed.

Definition other_promises (c_tgt: Configuration.t) (tid: Ident.t) :=
  all_promises (Configuration.threads c_tgt) (fun tid' => tid <> tid').

Inductive other_union tid
          (otherlocs: Ident.t -> Loc.t -> Time.t -> Prop)
  : Loc.t -> Time.t -> Prop :=
| other_updates_intro
    loc to tid'
    (NEQ: tid <> tid')
    (OTHERLOCS: otherlocs tid' loc to)
  :
    other_union tid otherlocs loc to
.

Definition other_updates (tid: Ident.t)
           (updates aupdates: Ident.t -> Loc.t -> Time.t -> Prop) :=
  other_union tid updates \2/ other_union tid aupdates.

Definition other_spaces (tid: Ident.t)
           (spaces: Ident.t -> Loc.t -> Time.t -> Prop) :=
  other_union tid spaces.

Lemma race_lemma c tid0 tid1 lang0 lang1 st0 st1 lc0 lc1 th0 th1 e1 e2
      (NEQ: tid0 <> tid1)
      (RACEFREE: pf_racefree APFConfiguration.step c)
      (WF: Configuration.wf c)
      (FIND0: IdentMap.find tid0 (Configuration.threads c) = Some (existT _ lang0 st0, lc0))
      (FIND1: IdentMap.find tid1 (Configuration.threads c) = Some (existT _ lang1 st1, lc1))
      (STEP0: rtc (tau (@AThread.program_step _)) (Thread.mk _ st0 lc0 (Configuration.sc c) (Configuration.memory c)) th0)
      (STEP1: rtc (tau (@AThread.program_step _)) (Thread.mk _ st1 lc1 (Thread.sc th0) (Thread.memory th0)) th1)
      (PROEVT0: can_step _ (Thread.state th0) e1)
      (PROEVT1: can_step _ (Thread.state th1) e2)
      (RACE: __guard__(pf_race_condition e1 e2 \/ pf_race_condition e2 e1))
  :
    False.
Proof.
  eapply rtc_tail in STEP0. des; ss; clarify.
  - eapply rtc_tail in STEP1. des; ss; clarify.
    + inv STEP2. inv STEP3. destruct th0, th1. exploit RACEFREE.
      * econs 2; [|econs 2; [|refl]].
        { econs. econs.
          - eapply FIND0.
          - eapply STEP0.
          - eauto. }
        { econs. econs.
          - ss. erewrite IdentMap.gso.
            + eapply FIND1.
            + eauto.
          - eapply STEP1.
          - eauto. }
      * unguard. des.
        { econs; ss.
          { erewrite IdentMap.gso.
            - erewrite IdentMap.gss. eauto.
            - eauto. }
          { erewrite IdentMap.gss. eauto. }
          { eauto. }
          { eauto. }
          { eauto. }
          { eauto. }
        }
        { econs; ss.
          { erewrite IdentMap.gss. eauto. }
          { erewrite IdentMap.gso.
            - erewrite IdentMap.gss. eauto.
            - eauto. }
          { eauto. }
          { eauto. }
          { eauto. }
          { eauto. }
        }
      * ss.
    + inv STEP2. destruct th0. exploit RACEFREE.
      * econs 2; [|refl]. econs. econs.
        { eapply FIND0. }
        { eapply STEP0. }
        { eauto. }
      * unguard. des.
        { econs; ss.
          { erewrite IdentMap.gss. eauto. }
          { erewrite IdentMap.gso.
            - eapply FIND1.
            - eauto. }
          { eauto. }
          { eauto. }
          { eauto. }
          { eauto. }
        }
        { econs; ss.
          { erewrite IdentMap.gso.
            - eapply FIND1.
            - eauto. }
          { erewrite IdentMap.gss. eauto. }
          { eauto. }
          { eauto. }
          { eauto. }
          { eauto. }
        }
      * ss.
  - eapply rtc_tail in STEP1. des; ss; clarify.
    + inv STEP0. destruct th1. exploit RACEFREE.
      * econs 2; [|refl]. econs. econs.
        { eapply FIND1. }
        { eapply STEP1. }
        { eauto. }
      * unguard. des.
        { econs; ss.
          { erewrite IdentMap.gso.
            - eapply FIND0.
            - eauto. }
          { erewrite IdentMap.gss. eauto. }
          { eauto. }
          { eauto. }
          { eauto. }
          { eauto. }
        }
        { econs; ss.
          { erewrite IdentMap.gss. eauto. }
          { erewrite IdentMap.gso.
            - eapply FIND0.
            - eauto. }
          { eauto. }
          { eauto. }
          { eauto. }
          { eauto. }
        }
      * ss.
    + exploit RACEFREE.
      * refl.
      * unguard. des.
        { econs.
          { eapply FIND0. }
          { eapply FIND1. }
          { eauto. }
          { eauto. }
          { eauto. }
          { eauto. }
        }
        { econs.
          { eapply FIND1. }
          { eapply FIND0. }
          { eauto. }
          { eauto. }
          { eauto. }
          { eauto. }
        }
      * eauto.
Qed.

Lemma inv_step mem0 mem1 lang (st: Language.state lang)
      lc proms spaces aupdates updates mlast
      (INV: Inv.t mem0 _ st lc proms spaces aupdates updates mlast)
      (FUTURE: Memory.future mem0 mem1)
  :
    Inv.t mem1 _ st lc proms spaces aupdates updates mlast.
Proof.
  inv INV. econs; eauto.
  i. eapply concrete_covered_same; eauto.
Qed.

Lemma forget_config_forget_thread
      c_src c_tgt tid
      (FORGET: forget_config c_src c_tgt)
      lang st_tgt lc_tgt
      (TIDTGT: IdentMap.find tid (Configuration.threads c_tgt) =
               Some (existT _ lang st_tgt, lc_tgt))
  :
    exists st_src lc_src,
      (<<TIDSRC: IdentMap.find tid (Configuration.threads c_src) =
                 Some (existT _ lang st_src, lc_src)>>) /\
      (<<FORGET: forget_thread
                   (other_promises c_tgt tid)
                   (Thread.mk _ st_src lc_src (Configuration.sc c_src) (Configuration.memory c_src))
                   (Thread.mk _ st_tgt lc_tgt (Configuration.sc c_tgt) (Configuration.memory c_tgt))>>).
Proof.
  inv FORGET. specialize (THS tid).
  unfold option_rel in THS. rewrite TIDTGT in *. des_ifs. inv THS.
  esplits; eauto. destruct lc1, lc_tgt. ss. clarify. rewrite SC. econs.
  replace (other_promises c_tgt tid \2/ promised promises0) with
      (all_promises (Configuration.threads c_tgt) (fun _ => True)); auto.
  extensionality loc. extensionality to.
  apply Coq.Logic.PropExtensionality.propositional_extensionality.
  split; i.
  - inv H. destruct (classic (tid = tid0)).
    + right. clarify.
    + left. econs; eauto.
  - des.
    + inv H. econs; eauto.
    + econs; eauto.
Qed.

Lemma sim_pf_other_promise
      c_src0 c_tgt0 tid mlast spaces updates aupdates
      (SIM: sim_pf_minus_one tid mlast spaces updates aupdates c_src0 c_tgt0)
      lang st0 lc0
      (TIDTGT:
         IdentMap.find tid (Configuration.threads c_tgt0) =
         Some (existT _ lang st0, lc0))
      tid' st1 lc1
      (NEQ: tid <> tid')
      (TIDTGT':
         IdentMap.find tid' (Configuration.threads c_tgt0) =
         Some (st1, lc1))
      loc from to msg
      (GET: Memory.get loc to (Local.promises lc1) = Some (from, msg))
  :
    unchangable (Configuration.memory c_tgt0) (Local.promises lc0) loc to from msg.
Proof.
  inv SIM. exploit THREADS; eauto. i.
  inv WFTGT. inv WF. destruct st1 as [lang1 st1].
  exploit THREADS0; try apply TIDTGT'. intros LCWF. inv LCWF.
  dup GET. eapply PROMISES in GET0. esplits. econs; eauto.
  exploit DISJOINT; eauto. intros [].
  destruct (Memory.get loc to (Local.promises lc0)) eqn: GET1; auto.
  destruct p. exfalso.
  eapply Memory.disjoint_get; eauto.
Qed.

Lemma sim_pf_other_promises
      c_src0 c_tgt0 tid mlast spaces updates aupdates
      (SIM: sim_pf_minus_one tid mlast spaces updates aupdates c_src0 c_tgt0)
      lang st0 lc0
      (TIDTGT:
         IdentMap.find tid (Configuration.threads c_tgt0) =
         Some (existT _ lang st0, lc0))
  :
    forall loc to (SAT: other_promises c_tgt0 tid loc to),
    exists from msg,
      (<<UNCH: unchangable (Configuration.memory c_tgt0) (Local.promises lc0) loc to from msg >>).
Proof.
  dup SIM. inv SIM. i. inv SAT. inv PROMISED.
  destruct msg as [from msg]. eapply sim_pf_other_promise in GET; eauto.
Qed.

Lemma sim_pf_not_attatched
      c_src0 c_tgt0 tid mlast spaces updates aupdates
      (SIM: sim_pf_minus_one tid mlast spaces updates aupdates c_src0 c_tgt0)
  :
    not_attatched (other_updates tid updates aupdates) (Configuration.memory c_src0).
Proof.
  inv SIM. ii. inv SAT.
  - inv H. exploit THREADS; eauto. intros [].
    eapply NOATTATCH; eauto.
  - inv H. exploit THREADS; eauto. intros [].
    eapply NOATTATCH; eauto.
Qed.

Lemma configuration_wf_promises_le c tid lang st lc
      (WF: Configuration.wf c)
      (TID: IdentMap.find tid (Configuration.threads c) =
            Some (existT _ lang st, lc))
  :
    Memory.le (Local.promises lc) (Configuration.memory c).
Proof.
  inv WF. inv WF0. exploit THREADS; eauto. intros []. auto.
Qed.

Lemma sim_pf_other_spaces
      c_src0 c_tgt0 tid mlast spaces updates aupdates
      lang st0 lc0
      (TIDTGT:
         IdentMap.find tid (Configuration.threads c_tgt0) =
         Some (existT _ lang st0, lc0))
      (SIM: sim_pf_minus_one tid mlast spaces updates aupdates c_src0 c_tgt0)
  :
    other_spaces tid spaces <2= unwritable (Configuration.memory c_tgt0) (Local.promises lc0).
Proof.
  ii. inv PR. inv SIM. exploit THREADS; eauto. intros [].
  inv FORGET. specialize (THS tid').
  unfold option_rel in THS. des_ifs.
  { inv THS. destruct st. exploit INV; eauto. intros [].
    exploit SPACES; eauto. intros CONCRETE.
    inv CONCRETE. inv COVERED. dup GET.
    dup Heq0. eapply configuration_wf_promises_le in Heq0; eauto.
    eapply Heq0 in GET. econs; eauto. econs; eauto.
    inv WFTGT. inv WF.
    destruct (Memory.get x0 to (Local.promises lc0)) eqn: GET1; auto.
    destruct p. exfalso.
    exploit DISJOINT; try eassumption. intros [].
    eapply Memory.disjoint_get; eauto. }
  { exfalso. exploit INVBOT; eauto. i. des. eapply SPACESBOT; eauto. }
Qed.

Lemma already_updated lang (th0 th1: Thread.t lang) e
      (MLE: Memory.le (Local.promises (Thread.local th0)) (Thread.memory th0))
      (STEP: AThread.step_allpf e th0 th1)
      loc from to msg
      (TS: Time.lt from to)
      (UNCH: unchangable (Thread.memory th0) (Local.promises (Thread.local th0)) loc to from msg)
  :
    (match e with
     | ThreadEvent.update loc0 from0 _ _ _ _ _ _ _ => (loc0, from0) <> (loc, from)
     | _ => True
     end: Prop).
Proof.
  des_ifs. ii. clarify.
  inv STEP. dup STEP0. eapply step_write_not_in in STEP1; auto.
  assert (TSRW: Time.lt from tsw).
  { inv STEP0; inv STEP. ss. inv LOCAL. destruct lc3, lc2.
    eapply write_msg_wf in LOCAL2. des. auto. }
  ss. eapply (STEP1 (Time.meet to tsw)).
  - unfold Time.meet. des_ifs; econs; ss. refl.
  - econs; eauto.
    unfold Time.meet. des_ifs; econs; ss.
    + refl.
    + left. auto.
Qed.

Lemma already_updated_locs lang (th0 th1: Thread.t lang) (L: Loc.t -> Time.t -> Prop) e
      (MLE: Memory.le (Local.promises (Thread.local th0)) (Thread.memory th0))
      (STEP: AThread.step_allpf e th0 th1)
      (UNCH: forall loc from (SAT: L loc from),
          exists to msg,
            (<<TS: Time.lt from to>>) /\
            (<<UNCH: unchangable (Thread.memory th0) (Local.promises (Thread.local th0)) loc to from msg>>))
  :
    no_update_on L e.
Proof.
  unfold no_update_on. des_ifs. ii. eapply UNCH in H. des.
  inv STEP. dup STEP0. eapply step_write_not_in in STEP1; auto.
  assert (TSRW: Time.lt tsr tsw).
  { inv STEP0; inv STEP. ss. inv LOCAL. destruct lc3, lc2.
    eapply write_msg_wf in LOCAL2. des. auto. }
  ss. eapply (STEP1 (Time.meet to tsw)).
  - unfold Time.meet. des_ifs; econs; ss. refl.
  - econs; eauto.
    unfold Time.meet. des_ifs; econs; ss.
    + refl.
    + left. auto.
Qed.


Lemma sim_pf_read_promise_race
      P Q c_src0 c_tgt0 tid mlast spaces updates aupdates
      (SIM: sim_pf_minus_one tid mlast spaces updates aupdates c_src0 c_tgt0)
      lang st0 lc0
      (TIDTGT:
         IdentMap.find tid (Configuration.threads c_tgt0) =
         Some (existT _ lang st0, lc0))
      th0'
      (STEPS0': rtc (tau (@pred_step P lang))
                    (Thread.mk _ st0 lc0 (Configuration.sc c_tgt0) (Configuration.memory c_tgt0))
                    th0')
      e' th1' th2'
      (STEP': AThread.step_allpf e' th0' th1')
      (RACE': ~ ((no_update_on (other_updates tid updates aupdates))
                   /1\ (no_read_msgs (other_promises c_tgt0 tid))) e')
      (STEPS1': rtc (tau (@pred_step Q lang)) th1' th2')
      (CONSISTENT': Local.promise_consistent (Thread.local th2'))
  :
    False.
Proof.
  assert (WF: Configuration.wf c_tgt0).
  { inv SIM. auto. }
  inv WF. inv WF0. exploit THREADS; eauto. intros LOCAL.
  clear DISJOINT THREADS.

  assert (CONSISTENT0: Local.promise_consistent (Thread.local th0')).
  { exploit AThread.rtc_tau_step_future.
    { eapply thread_steps_pred_steps; try apply STEPS0'. } all: ss. i. des.
    dup STEP'. inv STEP'. exploit AThread.step_future; eauto. i. des. clear STEP.
    hexploit rtc_tau_step_promise_consistent.
    { eapply thread_steps_pred_steps; try apply STEPS1'. } all: ss.
    intros CONSISTENT1.
    inv STEP'0. hexploit step_promise_consistent; eauto. }

  assert (exists e th1 th2,
             (<<STEPS: rtc (tau (@pred_step ((no_update_on (other_updates tid updates aupdates))
                                               /1\ (no_read_msgs (other_promises c_tgt0 tid))) lang))
                           (Thread.mk _ st0 lc0 (Configuration.sc c_tgt0) (Configuration.memory c_tgt0))
                           th1>>) /\
             (<<CONSISTENT: Local.promise_consistent (Thread.local th1)>>) /\
             (<<STEP: AThread.step_allpf e th1 th2>>) /\
             (<<RACE: ~ ((no_update_on (other_updates tid updates aupdates))
                           /1\ (no_read_msgs (other_promises c_tgt0 tid))) e>>)).
  { hexploit (@hold_or_not P ((no_update_on (other_updates tid updates aupdates))
                                /1\ (no_read_msgs (other_promises c_tgt0 tid))));
      try apply STEPS0'; eauto.
    i. des.
    - esplits.
      + eapply pred_step_rtc_mon; try apply HOLD. i. ss. des. split; auto.
      + ss.
      + eauto.
      + ss.
    - esplits.
      + eapply pred_step_rtc_mon; try apply STEPS0. i. ss. des. split; auto.
      + exploit AThread.rtc_tau_step_future.
        { eapply thread_steps_pred_steps; try apply STEPS0. } all: ss. i. des.
        dup STEP. inv STEP0. exploit AThread.step_future; eauto. i. des. clear STEP1.
        hexploit rtc_tau_step_promise_consistent.
        { eapply thread_steps_pred_steps; try apply STEPS1. } all: ss.
        intros CONSISTENT1.
        inv STEP. hexploit step_promise_consistent; eauto.
      + eauto.
      + ss. }
  clear th0' STEPS0' e' th1' th2' STEP' RACE' STEPS1' CONSISTENT' CONSISTENT0. des.

  generalize (sim_pf_other_promises SIM). intros OTHERPROMISE.

  dup SIM. inv SIM0.
  exploit forget_config_forget_thread; eauto. i. des.
  hexploit rtc_tau_step_lifting; try eassumption.
  { i. ss. des. split; eauto. }
  { eapply OTHERPROMISE; eauto. }
  { ss. eapply sim_pf_other_spaces; eauto. }
  { eapply sim_pf_not_attatched; eauto. }

  i. des. ss. apply not_and_or in RACE. des.

  - unfold no_update_on in RACE. des_ifs. apply NNPP in RACE.
    inv RACE.

    + inv H. exploit THREADS; eauto. intros [].
      inv FORGET. specialize (THS tid').
      unfold option_rel in THS. des_ifs.
      { inv THS. destruct st as [lang0 st].
        exploit INV; ss. intros [].
        exploit UPDATE.
        { eauto. }
        { etrans; eauto.
          eapply unchanged_on_mon; eauto.
          i. econs; eauto. }
        { eapply not_attatched_mon; eauto. i. des.
          - left. econs; eauto.
          - right. econs; eauto. }
        i. des.
        inv FORGET1. ss. unfold is_updating, is_updating in *. des.
        inv STEP. inv STEP1; inv STEP.
        exploit race_lemma; try eassumption; ss.
        - econs; eauto.
        - right. econs 2; eauto. ss. }
      { exfalso. exploit INVBOT; eauto. i. des. eapply UPDATESBOT; eauto. }

    + inv H. exploit THREADS; eauto. intros [].
      inv FORGET. specialize (THS tid').
      unfold option_rel in THS. des_ifs.
      { inv THS. destruct st as [lang0 st].
        exploit INV; ss. intros [].
        assert (AUALREADY:
                  forall loc from (SAT: (aupdates tid') loc from),
                  exists to msg,
                    (<<TS: Time.lt from to>>) /\
                    (<<UNCH: unchangable (Configuration.memory c_tgt0) (Local.promises lc0) loc to from msg>>)).
        { i. exploit AUPDATES; eauto. i. des.
          esplits; eauto.
          hexploit sim_pf_other_promise; eauto. }
        hexploit already_updated_locs; cycle 1.
        - eapply STEP.
        - instantiate (1:=aupdates tid'). i. eapply AUALREADY in SAT. des.
          eapply unchangable_rtc_increase in STEPS; try eassumption.
          esplits; eauto.
        - ss.
        - eapply steps_promises_le in STEPS; auto. ss.
          inv LOCAL. ss. }
      { exfalso. exploit INVBOT; eauto. i. des. eapply AUPDATESBOT; eauto. }

  - assert (exists loc to from val released,
               (<<OPROMS: other_promises c_tgt0 tid loc to>>) /\
               (<<READING: is_reading _ (Thread.state th1) loc Ordering.seqcst>>) /\
               (<<CONCRETE: Memory.get loc to (Thread.memory th1) = Some (from, Message.full val released)>>)).
    { unfold no_read_msgs in RACE. des_ifs.
      - apply NNPP in RACE. inv STEP. inv STEP1; inv STEP.
        inv LOCAL0. inv LOCAL1.
        esplits; eauto. ss. econs. esplits.
        + econs; eauto.
        + instantiate (1:=ord). destruct ord; ss.
        + ss.
      - apply NNPP in RACE. inv STEP. inv STEP1; inv STEP.
        inv LOCAL0. inv LOCAL1.
        esplits; eauto. ss. econs. esplits.
        + econs; eauto.
        + instantiate (1:=ordr). destruct ordr; ss.
        + ss. } des.

    exploit OTHERPROMISE; [eauto|eauto|]. i. des.
    eapply unchangable_rtc_increase in STEPS; [|eauto].
    inv UNCH. inv STEPS. clarify.

    inv OPROMS. destruct st as [lang0 st].
    exploit forget_config_forget_thread.
    { eauto. }
    { eapply TID1. }
    i. des.
    dup TID1. eapply configuration_wf_promises_le in TID1; auto.
    inv PROMISED. destruct msg as [from0 msg].
    dup GET1. eapply TID1 in GET1; auto. clarify.

    inv SIM. exploit THREADS0; [eauto|]. intros [].
    exploit INV.
    { eapply TIDSRC0. }
    { eapply TID0. }
    intros []. ss.
    clear UPDATE AUPDATE INV INVBOT. exploit PROMS.
    { econs; eauto. }
    { etrans; eauto.
      eapply unchanged_on_mon; eauto.
      i. econs; eauto. }
    { eapply not_attatched_mon; eauto. i. des.
      - left. econs; eauto.
      - right. econs; eauto. }
    i. des.
    inv FORGET1. ss. unfold is_reading, is_writing in *. des.
    exploit race_lemma; try eassumption; ss.
    econs; eauto.
Qed.


Lemma aupates_already_updated_unreserved tid mlast spaces updates aupdates c_src0 c_tgt0
      (SIM: sim_pf_minus_one tid mlast spaces updates aupdates c_src0 c_tgt0)
      lang st0 lc0
      (TIDTGT:
         IdentMap.find tid (Configuration.threads c_tgt0) =
         Some (existT _ lang st0, lc0))
      mem
      (FORGET: forget_memory (latest_other_reserves (Local.promises lc0) (Configuration.memory c_tgt0)) mem (Configuration.memory c_tgt0))
      loc ts
      (AUPDATES: other_union tid aupdates loc ts)
  :
    (exists to msg,
        (<<TS: Time.lt ts to>>) /\
        (<<UNCH: unchangable mem (Local.promises lc0) loc to ts msg>>)) \/
    ((<<LATSEST: Memory.latest_reserve loc (Local.promises lc0) (Configuration.memory c_tgt0)>>) /\
     (<<MAX: Memory.max_full_ts (Configuration.memory c_tgt0) loc ts>>)).
Proof.
  dup SIM. inv SIM. inv WFTGT. inv WF.
  inv AUPDATES. exploit THREADS; eauto. intros [].
  inv FORGET0. specialize (THS tid'). unfold option_rel in THS. des_ifs; cycle 1.
  { exfalso. exploit INVBOT; auto. i. des. eapply AUPDATESBOT; eauto. }
  inv THS. destruct st as [lang' st']. exploit INV; eauto. intros [].
  exploit AUPDATES; eauto. i. des.
  destruct (classic ((latest_other_reserves (Local.promises lc0) (Configuration.memory c_tgt0)) loc to)).
  - right. inv H. unfold Memory.latest_reserve. rewrite NONE. split; auto.
    exploit THREADS0; eauto. intros LCWF. inv LCWF. eapply PROMISES in GET.
    inv MEM. exploit Memory.max_full_ts_exists; eauto.
    instantiate (1:=loc). i. des.
    exploit max_full_ts_max_ts; eauto. i. des; clarify.
    inv x0. des. unfold Memory.get in GET0. rewrite GET0 in *. clarify.
  - left. exploit THREADS0; eauto. intros LCWF. inv LCWF. dup GET. eapply PROMISES in GET.
    inv FORGET. esplits; eauto.
    hexploit sim_pf_other_promise; try eassumption. intros UNCH. inv UNCH.
    econs; eauto. erewrite COMPLETE; eauto.
Qed.



Require Import APFPF.


Lemma sim_pf_step_minus
      c_src0 c_tgt0 c_tgt1 tid e mlast spaces updates aupdates
      (SIM: sim_pf_minus_one tid mlast spaces updates aupdates c_src0 c_tgt0)
      (STEP: Configuration.step e tid c_tgt0 c_tgt1)
  :
    (exists c_src1,
        (<<STEP: APFConfiguration.opt_step e tid c_src0 c_src1>>) /\
        (<<FORGET: forget_config c_src1 c_tgt1>>) /\
        (<<SIM: forall tid' (NEQ: tid <> tid'),
            sim_pf_one tid' (mlast tid') (spaces tid') (updates tid')
                       (aupdates tid') c_src1 c_tgt1>>)) /\
    __guard__((exists lang st_tgt lc_tgt,
                  (<<FIND: IdentMap.find tid (Configuration.threads c_tgt1) = Some (existT _ lang st_tgt, lc_tgt)>>) /\
                  (<<CONSISTENT: pf_consistent_drf (Thread.mk _ st_tgt lc_tgt (Configuration.sc c_tgt1) (Configuration.memory c_tgt1))>>)) \/
              (<<ABORT: e = MachineEvent.failure>>))
.
Proof.
  dup STEP. rename STEP0 into CSTEP. eapply configuration_step_equivalent in STEP. inv STEP; ss.
  eapply thread_steps_athread_steps in STEPS.
  assert (STEP: AThread.step_allpf e0 e2 (Thread.mk _ st3 lc3 sc3 memory3)).
  { eapply thread_step_athread_step. econs; eauto. }
  assert (WF: Configuration.wf c_tgt0).
  { inv SIM. auto. }
  inv WF. inv WF0. exploit THREADS; eauto. intros LOCAL.
  clear DISJOINT THREADS.

  exploit AThread.rtc_tau_step_future; try apply STEPS; ss. i. des.
  exploit Thread.step_future; eauto. i. des. ss. clear STEP0.
  assert (CONSISTENT1: Local.promise_consistent lc3).
  { destruct (classic (e0 = ThreadEvent.failure)).
    - clarify. inv STEP. inv STEP0; inv STEP.
      inv LOCAL0. inv LOCAL1. auto.
    - hexploit CONSISTENT; eauto. intros CONSISTENT2.
      eapply PromiseConsistent.consistent_promise_consistent in CONSISTENT2; eauto. }
  assert (CONSISTENT0: Local.promise_consistent (Thread.local e2)).
  { inv STEP. eapply step_promise_consistent; eauto. }

  split; cycle 1.
  { destruct (classic (e0 = ThreadEvent.failure)).
    - right. clarify.
    - left. rewrite IdentMap.gss. esplits; eauto.
      eapply pf_consistent_pf_consistent_drf; eauto.
      + eapply PFConsistent.consistent_pf_consistent; eauto.
      + inv SIM. eapply memory_reserve_wf_configuration_step in CSTEP; ss. }

  destruct (classic (((no_update_on (other_updates tid updates aupdates))
                        /1\ (no_read_msgs (other_promises c_tgt0 tid))) e0)); cycle 1.
  { exfalso. exploit sim_pf_read_promise_race.
    - eauto.
    - eauto.
    - eapply pred_steps_thread_steps; eauto.
    - eauto.
    - ss.
    - instantiate (2:=fun _ => True). refl.
    - eauto.
    - ss. }

  hexploit (@hold_or_not (fun _ => True) ((no_update_on (other_updates tid updates aupdates))
                                            /1\ (no_read_msgs (other_promises c_tgt0 tid)))).
  { eapply pred_steps_thread_steps. eapply STEPS. }
  i. des; cycle 1.
  { exfalso. exploit sim_pf_read_promise_race.
    - eauto.
    - eauto.
    - eapply STEPS0.
    - eauto.
    - ss.
    - eapply STEPS1.
    - eauto.
    - ss. }

  generalize (sim_pf_other_promises SIM). intros OTHERPROMISE.

  dup SIM. inv SIM0.
  exploit forget_config_forget_thread; eauto. i. des.
  hexploit rtc_tau_step_lifting; try eassumption.
  { i. ss. des. split; eauto. }
  { eapply OTHERPROMISE; eauto. }
  { ss. eapply sim_pf_other_spaces; eauto. }
  { eapply sim_pf_not_attatched; eauto. }
  i. des.

  exploit step_lifting; try eassumption.
  { eauto. }
  { i. eapply OTHERPROMISE in SAT. des.
    hexploit unchangable_rtc_increase.
    - eapply HOLD.
    - eauto.
    - i. esplits; eauto.
    - eauto. }
  { instantiate (1:= other_spaces tid spaces).
    i. eapply sim_pf_other_spaces in SIM; eauto.
    eapply rtc_unwritable_increase; eauto. }
  i. des.

  assert (NEWPROMS: all_promises
                      (IdentMap.add tid (existT _ lang st3, lc3)
                                    (Configuration.threads c_tgt0)) (fun _ => True) =
                    (other_promises c_tgt0 tid \2/ promised (Local.promises lc3))).
  { extensionality loc. extensionality to.
    apply Coq.Logic.PropExtensionality.propositional_extensionality.
    split; i.
    - inv H0. erewrite IdentMap.gsspec in TID1. des_ifs; eauto.
      left. econs; eauto.
    - des.
      + inv H0. econs; eauto. erewrite IdentMap.gso; eauto.
      + econs; eauto. erewrite IdentMap.gss. ss.
  }

  inv STEP1.
  { eapply rtc_tail in STEP0. des.

    { inv STEP1. erewrite <- drf_sim_event_same_machine_event; eauto. ss.
      rewrite <- EVENT. inv FORGET. inv FORGET2. esplits.
      - econs; eauto. econs; eauto.
      - econs; ss.
        + i. repeat erewrite IdentMap.gsspec. des_ifs.
        + rewrite NEWPROMS. auto.
      - i. exploit THREADS; eauto. intros []. econs; ss.
        + etrans; eauto.
          eapply unchanged_on_mon.
          * etrans; eauto.
          * i. econs; eauto.
        + eapply not_attatched_mon; eauto. i. des.
          * left. econs; eauto.
          * right. econs; eauto.
        + i. erewrite IdentMap.gso in TIDTGT, TIDSRC0; auto.
          exploit INV; eauto. i.
          eapply inv_step; eauto.
          eapply Configuration.step_future in CSTEP; eauto. ss. des. auto.
        + i. erewrite IdentMap.gso in TIDSRC0; auto. }

    { clarify. ss.
      erewrite <- drf_sim_event_same_machine_event; eauto. ss.
      inv FORGET. inv FORGET2. exists c_src0. splits.
      - econs.
      - econs; ss.
        + i. erewrite IdentMap.gsspec. des_ifs.
          rewrite TIDSRC. econs; eauto.
        + rewrite NEWPROMS. auto.
      - i. exploit THREADS; eauto. intros []. econs; ss.
        i. erewrite IdentMap.gso in TIDTGT; auto.
        exploit INV; eauto. i.
        eapply inv_step; eauto.
        eapply Configuration.step_future in CSTEP; eauto. ss. des; auto. }
  }


  { dup STEP2. inv STEP2.
    { inv EVT; inv STEP3. }
    erewrite <- drf_sim_event_same_machine_event; eauto.
    inv FORGET. inv FORGET2. esplits.
    - econs; eauto. econs; eauto.
    - econs; ss.
      + i. repeat erewrite IdentMap.gsspec. des_ifs.
      + rewrite NEWPROMS. auto.
    - i. exploit THREADS; eauto. intros []. econs; ss.
      + etrans; eauto.
        eapply unchanged_on_mon.
        * etrans; eauto.
        * i. econs; eauto.
      + eapply not_attatched_mon; eauto. i. des.
        * left. econs; eauto.
        * right. econs; eauto.
      + i. erewrite IdentMap.gso in TIDTGT, TIDSRC0; auto.
        exploit INV; eauto. i.
        eapply inv_step; eauto.
        eapply Configuration.step_future in CSTEP; eauto. ss. des. auto.
      + i. erewrite IdentMap.gso in TIDSRC0; auto. }
Qed.


Lemma sim_pf_other_promise_unreserved
      c_src0 c_tgt0 tid mlast spaces updates aupdates L
      (SIM: sim_pf_minus_one tid mlast spaces updates aupdates c_src0 c_tgt0)
      lang st0 lc0
      (TIDTGT:
         IdentMap.find tid (Configuration.threads c_tgt0) =
         Some (existT _ lang st0, lc0))
      mem
      (FORGET: forget_memory L mem (Configuration.memory c_tgt0))
      tid' st1 lc1
      (NEQ: tid <> tid')
      (TIDTGT':
         IdentMap.find tid' (Configuration.threads c_tgt0) =
         Some (st1, lc1))
      loc from to msg
      (GET: Memory.get loc to (Local.promises lc1) = Some (from, msg))
      (NOT: ~ L loc to)
  :
    unchangable mem (Local.promises lc0) loc to from msg.
Proof.
  inv SIM. exploit THREADS; eauto. i.
  inv WFTGT. inv WF. destruct st1 as [lang1 st1].
  exploit THREADS0; try apply TIDTGT'. intros LCWF. inv LCWF.
  dup GET. eapply PROMISES in GET0.
  inv FORGET. erewrite <- COMPLETE in GET0; auto.
  esplits. econs; eauto.
  exploit DISJOINT; eauto. intros [].
  destruct (Memory.get loc to (Local.promises lc0)) eqn: GET1; auto.
  destruct p. exfalso.
  eapply Memory.disjoint_get; eauto.
Qed.

Lemma sim_pf_other_promises_unreserved
      L c_src0 c_tgt0 tid mlast spaces updates aupdates
      (SIM: sim_pf_minus_one tid mlast spaces updates aupdates c_src0 c_tgt0)
      lang st0 lc0
      (TIDTGT:
         IdentMap.find tid (Configuration.threads c_tgt0) =
         Some (existT _ lang st0, lc0))
      mem
      (FORGET: forget_memory L mem (Configuration.memory c_tgt0))
  :
    forall loc to (SAT: ((other_promises c_tgt0 tid) -2 L) loc to),
    exists from msg,
      (<<UNCH: unchangable mem (Local.promises lc0) loc to from msg >>).
Proof.
  dup SIM. inv SIM. i. des. inv SAT. inv PROMISED.
  destruct msg as [from msg]. eapply sim_pf_other_promise_unreserved in GET; eauto.
Qed.

Lemma forget_memory_equivalent L0 L1 mem0 mem1
      (EQUIV: forall loc to, L0 loc to <-> L1 loc to)
      (FORGET: forget_memory L0 mem0 mem1)
  :
    forget_memory L1 mem0 mem1.
Proof.
  inv FORGET. econs; eauto.
  - ii. eapply COMPLETE; eauto. ii. eapply NPROMS. eapply EQUIV; auto.
  - ii. eapply FORGET0; eauto. eapply EQUIV; auto.
Qed.

Lemma forget_memory_overlap L0 L1 P mem0 mem1 mem2
      (FORGET0: forget_memory P mem1 mem2)
      (EQUIV: forall loc to (NSAT: ~ P loc to), L0 loc to <-> L1 loc to)
      (FORGET1: forget_memory L0 mem0 mem1)
  :
    forget_memory L1 mem0 mem1.
Proof.
  dup FORGET0. dup FORGET1.
  inv FORGET0. inv FORGET1. econs.
  - i. destruct (Memory.get l t mem1) eqn:GET.
    + erewrite <- GET. eapply COMPLETE0.
      ii. eapply NPROMS. apply EQUIV; auto.
      ii. erewrite FORGET in GET; auto. clarify.
    + eapply memory_le_get_none; eauto. eapply forget_memory_le; eauto.
  - i. destruct (Memory.get l t mem1) eqn:GET.
    + eapply FORGET0. eapply EQUIV; auto. ii.
      erewrite FORGET in GET; auto. clarify.
    + eapply memory_le_get_none; eauto. eapply forget_memory_le; eauto.
Qed.

Lemma pf_sim_memory_middle P L mem_src mem_tgt mem_tgt'
      (SIM: pf_sim_memory P mem_src mem_tgt)
      (FORGET: forget_memory L mem_tgt' mem_tgt)
      (LE: L <2= P)
  :
    pf_sim_memory (P -2 L) mem_src mem_tgt'.
Proof.
  inv SIM. econs; eauto.
  eapply forget_compose_middle; eauto.
  eapply forget_memory_equivalent; eauto.
  i. split; i.
  - destruct (classic (L loc to)); auto.
  - des; auto.
Qed.

Lemma latest_other_reserves_promised tid mlast spaces updates aupdates c_src0 c_tgt0
      (SIM: sim_pf_minus_one tid mlast spaces updates aupdates c_src0 c_tgt0)
      lang st0 lc0
      (TIDTGT:
         IdentMap.find tid (Configuration.threads c_tgt0) =
         Some (existT _ lang st0, lc0))
  :
    latest_other_reserves (Local.promises lc0) (Configuration.memory c_tgt0)
    <2= other_promises c_tgt0 tid.
Proof.
  inv SIM. i. inv PR.
  eapply RESERVERTGT in GET. des. econs.
  - eauto.
  - econs; eauto.
  - ii. clarify.
Qed.

Lemma forget_config_forget_thread_unreserved
      c_src c_tgt tid mlast spaces updates aupdates
      (SIM: sim_pf_minus_one tid mlast spaces updates aupdates c_src c_tgt)
      lang st_tgt lc_tgt
      (TIDTGT: IdentMap.find tid (Configuration.threads c_tgt) =
               Some (existT _ lang st_tgt, lc_tgt))
      mem_unreserved
      (MEMORY: forget_memory (latest_other_reserves (Local.promises lc_tgt) (Configuration.memory c_tgt)) mem_unreserved (Configuration.memory c_tgt))
  :
    exists st_src lc_src,
      (<<TIDSRC: IdentMap.find tid (Configuration.threads c_src) =
                 Some (existT _ lang st_src, lc_src)>>) /\
      (<<FORGET: forget_thread
                   ((other_promises c_tgt tid) -2 (latest_other_reserves (Local.promises lc_tgt) (Configuration.memory c_tgt)))
                   (Thread.mk _ st_src lc_src (Configuration.sc c_src) (Configuration.memory c_src))
                   (Thread.mk _ st_tgt lc_tgt (Configuration.sc c_tgt) mem_unreserved)>>).
Proof.
  dup SIM. inv SIM. exploit forget_config_forget_thread; eauto. i. des. inv FORGET0.
  esplits; eauto. econs; eauto.
  exploit pf_sim_memory_middle; eauto.
  - i. left. eapply latest_other_reserves_promised; eauto.
  - i. inv x0. econs; eauto. eapply forget_memory_equivalent; eauto.
    i. ss. split; i; des; auto. split; auto.
    ii. inv H0. inv H. clarify.
Qed.

Lemma sim_pf_other_spaces_unreserved
      c_src0 c_tgt0 tid mlast spaces updates aupdates
      lang st0 lc0
      (TIDTGT:
         IdentMap.find tid (Configuration.threads c_tgt0) =
         Some (existT _ lang st0, lc0))
      (SIM: sim_pf_minus_one tid mlast spaces updates aupdates c_src0 c_tgt0)
      mem_unreserved
      (MEMORY: forget_memory (latest_other_reserves (Local.promises lc0) (Configuration.memory c_tgt0)) mem_unreserved (Configuration.memory c_tgt0))
  :
    other_spaces tid spaces <2= unwritable mem_unreserved (Local.promises lc0).
Proof.
  ii. dup PR. eapply sim_pf_other_spaces in PR; eauto. inv PR. inv UNCH.
  inv MEMORY. erewrite <- COMPLETE in GET.
  - econs; eauto. econs; eauto.
  - ii. inv H. inv PR0. inv SIM. exploit THREADS; eauto. intros [].
    inv FORGET0. specialize (THS tid'). unfold option_rel in THS. des_ifs.
    + inv THS. destruct st as [lang0 st']. exploit INV; ss. intros [].
      ss. eapply SPACES in OTHERLOCS. inv OTHERLOCS.
      clear INVBOT INV SC MEM TVIEW PROMS SPACES AUPDATES PROMS0 UPDATE AUPDATE.
      inv COVERED.
      inv WFTGT. inv MEM. inv WF.
      exploit THREADS0; try eassumption. intros [].
      eapply PROMISES in GET.
      exploit Memory.get_disjoint.
      { eapply GET0. }
      { eapply GET. }
      i. des; clarify.
      * exploit max_full_ts_max_ts; try eassumption.
        i. des; clarify.
        { inv MAX. des. unfold Memory.get in GET. clarify. }
        { inv ITV. inv ITV0. ss.
          eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          - eapply FROM.
          - eauto. }
      * eapply x2; eauto.
    + exfalso. exploit INVBOT; eauto. i. des. eapply SPACESBOT; eauto.
Qed.

Lemma sim_pf_read_promise_race_unreserved
      P Q c_src0 c_tgt0 tid mlast spaces updates aupdates
      (SIM: sim_pf_minus_one tid mlast spaces updates aupdates c_src0 c_tgt0)
      lang st0 lc0 mem_unreserved
      (TIDTGT:
         IdentMap.find tid (Configuration.threads c_tgt0) =
         Some (existT _ lang st0, lc0))
      th0'
      (FORGETMEM: forget_memory (latest_other_reserves (Local.promises lc0) (Configuration.memory c_tgt0)) mem_unreserved (Configuration.memory c_tgt0))
      (STEPS0': rtc (tau (@pred_step P lang))
                    (Thread.mk _ st0 lc0 (Configuration.sc c_tgt0) mem_unreserved)
                    th0')
      e' th1' th2'
      (STEP': AThread.step_allpf e' th0' th1')
      (PREDS': P <1= (no_acq_update_on (fun loc to => Memory.latest_reserve loc (Local.promises lc0) (Configuration.memory c_tgt0) /\ Memory.max_full_ts (Configuration.memory c_tgt0) loc to)))
      (PRED': no_acq_update_on (fun loc to => Memory.latest_reserve loc (Local.promises lc0) (Configuration.memory c_tgt0) /\ Memory.max_full_ts (Configuration.memory c_tgt0) loc to) e')
      (RACE': ~ ((no_update_on (other_updates tid updates aupdates))
                   (* /1\ (no_acq_update_on (other_union tid aupdates)) *)
                   /1\ (no_read_msgs (((other_promises c_tgt0 tid) -2 (latest_other_reserves (Local.promises lc0) (Configuration.memory c_tgt0)))))) e')
      (STEPS1': rtc (tau (@pred_step Q lang)) th1' th2')
      (CONSISTENT': Local.promise_consistent (Thread.local th2'))
  :
    False.
Proof.
  assert (WF: Configuration.wf c_tgt0).
  { inv SIM. auto. }
  inv WF. inv WF0. exploit THREADS; eauto. intros LOCAL.
  clear DISJOINT THREADS.

  assert (CONCRETELE: memory_concrete_le (Configuration.memory c_tgt0) mem_unreserved).
  { eapply forget_latest_other_reserves_concrete_le; eauto. }
  assert (LCWFTGT: Local.wf lc0 mem_unreserved).
  { inv LOCAL. econs; eauto.
    - eapply memory_concrete_le_closed_tview; eauto.
    - eapply forget_latest_other_reserves_promises_le; eauto.
    - eapply memory_concrete_le_reserve_wf; eauto. }
  assert (CLOSEDMEM: Memory.closed mem_unreserved).
  { inv LOCAL. eapply forget_latest_other_reserves_closed; eauto. }
  assert (CLOSEDSC: Memory.closed_timemap (Configuration.sc c_tgt0) mem_unreserved).
  { eapply memory_concrete_le_closed_timemap; eauto. }

  assert (CONSISTENT0: Local.promise_consistent (Thread.local th0')).
  { exploit AThread.rtc_tau_step_future.
    { eapply thread_steps_pred_steps; try apply STEPS0'. } all: ss. i. des.
    dup STEP'. inv STEP'. exploit AThread.step_future; eauto. i. des. clear STEP.
    hexploit rtc_tau_step_promise_consistent.
    { eapply thread_steps_pred_steps; try apply STEPS1'. } all: ss.
    intros CONSISTENT1.
    inv STEP'0. hexploit step_promise_consistent; eauto. }

  assert (exists e th1 th2,
             (<<STEPS: rtc (tau (@pred_step ((no_update_on (other_updates tid updates aupdates))
                                               /1\
                                               (no_acq_update_on (fun loc to => Memory.latest_reserve loc (Local.promises lc0) (Configuration.memory c_tgt0) /\ Memory.max_full_ts (Configuration.memory c_tgt0) loc to))
                                               /1\ (no_read_msgs ((other_promises c_tgt0 tid) -2 (latest_other_reserves (Local.promises lc0) (Configuration.memory c_tgt0))))) lang))
                           (Thread.mk _ st0 lc0 (Configuration.sc c_tgt0) mem_unreserved)
                           th1>>) /\
             (<<CONSISTENT: Local.promise_consistent (Thread.local th1)>>) /\
             (<<STEP: AThread.step_allpf e th1 th2>>) /\
             (<<RACE: ~ ((no_update_on (other_updates tid updates aupdates))
                           /1\ (no_read_msgs ((other_promises c_tgt0 tid) -2 (latest_other_reserves (Local.promises lc0) (Configuration.memory c_tgt0))))) e>>) /\
             (<<NOACQU: no_acq_update_on (fun loc to => Memory.latest_reserve loc (Local.promises lc0) (Configuration.memory c_tgt0) /\ Memory.max_full_ts (Configuration.memory c_tgt0) loc to) e>>)).
  { hexploit (@hold_or_not P ((no_update_on (other_updates tid updates aupdates))
                                /1\ (no_read_msgs ((other_promises c_tgt0 tid) -2 (latest_other_reserves (Local.promises lc0) (Configuration.memory c_tgt0))))));
      try apply STEPS0'; eauto.
    i. des.
    - esplits.
      + eapply pred_step_rtc_mon; try apply HOLD. i. ss. des. splits; auto.
      + ss.
      + eauto.
      + ss.
      + ss.
    - esplits.
      + eapply pred_step_rtc_mon; try apply STEPS0. i. ss. des. split; auto.
      + exploit AThread.rtc_tau_step_future.
        { eapply thread_steps_pred_steps; try apply STEPS0. } all: ss. i. des.
        dup STEP. inv STEP0. exploit AThread.step_future; eauto. i. des. clear STEP1.
        hexploit rtc_tau_step_promise_consistent.
        { eapply thread_steps_pred_steps; try apply STEPS1. } all: ss.
        intros CONSISTENT1.
        inv STEP. hexploit step_promise_consistent; eauto.
      + eauto.
      + eauto.
      + eauto.
  }


  clear th0' STEPS0' e' th1' th2' STEP' PREDS' PRED' RACE' STEPS1' CONSISTENT' CONSISTENT0. des.
  generalize (sim_pf_other_promises_unreserved SIM TIDTGT FORGETMEM).
  intros OTHERPROMISE.

  dup SIM. inv SIM0.
  exploit forget_config_forget_thread_unreserved; eauto. i. des.

  hexploit rtc_tau_step_lifting; try eassumption.
  { i. ss. des. split; eauto. }
  { ss. eapply sim_pf_other_spaces_unreserved; eauto. }
  { eapply sim_pf_not_attatched; eauto. }

  i. des. ss. apply not_and_or in RACE. des.


  - unfold no_update_on in RACE. des_ifs. apply NNPP in RACE.
    inv RACE.

    + inv H. exploit THREADS; eauto. intros [].
      inv FORGET. specialize (THS tid').
      unfold option_rel in THS. des_ifs.
      { inv THS. destruct st as [lang0 st].
        exploit INV; ss. intros [].
        exploit UPDATE.
        { eauto. }
        { etrans; eauto.
          eapply unchanged_on_mon; eauto.
          i. econs; eauto. }
        { eapply not_attatched_mon; eauto. i. des.
          - left. econs; eauto.
          - right. econs; eauto. }
        i. des.
        inv FORGET1. ss. unfold is_updating, is_updating in *. des.
        inv STEP. inv STEP1; inv STEP.
        exploit race_lemma; try eassumption; ss.
        - econs; eauto.
        - right. econs 2; eauto. ss. }
      { exfalso. exploit INVBOT; eauto. i. des. eapply UPDATESBOT; eauto. }

    + hexploit aupates_already_updated_unreserved; try eassumption. i. des.
      * inv H. exploit THREADS; eauto. intros [].
        inv FORGET. specialize (THS tid').
        unfold option_rel in THS. des_ifs.
        { inv THS. destruct st as [lang0 st].
          exploit INV; ss. intros [].
          exploit already_updated; eauto.
          - eapply steps_promises_le in STEPS; auto. ss.
            inv LCWFTGT. ss.
          - eapply unchangable_rtc_increase in STEPS; try eassumption.
        }
        { exfalso. exploit INVBOT; eauto. i. des. eapply AUPDATESBOT; eauto. }


      * inv H. exploit THREADS; eauto. intros [].
        inv FORGET. specialize (THS tid').
        unfold option_rel in THS. des_ifs.
        { inv THS. destruct st as [lang0 st].
          exploit INV; ss. intros [].
          exploit AUPDATE.
          { eauto. }
          { etrans; eauto.
            eapply unchanged_on_mon; eauto.
            i. econs; eauto. }
          { eapply not_attatched_mon; eauto. i. des.
            - left. econs; eauto.
            - right. econs; eauto. }
          i. des.
          inv FORGET1. ss. unfold is_updating, is_updating in *. des.
          inv STEP. inv STEP1; inv STEP.
          exploit race_lemma; try eassumption; ss.
          - econs; eauto.
          - left. econs 2; eauto. ss.
            dup NOACQU. hexploit NOACQU0; eauto.
            intros. destruct ordr; ss; auto. }
        { exfalso. exploit INVBOT; eauto. i. des. eapply AUPDATESBOT; eauto. }

  - assert (exists loc to from val released,
               (<<OPROMS: other_promises c_tgt0 tid loc to>>) /\
               (<<NOTLATEST: ~ latest_other_reserves (Local.promises lc0) (Configuration.memory c_tgt0) loc to>>) /\
               (<<READING: is_reading _ (Thread.state th1) loc Ordering.seqcst>>) /\
               (<<CONCRETE: Memory.get loc to (Thread.memory th1) = Some (from, Message.full val released)>>)).
    { unfold no_read_msgs in RACE. des_ifs.
      - apply NNPP in RACE. des. inv STEP. inv STEP1; inv STEP.
        inv LOCAL0. inv LOCAL1.
        esplits; eauto. ss. econs. esplits.
        + econs; eauto.
        + instantiate (1:=ord). destruct ord; ss.
        + ss.
      - apply NNPP in RACE. des. inv STEP. inv STEP1; inv STEP.
        inv LOCAL0. inv LOCAL1.
        esplits; eauto. ss. econs. esplits.
        + econs; eauto.
        + instantiate (1:=ordr). destruct ordr; ss.
        + ss. } des.

    exploit OTHERPROMISE.
    { split; eauto. } i. des.

    eapply unchangable_rtc_increase in STEPS; [|eauto].
    inv UNCH. inv STEPS. clarify.

    inv OPROMS. destruct st as [lang0 st].
    exploit forget_config_forget_thread.
    { eauto. }
    { eapply TID1. }
    i. des.
    dup TID1. eapply configuration_wf_promises_le in TID1; auto.
    inv PROMISED. destruct msg as [from0 msg].
    dup GET1. eapply TID1 in GET1; auto. clarify.

    inv SIM. exploit THREADS0; [eauto|]. intros [].
    exploit INV.
    { eapply TIDSRC0. }
    { eapply TID0. }
    intros []. ss.
    clear UPDATE AUPDATE INV INVBOT. exploit PROMS.
    { dup GET2. eapply TID1 in GET2. inv FORGETMEM.
      erewrite <- COMPLETE in GET2; eauto. clarify. econs; eauto. }

    { etrans; eauto.
      eapply unchanged_on_mon; eauto.
      i. econs; eauto. }
    { eapply not_attatched_mon; eauto. i. des.
      - left. econs; eauto.
      - right. econs; eauto. }
    i. des.
    inv FORGET1. ss. unfold is_reading, is_writing in *. des.
    exploit race_lemma; try eassumption; ss.
    econs; eauto.
Qed.


Lemma sim_pf_step_minus_full
      c_src0 c_tgt0 c_tgt1 tid e mlast spaces updates aupdates
      (SIM: sim_pf_minus_one tid mlast spaces updates aupdates c_src0 c_tgt0)
      (STEP: Configuration.step e tid c_tgt0 c_tgt1)
  :
    exists c_src1,
      (<<STEP: APFConfiguration.opt_step e tid c_src0 c_src1>>) /\
      (<<SIM: sim_pf_minus_one tid mlast spaces updates aupdates c_src1 c_tgt1>>) /\
      (<<CONSISTENT: __guard__((exists lang st_tgt lc_tgt,
                                   (<<FIND: IdentMap.find tid (Configuration.threads c_tgt1) = Some (existT _ lang st_tgt, lc_tgt)>>) /\
                                   (<<CONSISTENT: pf_consistent_drf (Thread.mk _ st_tgt lc_tgt (Configuration.sc c_tgt1) (Configuration.memory c_tgt1))>>)) \/
                               (<<ABORT: e = MachineEvent.failure>>))>>)
.
Proof.
  exploit sim_pf_step_minus; eauto. i. des. esplits; eauto. inv SIM.
  inv STEP0.
  - econs; eauto.
    + eapply Configuration.step_future; eauto.
    + eapply memory_reserve_wf_configuration_step; eauto.
    + eapply step_reserver_exists_tgt; cycle 1; eauto.
  - econs; eauto.
    + eapply pf_racefree_step; eauto.
    + eapply APFConfiguration.step_future; eauto.
    + eapply Configuration.step_future; eauto.
    + eapply memory_reserve_wf_configuration_step; eauto.
    + eapply step_reserver_exists_tgt; cycle 1; eauto.
    + eapply step_reserver_exists_src; cycle 1; eauto.
Qed.



Definition rlx_write_loc (loc: Loc.t) (e: ThreadEvent.t): Prop :=
  match e with
  | ThreadEvent.write loc0 _ _ _ _ ordw
  | ThreadEvent.update loc0 _ _ _ _ _ _ _ ordw =>
    loc = loc0 /\ Ordering.le ordw Ordering.relaxed
  | _ => False
  end.


Lemma drf_sim_event_shift2 L
      e_src e_tgt
      (SAT: write_not_in L e_tgt)
      (EVT: drf_sim_event e_src e_tgt)
  :
    write_not_in L e_src.
Proof.
  inv EVT; ss. i. apply SAT. inv IN. econs; ss.
  eapply TimeFacts.le_lt_lt; eauto.
Qed.

Lemma drf_sim_event_write_in L
      e_src e_tgt
      (SAT: write_in L e_tgt)
      (EVT: drf_sim_event e_src e_tgt)
  :
    write_in L e_src.
Proof.
  inv EVT; ss. i. apply SAT. inv IN. econs; ss.
  eapply TimeFacts.le_lt_lt; eauto.
Qed.



Definition pf_consistent_drf_src lang (e0:Thread.t lang)
           (spaces: Loc.t -> Time.t -> Prop)
           (promises: Loc.t -> Time.t -> Prop)
           (max: TimeMap.t)
           (U AU: Loc.t -> Prop): Prop :=
  exists (MU: Loc.t -> Prop) e2 tr max',
    (* (<<DISJOINT: forall loc (INU: U loc) (INAU: AU loc), False>>) /\ *)
    (<<STEPS: traced_step tr e0 e2>>) /\
    (<<MAX: TimeMap.le (Memory.max_timemap (Thread.memory e0)) max>>) /\
    (<<SPACES: spaces <2= earlier_times max>>) /\

    (<<TIMEMAP: TimeMap.le max max'>>) /\
    (<<GAP: forall loc (NUPDATES: ~ U loc /\ ~ AU loc /\ ~ MU loc),
        Time.lt (max loc) (max' loc)>>) /\

    (<<TRACE: List.Forall (fun em => (no_sc /1\ no_promise /1\ (fun e => ThreadEvent.get_machine_event e = MachineEvent.silent) /1\ __guard__(write_in (later_times max') \1/ write_in (spaces /2\ earlier_times max))) (fst em)) tr>>) /\

    (<<UPDATESMAX: forall loc (UPDATES: (U \1/ AU) loc), max loc = Memory.max_ts loc (Thread.memory e0)>>) /\

    (<<COMPLETEU:
       forall loc (SAT: U loc),
       exists to from valr valw releasedr releasedw ordr ordw mem,
         <<IN: List.In (ThreadEvent.update loc from to valr valw releasedr releasedw ordr ordw, mem) tr>> /\ <<ORDR: Ordering.le ordr Ordering.strong_relaxed>> >>) /\

    (<<COMPLETEAU:
       forall loc (SAT: AU loc),
       exists to from valr valw releasedr releasedw ordr ordw mem,
         <<IN: List.In (ThreadEvent.update loc from to valr valw releasedr releasedw ordr ordw, mem) tr>> >>) /\

    (<<MYUPDATES: forall loc (SAT: MU loc),
        (<<NOTUPDATES: ~ U loc /\ ~ AU loc>>) /\
        exists to,
          (<<TS0: Time.le (Memory.max_ts loc (Thread.memory e0)) to>>) /\
          (<<TS1: Time.lt to (max loc)>>) /\
          (<<BLANK: Interval.mem (to, (max loc)) <1= spaces loc>>)>>) /\

    (<<COMPLETEW: forall loc to (PROMISED: promises loc to),
        exists e m,
          (<<IN: List.In (e, m) tr>>) /\
          (<<WRITETO: rlx_write_loc loc e>>)>>)
.


Lemma sim_pf_step_pf_consistent
      c_src0 c_tgt0 tid mlast spaces updates aupdates
      (SIM: sim_pf_minus_one tid mlast spaces updates aupdates c_src0 c_tgt0)
      lang st_tgt lc_tgt
      (FIND: IdentMap.find tid (Configuration.threads c_tgt0) = Some (existT _ lang st_tgt, lc_tgt))
      (CONSISTENT: pf_consistent_drf (Thread.mk _ st_tgt lc_tgt (Configuration.sc c_tgt0) (Configuration.memory c_tgt0)))
  :
    (exists st_src lc_src max U AU,
      (<<FIND: IdentMap.find tid (Configuration.threads c_src0) = Some (existT _ lang st_src, lc_src)>>) /\
      (<<MAX: Memory.max_full_timemap (Configuration.memory c_tgt0) max>>) /\
      (<<CONSISTENT: pf_consistent_drf_src
                       (Thread.mk _ st_src lc_src (Configuration.sc c_src0) (Configuration.memory c_src0))
                       (concrete_covered (Local.promises lc_tgt) (Configuration.memory c_tgt0))
                       (concrete_promised (Local.promises lc_tgt))
                       max U AU>>) /\
      (<<AUPDATES: forall loc (SAT: AU loc),
          ~ Memory.latest_reserve loc (Local.promises lc_tgt) (Configuration.memory c_tgt0)>>)) \/
    (exists c_src1,
        (<<STEP: APFConfiguration.step MachineEvent.failure tid c_src0 c_src1>>))
.
Proof.
  assert (WF: Configuration.wf c_tgt0).
  { inv SIM. auto. }
  inv WF. inv WF0. exploit THREADS; eauto. intros LOCAL.
  clear DISJOINT THREADS.

  exploit Memory.max_full_timemap_exists.
  { inv MEM. eauto. } intros [max MAX].

  hexploit (forget_exists
             (latest_other_reserves (Local.promises lc_tgt) (Configuration.memory c_tgt0))
             (Configuration.memory c_tgt0)).
  intros [mem_unreserved FORGETMEM]. red in FORGETMEM.
  exploit CONSISTENT; eauto. i. des. ss.

  generalize (sim_pf_other_promises_unreserved SIM FIND FORGETMEM).
  intros OTHERPROMISE.
  exploit forget_config_forget_thread_unreserved; eauto. i. des.

  assert (CONCRETELE: memory_concrete_le (Configuration.memory c_tgt0) mem_unreserved).
  { eapply forget_latest_other_reserves_concrete_le; eauto. }
  assert (LCWFTGT: Local.wf lc_tgt mem_unreserved).
  { inv LOCAL. econs; eauto.
    - eapply memory_concrete_le_closed_tview; eauto.
    - eapply forget_latest_other_reserves_promises_le; eauto.
    - eapply memory_concrete_le_reserve_wf; eauto. }
  assert (CLOSEDMEM: Memory.closed mem_unreserved).
  { inv LOCAL. eapply forget_latest_other_reserves_closed; eauto. }
  assert (CLOSEDSC: Memory.closed_timemap (Configuration.sc c_tgt0) mem_unreserved).
  { eapply memory_concrete_le_closed_timemap; eauto. }

  assert (CONSISTENT0: Local.promise_consistent (Thread.local e2)).
  { unguard. des.
    - inv LOCAL0. auto.
    - ii. rewrite PROMISES in *. rewrite Memory.bot_get in PROMISE. clarify. }

  assert (NORACE:
            List.Forall
              (fun em =>
                 (no_update_on (other_updates tid updates aupdates) /1\
                               no_read_msgs ((other_promises c_tgt0 tid) -2 (latest_other_reserves (Local.promises lc_tgt) (Configuration.memory c_tgt0))))
                   (fst em)) tr).
  { apply List.Forall_forall. ii. destruct x.
    eapply traced_step_in in H; eauto. des. clarify.
    apply NNPP. ii.
    exploit sim_pf_read_promise_race_unreserved; try eassumption; ss.
    - eapply pred_steps_traced_step2; eauto.
      instantiate (1:=no_acq_update_on (fun loc to => Memory.latest_reserve loc (Local.promises lc_tgt) (Configuration.memory c_tgt0) /\ Memory.max_full_ts (Configuration.memory c_tgt0) loc to)).
      apply List.Forall_forall. i. destruct x.
      eapply List.Forall_forall in TRACE; cycle 1.
      + apply List.in_or_app. left. eauto.
      + ss. des; split; auto.
    - ss.
    - eapply pred_steps_traced_step2; eauto.
      instantiate (1:=fun _ => True).
      apply List.Forall_forall. i. destruct x. split; ss.
      eapply List.Forall_forall in TRACE; cycle 1.
      + apply List.in_or_app. right. ss. right. eauto.
      + ss. des; auto.
  } ss.

  hexploit traced_step_lifting; try eassumption.
  { ss. eapply sim_pf_other_spaces_unreserved; eauto. }
  { eapply sim_pf_not_attatched; eauto. }
  i. des.

  unguard. des.
  { inv FORGET0. ss.
    right. eapply pred_steps_traced_step2 in STEP; cycle 1.
    - instantiate (1:=no_promise).
      apply List.Forall_forall. i. destruct x.
      (* dup EVT. eapply drf_sim_trace_no_promise in EVT. *)
      apply List.in_map with (f := fst) in H. ss.
      eapply drf_sim_trace_in in H; eauto. des.
      eapply List.in_map_iff in IN. des. clarify.
      eapply List.Forall_forall in TRACE; eauto.
      ss. destruct x. ss. des; ss; inv EVENT; ss.
    - esplits.
      replace MachineEvent.failure with
                   (ThreadEvent.get_machine_event ThreadEvent.failure); auto. econs.
      + eauto.
      + eapply no_promise_program_step_rtc. eapply STEP.
      + econs; eauto. econs; eauto. econs. ii.
        rewrite Memory.bot_get in PROMISE. clarify. }

  set (U_src := fun loc => List.In loc U /\ Memory.get loc (max loc) (Configuration.memory c_src0) <> None).
  set (AU_src := fun loc => List.In loc AU /\ Memory.get loc (max loc) (Configuration.memory c_src0) <> None).
  set (MU_src := fun loc => (List.In loc (AU ++ U)) /\ ~ Memory.get loc (max loc) (Configuration.memory c_src0) <> None).

  hexploit sim_pf_max_timemap; eauto. intros MAXLE.

  left. exists st_src, lc_src, max, U_src, AU_src. esplits; eauto.
  { unfold pf_consistent_drf_src.
    exists MU_src, th_src', tr_src, max'. splits; auto.
    - i. inv PR.
      exploit Memory.max_full_ts_inj.
      { eapply MAX0. }
      { eapply MAX. } i. clarify.
    - unfold U_src, AU_src, MU_src. ii. des. apply GAP.
      ii. apply List.in_app_or in H. des.
      + destruct (Memory.get loc (max loc) (Configuration.memory c_src0)) eqn:GET.
        * apply NUPDATES. split; auto. clarify.
        * apply NUPDATES1. split; auto. apply List.in_or_app. auto.
      + destruct (Memory.get loc (max loc) (Configuration.memory c_src0)) eqn:GET.
        * apply NUPDATES0. split; auto. clarify.
        * apply NUPDATES1. split; auto. apply List.in_or_app. auto.
    - apply List.Forall_forall. i. dup H. apply List.in_map with (f := fst) in H.
      eapply drf_sim_trace_in in H; eauto. des.
      eapply List.in_map_iff in IN. des. clarify.
      eapply List.Forall_forall in TRACE; eauto. ss.
      destruct x, x0. ss. des; split.
      + ss. inv EVENT; ss.
      + unguard. left. eapply drf_sim_event_write_in; eauto.
      + ss. inv EVENT; ss.
      + unguard. right. eapply drf_sim_event_write_in; eauto.

    - unfold U_src, AU_src. i. ss. des.
      + apply TimeFacts.antisym.
        * destruct (Memory.get loc (max loc) (Configuration.memory c_src0)) eqn:GET; clarify.
          destruct p. apply Memory.max_ts_spec in GET. des. auto.
        * eapply MAXLE.
      + apply TimeFacts.antisym.
        * destruct (Memory.get loc (max loc) (Configuration.memory c_src0)) eqn:GET; clarify.
          destruct p. apply Memory.max_ts_spec in GET. des. auto.
        * eapply MAXLE.

    - unfold U_src. i. des. ss.
      apply COMPLETEU in SAT. des.
      dup IN. apply List.in_map with (f := fst) in IN. ss.
      eapply drf_sim_trace_in2 in IN; eauto; cycle 1.
      { ii. inv H. } des. inv EVENT.
      eapply List.in_map_iff in IN1. des. destruct x; ss.
      esplits; eauto. rewrite IN1 in IN2. esplits; eauto.

    - unfold AU_src. i. des. ss.
      apply COMPLETEAU in SAT. des.
      dup IN. apply List.in_map with (f := fst) in IN. ss.
      eapply drf_sim_trace_in2 in IN; eauto; cycle 1.
      { ii. inv H. } des. inv EVENT.
      eapply List.in_map_iff in IN1. des. destruct x; ss.
      esplits; eauto. rewrite IN1 in IN2. esplits; eauto.

    - unfold MU_src. i. ss. des. apply NNPP in SAT0.
      split.
      { unfold U_src, AU_src. split; ii; des; clarify. }
      destruct (MAX loc). des.
      assert (PROMISED: all_promises (Configuration.threads c_tgt0) (fun _ => True) loc (max loc)).
      { apply NNPP. intros NPROM.
        inv SIM. inv FORGET1. inv MEM0. inv FORGET1.
        unfold Memory.get in COMPLETE. rewrite <- COMPLETE in GET; auto.
        inv SHORTER. apply COMPLETE0 in GET. des. clarify. }
      inv PROMISED. destruct (classic (tid = tid0)).
      + clarify. dup PROMISED0. inv PROMISED0. destruct msg as [from0 msg].

        exists (Time.join (Memory.max_ts loc (Configuration.memory c_src0)) from0).
        splits.
        * eapply Time.join_l.
        * unfold Time.join. des_ifs.
          { dup GET0. apply memory_get_ts_strong in GET0. des; clarify.
            erewrite GET2 in *.
            inv SIM. inv WFSRC. inv MEM0. erewrite INHABITED in SAT0. clarify. }
          { destruct (MAXLE loc); auto. inv H. rewrite <- H1 in *.
            inv SIM. inv WFSRC. inv MEM0. specialize (INHABITED loc).
            eapply Memory.max_ts_spec in INHABITED. des.
            unfold Memory.max_timemap in *. clarify. }
        * i. inv PR. econs; eauto. econs; eauto. ss.
          unfold Time.join in FROM. des_ifs. econs; ss. etrans; eauto.

      + exfalso. apply List.in_app_or in SAT. des.
        * exploit COMPLETEAU; eauto. i. des.
          eapply List.Forall_forall in NORACE; eauto. des. ss.
          apply NORACE0. split.
          { econs; eauto. }
          { intros LATEST. inv LATEST. unfold Memory.get in GET0. clarify. }
        * exploit COMPLETEU; eauto. i. des.
          eapply List.Forall_forall in NORACE; eauto. des. ss.
          apply NORACE0. split.
          { econs; eauto. }
          { intros LATEST. inv LATEST. unfold Memory.get in GET0.
            rewrite GET0 in *. inv GET. }

    - inv FORGET0. ii.
      exploit COMPLETEW; eauto. i. des.
      dup IN. apply List.in_map with (f := fst) in IN. ss.
      eapply drf_sim_trace_in2 in IN; eauto; cycle 1.
      { ii. inv H; ss. } des.
      eapply List.in_map_iff in IN1. des. destruct x; ss. subst.
      esplits; eauto. inv EVENT; ss.
      + des. inv WRITETO. split; auto.
      + des. inv WRITETO. split; auto.
  }
  { unfold AU_src. i. des. apply AUPDATES in SAT. auto. }
Qed.
