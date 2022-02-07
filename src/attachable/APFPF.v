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
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.
Require Import Behavior.

Require Import AMemory.
Require Import ALocal.
Require Import AThread.

Require Import APF.
Require Import PF.


Lemma promise_apromise
  :
    Memory.promise <9= AMemory.promise.
Proof.
  i. inv PR; econs; eauto.
Qed.

Lemma write_awrite
  :
    Memory.write <10= AMemory.write.
Proof.
  i. inv PR; econs; eauto.
  eapply promise_apromise; eauto.
Qed.

Lemma program_step_aprogram_step
  :
    Thread.program_step <4= AThread.program_step.
Proof.
  i. inv PR. inv LOCAL.
  - econs; eauto.
  - econs; eauto.
  - inv LOCAL0. econs; eauto. econs; eauto.
    econs; eauto. eapply write_awrite; eauto.
  - inv LOCAL2. econs; eauto. econs; eauto.
    econs; eauto. eapply write_awrite; eauto.
  - econs; eauto.
  - econs; eauto.
  - econs; eauto.
Qed.

Lemma thread_step_athread_step
  :
    Thread.step_allpf <4= AThread.step_allpf.
Proof.
  i. inv PR. inv STEP.
  - inv STEP0. inv LOCAL. econs; eauto. econs; eauto.
    econs; eauto. econs; eauto. eapply promise_apromise; eauto.
  - econs. econs 2. eapply program_step_aprogram_step; eauto.
Qed.

Lemma thread_steps_athread_steps lang
  :
    rtc (tau (@Thread.step_allpf lang)) <2= rtc (tau (@AThread.step_allpf lang)).
Proof.
  eapply rtc_implies. i. inv H. econs; eauto.
  eapply thread_step_athread_step; eauto.
Qed.

Lemma program_steps_aprogram_steps lang
  :
    rtc (tau (@Thread.program_step lang)) <2= rtc (tau (@AThread.program_step lang)).
Proof.
  eapply rtc_implies. i. inv H. econs; eauto.
  eapply program_step_aprogram_step; eauto.
Qed.

Lemma pfstep_apfstep:
  PFConfiguration.step <4= APFConfiguration.step.
Proof.
  ii. inv PR.
  eapply program_steps_aprogram_steps in STEPS.
  eapply program_step_aprogram_step in STEP.
  econs; eauto.
Qed.

Record shorter (mem_src mem_tgt: Memory.t): Prop :=
  shorter_intro
    {
      shorter_get: forall loc to from msg (GET: Memory.get loc to mem_tgt = Some (from, msg)),
        exists from', (<<GET: Memory.get loc to mem_src = Some (from', msg)>>);

      shorter_get_iff: forall loc to from' msg (GET: Memory.get loc to mem_src = Some (from', msg)),
          exists from msg, (<<GET: Memory.get loc to mem_tgt = Some (from, msg)>>) /\
                           (<<TS: Time.le from from'>>) /\
                           (<<ATTATCH:
                              forall (BLANK: Memory.get loc from' mem_src = None),
                                Time.lt from from'>>);
    }
.

Lemma shorter_write mem_src0 mem_tgt0 loc from to val released prom1 mem_tgt1 kind
      (WRITE: AMemory.write Memory.bot mem_tgt0 loc from to val released prom1 mem_tgt1 kind)
      (SHORT: shorter mem_src0 mem_tgt0)
  :
    exists from' mem_src1,
      (<<WRITE: Memory.write Memory.bot mem_src0 loc from' to val released prom1 mem_src1 kind>>) /\
      (<<SHORT: shorter mem_src1 mem_tgt1>>).
Proof.
  exploit APFConfiguration.write_no_promise; eauto. i. des. clarify.
  inv WRITE. inv PROMISE. exists (Time.middle from to).
  assert (WF: (<<MSG_WF: Message.wf (Message.full val released)>>) /\
              (<<TO: Time.lt from to>>) /\
              (<<DISJOINT: forall to2 from2 msg2
                                  (GET: Memory.get loc to2 mem_tgt0 = Some (from2, msg2)),
                  Interval.disjoint (from, to) (from2, to2)>>)).
  { inv MEM. inv ADD. splits; auto. } des.
  exploit (@Memory.add_exists mem_src0 loc (Time.middle from to) to (Message.full val released)).
  { ii. inv LHS. inv RHS. ss.
    eapply shorter_get_iff in GET2; eauto. des.
    eapply DISJOINT; eauto.
    - instantiate (1:=x). econs; ss. etrans.
      + eapply Time.middle_spec; eauto.
      + eauto.
    - econs; ss. eapply TimeFacts.le_lt_lt; eauto.
  }
  { eapply Time.middle_spec; eauto. }
  { ss. }
  intros [mem_src1 ADD].
  exploit (Memory.add_exists_le).
  { eapply Memory.bot_le. }
  { eapply ADD. } intros [prom0' ADDPROM].
  exploit Memory.remove_exists.
  { eapply Memory.add_get0. eapply ADDPROM. } intros [prom1 REMOVEPROM].

  exists mem_src1. split.
  - econs.
    + econs; eauto; i; clarify.
      dup GET. eapply shorter_get_iff in GET; eauto. des.
      dup GET1. eapply shorter_get in GET1; eauto. des. clarify.
      eapply DISJOINT; eauto.
      * instantiate (1:=to). econs; ss. refl.
      * econs; ss.
        { eapply ATTATCH; eauto.
          eapply Memory.add_get0 in ADD. des. clarify. }
        { eapply Memory.get_ts in GET. des; auto.
          - clarify. refl.
          - left. auto. }
    + exploit MemoryFacts.add_remove_eq; eauto. i. clarify.

  - econs.
    + i. dup GET. erewrite Memory.add_o in GET; eauto. des_ifs.
      * ss. des. clarify. esplits. eapply Memory.add_get0; eauto.
      * guardH o. dup GET. eapply shorter_get in GET; cycle 1; eauto. des.
        eapply Memory.add_get1 in GET2; eauto.
    + i. dup GET. erewrite Memory.add_o in GET; eauto. des_ifs.
      * ss. des. clarify. esplits.
        { eapply Memory.add_get0; eauto. }
        { left. eapply Time.middle_spec; eauto. }
        { i. eapply Time.middle_spec; eauto. }
      * guardH o. dup GET. eapply shorter_get_iff in GET; cycle 1; eauto. des.
        eapply Memory.add_get1 in GET2; eauto.
        esplits; eauto.
        i. eapply ATTATCH. destruct (Memory.get loc0 from' mem_src0) eqn:GET3; auto.
        destruct p. eapply Memory.add_get1 in GET3; eauto. clarify.
Qed.


Lemma shorter_update mem_src0 mem_tgt0 loc from to val released prom1 mem_tgt1 kind
      (WRITE: AMemory.write Memory.bot mem_tgt0 loc from to val released prom1 mem_tgt1 kind)
      ts msg
      (READ: Memory.get loc from mem_tgt0 = Some (ts, msg))
      (SHORT: shorter mem_src0 mem_tgt0)
  :
    exists mem_src1,
      (<<WRITE: Memory.write Memory.bot mem_src0 loc from to val released prom1 mem_src1 kind>>) /\
      (<<SHORT: shorter mem_src1 mem_tgt1>>).
Proof.
  exploit APFConfiguration.write_no_promise; eauto. i. des. clarify.
  inv WRITE. inv PROMISE.
  assert (WF: (<<MSG_WF: Message.wf (Message.full val released)>>) /\
              (<<TO: Time.lt from to>>) /\
              (<<DISJOINT: forall to2 from2 msg2
                                  (GET: Memory.get loc to2 mem_tgt0 = Some (from2, msg2)),
                  Interval.disjoint (from, to) (from2, to2)>>)).
  { inv MEM. inv ADD. splits; auto. } des.
  exploit (@Memory.add_exists mem_src0 loc from to (Message.full val released)).
  { ii. inv LHS. inv RHS. ss.
    eapply shorter_get_iff in GET2; eauto. des.
    eapply DISJOINT; eauto.
    - instantiate (1:=x). econs; ss.
    - econs; ss. eapply TimeFacts.le_lt_lt; eauto.
  }
  { ss. }
  { ss. }
  intros [mem_src1 ADD].
  exploit (Memory.add_exists_le).
  { eapply Memory.bot_le. }
  { eapply ADD. } intros [prom0' ADDPROM].
  exploit Memory.remove_exists.
  { eapply Memory.add_get0. eapply ADDPROM. } intros [prom1 REMOVEPROM].

  exists mem_src1. split.
  - econs.
    + econs; eauto; i; clarify.
      dup GET. eapply shorter_get_iff in GET; eauto. des.
      dup GET1. eapply shorter_get in GET1; eauto. des. clarify.
      eapply DISJOINT; eauto.
      * instantiate (1:=to). econs; ss. refl.
      * econs; ss.
        { eapply ATTATCH; eauto.
          eapply Memory.add_get0 in ADD. des. clarify. }
        { eapply Memory.get_ts in GET. des; auto.
          - clarify. refl.
          - left. auto. }
    + exploit MemoryFacts.add_remove_eq; eauto. i. clarify.
  - econs.
    + i. dup GET. erewrite Memory.add_o in GET; eauto. des_ifs.
      * ss. des. clarify. esplits. eapply Memory.add_get0; eauto.
      * guardH o. dup GET. eapply shorter_get in GET; cycle 1; eauto. des.
        eapply Memory.add_get1 in GET2; eauto.
    + i. dup GET. erewrite Memory.add_o in GET; eauto. des_ifs.
      * ss. des. clarify. esplits.
        { eapply Memory.add_get0; eauto. }
        { refl. }
        { i. eapply shorter_get in READ; eauto. des.
          eapply Memory.add_get1 in GET; eauto. clarify. }
      * guardH o. dup GET. eapply shorter_get_iff in GET; cycle 1; eauto. des.
        eapply Memory.add_get1 in GET2; eauto.
        esplits; eauto.
        i. eapply ATTATCH. destruct (Memory.get loc0 from' mem_src0) eqn:GET3; auto.
        destruct p. eapply Memory.add_get1 in GET3; eauto. clarify.
Qed.

Lemma shorter_program_step lang th_src th_tgt th_tgt' st st' v v' prom' sc sc'
      mem_tgt mem_tgt' mem_src e_tgt
      (STEP: AThread.program_step e_tgt th_tgt th_tgt')
      (SHORT: shorter mem_src mem_tgt)
      (TH_SRC: th_src = Thread.mk lang st (Local.mk v Memory.bot) sc mem_src)
      (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v Memory.bot) sc mem_tgt)
      (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
  :
    exists mem_src' e_src,
      (<<STEP: Thread.program_step
                 e_src th_src
                 (Thread.mk lang st' (Local.mk v' prom') sc' mem_src')>>) /\
      (<<SHORT: shorter mem_src' mem_tgt'>>) /\
      (<<EVENT: ThreadEvent.get_machine_event e_tgt = ThreadEvent.get_machine_event e_src>>)
.
Proof.
  inv STEP. clarify. inv LOCAL.
  - esplits; eauto. econs; eauto.
  - esplits; eauto. inv LOCAL0. ss. clarify. econs; eauto. econs; eauto.
    eapply shorter_get in GET; eauto. des. econs; eauto.
  - inv LOCAL0. ss. clarify.
    exploit shorter_write; eauto. i. des. exists mem_src1.
    esplits; eauto.
    + econs; eauto; ss.
    + ss.
  - inv LOCAL1. inv LOCAL2. clarify.
    dup GET. eapply shorter_get in GET; eauto. des.
    exploit shorter_update; eauto. i. des. exists mem_src1.
    esplits; eauto. econs; eauto.
  - esplits; eauto. inv LOCAL0. ss. clarify. econs; eauto.
  - esplits; eauto. inv LOCAL0. ss. clarify. econs; eauto.
  - esplits; eauto. inv LOCAL0. ss. clarify. econs; eauto.
Qed.

Lemma shorter_program_steps lang th_src th_tgt th_tgt' st st' v v' prom' sc sc'
      mem_tgt mem_tgt' mem_src
      (STEPS: rtc (tau (@AThread.program_step lang)) th_tgt th_tgt')
      (SHORT: shorter mem_src mem_tgt)
      (TH_SRC: th_src = Thread.mk lang st (Local.mk v Memory.bot) sc mem_src)
      (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v Memory.bot) sc mem_tgt)
      (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
  :
    exists mem_src',
      (<<STEPS: rtc (tau (@Thread.program_step lang))
                    th_src
                    (Thread.mk lang st' (Local.mk v' prom') sc' mem_src')>>) /\
      (<<SHORT: shorter mem_src' mem_tgt'>>)
.
Proof.
  ginduction STEPS.
  - i. clarify. esplits; eauto.
  - i. clarify. inv H. destruct y. destruct local.
    exploit shorter_program_step; eauto. i. des.
    exploit PFConfiguration.program_step_no_promise; eauto. i. ss. clarify.
    exploit IHSTEPS; eauto. i. des. esplits; eauto.
    econs; eauto. econs; eauto. rewrite <- EVENT. auto.
Qed.

Inductive sim_apf_pf: Configuration.t -> Configuration.t -> Prop :=
| sim_apf_pf_intro
    c_src c_tgt
    ths sc mem_src mem_tgt
    (SRC: c_src = Configuration.mk ths sc mem_src)
    (TGT: c_tgt = Configuration.mk ths sc mem_tgt)
    (PROMISESRC: ~ Configuration.has_promise c_src)
    (PROMISETGT: ~ Configuration.has_promise c_tgt)
    (MEMORY: shorter mem_src mem_tgt)
  :
    sim_apf_pf c_src c_tgt
.

Lemma sim_apf_pf_step c_tgt0 c_tgt1 c_src0 tid e
      (SIM: sim_apf_pf c_src0 c_tgt0)
      (STEP: APFConfiguration.step tid e c_tgt0 c_tgt1)
  :
    exists c_src1,
      (<<STEP: PFConfiguration.step tid e c_src0 c_src1>>) /\
      (<<SIM: sim_apf_pf c_src1 c_tgt1>>).
Proof.
  inv SIM. dup STEP. inv STEP. ss. destruct e2. destruct lc1, local, lc3.
  exploit APFConfiguration.no_promise_spec; eauto. i. ss. clarify.
  exploit shorter_program_steps; eauto. i. des.
  exploit APFConfiguration.program_steps_no_promise; eauto. i. ss. clarify.
  exploit shorter_program_step; eauto. i. des.
  assert (STEPSRC: PFConfiguration.step
                     (ThreadEvent.get_machine_event e_src) e
                     (Configuration.mk ths sc mem_src)
                     (Configuration.mk (IdentMap.add e (existT _ lang st3, Local.mk tview1 promises1) ths) sc3 mem_src'0)).
  { econs; eauto. }
  rewrite EVENT. esplits; eauto. econs; eauto.
  - eapply PFConfiguration.configuration_step_no_promise in STEPSRC; eauto.
  - eapply APFConfiguration.configuration_step_no_promise in STEP0; eauto.
Qed.

Lemma sim_apf_pf_init s
  :
    sim_apf_pf (Configuration.init s) (Configuration.init s).
Proof.
  econs; ss.
  - ii. inv H. ss. unfold Threads.init in FIND.
    erewrite IdentMap.Properties.F.map_o in *.
    unfold option_map, Local.init in *. des_ifs. ss. erewrite Memory.bot_get in GET. clarify.
  - ii. inv H. ss. unfold Threads.init in FIND.
    erewrite IdentMap.Properties.F.map_o in *.
    unfold option_map, Local.init in *. des_ifs. ss. erewrite Memory.bot_get in GET. clarify.
  - econs; i.
    + unfold Memory.init, Memory.get in *. erewrite Cell.init_get in *.
      des_ifs. esplits; eauto.
    + unfold Memory.init, Memory.get in *. erewrite Cell.init_get in *.
      des_ifs. esplits; eauto.
      * refl.
      * i. erewrite Cell.init_get in *. des_ifs.
Qed.

Lemma sim_apf_pf_terminal c_src c_tgt
      (SIM: sim_apf_pf c_src c_tgt)
      (TERMINAL: Configuration.is_terminal c_tgt)
  :
    Configuration.is_terminal c_src.
Proof.
  inv SIM. ii. eauto.
Qed.

Lemma sim_apf_pf_adequacy c_src c_tgt
      (SIM: sim_apf_pf c_src c_tgt)
  :
    behaviors APFConfiguration.step c_tgt <1=
    behaviors PFConfiguration.step c_src.
Proof.
  i. ginduction PR; i.
  - econs 1. eapply sim_apf_pf_terminal; eauto.
  - exploit sim_apf_pf_step; eauto. i. des. econs 2; eauto.
  - exploit sim_apf_pf_step; eauto. i. des. econs 3; eauto.
  - exploit sim_apf_pf_step; eauto. i. des. econs 4; eauto.
Qed.

Theorem apf_pf_equiv s
  :
    behaviors APFConfiguration.step (Configuration.init s) <1=
    behaviors PFConfiguration.step (Configuration.init s).
Proof.
  eapply sim_apf_pf_adequacy.
  eapply sim_apf_pf_init; auto.
Qed.

Theorem apf_pf_equiv2 c
  :
    behaviors PFConfiguration.step c <1=
    behaviors APFConfiguration.step c.
Proof.
  eapply le_step_behavior_improve; eauto.
  i. eapply pfstep_apfstep; eauto.
Qed.
