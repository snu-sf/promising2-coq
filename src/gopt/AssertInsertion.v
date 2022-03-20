Require Import Omega.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.

Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Behavior.

Require Import Syntax.
Require Import Semantics.

Require Import PromiseConsistent.
Require Import SimpleSimulation.

Require Import AMemory.
Require Import ALocal.
Require Import ATView.
Require Import AThread.

Require Import PFCommon.
Require Import PFStep.
Require Import PFCertify.
Require Import Invariant.

Set Implicit Arguments.


Section AssertInsertion.
  Variable
    (S:ThreadsProp)
    (J:MemoryProp)
    (program: Threads.syntax).

  Context `{LOGIC: Logic.t S J program}.


  (* simulation relations on threads *)

  Inductive insert_assertion (tid: Ident.t): forall (stmts_src stmts_tgt: list Stmt.t), Prop :=
  | insert_assertion_nil:
      insert_assertion tid [] []
  | insert_assertion_instr
      (i: Instr.t) stmts_src stmts_tgt
      (SIM: insert_assertion tid stmts_src stmts_tgt):
      insert_assertion tid ((Stmt.instr i)::stmts_src) ((Stmt.instr i)::stmts_tgt)
  | insert_assertion_ite
      cond
      stmts1_src stmts2_src stmts_src
      stmts1_tgt stmts2_tgt stmts_tgt
      (SIM1: insert_assertion tid (stmts1_src ++ stmts_src) (stmts1_tgt ++ stmts_tgt))
      (SIM2: insert_assertion tid (stmts2_src ++ stmts_src) (stmts2_tgt ++ stmts_tgt)):
      insert_assertion tid
                       ((Stmt.ite cond stmts1_src stmts2_src)::stmts_src)
                       ((Stmt.ite cond stmts1_tgt stmts2_tgt)::stmts_tgt)
  | insert_assertion_dowhile
      cond
      stmts1_src stmts_src
      stmts1_tgt stmts_tgt
      (SIM: insert_assertion tid
                             (stmts1_src ++ (Stmt.ite cond ((Stmt.dowhile stmts1_src cond)::nil) nil) :: stmts_src)
                             (stmts1_tgt ++ (Stmt.ite cond ((Stmt.dowhile stmts1_tgt cond)::nil) nil) :: stmts_tgt)):
      insert_assertion tid
                       ((Stmt.dowhile stmts1_src cond)::stmts_src)
                       ((Stmt.dowhile stmts1_tgt cond)::stmts_tgt)
  | insert_assertion_assert
      c stmts_src stmts_tgt
      (SIM: insert_assertion tid stmts_src stmts_tgt)
      (SUCCESS: forall rs (TH: S tid lang (State.mk rs stmts_src)),
          RegFile.eval_expr rs c <> 0):
      insert_assertion tid stmts_src ((Stmt.ite c [Stmt.instr Instr.abort] nil)::stmts_tgt)
  .
  #[local]
  Hint Constructors insert_assertion: core.

  Inductive sim_state (tid: Ident.t) (st_src st_tgt: State.t): Prop :=
  | sim_state_intro
      (STMTS: insert_assertion tid (State.stmts st_src) (State.stmts st_tgt))
      (REGS: (State.regs st_src) = (State.regs st_tgt))
  .
  #[local]
  Hint Constructors sim_state: core.

  Inductive sim_thread (tid: Ident.t) (e_src e_tgt: Thread.t lang): Prop :=
  | sim_thread_intro
      (STATE: sim_state tid (Thread.state e_src) (Thread.state e_tgt))
      (LOCAL: (Thread.local e_src) = (Thread.local e_tgt))
      (SC: (Thread.sc e_src) = (Thread.sc e_tgt))
      (MEMORY: (Thread.memory e_src) = (Thread.memory e_tgt))
  .
  #[local]
  Hint Constructors sim_thread: core.


  Lemma sim_state_step
        tid st1_src
        e st1_tgt st2_tgt
        (SIM1: sim_state tid st1_src st1_tgt)
        (STEP: (Language.step lang) e st1_tgt st2_tgt):
    (exists st2_src,
        <<STEP_SRC: State.opt_step e st1_src st2_src>> /\
        <<SIM2: sim_state tid st2_src st2_tgt>>) \/
    (exists c stmts,
        <<STMTS: (State.stmts st1_tgt) =
                 (Stmt.ite c [Stmt.instr Instr.abort] nil)::stmts>> /\
        <<SUCCESS: forall (SOUND: S tid lang st1_src),
            RegFile.eval_expr (State.regs st1_src) c <> 0>> /\
        <<FAIL: RegFile.eval_expr (State.regs st1_src) c = 0>>).
  Proof.
    destruct st1_src, st1_tgt, st2_tgt.
    inv SIM1. ss. subst.
    inv STMTS.
    - inv STEP.
    - left.
      exists (State.mk regs1 stmts_src).
      inv STEP. split; eauto.
      econs 2. econs; eauto.
    - left.
      inv STEP. esplits.
      + econs 2. econs; eauto.
      + condtac; eauto.
    - left.
      inv STEP. esplits.
      + econs 2. econs; eauto.
      + ss.
    - inv STEP. condtac; ss.
      + right. esplits; eauto.
      + left. esplits; [econs 1|]. ss.
  Qed.

  Lemma sim_thread_promise_step
        tid e1_src
        pf e e1_tgt e2_tgt
        (SIM1: sim_thread tid e1_src e1_tgt)
        (STEP_TGT: Thread.promise_step pf e e1_tgt e2_tgt):
    exists e2_src,
      <<STEP_SRC: Thread.promise_step pf e e1_src e2_src>> /\
      <<SIM2: sim_thread tid e2_src e2_tgt>>.
  Proof.
    destruct e1_src, e1_tgt, e2_tgt. ss.
    inv SIM1. ss. subst.
    inv STEP_TGT; ss.
    esplits.
    - econs; eauto.
    - eauto.
  Qed.

  Lemma sim_thread_program_step
        tid e1_src
        e e1_tgt e2_tgt
        (SIM1: sim_thread tid e1_src e1_tgt)
        (STEP_TGT: Thread.program_step e e1_tgt e2_tgt):
    (exists e2_src,
        <<STEP_SRC: Thread.opt_program_step e e1_src e2_src>> /\
        <<SIM2: sim_thread tid e2_src e2_tgt>>) \/
    (exists c stmts,
        <<STMTS: (State.stmts (Thread.state e1_tgt)) =
                 (Stmt.ite c [Stmt.instr Instr.abort] nil)::stmts>> /\
        <<SUCCESS: forall (SOUND: S tid lang (Thread.state e1_src)),
            RegFile.eval_expr (State.regs (Thread.state e1_src)) c <> 0>> /\
        <<FAIL: RegFile.eval_expr (State.regs (Thread.state e1_src)) c = 0>>).
  Proof.
    destruct e1_src, e1_tgt, e2_tgt. ss.
    inv SIM1. ss. subst.
    inv STEP_TGT; ss.
    exploit sim_state_step; eauto. i. des; cycle 1.
    { right. esplits; eauto. }
    left. inv LOCAL; inv STEP_SRC; ss.
    - esplits.
      + econs 1.
      + econs; eauto.
    - esplits.
      + econs 2. econs; eauto.
      + econs; eauto.
    - esplits.
      + econs 2. econs; eauto.
      + econs; eauto.
    - esplits.
      + econs 2. econs; eauto.
      + econs; eauto.
    - esplits.
      + econs 2. econs; eauto.
      + econs; eauto.
    - esplits.
      + econs 2. econs; eauto.
      + econs; eauto.
    - esplits.
      + econs 2. econs; eauto.
      + econs; eauto.
    - esplits.
      + econs 2. econs; eauto.
      + econs; eauto.
  Qed.

  Lemma sim_thread_step
        tid e1_src
        pf e e1_tgt e2_tgt
        (SIM1: sim_thread tid e1_src e1_tgt)
        (STEP_TGT: Thread.step pf e e1_tgt e2_tgt):
    (exists e2_src,
        <<STEP_SRC: Thread.opt_step e e1_src e2_src>> /\
        <<SIM2: sim_thread tid e2_src e2_tgt>>) \/
    (exists c stmts,
        <<STMTS: (State.stmts (Thread.state e1_tgt)) =
                 (Stmt.ite c [Stmt.instr Instr.abort] nil)::stmts>> /\
        <<ASSERT: forall (SOUND: S tid lang (Thread.state e1_src)),
            RegFile.eval_expr (State.regs (Thread.state e1_src)) c <> 0>> /\
        <<FAIL: RegFile.eval_expr (State.regs (Thread.state e1_src)) c = 0>>).
  Proof.
    inv STEP_TGT.
    - left.
      exploit sim_thread_promise_step; eauto. i. des.
      esplits; eauto.
      econs 2. econs 1. eauto.
    - exploit sim_thread_program_step; eauto. i. des.
      + left. esplits; eauto.
        inv STEP_SRC.
        * econs 1.
        * econs 2. econs 2. eauto.
      + right. esplits; eauto.
  Qed.

  Lemma sim_thread_rtc_tau_step
        tid e1_src e1_tgt e2_tgt
        (SIM1: sim_thread tid e1_src e1_tgt)
        (STEPS_TGT: rtc (@Thread.tau_step lang) e1_tgt e2_tgt):
    (exists e2_src,
        <<STEPS_SRC: rtc (@Thread.tau_step lang) e1_src e2_src>> /\
        <<SIM2: sim_thread tid e2_src e2_tgt>>) \/
    (exists e_src e_tgt c stmts,
        <<STEPS1_TGT: rtc (@Thread.tau_step lang) e1_tgt e_tgt>> /\
        <<STEPS2_TGT: rtc (@Thread.tau_step lang) e_tgt e2_tgt>> /\
        <<STEPS_SRC: rtc (@Thread.tau_step lang) e1_src e_src>> /\
        <<SIM: sim_thread tid e_src e_tgt>> /\
        <<STMTS: (State.stmts (Thread.state e_tgt)) =
                 (Stmt.ite c [Stmt.instr Instr.abort] nil)::stmts>> /\
        <<ASSERT: forall (SOUND: S tid lang (Thread.state e_src)),
            RegFile.eval_expr (State.regs (Thread.state e_src)) c <> 0>> /\
        <<FAIL: RegFile.eval_expr (State.regs (Thread.state e_src)) c = 0>>).
  Proof.
    revert e1_src SIM1.
    induction STEPS_TGT; eauto; i.
    inv H. inv TSTEP.
    exploit sim_thread_step; eauto. i. des.
    - exploit IHSTEPS_TGT; eauto. i. des.
      + left. esplits; [|eauto].
        inv STEP_SRC; eauto.
        econs 2; eauto.
        econs; [econs; eauto|ss].
      + right.
        esplits; try exact STEPS2_TGT; try exact SIM; eauto.
        * econs 2; eauto.
          econs; [econs; eauto|ss].
        * inv STEP_SRC; eauto.
          econs 2; eauto.
          econs; [econs; eauto|ss].
    - right.
      esplits; try exact SIM1; eauto.
      econs 2; eauto.
      econs; [econs; eauto| ss].
  Qed.

  Lemma sim_thread_rtc_program_step
        tid e1_src e1_tgt e2_tgt
        (SIM1: sim_thread tid e1_src e1_tgt)
        (STEPS_TGT: rtc (tau (@Thread.program_step lang)) e1_tgt e2_tgt):
    (exists e2_src,
        <<STEPS_SRC: rtc (tau (@Thread.program_step lang)) e1_src e2_src>> /\
        <<SIM2: sim_thread tid e2_src e2_tgt>>) \/
    (exists e_src e_tgt c stmts,
        <<STEPS1_TGT: rtc (tau (@Thread.program_step lang)) e1_tgt e_tgt>> /\
        <<STEPS2_TGT: rtc (tau (@Thread.program_step lang)) e_tgt e2_tgt>> /\
        <<STEPS_SRC: rtc (tau (@Thread.program_step lang)) e1_src e_src>> /\
        <<SIM: sim_thread tid e_src e_tgt>> /\
        <<STMTS: (State.stmts (Thread.state e_tgt)) =
                 (Stmt.ite c [Stmt.instr Instr.abort] nil)::stmts>> /\
        <<ASSERT: forall (SOUND: S tid lang (Thread.state e_src)),
            RegFile.eval_expr (State.regs (Thread.state e_src)) c <> 0>> /\
        <<FAIL: RegFile.eval_expr (State.regs (Thread.state e_src)) c = 0>>).
  Proof.
    revert e1_src SIM1.
    induction STEPS_TGT; eauto; i.
    inv H.
    exploit sim_thread_program_step; eauto. i. des.
    - exploit IHSTEPS_TGT; eauto. i. des.
      + left. esplits; [|eauto].
        inv STEP_SRC; eauto.
      + right.
        esplits; try exact STEPS2_TGT; try exact SIM; eauto.
        inv STEP_SRC; eauto.
    - right.
      esplits; try exact SIM1; eauto.
  Qed.


  (* simulation relation on configurations *)

  Inductive sim_conf (c_src c_tgt: Configuration.t): Prop :=
  | sim_conf_intro
      (SEM: sem S J c_src)
      (TIDS: Threads.tids (Configuration.threads c_src) = Threads.tids (Configuration.threads c_tgt))
      (FIND_SRC: forall tid l st_src lc_src
                   (FIND: IdentMap.find tid (Configuration.threads c_src) = Some (existT _ l st_src, lc_src)),
          l = lang)
      (FIND_TGT: forall tid l st_tgt lc_tgt
                   (FIND: IdentMap.find tid (Configuration.threads c_tgt) = Some (existT _ l st_tgt, lc_tgt)),
          l = lang)
      (THREADS: forall tid st_src lc_src st_tgt lc_tgt
                  (FIND_SRC: IdentMap.find tid (Configuration.threads c_src) = Some (existT _ lang st_src, lc_src))
                  (FIND_TGT: IdentMap.find tid (Configuration.threads c_tgt) = Some (existT _ lang st_tgt, lc_tgt)),
          <<STATE: sim_state tid st_src st_tgt>> /\
          <<LOCAL: lc_src = lc_tgt>>)
      (SC: (Configuration.sc c_src) = (Configuration.sc c_tgt))
      (MEMORY: (Configuration.memory c_src) = (Configuration.memory c_tgt))
  .
  #[local]
  Hint Constructors sim_conf: core.


  Lemma sim_conf_find
        c_src c_tgt tid
        (SIM: sim_conf c_src c_tgt):
    (exists lang_src st_src lc_src,
        IdentMap.find tid (Configuration.threads c_src) = Some (existT _ lang_src st_src, lc_src)) <->
    (exists lang_tgt st_tgt lc_tgt,
        IdentMap.find tid (Configuration.threads c_tgt) = Some (existT _ lang_tgt st_tgt, lc_tgt)).
  Proof.
    inv SIM. destruct c_src, c_tgt. ss.
    eapply Threads.tids_find; eauto.
  Qed.

  Lemma sim_conf_sim_thread
        c_src c_tgt
        tid st_src lc_src st_tgt lc_tgt
        (SIM: sim_conf c_src c_tgt)
        (FIND_SRC: IdentMap.find tid (Configuration.threads c_src) = Some (existT _ lang st_src, lc_src))
        (FIND_TGT: IdentMap.find tid (Configuration.threads c_tgt) = Some (existT _ lang st_tgt, lc_tgt)):
    sim_thread tid
               (Thread.mk lang st_src lc_src (Configuration.sc c_src) (Configuration.memory c_src))
               (Thread.mk lang st_tgt lc_tgt (Configuration.sc c_tgt) (Configuration.memory c_tgt)).
  Proof.
    inv SIM. exploit THREADS; eauto. i. des.
    econs; eauto.
  Qed.

  Lemma sim_conf_sim
        c_src c_tgt
        (SIM: sim_conf c_src c_tgt):
    sim c_src c_tgt.
  Proof.
    revert c_src c_tgt SIM.
    pcofix CIH. i. pfold. econs; ii.
    { (* terminal *)
      esplits; eauto. ii.
      exploit sim_conf_find; eauto. i. des.
      exploit x0; eauto. i. des.
      inv SIM. ss.
      exploit FIND_SRC; eauto. i. subst.
      exploit FIND_TGT; eauto. i. subst.
      exploit THREADS; eauto. i. des. subst.
      exploit TERMINAL_TGT; eauto. i. des.
      split; auto.
      destruct st, st_tgt; ss. inv STATE0. ss. subst.
      inv STATE. inv STMTS. ss.
    }
    inv STEP_TGT.
    { (* failure step *)
      exploit sim_conf_find; eauto. i. des.
      exploit x1; eauto. i. des. clear x0 x1.
      destruct c_src as [ths1_src sc1_src mem1_src].
      destruct c_tgt as [ths1_tgt sc1 mem1].
      dup SIM. inv SIM0. ss. subst.
      exploit FIND_SRC; eauto. i. subst.
      exploit FIND_TGT; eauto. i. subst.
      clear FIND_SRC FIND_TGT THREADS.
      exploit sim_conf_sim_thread; eauto. s. intro SIM_TH.
      exploit sim_thread_rtc_tau_step; eauto. i. des.
      - exploit sim_thread_step; eauto. i. des; cycle 1.
        { destruct e2, state. ss. subst.
          inv STEP; inv STEP0. inv STATE. }
        inv STEP_SRC. destruct e2_src0. ss.
        assert (CSTEP: Configuration.step
                         MachineEvent.failure tid
                         (Configuration.mk ths1_src sc1 mem1)
                         (Configuration.mk
                            (IdentMap.add tid (existT (fun (lang: language) => (Language.state lang)) lang state, local) ths1_src)
                            sc memory)).
        { econs 1; eauto. }
        esplits; [econs 2; eauto|].
        right. apply CIH. econs; ss; try by (inv SIM0; ss).
        + eapply configuration_step_sem; try exact CSTEP; eauto.
        + repeat rewrite Threads.tids_add.
          repeat rewrite IdentSet.add_mem; ss.
          * rewrite Threads.tids_o. rewrite TID. ss.
          * rewrite Threads.tids_o. rewrite x. ss.
        + i. revert FIND. rewrite IdentMap.gsspec. condtac; ss; i.
          * inv FIND. ss.
          * inv SIM. eapply FIND_SRC; eauto.
        + i. revert FIND. rewrite IdentMap.gsspec. condtac; ss; i.
          * inv FIND. ss.
          * inv SIM. eapply FIND_TGT; eauto.
        + i. revert FIND_SRC. rewrite IdentMap.gsspec. condtac; ss; i.
          * subst. revert FIND_TGT. rewrite IdentMap.gsspec. condtac; ss; i.
            Configuration.simplify2. inv SIM0. ss.
          * revert FIND_TGT. rewrite IdentMap.gsspec. condtac; ss; i.
            inv SIM. eauto.
      - exfalso.
        dup WF_TGT. inv WF_TGT0. inv WF. ss. clear DISJOINT.
        exploit THREADS; eauto. intro WF1_TGT. clear THREADS.
        dup WF_SRC. inv WF_SRC0. inv WF. ss. clear DISJOINT.
        exploit THREADS; eauto. intro WF1_SRC. clear THREADS.
        exploit Thread.rtc_tau_step_future; try exact STEPS1_TGT; eauto. s. i. des.
        exploit (@PFStep.sim_thread_exists lang (Thread.mk lang st_src lc_src sc1 mem1)); ss; eauto. i. des.
        exploit PFStep.thread_rtc_tau_step; try exact SIM1; eauto.
        { inv SIM0. rewrite LOCAL.
          inv STEP; inv STEP0. inv LOCAL0. inv LOCAL1.
          eapply rtc_tau_step_promise_consistent; eauto. }
        i. des.
        inv SEM. ss. exploit TH; eauto. i.
        exploit rtc_tau_aprogram_step_sem; try exact STEPS_SRC0; eauto.
        { inv SIM1. ss. rewrite STATE. eauto. }
        { eapply vals_incl_sem_memory; eauto.
          eapply PFStep.sim_memory_vals_incl; try eapply SIM1. }
        { eapply PFStep.sim_memory_inhabited; try eapply SIM1; ss.
          - apply WF1_SRC.
          - apply MEM. }
        i. des.
        inv SIM2. rewrite STATE in *.
        eapply ASSERT; eauto.
    }
    (* normal step *)
    exploit sim_conf_find; eauto. i. des.
    exploit x1; eauto. i. des. clear x0 x1.
    destruct c_src as [ths1_src sc1_src mem1_src].
    destruct c_tgt as [ths1_tgt sc1 mem1].
    dup SIM. inv SIM0. ss. subst.
    exploit FIND_SRC; eauto. i. subst.
    exploit FIND_TGT; eauto. i. subst.
    clear FIND_SRC FIND_TGT THREADS.
    exploit sim_conf_sim_thread; eauto. s. intro SIM_TH.
    dup WF_TGT. inv WF_TGT0. inv WF. ss. clear DISJOINT.
    exploit THREADS; eauto. intro WF1_TGT. clear THREADS.
    dup WF_SRC. inv WF_SRC0. inv WF. ss. clear DISJOINT.
    exploit THREADS; eauto. intro WF1_SRC. clear THREADS.
    exploit Thread.rtc_tau_step_future; eauto. s. i. des.
    exploit Thread.step_future; eauto. s. i. des.
    exploit sim_thread_rtc_tau_step; eauto. i. des; cycle 1.
    { exfalso.
      exploit Thread.rtc_tau_step_future; try exact STEPS1_TGT; eauto. s. i. des.
      exploit (@PFStep.sim_thread_exists lang (Thread.mk lang st_src lc_src sc1 mem1)); ss; eauto. i. des.
      exploit PFStep.thread_rtc_tau_step; try exact SIM1; eauto.
      { inv SIM0. rewrite LOCAL.
        eapply rtc_tau_step_promise_consistent; eauto.
        eapply step_promise_consistent; eauto.
        eapply consistent_promise_consistent; eauto. }
      i. des.
      inv SEM. ss. exploit TH; eauto. i.
      exploit rtc_tau_aprogram_step_sem; try exact STEPS_SRC0; eauto.
      { inv SIM1. ss. rewrite STATE. eauto. }
      { eapply vals_incl_sem_memory; eauto.
        eapply PFStep.sim_memory_vals_incl; try eapply SIM1. }
      { eapply PFStep.sim_memory_inhabited; try eapply SIM1; ss.
        - apply WF1_SRC.
        - apply MEM. }
      i. des.
      inv SIM2. rewrite STATE in *.
      eapply ASSERT; eauto.
    }
    exploit sim_thread_step; eauto. i. des; cycle 1.
    { exfalso.
      exploit Thread.rtc_tau_step_future; try exact STEPS1_TGT; eauto. s. i. des.
      exploit (@PFStep.sim_thread_exists lang (Thread.mk lang st_src lc_src sc1 mem1)); ss; eauto. i. des.
      exploit PFStep.thread_rtc_tau_step; try exact SIM0; eauto.
      { inv SIM2. rewrite LOCAL.
        eapply step_promise_consistent; eauto.
        eapply consistent_promise_consistent; eauto. }
      i. des.
      inv SEM. ss. exploit TH; eauto. i.
      exploit rtc_tau_aprogram_step_sem; try exact STEPS_SRC0; eauto.
      { inv SIM0. ss. rewrite STATE. eauto. }
      { eapply vals_incl_sem_memory; eauto.
        eapply PFStep.sim_memory_vals_incl; try eapply SIM0. }
      { eapply PFStep.sim_memory_inhabited; try eapply SIM0; ss.
        - apply WF1_SRC.
        - apply MEM. }
      i. des.
      inv SIM1. rewrite STATE in *.
      eapply ASSERT; eauto.
    }
    destruct e2_src0.
    assert (CONSISTENT_SRC: Thread.consistent (Thread.mk lang state local sc memory)).
    { exploit Memory.cap_exists; try exact CLOSED0. i. des.
      exploit Memory.cap_closed; eauto. intro CLOSED_CAP.
      exploit Local.cap_wf; try exact WF0; eauto. intro WF_CAP.
      exploit Memory.max_full_timemap_exists; try apply CLOSED_CAP. i. des.
      hexploit Memory.max_full_timemap_closed; try exact x1; eauto. intro SC_MAX.
      dup SIM0. inv SIM1. ss. subst. ii. ss.
      exploit Memory.cap_inj; [exact CAP|exact CAP0|..]; eauto. i. subst.
      exploit Memory.max_full_timemap_inj; [exact x1|exact SC_MAX0|..]. i. subst.
      exploit CONSISTENT; eauto. s. i. des.
      - (* failure certification *)
        left. unfold Thread.steps_failure in *. des.
        exploit (@sim_thread_rtc_tau_step tid (Thread.mk lang state lc3 sc0 mem0));
          try exact STEPS0; eauto.
        i. des; cycle 1.
        { exfalso.
          exploit Thread.tau_opt_all; try exact STEPS_SRC; eauto. i.
          exploit (@PFStep.sim_thread_exists lang (Thread.mk lang st_src lc_src sc1 mem1)); ss; eauto. i. des.
          exploit PFStep.thread_rtc_all_step; try exact x2; eauto.
          { hexploit consistent_promise_consistent; eauto. }
          i. des.
          exploit PFCertify.sim_thread_exists; try exact SIM4; eauto. s. i. des.
          exploit PFCertify.thread_rtc_tau_step; try exact STEPS_SRC0; eauto.
          { exploit Thread.rtc_tau_step_future; try exact STEPS1_TGT; eauto. s. i. des.
            inv SIM1. rewrite LOCAL.
            eapply rtc_tau_step_promise_consistent; eauto.
            inv FAILURE0; inv STEP0. inv LOCAL0. inv LOCAL1. ss. }
          i. des.
          inv SEM. ss. exploit TH; eauto. i.
          exploit rtc_all_aprogram_step_sem; try exact STEPS_SRC; eauto.
          { inv SIM3. ss. rewrite STATE0. eauto. }
          { eapply vals_incl_sem_memory; eauto.
            eapply PFStep.sim_memory_vals_incl; try eapply SIM3. }
          { eapply PFStep.sim_memory_inhabited; try eapply SIM3; ss.
            - apply WF1_SRC.
            - apply MEM. }
          i. des.
          exploit rtc_pf_step_sem; try exact STEPS_SRC2; eauto; s.
          { eapply vals_incl_sem_memory; eauto. }
          { eapply PFCertify.sim_memory_inhabited; try eapply SIM5.
            - apply WF0.
            - eapply Memory.cap_closed; eauto. }
          i. des.
          inv SIM6. rewrite STATE0 in *.
          eapply ASSERT; eauto.
        }
        exploit sim_thread_step; try exact SIM1; eauto. i. des; cycle 1.
        { exfalso.
          exploit Thread.tau_opt_all; try exact STEPS_SRC; eauto. i.
          exploit (@PFStep.sim_thread_exists lang (Thread.mk lang st_src lc_src sc1 mem1)); ss; eauto. i. des.
          exploit PFStep.thread_rtc_all_step; try exact x2; eauto.
          { hexploit consistent_promise_consistent; eauto. }
          i. des.
          exploit PFCertify.sim_thread_exists; try exact SIM4; eauto. s. i. des.
          exploit PFCertify.thread_rtc_tau_step; try exact STEPS_SRC0; eauto.
          { exploit Thread.rtc_tau_step_future; try exact STEPS0; eauto. s. i. des.
            inv SIM1. rewrite LOCAL.
            eapply rtc_tau_step_promise_consistent; eauto.
            inv FAILURE0; inv STEP0. inv LOCAL0. inv LOCAL1. ss. }
          i. des.
          inv SEM. ss. exploit TH; eauto. i.
          exploit rtc_all_aprogram_step_sem; try exact STEPS_SRC; eauto.
          { inv SIM3. ss. rewrite STATE0. eauto. }
          { eapply vals_incl_sem_memory; eauto.
            eapply PFStep.sim_memory_vals_incl; try eapply SIM3. }
          { eapply PFStep.sim_memory_inhabited; try eapply SIM3; ss.
            - apply WF1_SRC.
            - apply MEM. }
          i. des.
          exploit rtc_pf_step_sem; try exact STEPS_SRC2; eauto; s.
          { eapply vals_incl_sem_memory; eauto. }
          { eapply PFCertify.sim_memory_inhabited; try eapply SIM5.
            - apply WF0.
            - eapply Memory.cap_closed; eauto. }
          i. des.
          inv SIM6. rewrite STATE0 in *.
          eapply ASSERT; eauto.
        }
        inv STEP_SRC0. destruct pf0; try by (inv STEP0; inv STEP1).
        esplits; eauto.
      - (* normal certification *)
        right.
        exploit (@sim_thread_rtc_tau_step tid (Thread.mk lang state lc3 sc0 mem0));
          try exact STEPS0; eauto. i. des; cycle 1.
        { exfalso.
          exploit Thread.tau_opt_all; try exact STEPS_SRC; eauto. i.
          exploit (@PFStep.sim_thread_exists lang (Thread.mk lang st_src lc_src sc1 mem1)); ss; eauto. i. des.
          exploit PFStep.thread_rtc_all_step; try exact x2; eauto.
          { hexploit consistent_promise_consistent; eauto. }
          i. des.
          exploit PFCertify.sim_thread_exists; try exact SIM4; eauto. s. i. des.
          exploit PFCertify.thread_rtc_tau_step; try exact STEPS_SRC0; eauto.
          { exploit Thread.rtc_tau_step_future; try exact STEPS1_TGT; eauto. s. i. des.
            inv SIM1. rewrite LOCAL.
            eapply rtc_tau_step_promise_consistent; eauto.
            eapply Local.bot_promise_consistent; eauto. }
          i. des.
          inv SEM. ss. exploit TH; eauto. i.
          exploit rtc_all_aprogram_step_sem; try exact STEPS_SRC; eauto.
          { inv SIM3. ss. rewrite STATE0. eauto. }
          { eapply vals_incl_sem_memory; eauto.
            eapply PFStep.sim_memory_vals_incl; try eapply SIM3. }
          { eapply PFStep.sim_memory_inhabited; try eapply SIM3; ss.
            - apply WF1_SRC.
            - apply MEM. }
          i. des.
          exploit rtc_pf_step_sem; try exact STEPS_SRC2; eauto; s.
          { eapply vals_incl_sem_memory; eauto. }
          { eapply PFCertify.sim_memory_inhabited; try eapply SIM5.
            - apply WF0.
            - eapply Memory.cap_closed; eauto. }
          i. des.
          inv SIM6. rewrite STATE0 in *.
          eapply ASSERT; eauto.
        }
        esplits; eauto.
        inv SIM1. rewrite LOCAL. ss.
    }
    assert (CSTEP: Configuration.opt_step
                     (ThreadEvent.get_machine_event e0) tid
                     (Configuration.mk ths1_src sc1 mem1)
                     (Configuration.mk
                        (IdentMap.add tid (existT (fun (lang: language) => (Language.state lang)) lang state, local) ths1_src)
                        sc memory)).
    { inv STEP_SRC.
      - generalize (rtc_tail STEPS_SRC). i. des.
        + inv H0. inv TSTEP. ss. rewrite <- EVENT0.
          econs 2. econs; try exact x; try exact H; eauto.
          destruct e; ss.
        + inv H. ss.
          replace (IdentMap.add
                     tid
                     (existT (fun lang:language => (Language.state lang)) lang state, local)
                     ths1_src)
            with ths1_src; eauto.
          apply IdentMap.eq_leibniz. ii.
          rewrite -> IdentMap.gsident; auto.
      - econs 2. econs 2; try exact x; try exact H; eauto.
    }
    esplits; eauto.
    right. apply CIH. econs; ss; try by (inv SIM0; ss).
    - inv CSTEP; ss.
      + repeat rewrite <- H. ss.
      + eapply configuration_step_sem; try exact STEP0; eauto.
    - repeat rewrite Threads.tids_add.
      repeat rewrite IdentSet.add_mem; ss.
      + rewrite Threads.tids_o. rewrite TID. ss.
      + rewrite Threads.tids_o. rewrite x. ss.
    - i. revert FIND. rewrite IdentMap.gsspec. condtac; ss; i.
      + inv FIND. ss.
      + inv SIM. eapply FIND_SRC; eauto.
    - i. revert FIND. rewrite IdentMap.gsspec. condtac; ss; i.
      + inv FIND. ss.
      + inv SIM. eapply FIND_TGT; eauto.
    - i. revert FIND_SRC. rewrite IdentMap.gsspec. condtac; ss; i.
      + subst. revert FIND_TGT. rewrite IdentMap.gsspec. condtac; ss; i.
        Configuration.simplify2. inv SIM0. ss.
      + revert FIND_TGT. rewrite IdentMap.gsspec. condtac; ss; i.
        inv SIM. eauto.
  Qed.


  (* assert insertion *)

  Definition syntax_tids (pgm: Threads.syntax): IdentSet.t :=
    List.fold_right (fun p s => IdentSet.add (fst p) s) IdentSet.empty (IdentMap.elements pgm).

  Lemma syntax_tids_o tid pgm:
    IdentSet.mem tid (syntax_tids pgm) = IdentMap.find tid pgm.
  Proof.
    unfold syntax_tids. rewrite IdentMap.Facts.elements_o.
    induction (IdentMap.elements pgm); ss. destruct a. s.
    rewrite IdentSet.Facts.add_b, IHl.
    unfold IdentSet.Facts.eqb, IdentMap.Facts.eqb.
    repeat match goal with
           | [|- context[if ?c then true else false]] => destruct c
           end; ss; congr.
  Qed.

  Inductive insert_assertion_program (program_tgt: Threads.syntax): Prop :=
  | insert_assertion_program_intro
      (TIDS: syntax_tids program_tgt = syntax_tids program)
      (FIND_SRC: forall tid l syn_src
                   (FIND: IdentMap.find tid program = Some (existT _ l syn_src)),
          l = lang)
      (FIND_TGT: forall tid l syn_tgt
                   (FIND: IdentMap.find tid program_tgt = Some (existT _ l syn_tgt)),
          l = lang)
      (THREADS: forall tid syn_src syn_tgt
                  (FIND_SRC: IdentMap.find tid program = Some (existT _ lang syn_src))
                  (FIND_TGT: IdentMap.find tid program_tgt = Some (existT _ lang syn_tgt)),
          insert_assertion tid syn_src syn_tgt)
  .

  Lemma init_sim_conf
        program_tgt
        (INSERT: insert_assertion_program program_tgt):
    sim_conf (Configuration.init program) (Configuration.init program_tgt).
  Proof.
    inv INSERT. econs; ss; i.
    - apply init_sem; ss.
    - apply IdentSet.ext. i.
      repeat rewrite Threads.tids_o.
      unfold Threads.init.
      repeat rewrite IdentMap.Facts.map_o.
      specialize (@syntax_tids_o i program). i.
      specialize (@syntax_tids_o i program_tgt). i.
      destruct (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) i program) eqn:SRC;
        destruct (@UsualFMapPositive.UsualPositiveMap'.find
                    (@sigT _ (@Language.syntax ProgramEvent.t)) i program_tgt) eqn:TGT; ss.
      + assert (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) i program = IdentMap.find i program) by ss.
        rewrite <- H1 in *. rewrite SRC in *. ss.
        assert (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) i program_tgt = IdentMap.find i program_tgt) by ss.
        rewrite <- H2 in *. rewrite TGT in *. ss.
        rewrite TIDS in *. congr.
      + assert (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) i program = IdentMap.find i program) by ss.
        rewrite <- H1 in *. rewrite SRC in *. ss.
        assert (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) i program_tgt = IdentMap.find i program_tgt) by ss.
        rewrite <- H2 in *. rewrite TGT in *. ss.
        rewrite TIDS in *. congr.
    - unfold Threads.init in *.
      rewrite IdentMap.Facts.map_o in *.
      destruct (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) tid program) eqn:SRC; ss.
      destruct s. ss. inv FIND. eapply FIND_SRC; eauto.
    - unfold Threads.init in *.
      rewrite IdentMap.Facts.map_o in *.
      destruct (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) tid program_tgt) eqn:SRC; ss.
      destruct s. ss. inv FIND. eapply FIND_TGT; eauto.
    - unfold Threads.init in *.
      rewrite IdentMap.Facts.map_o in *.
      destruct (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) tid program) eqn:SRC;
        destruct (@UsualFMapPositive.UsualPositiveMap'.find
                    (@sigT _ (@Language.syntax ProgramEvent.t)) tid program_tgt) eqn:TGT; ss.
      destruct s, s0; ss.
      inv FIND_SRC0. inv FIND_TGT0. split; ss. Configuration.simplify2.
      unfold State.init. econs; ss.
      eapply THREADS; eauto.
  Qed.

  Theorem insert_assertion_behavior
          program_tgt
          (INSERT: insert_assertion_program program_tgt):
    behaviors Configuration.step (Configuration.init program_tgt) <1=
    behaviors Configuration.step (Configuration.init program).
  Proof.
    exploit init_sim_conf; eauto. i.
    specialize (Configuration.init_wf program). intro WF_SRC.
    specialize (Configuration.init_wf program_tgt). intro WF_TGT.
    hexploit sim_conf_sim; eauto. i.
    exploit sim_adequacy; try exact H; eauto.
  Qed.
End AssertInsertion.
