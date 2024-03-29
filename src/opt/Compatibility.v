Require Import Bool.
Require Import List.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
Require Import Event.
Require Import Time.
From PromisingLib Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import FulfillStep.
Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import SimThread.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Definition SIM_REGS := forall (rs_src rs_tgt:RegFile.t), Prop.

Inductive sim_terminal
          (sim_regs:SIM_REGS)
          (st_src:(Language.state lang)) (st_tgt:(Language.state lang)): Prop :=
| sim_terminal_intro
    (REGS: sim_regs (State.regs st_src) (State.regs st_tgt))
.

Definition sim_expr
           (sim_regs:SIM_REGS)
           e_src e_tgt :=
  forall rs_src rs_tgt (RS: sim_regs rs_src rs_tgt),
    RegFile.eval_expr rs_src e_src = RegFile.eval_expr rs_tgt e_tgt.

Definition _sim_stmts
           (sim_thread:SIM_THREAD lang lang)
           (sim_regs0:SIM_REGS)
           (stmts_src stmts_tgt:list Stmt.t)
           (sim_regs1:SIM_REGS): Prop :=
  forall rs_src rs_tgt lc_src lc_tgt sc0_src sc0_tgt mem0_src mem0_tgt
    (RS: sim_regs0 rs_src rs_tgt)
    (LOCAL: sim_local SimPromises.bot lc_src lc_tgt),
    sim_thread
      (sim_terminal sim_regs1)
      (State.mk rs_src stmts_src) lc_src sc0_src mem0_src
      (State.mk rs_tgt stmts_tgt) lc_tgt sc0_tgt mem0_tgt.

Lemma _sim_stmts_mon
      s1 s2 (S: s1 <9= s2):
  _sim_stmts s1 <4= _sim_stmts s2.
Proof.
  ii. apply S. apply PR; auto.
Qed.

Lemma lang_step_seq
      stmts rs1 stmts1 rs2 stmts2 e
      (STEP: State.step e
                        (State.mk rs1 stmts1)
                        (State.mk rs2 stmts2)):
  State.step e
             (State.mk rs1 (stmts1 ++ stmts))
             (State.mk rs2 (stmts2 ++ stmts)).
Proof.
  inv STEP.
  - econs 1. auto.
  - s. rewrite <- app_assoc. econs 2.
  - s. rewrite <- app_assoc. econs 3.
Qed.

Lemma lang_step_deseq
      stmts rs1 stmt1 stmts1 rs2 stmts2 e
      (STEP: State.step e
                        (State.mk rs1 (stmt1 :: stmts1 ++ stmts))
                        (State.mk rs2 stmts2)):
  exists stmts2',
    stmts2 = stmts2' ++ stmts /\
    State.step e
               (State.mk rs1 (stmt1 :: stmts1))
               (State.mk rs2 stmts2').
Proof.
  inv STEP.
  - esplits; eauto. econs; eauto.
  - eexists. rewrite app_assoc. splits; eauto. econs.
  - eexists. rewrite app_comm_cons, app_assoc. splits; eauto. econs.
Qed.

Lemma program_step_seq
      stmts e
      rs1 stmts1 lc1 sc1 mem1
      rs2 stmts2 lc2 sc2 mem2
      (STEP: Thread.program_step
               e
               (Thread.mk lang (State.mk rs1 stmts1) lc1 sc1 mem1)
               (Thread.mk lang (State.mk rs2 stmts2) lc2 sc2 mem2)):
  Thread.program_step
    e
    (Thread.mk lang (State.mk rs1 (stmts1 ++ stmts)) lc1 sc1 mem1)
    (Thread.mk lang (State.mk rs2 (stmts2 ++ stmts)) lc2 sc2 mem2).
Proof.
  inv STEP; inv LOCAL; ss.
  - econs; [|econs 1]; s; eauto. apply lang_step_seq. auto.
  - econs; [|econs 2]; s; eauto. apply lang_step_seq. auto.
  - econs; [|econs 3]; s; eauto. apply lang_step_seq. auto.
  - econs; [|econs 4]; s; eauto. apply lang_step_seq. auto.
  - econs; [|econs 5]; s; eauto. apply lang_step_seq. auto.
  - econs; [|econs 6]; s; eauto. apply lang_step_seq. auto.
  - econs; [|econs 7]; s; eauto. apply lang_step_seq. auto.
Qed.

Lemma step_seq
      stmts pf e
      rs1 stmts1 lc1 sc1 mem1
      rs2 stmts2 lc2 sc2 mem2
      (STEP: Thread.step pf e
                         (Thread.mk lang (State.mk rs1 stmts1) lc1 sc1 mem1)
                         (Thread.mk lang (State.mk rs2 stmts2) lc2 sc2 mem2)):
  Thread.step pf e
              (Thread.mk lang (State.mk rs1 (stmts1 ++ stmts)) lc1 sc1 mem1)
              (Thread.mk lang (State.mk rs2 (stmts2 ++ stmts)) lc2 sc2 mem2).
Proof.
  inv STEP.
  - econs 1. inv STEP0. econs; eauto.
  - econs 2. apply program_step_seq. eauto.
Qed.

Lemma opt_step_seq
      stmts e
      rs1 stmts1 lc1 sc1 mem1
      rs2 stmts2 lc2 sc2 mem2
      (STEP: Thread.opt_step e
                             (Thread.mk lang (State.mk rs1 stmts1) lc1 sc1 mem1)
                             (Thread.mk lang (State.mk rs2 stmts2) lc2 sc2 mem2)):
  Thread.opt_step e
                  (Thread.mk lang (State.mk rs1 (stmts1 ++ stmts)) lc1 sc1 mem1)
                  (Thread.mk lang (State.mk rs2 (stmts2 ++ stmts)) lc2 sc2 mem2).
Proof.
  inv STEP.
  - econs 1.
  - econs 2. apply step_seq. eauto.
Qed.

Lemma thread_step_deseq
      stmts pf e
      rs1 stmt1 stmts1 lc1 sc1 mem1
      rs2 stmts2 lc2 sc2 mem2
      (STEP: Thread.step pf e
                         (Thread.mk lang (State.mk rs1 (stmt1 :: stmts1 ++ stmts)) lc1 sc1 mem1)
                         (Thread.mk lang (State.mk rs2 stmts2) lc2 sc2 mem2)):
  exists stmts2',
    stmts2 = stmts2' ++ stmts /\
  Thread.step pf e
              (Thread.mk lang (State.mk rs1 (stmt1 :: stmts1)) lc1 sc1 mem1)
              (Thread.mk lang (State.mk rs2 stmts2') lc2 sc2 mem2).
Proof.
  inv STEP.
  - inv STEP0.
    rewrite app_comm_cons.
    esplits; eauto.
    econs 1. econs; eauto.
  - inv STEP0; ss.
    apply lang_step_deseq in STATE. des. subst.
    esplits; eauto. econs 2. econs; eauto.
Qed.

Lemma sim_rtc
      A B
      (sim:A -> B -> Prop)
      (rA:A -> A -> Prop)
      (rB:B -> B -> Prop)
      (SIM:
         forall a1 a2 b1 (RA: rA a1 a2) (SIM1: sim a1 b1),
         exists b2, rB b1 b2 /\ sim a2 b2)
      a1 a2 b1
      (RA: rtc rA a1 a2) (SIM1: sim a1 b1):
  exists b2, rtc rB b1 b2 /\ sim a2 b2.
Proof.
  revert b1 SIM1. induction RA; i.
  - esplits; eauto.
  - exploit SIM; eauto. i. des.
    exploit IHRA; eauto. i. des.
    esplits; [|eauto].
    econs; eauto.
Qed.

Inductive sim_seq (s:list Stmt.t): forall (lhs rhs:Thread.t lang), Prop :=
| sim_seq_intro
    rs stmts lc sc mem:
    sim_seq s
            (Thread.mk lang (State.mk rs stmts) lc sc mem)
            (Thread.mk lang (State.mk rs (stmts ++ s)) lc sc mem)
.

Lemma rtc_internal_step_seq
      stmts
      rs1 stmts1 lc1 sc1 mem1
      rs2 stmts2 lc2 sc2 mem2
      (STEP: rtc (@Thread.tau_step lang)
                 (Thread.mk lang (State.mk rs1 stmts1) lc1 sc1 mem1)
                 (Thread.mk lang (State.mk rs2 stmts2) lc2 sc2 mem2)):
  rtc (@Thread.tau_step lang)
      (Thread.mk lang (State.mk rs1 (stmts1 ++ stmts)) lc1 sc1 mem1)
      (Thread.mk lang (State.mk rs2 (stmts2 ++ stmts)) lc2 sc2 mem2).
Proof.
  exploit (sim_rtc (sim_seq stmts)); eauto.
  - i. inv SIM1. destruct a2. destruct state. destruct local. inv RA. inv TSTEP.
    generalize (step_seq stmts STEP0). i.
    esplits; [|econs; eauto].
    eapply tau_intro; eauto. eapply Thread.step_nopf_intro. eauto.
  - econs; ss.
  - i. des. inv x1. auto.
Qed.

Inductive ctx (sim_thread:SIM_THREAD lang lang): SIM_THREAD lang lang :=
| ctx_incl
    sim_terminal
    st1 lc1 sc0_src mem0_src st2 lc2 sc0_tgt mem0_tgt
    (SIM: sim_thread sim_terminal st1 lc1 sc0_src mem0_src st2 lc2 sc0_tgt mem0_tgt):
    ctx sim_thread sim_terminal st1 lc1 sc0_src mem0_src st2 lc2 sc0_tgt mem0_tgt
| ctx_nil
    (sim_regs:SIM_REGS)
    rs_src sc0_src mem0_src
    rs_tgt sc0_tgt mem0_tgt
    lc_src lc_tgt
    (RS: sim_regs rs_src rs_tgt)
    (LOCAL: sim_local SimPromises.bot lc_src lc_tgt):
    ctx sim_thread
        (sim_terminal sim_regs)
        (State.mk rs_src []) lc_src sc0_src mem0_src
        (State.mk rs_tgt []) lc_tgt sc0_tgt mem0_tgt
| ctx_seq
    sim_regs1 sim_regs2
    stmts1_src stmts2_src rs_src lc_src sc0_src mem0_src
    stmts1_tgt stmts2_tgt rs_tgt lc_tgt sc0_tgt mem0_tgt
    (SIM1: sim_thread (sim_terminal sim_regs1)
                      (State.mk rs_src stmts1_src) lc_src sc0_src mem0_src
                      (State.mk rs_tgt stmts1_tgt) lc_tgt sc0_tgt mem0_tgt)
    (SIM2: _sim_stmts sim_thread sim_regs1 stmts2_src stmts2_tgt sim_regs2):
    ctx sim_thread
        (sim_terminal sim_regs2)
        (State.mk rs_src (stmts1_src ++ stmts2_src)) lc_src sc0_src mem0_src
        (State.mk rs_tgt (stmts1_tgt ++ stmts2_tgt)) lc_tgt sc0_tgt mem0_tgt
| ctx_ite
    sim_regs0 sim_regs1
    cond_src stmts1_src stmts2_src rs_src sc0_src mem0_src
    cond_tgt stmts1_tgt stmts2_tgt rs_tgt sc0_tgt mem0_tgt
    lc_src lc_tgt
    (COND: sim_expr sim_regs0 cond_src cond_tgt)
    (RS: sim_regs0 rs_src rs_tgt)
    (LOCAL: sim_local SimPromises.bot lc_src lc_tgt)
    (SIM1: _sim_stmts sim_thread sim_regs0 stmts1_src stmts1_tgt sim_regs1)
    (SIM2: _sim_stmts sim_thread sim_regs0 stmts2_src stmts2_tgt sim_regs1):
    ctx sim_thread
        (sim_terminal sim_regs1)
        (State.mk rs_src [Stmt.ite cond_src stmts1_src stmts2_src]) lc_src sc0_src mem0_src
        (State.mk rs_tgt [Stmt.ite cond_tgt stmts1_tgt stmts2_tgt]) lc_tgt sc0_tgt mem0_tgt
| ctx_dowhile
    sim_regs
    cond_src stmts_src rs_src sc0_src mem0_src
    cond_tgt stmts_tgt rs_tgt sc0_tgt mem0_tgt
    lc_src lc_tgt
    (COND: sim_expr sim_regs cond_src cond_tgt)
    (RS: sim_regs rs_src rs_tgt)
    (LOCAL: sim_local SimPromises.bot lc_src lc_tgt)
    (SIM: _sim_stmts sim_thread sim_regs stmts_src stmts_tgt sim_regs):
    ctx sim_thread
        (sim_terminal sim_regs)
        (State.mk rs_src [Stmt.dowhile stmts_src cond_src]) lc_src sc0_src mem0_src
        (State.mk rs_tgt [Stmt.dowhile stmts_tgt cond_tgt]) lc_tgt sc0_tgt mem0_tgt
.
#[export]
Hint Constructors ctx: core.

Lemma ctx_mon: monotone9 ctx.
Proof.
  ii. inv IN.
  - econs 1. auto.
  - econs 2; auto.
  - econs 3; eauto; eapply _sim_stmts_mon; eauto.
  - econs 4; eauto; eapply _sim_stmts_mon; eauto.
  - econs 5; eauto; eapply _sim_stmts_mon; eauto.
Qed.
#[export]
Hint Resolve ctx_mon: core.


Lemma ctx_wcompat: wcompatible9 (@_sim_thread lang lang) ctx.
Proof.
  assert (MON: monotone9 (@_sim_thread lang lang)).
  (* paco tactics do not work well without this *)
  { eapply _sim_thread_mon; eauto. }
  econs; auto. i. destruct PR.
  - (* incl *)
    eapply _sim_thread_mon; eauto.
    i. gbase. auto.
  - (* nil *)
    ii.
    inversion LOCAL. apply SimPromises.sem_bot_inv in PROMISES; auto.
    destruct lc_src, lc_tgt. ss. subst.
    splits; s; ii.
    { right. inv TERMINAL_TGT. ss. esplits; eauto; ss. }
    { exploit SimPromises.cap; try eapply LOCAL; eauto. }
    { right. subst. esplits; eauto. }
    inv STEP_TGT; try by inv STEP; inv STATE.
    inv STEP; ss.
    exploit sim_local_promise; eauto. i. des.
    right. esplits.
    + ss.
    + eauto.
    + econs 2. econs 1. econs; eauto.
    + eauto.
    + eauto.
    + eauto.
    + gclo. eapply ctx_nil; auto.
  - (* seq *)
    ii. ss.
    exploit SIM1; try apply SC; eauto. i. des.
    splits; s; ii.
    { inv TERMINAL_TGT. destruct stmts1_tgt, stmts2_tgt; inv H0.
      exploit TERMINAL; try by econs. i. des.
      - left.
        unfold Thread.steps_failure in *. des.
        destruct e2, e3, state, state0.
        eapply rtc_internal_step_seq in STEPS.
        eapply step_seq in FAILURE0.
        esplits; eauto.
      - inversion LOCAL. exploit SimPromises.sem_bot_inv; eauto. i.
        destruct lc2_src. ss. subst.
        destruct st2_src. inv TERMINAL_SRC. ss. subst.
        exploit Thread.rtc_tau_step_future; eauto. s. i. des.
        inv TERMINAL0. ss.
        exploit SIM2; try apply SC0; eauto. s. i. des.
        eauto using Memory.future_future_weak.
        s. i. des.
        exploit TERMINAL0; try by econs. i. des.
        + left.
          unfold Thread.steps_failure in *. des.
          destruct e2, state.
          esplits; [|eauto].
          etrans; try exact STEPS0.
          eapply rtc_internal_step_seq in STEPS. eauto.
        + right.
          destruct st2_src, lc2_src. inv TERMINAL_SRC. ss. subst.
          esplits; cycle 1; eauto.
          * econs.
          * etrans; [|eauto].
            eapply rtc_internal_step_seq in STEPS. eauto.
    }
    { eapply CAP; eauto. }
    { exploit PROMISES; eauto. i. des.
      - left.
        unfold Thread.steps_failure in *. des.
        destruct e2, e3, state, state0.
        eapply rtc_internal_step_seq in STEPS.
        eapply step_seq in FAILURE0.
        esplits; eauto.
      - right.
        destruct lc_tgt, st2_src, lc2_src. ss. subst.
        esplits; [|eauto].
        + eapply rtc_internal_step_seq. apply STEPS.
        + ss.
    }
    destruct stmts1_tgt.
    + exploit TERMINAL; try by econs. i. des.
      * left.
        unfold Thread.steps_failure in *. des.
        destruct e2, e3, state, state0. ss.
        eapply rtc_internal_step_seq in STEPS.
        eapply step_seq in FAILURE0.
        esplits; eauto.
      * inversion LOCAL. exploit SimPromises.sem_bot_inv; eauto. i. subst.
        destruct st2_src, lc2_src. inv TERMINAL_SRC. ss. subst.
        exploit Thread.rtc_tau_step_future; eauto. s. i. des.
        inv TERMINAL0. ss. subst.
        exploit SIM2; try apply SC0; eauto using Memory.future_future_weak. i. des.
        exploit STEP0; eauto. i. des.
        { left.
          unfold Thread.steps_failure in *. des.
          destruct e2, e3, state, state0.
          eapply rtc_internal_step_seq in STEPS.
          esplits; try exact FAILURE0.
          etrans; eauto. }
        { right.
          esplits; cycle 2; eauto.
          - gbase. auto.
          - eapply rtc_internal_step_seq in STEPS.
            etrans; [apply STEPS|eauto]. }
    + destruct st3_tgt, lc3_tgt.
      exploit thread_step_deseq; eauto. i. des. ss. subst.
      exploit STEP; eauto. i. des.
      * left.
        unfold Thread.steps_failure in *. des.
        destruct e2, e3, state, state0.
        eapply rtc_internal_step_seq in STEPS.
        eapply step_seq in FAILURE0.
        esplits; eauto.
      * right.
        destruct st2_src, lc2_src. destruct st3_src, lc3_src.
        esplits; [|M|M| | | |]; Mskip eauto.
        { eapply rtc_internal_step_seq. eauto. }
        { eapply opt_step_seq. eauto. }
        { gclo. eapply ctx_seq; eauto.
          - gbase. eauto.
          - eapply _sim_stmts_mon; cycle 1; eauto.
            i. gstep. eapply _sim_thread_mon; eauto. i. gbase. auto.
        }
  - (* ite *)
    ii.
    inversion LOCAL. exploit SimPromises.sem_bot_inv; eauto. i.
    destruct lc_src, lc_tgt. ss. subst.
    splits; s; ii.
    { inv TERMINAL_TGT. }
    { exploit SimPromises.cap; try apply LOCAL; eauto. }
    { right. subst. esplits; eauto. }
    right. inv STEP_TGT; ss.
    + (* promise *)
      inv STEP; ss.
      exploit sim_local_promise; eauto. i. des.
      esplits; try apply SC; eauto; ss.
      { econs 2. econs 1. econs; eauto. }
      { eauto. }
      { gclo. eapply ctx_ite; eauto.
        - eapply _sim_stmts_mon; cycle 1; eauto.
          i. gstep. eapply _sim_thread_mon; eauto. i. gbase. auto.
        - eapply _sim_stmts_mon; cycle 1; eauto.
          i. gstep. eapply _sim_thread_mon; eauto. i. gbase. auto.
      }
    + (* ite *)
      inv STEP. inv LOCAL0; inv STATE; ss.
      inv LOCAL. ss.
      esplits; try apply MEMORY; try apply SC; eauto; ss.
      { econs 2. econs 2. econs; [|econs 1]; eauto. econs; eauto. }
      { eauto. }
      { s. rewrite ? app_nil_r.
        exploit COND; eauto. intro C. rewrite C.
        destruct (RegFile.eval_expr rs_tgt cond_tgt).
        - gstep. eapply _sim_thread_mon; try apply SIM1; ss. i. gbase. auto.
        - gstep. eapply _sim_thread_mon; try apply SIM2; ss. i. gbase. auto.
      }
  - (* dowhile *)
    ii.
    inversion LOCAL. exploit SimPromises.sem_bot_inv; eauto. i.
    destruct lc_src, lc_tgt. ss. subst.
    splits; s; ii.
    { inv TERMINAL_TGT. }
    { exploit SimPromises.cap; try apply LOCAL; eauto. }
    { right. subst. esplits; eauto. }
    right. inv STEP_TGT; ss.
    + (* promise *)
      inv STEP; ss.
      exploit sim_local_promise; eauto. i. des.
      esplits; try apply SC; eauto; ss.
      { econs 2. econs 1. econs; eauto. }
      { eauto. }
      { gclo. eapply ctx_dowhile; eauto.
        eapply _sim_stmts_mon; cycle 1; eauto.
        i. gstep. eapply _sim_thread_mon; eauto. i. gbase. auto.
      }
    + (* dowhile *)
      inv STEP. inv LOCAL0; inv STATE; ss.
      inv LOCAL. ss.
      esplits; try apply SC; eauto; ss.
      { econs 2. econs 2. econs; [|econs 1]; eauto. econs; eauto. }
      { eauto. }
      { gclo. eapply ctx_seq; eauto.
        { gstep. eapply _sim_thread_mon; try apply SIM; ss. i. gbase. auto. }
        ii. gclo. eapply ctx_ite; eauto.
        - ii. gclo. eapply ctx_dowhile; eauto.
          eapply _sim_stmts_mon; cycle 1; eauto.
          i. gstep. eapply _sim_thread_mon; eauto. i. gbase. auto.
        - ii. gclo; auto.
      }
Qed.

Definition sim_stmts := @_sim_stmts (@sim_thread lang lang).

Lemma sim_stmts_frame
      sim_regs0 sim_regs1
      sim_regs2 sim_regs3
      stmts_src stmts_tgt
      (SIM01: sim_regs0 <2= sim_regs1)
      (SIM23: sim_regs2 <2= sim_regs3)
      (SIM: sim_stmts sim_regs1 stmts_src stmts_tgt sim_regs2):
  sim_stmts sim_regs0 stmts_src stmts_tgt sim_regs3.
Proof.
  ii. eapply sim_thread_mon; [|eauto].
  i. inv PR. econs; eauto.
Qed.

Lemma sim_stmts_nil sim_regs:
  sim_stmts sim_regs [] [] sim_regs.
Proof.
  ii. ginit; [apply ctx_wcompat|]. gclo. eauto.
Qed.

Lemma sim_stmts_seq
      sim_regs0 sim_regs1 sim_regs2
      stmts1_src stmts2_src
      stmts1_tgt stmts2_tgt
      (SIM1: sim_stmts sim_regs0 stmts1_src stmts1_tgt sim_regs1)
      (SIM2: sim_stmts sim_regs1 stmts2_src stmts2_tgt sim_regs2):
  sim_stmts sim_regs0 (stmts1_src ++ stmts2_src) (stmts1_tgt ++ stmts2_tgt) sim_regs2.
Proof.
  ii. ginit; [apply ctx_wcompat|].
  gclo. econs 3.
  - gfinal. right. apply SIM1; auto.
  - ii. gfinal. right. apply SIM2; auto.
Qed.

Lemma sim_stmts_ite
      sim_regs0 sim_regs1
      cond_src stmts1_src stmts2_src
      cond_tgt stmts1_tgt stmts2_tgt
      (COND: sim_expr sim_regs0 cond_src cond_tgt)
      (SIM1: sim_stmts sim_regs0 stmts1_src stmts1_tgt sim_regs1)
      (SIM2: sim_stmts sim_regs0 stmts2_src stmts2_tgt sim_regs1):
  sim_stmts sim_regs0 [Stmt.ite cond_src stmts1_src stmts2_src] [Stmt.ite cond_tgt stmts1_tgt stmts2_tgt] sim_regs1.
Proof.
  ii. ginit; [apply ctx_wcompat|].
  gclo. econs 4; eauto.
  - ii. gfinal. right. apply SIM1; auto.
  - ii. gfinal. right. apply SIM2; auto.
Qed.

Lemma sim_stmts_dowhile
      sim_regs
      cond_src stmts_src
      cond_tgt stmts_tgt
      (COND: sim_expr sim_regs cond_src cond_tgt)
      (SIM: sim_stmts sim_regs stmts_src stmts_tgt sim_regs):
  sim_stmts sim_regs [Stmt.dowhile stmts_src cond_src] [Stmt.dowhile stmts_tgt cond_tgt] sim_regs.
Proof.
  ii. ginit; [apply ctx_wcompat|].
  gclo. econs 5; eauto. ii. gfinal. right. apply SIM; auto.
Qed.
