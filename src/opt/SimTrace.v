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
Require Import Compatibility.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.

Definition lang_steps_failure (st1: State.t): Prop :=
  exists st2 st3,
    <<STEPS: rtc ((Language.step lang) ProgramEvent.silent) st1 st2>> /\
    <<FAILURE: (Language.step lang) ProgramEvent.failure st2 st3>>.


Definition SIM_TRACE :=
  forall (sim_regs:SIM_REGS)
    (st1_src:(Language.state lang))
    (st1_tgt:(Language.state lang)), Prop.

Definition _sim_trace
           (sim_trace:SIM_TRACE)
           (sim_regs:SIM_REGS)
           (st1_src:(Language.state lang))
           (st1_tgt:(Language.state lang)): Prop :=
  <<TERMINAL:
    forall (TERMINAL_TGT: (Language.is_terminal lang) st1_tgt),
      <<FAILURE: lang_steps_failure st1_src>> \/
      exists st2_src,
        <<STEPS: rtc ((Language.step lang) ProgramEvent.silent) st1_src st2_src>> /\
        <<TERMINAL_SRC: (Language.is_terminal lang) st2_src>> /\
        <<TERMINAL: sim_regs (State.regs st2_src) (State.regs st1_tgt)>>>> /\
  <<STEP:
    forall e_tgt st3_tgt
      (STEP_TGT: (Language.step lang) e_tgt st1_tgt st3_tgt),
      <<FAILURE: lang_steps_failure st1_src>> \/
      exists e_src st2_src st3_src,
        <<EVT: ProgramEvent.ord e_src e_tgt>> /\
        <<STEPS: rtc ((Language.step lang) ProgramEvent.silent) st1_src st2_src>> /\
        <<STEP_SRC: State.opt_step e_src st2_src st3_src>> /\
        <<SIM: sim_trace sim_regs st3_src st3_tgt>>>>.

Lemma _sim_trace_mon: monotone3 _sim_trace.
Proof.
  ii. unfold _sim_trace in *. des; splits; ss.
  i. exploit STEP; eauto. i. des; eauto.
  right. esplits; eauto.
Qed.
#[export]
Hint Resolve _sim_trace_mon: paco.

Definition sim_trace: SIM_TRACE := paco3 _sim_trace bot3.

Lemma rtc_lang_tau_step_rtc_thread_tau_step
      st1 st2 lc sc mem
      (STEP: rtc ((Language.step lang) ProgramEvent.silent) st1 st2):
  rtc (@Thread.tau_step lang) (Thread.mk lang st1 lc sc mem) (Thread.mk lang st2 lc sc mem).
Proof.
  induction STEP.
  - econs 1.
  - econs 2; eauto. econs.
    + econs. econs 2. econs; [|econs 1]; eauto.
    + ss.
Qed.

Lemma sim_trace_sim_thread
      sim_regs
      st1_src lc1_src sc1_src mem1_src
      st1_tgt lc1_tgt sc1_tgt mem1_tgt
      (SIM: sim_trace sim_regs st1_src st1_tgt)
      (LOCAL: sim_local SimPromises.bot lc1_src lc1_tgt):
  sim_thread
    (sim_terminal sim_regs)
    st1_src lc1_src sc1_src mem1_src
    st1_tgt lc1_tgt sc1_tgt mem1_tgt.
Proof.
  revert_until sim_regs. pcofix CIH. i.
  generalize SIM. i. punfold SIM0. unfold _sim_trace in SIM0. des.
  pfold. ii. splits.
  - i. exploit TERMINAL; eauto. i. des.
    + left.
      unfold lang_steps_failure, Thread.steps_failure in *. des.
      exploit rtc_lang_tau_step_rtc_thread_tau_step; try exact STEPS. i.
      esplits; eauto.
      hexploit sim_local_promise_consistent; eauto. i. des.
      econs 2. econs; eauto.
    + right.
      exploit rtc_lang_tau_step_rtc_thread_tau_step; eauto. i.
      esplits; eauto. econs. ss.
  - i. exploit SimPromises.cap; try eapply LOCAL; eauto.
  - i. right.
    exploit sim_local_memory_bot; eauto. i.
    esplits; eauto.
  - ii. inv STEP_TGT; inv STEP0; [|inv LOCAL0].
    + right.
      exploit sim_local_promise_bot; eauto. i. des.
      esplits; (try exact SC); eauto; ss.
      econs 2. econs 1. econs; eauto.
    + exploit STEP; eauto. i. des.
      * left.
        unfold lang_steps_failure, Thread.steps_failure in *. des.
        exploit rtc_lang_tau_step_rtc_thread_tau_step; try exact STEPS. i.
        esplits; eauto.
        hexploit sim_local_promise_consistent; eauto. i. des.
        econs 2. econs; eauto.
      * right.
        inv SIM0; [|done].
        inv EVT. inv STEP_SRC.
        { esplits;
            (try by apply rtc_lang_tau_step_rtc_thread_tau_step; eauto);
            (try exact SC);
            eauto; ss.
          econs 1.
        }
        { esplits;
            (try by apply rtc_lang_tau_step_rtc_thread_tau_step; eauto);
            (try exact SC);
            eauto; ss.
          econs 2. econs 2. econs; [|econs 1]; eauto.
        }
    + exploit STEP; eauto. i. des.
      { left.
        unfold lang_steps_failure, Thread.steps_failure in *. des.
        exploit rtc_lang_tau_step_rtc_thread_tau_step; try exact STEPS. i.
        esplits; eauto.
        hexploit sim_local_promise_consistent; eauto. i. des.
        econs 2. econs; eauto. }
      right.
      inv SIM0; ss.
      inv EVT. inv STEP_SRC.
      exploit sim_local_read; eauto. i. des.
      esplits;
        (try by apply rtc_lang_tau_step_rtc_thread_tau_step; eauto);
        (try exact SC).
      * ss.
      * econs 2. econs 2. econs; [|econs 2]; eauto.
      * ss.
      * ss.
      * right. apply CIH; auto.
    + exploit STEP; eauto. i. des.
      { left.
        unfold lang_steps_failure, Thread.steps_failure in *. des.
        exploit rtc_lang_tau_step_rtc_thread_tau_step; try exact STEPS. i.
        esplits; eauto.
        hexploit sim_local_promise_consistent; eauto. i. des.
        econs 2. econs; eauto. }
      right.
      inv SIM0; [|done].
      inv EVT. inv STEP_SRC.
      hexploit sim_local_write_bot;
        (try exact LOCAL);
        (try exact SC);
        eauto; try refl; try by viewtac. i. des.
      esplits;
        (try by apply rtc_lang_tau_step_rtc_thread_tau_step; eauto);
        (try exact SC).
      * ss.
      * econs 2. econs 2. econs; [|econs 3]; eauto.
      * ss.
      * ss.
      * ss.
      * right. apply CIH; auto.
    + exploit STEP; eauto. i. des.
      { left.
        unfold lang_steps_failure, Thread.steps_failure in *. des.
        exploit rtc_lang_tau_step_rtc_thread_tau_step; try exact STEPS. i.
        esplits; eauto.
        hexploit sim_local_promise_consistent; eauto. i. des.
        econs 2. econs; eauto. }
      right.
      inv SIM0; [|done].
      inv EVT. inv STEP_SRC.
      exploit Local.read_step_future; eauto. i. des.
      exploit sim_local_read; eauto; try refl. i. des.
      exploit Local.read_step_future; eauto. i. des.
      hexploit sim_local_write_bot;
        (try exact LOCAL0);
        (try exact SC);
        eauto; try refl; try by viewtac. i. des.
      esplits;
        (try by apply rtc_lang_tau_step_rtc_thread_tau_step; eauto);
        (try exact SC).
      * ss.
      * econs 2. econs 2. econs; [|econs 4]; eauto.
      * ss.
      * ss.
      * ss.
      * right. apply CIH; auto.
    + exploit STEP; eauto. i. des.
      { left.
        unfold lang_steps_failure, Thread.steps_failure in *. des.
        exploit rtc_lang_tau_step_rtc_thread_tau_step; try exact STEPS. i.
        esplits; eauto.
        hexploit sim_local_promise_consistent; eauto. i. des.
        econs 2. econs; eauto. }
      right.
      inv SIM0; [|done].
      inv EVT. inv STEP_SRC.
      exploit sim_local_fence;
        (try exact LOCAL);
        (try exact SC);
        eauto; try refl. i. des.
      esplits;
        (try by apply rtc_lang_tau_step_rtc_thread_tau_step; eauto);
        (try exact SC).
      * ss.
      * econs 2. econs 2. econs; [|econs 5]; eauto.
      * ss.
      * ss.
      * ss.
      * right. apply CIH; auto.
    + exploit STEP; eauto. i. des.
      { left.
        unfold lang_steps_failure, Thread.steps_failure in *. des.
        exploit rtc_lang_tau_step_rtc_thread_tau_step; try exact STEPS. i.
        esplits; eauto.
        hexploit sim_local_promise_consistent; eauto. i. des.
        econs 2. econs; eauto. }
      right.
      inv SIM0; [|done].
      inv EVT. inv STEP_SRC.
      exploit sim_local_fence;
        (try exact LOCAL);
        (try exact SC);
        eauto; try refl. i. des.
      esplits;
        (try by apply rtc_lang_tau_step_rtc_thread_tau_step; eauto);
        (try exact SC).
      * ss.
      * econs 2. econs 2. econs; [|econs 6]; eauto.
      * ss.
      * ss.
      * ss.
      * right. apply CIH; auto.
    + exploit STEP; eauto. i. des.
      { left.
        unfold lang_steps_failure, Thread.steps_failure in *. des.
        exploit rtc_lang_tau_step_rtc_thread_tau_step; try exact STEPS. i.
        esplits; eauto.
        hexploit sim_local_promise_consistent; eauto. i. des.
        econs 2. econs; eauto. }
      left.
      inv SIM0; [|done].
      inv EVT. inv STEP_SRC.
      exploit sim_local_failure;
        (try exact LOCAL);
        eauto. i. des.
      unfold Thread.steps_failure.
      esplits;
        (try by apply rtc_lang_tau_step_rtc_thread_tau_step; eauto).
      econs 2. econs; [|econs 7]; eauto.
Qed.

Lemma sim_trace_sim_stmts
      (sim_regs1 sim_regs2:SIM_REGS)
      stmts1_src
      stmts1_tgt
      (SIM: forall rs1_src rs1_tgt
              (SIM_REGS1: sim_regs1 rs1_src rs1_tgt),
          sim_trace sim_regs2 (State.mk rs1_src stmts1_src) (State.mk rs1_tgt stmts1_tgt)):
  sim_stmts sim_regs1
            stmts1_src
            stmts1_tgt
            sim_regs2.
Proof.
  ii. apply sim_trace_sim_thread; auto.
Qed.

Lemma sim_trace_nil
      rs_src
      rs_tgt
      (sim_regs:SIM_REGS)
      (RS: sim_regs rs_src rs_tgt):
  sim_trace sim_regs
            (State.mk rs_src [])
            (State.mk rs_tgt []).
Proof.
  pfold. unfold _sim_trace. splits.
  - i. esplits; eauto.
  - i. inv STEP_TGT.
Qed.


(* instr *)

Lemma sim_trace_instr
      instr_src rs_src
      instr_tgt rs_tgt
      regs
      (ORD: Instr.ord instr_src instr_tgt)
      (RS: RegFile.eq_except regs rs_src rs_tgt)
      (REGS: RegSet.disjoint regs (Instr.regs_of instr_src)):
  sim_trace (RegFile.eq_except regs)
            (State.mk rs_src [Stmt.instr instr_src])
            (State.mk rs_tgt [Stmt.instr instr_tgt]).
Proof.
  pfold. unfold _sim_trace. splits.
  { i. inv TERMINAL_TGT. }
  i. inv STEP_TGT. inv INSTR.
  - right.
    inv ORD. esplits; eauto.
    + econs.
    + econs 2. econs. econs.
    + left. apply sim_trace_nil. ss.
  - right.
    inv ORD. esplits; eauto.
    + econs.
    + econs 2. econs. econs.
    + left. apply sim_trace_nil.
      ss. symmetry in REGS. apply RegSet.disjoint_add in REGS. des. symmetry in REGS0.
      erewrite RegFile.eq_except_expr; eauto.
      apply RegFile.eq_except_add. ss.
  - right.
    inv ORD. esplits; eauto.
    + econs. eauto.
    + econs 2. econs. econs.
    + left. apply sim_trace_nil.
      apply RegFile.eq_except_add. ss.
  - right.
    inv ORD. esplits; eauto.
    + econs. eauto.
    + econs 2. econs.
      erewrite <- RegFile.eq_except_value; eauto. econs.
    + left. apply sim_trace_nil. ss.
  - right.
    inv ORD. esplits; eauto.
    + econs; eauto.
    + econs 2. econs. econs.
      ss. symmetry in REGS. apply RegSet.disjoint_add in REGS. des. symmetry in REGS0.
      erewrite <- RegFile.eq_except_rmw; eauto. symmetry. ss.
    + left. apply sim_trace_nil.
      apply RegFile.eq_except_add. ss.
  - right.
    inv ORD. esplits; eauto.
    + econs; eauto.
    + econs 2. econs. econs.
      ss. symmetry in REGS. apply RegSet.disjoint_add in REGS. des. symmetry in REGS0.
      erewrite <- RegFile.eq_except_rmw; eauto. symmetry. ss.
    + left. apply sim_trace_nil.
      apply RegFile.eq_except_add. ss.
  - right.
    inv ORD. esplits; eauto.
    + econs; eauto.
    + econs 2. econs. econs.
    + left. apply sim_trace_nil. ss.
  - right.
    inv ORD. esplits; eauto.
    + econs.
    + econs 2. econs.
      ss. symmetry in REGS. apply RegSet.disjoint_add in REGS. des. symmetry in REGS0.
      erewrite <- RegFile.eq_except_value_list; eauto. econs.
    + left. apply sim_trace_nil.
      apply RegFile.eq_except_add. ss.
  - right.
    inv ORD. esplits; eauto.
    + econs.
    + econs 2. econs. econs.
    + left. apply sim_trace_nil. ss.
Qed.

Lemma sim_stmts_instr
      instr_src instr_tgt regs
      (ORD: Instr.ord instr_src instr_tgt)
      (REGS: RegSet.disjoint regs (Instr.regs_of instr_src)):
  sim_stmts (RegFile.eq_except regs) [Stmt.instr instr_src] [Stmt.instr instr_tgt] (RegFile.eq_except regs).
Proof.
  apply sim_trace_sim_stmts; ss. i.
  apply sim_trace_instr; ss.
Qed.

Lemma sim_stmts_instr_refl
      instr regs
      (REGS: RegSet.disjoint regs (Instr.regs_of instr)):
  sim_stmts (RegFile.eq_except regs) [Stmt.instr instr] [Stmt.instr instr] (RegFile.eq_except regs).
Proof.
  apply sim_stmts_instr; auto. refl.
Qed.


(* replacing abort with arbitrary instructions *)

Lemma sim_trace_replace_abort
      rs_src rs_tgt regs stmts_tgt
      (RS: RegFile.eq_except regs rs_src rs_tgt):
  sim_trace (RegFile.eq_except regs)
            (State.mk rs_src [Stmt.instr Instr.abort])
            (State.mk rs_tgt stmts_tgt).
Proof.
  pfold. unfold _sim_trace. splits; i.
  - left.
    unfold lang_steps_failure. esplits; eauto.
    econs. econs.
  - left.
    unfold lang_steps_failure. esplits; eauto.
    econs. econs.
Qed.

Lemma sim_stmts_replace_abort
      regs stmts_tgt:
  sim_stmts (RegFile.eq_except regs) [Stmt.instr Instr.abort] stmts_tgt (RegFile.eq_except regs).
Proof.
  apply sim_trace_sim_stmts. i.
  apply sim_trace_replace_abort; ss.
Qed.


(* eliminating instructions after abort *)

Lemma sim_trace_elim_after_abort
      rs_src rs_tgt regs stmts_src
      (RS: RegFile.eq_except regs rs_src rs_tgt):
  sim_trace (RegFile.eq_except regs)
            (State.mk rs_src ((Stmt.instr Instr.abort) :: stmts_src))
            (State.mk rs_tgt [Stmt.instr Instr.abort]).
Proof.
  pfold. unfold _sim_trace. splits; i.
  - inv TERMINAL_TGT.
  - left.
    unfold lang_steps_failure. esplits; eauto.
    econs. econs.
Qed.

Lemma sim_stmts_elim_after_abort
      regs stmts_src:
  sim_stmts (RegFile.eq_except regs) ((Stmt.instr Instr.abort) :: stmts_src) [Stmt.instr Instr.abort] (RegFile.eq_except regs).
Proof.
  apply sim_trace_sim_stmts. i.
  apply sim_trace_elim_after_abort; ss.
Qed.
