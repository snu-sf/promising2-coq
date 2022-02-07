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

Require Import Pred.

Require Import Coq.Logic.Classical.

Set Implicit Arguments.

Section PredStep.

  Inductive pred_step (P : te_pred) lang (e:ThreadEvent.t)
             (e1 e2:Thread.t lang) : Prop :=
  | pred_step_intro (STEP : Thread.step_allpf e e1 e2) (SAT : P e)
  .

  Inductive traced_step lang: list (ThreadEvent.t * Memory.t) -> (Thread.t lang) -> (Thread.t lang) -> Prop :=
  | traced_step_refl
      th0
    :
      traced_step [] th0 th0
  | traced_step_step
      th0 th1 th2 hde hdm tl
      (HD: Thread.step_allpf hde th0 th1)
      (TL: traced_step tl th1 th2)
      (MEM: hdm = (Thread.memory th0))
    :
      traced_step ((hde, hdm)::tl) th0 th2
  .

  Inductive traced_step_n1 lang: list (ThreadEvent.t * Memory.t) -> (Thread.t lang) -> (Thread.t lang) -> Prop :=
  | traced_step_n1_refl
      th0
    :
      traced_step_n1 [] th0 th0
  | traced_step_n1_step
      th0 th1 th2 hds tle tlm
      (HD: traced_step_n1 hds th0 th1)
      (TL: Thread.step_allpf tle th1 th2)
      (MEM: tlm = (Thread.memory th1))
    :
      traced_step_n1 (hds++[(tle, tlm)]) th0 th2
  .

  Lemma traced_step_n1_one lang (th0 th1: Thread.t lang) e
        (STEP: Thread.step_allpf e th0 th1)
    :
      traced_step_n1 [(e, (Thread.memory th0))] th0 th1.
  Proof.
    erewrite <- List.app_nil_l at 1. econs; eauto. econs 1.
  Qed.

  Lemma traced_step_n1_trans lang (th0 th1 th2: Thread.t lang) tr0 tr1
        (STEPS0: traced_step_n1 tr0 th0 th1)
        (STEPS1: traced_step_n1 tr1 th1 th2)
    :
      traced_step_n1 (tr0 ++ tr1) th0 th2.
  Proof.
    ginduction STEPS1; i; ss.
    - erewrite List.app_nil_r. auto.
    - rewrite List.app_assoc. econs; eauto.
  Qed.

  Lemma traced_step_one lang (th0 th1: Thread.t lang) e
        (STEP: Thread.step_allpf e th0 th1)
    :
      traced_step [(e, (Thread.memory th0))] th0 th1.
  Proof.
    econs 2; eauto. econs 1.
  Qed.

  Lemma traced_step_trans lang (th0 th1 th2: Thread.t lang) tr0 tr1
        (STEPS0: traced_step tr0 th0 th1)
        (STEPS1: traced_step tr1 th1 th2)
    :
      traced_step (tr0 ++ tr1) th0 th2.
  Proof.
    ginduction STEPS0; i; ss.
    econs; eauto.
  Qed.

  Lemma traced_step_equivalent lang (th0 th1: Thread.t lang) tr
    :
        traced_step tr th0 th1 <-> traced_step_n1 tr th0 th1.
  Proof.
    split; intros STEP.
    - ginduction STEP.
      + econs.
      + exploit traced_step_n1_trans.
        * apply traced_step_n1_one; eauto.
        * eauto.
        * ss. clarify.
    - ginduction STEP.
      + econs.
      + eapply traced_step_trans; eauto.
        clarify. eapply traced_step_one; eauto.
  Qed.

  Lemma traced_step_separate lang (th0 th2: Thread.t lang) tr0 tr1
        (STEPS: traced_step (tr0++tr1) th0 th2)
    :
      exists th1,
        (<<STEPS0: traced_step tr0 th0 th1>>) /\
        (<<STEPS1: traced_step tr1 th1 th2>>).
  Proof.
    ginduction tr0; i; ss.
    - exists th0. splits; ss. econs.
    - inv STEPS. eapply IHtr0 in TL. des.
      exists th1. splits; ss.
      econs; eauto.
  Qed.

  Lemma traced_step_in P lang (th0 th1: Thread.t lang) tr e m
        (STEPS: traced_step tr th0 th1)
        (IN: List.In (e, m) tr)
        (PRED: List.Forall P tr)
    :
      exists th' th'' tr0 tr1,
        (<<STEPS0: traced_step tr0 th0 th'>>) /\
        (<<STEP: Thread.step_allpf e th' th''>>) /\
        (<<MEM: m = (Thread.memory th')>>) /\
        (<<STEPS1: traced_step tr1 th'' th1>>) /\
        (<<TRACES: tr = tr0 ++ [(e, m)] ++ tr1>>) /\
        (<<SAT: P (e, m)>>).
  Proof.
    ginduction STEPS; i; ss. inv PRED. des.
    - clarify. exists th0, th1. esplits; eauto.
      + econs 1.
      + ss.
    - exploit IHSTEPS; eauto. i. des.
      esplits; eauto.
      + econs 2; eauto.
      + clarify.
  Qed.

  Lemma pred_step_program_step P:
        @pred_step P <4= @Thread.step_allpf.
  Proof.
    i. inv PR. eauto.
  Qed.

  Lemma program_step_true_step:
        @Thread.step_allpf <4= @pred_step (fun _ => True).
  Proof.
    econs; eauto.
  Qed.

  Lemma pred_step_mon P Q (LE : P <1= Q) :
    @pred_step P <4= @pred_step Q.
  Proof.
    i. inv PR. econs; eauto.
  Qed.

  Lemma pred_step_rtc_mon P Q lang (LE : P <1= Q) :
    rtc (tau (@pred_step P lang)) <2= rtc (tau (@pred_step Q lang)).
  Proof.
    i. induction PR; eauto.
    eapply Relation_Operators.rt1n_trans; eauto.
    inv H. econs; eauto. eapply pred_step_mon; eauto.
  Qed.

  Lemma thread_steps_pred_steps P lang:
    rtc (tau (@pred_step P lang)) <2= rtc (@Thread.tau_step lang).
  Proof.
    i. induction PR; eauto.
    eapply Relation_Operators.rt1n_trans; eauto.
    inv H. inv TSTEP. econs; eauto.
  Qed.

  Lemma pred_steps_thread_steps lang:
    rtc (@Thread.tau_step lang) <2= rtc (tau (@pred_step (fun _ => True) lang)).
  Proof.
    i. induction PR; eauto.
    eapply Relation_Operators.rt1n_trans; eauto.
    inv H. econs; eauto. eapply program_step_true_step; eauto.
  Qed.

  Lemma hold_or_not (P Q : te_pred) lang e1 e2
        (STEP : rtc (tau (@pred_step P lang)) e1 e2) :
    (<<HOLD : rtc (tau (@pred_step (P /1\ Q) lang)) e1 e2>>) \/
    (<<NOT : exists e e2' e3, (<<STEPS0 : rtc (tau (@pred_step (P /1\ Q) lang)) e1 e2'>>) /\
                              (<<STEP : Thread.step_allpf e e2' e3>>) /\
                              (<<BREAKP : P e>>) /\ (<<BREAKQ : ~ Q e>>) /\
                              (<<STEPS1 : rtc (tau (@pred_step P lang)) e3 e2>>)>>).
  Proof.
    induction STEP as [th | th1 th2 th3 HD TL IH]; auto.
    inv HD. inv TSTEP. destruct (classic (Q e)) as [QT | QF]. des.
    - left. repeat (econs; eauto).
    - right. do 4 (eauto; econs).
      * apply Operators_Properties.clos_rt_rt1n.
        eapply Relation_Operators.rt_trans. repeat (econs; eauto).
        eapply Operators_Properties.clos_rt1n_rt. eauto.
      * eauto.
    - right. repeat (econs; eauto).
  Qed.

  Lemma no_promise_program_step lang :
    (@pred_step no_promise lang) <3= (@Thread.program_step lang).
  Proof.
    i. inv PR. inv STEP. inv STEP0; clarify.
    inv STEP. ss.
  Qed.

  Lemma no_promise_program_step_rtc lang :
    rtc (tau (@pred_step no_promise lang)) <2= rtc (tau (@Thread.program_step _)).
  Proof.
    i. induction PR.
    - refl.
    - econs; eauto. inv H. econs; eauto.
      eapply no_promise_program_step; eauto.
  Qed.

  Lemma pred_steps_traced_step P lang
        th0 th1
    :
      rtc (tau (@pred_step P lang)) th0 th1 <->
      exists tr,
        (<<STEPS: traced_step tr th0 th1>>) /\
        (<<EVENTS: List.Forall (fun em => <<SAT: P (fst em)>> /\ <<TAU: ThreadEvent.get_machine_event (fst em) = MachineEvent.silent>>) tr >>)
  .
  Proof.
    split; i.
    - ginduction H; i.
      + exists []. splits; eauto. econs 1.
      + des. inv H. inv TSTEP. exists ((e, (Thread.memory x))::tr). splits.
        * econs; eauto.
        * i. ss. des; clarify. eauto.
    - des. ginduction STEPS; i.
      + refl.
      + inv EVENTS. des. econs.
        * econs; eauto. econs; eauto.
        * eauto.
  Qed.

  Lemma pf_step_promise_free_step lang:
    @Thread.step lang true <3= @pred_step promise_free lang.
  Proof.
    i. inv PR.
    - econs; eauto.
      + econs; eauto. econs 1; eauto.
      + inv STEP. ss.
    - econs; eauto.
      + econs; eauto. econs 2; eauto.
      + inv STEP. inv LOCAL; ss.
  Qed.

  Lemma pf_step_promise_free_step_rtc lang :
    rtc (tau (@Thread.step _ true)) <2= rtc (tau (@pred_step promise_free lang)).
  Proof.
    i. induction PR.
    - refl.
    - econs; eauto. inv H. econs; eauto.
      eapply pf_step_promise_free_step; eauto.
  Qed.

  Definition te_rel := ThreadEvent.t -> ThreadEvent.t -> Prop.

  Definition te_pred_shift (P_src P_tgt: te_pred) (R: te_rel) :=
    forall e_src e_tgt (SAT: P_tgt e_tgt) (REL: R e_src e_tgt), P_src e_src.

  Lemma pred_step_shift (P_src P_tgt: te_pred) (R: te_rel)
        (SHIFT: te_pred_shift P_src P_tgt R)
        e_src e_tgt lang (th0 th1: Thread.t lang)
        (SAT: P_tgt e_tgt)
        (REL: R e_src e_tgt)
        (STEP: Thread.step_allpf e_src th0 th1)
    :
      pred_step P_src e_src th0 th1.
  Proof.
    econs; eauto.
  Qed.

  Definition same_machine_event e_src e_tgt :=
    ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt.

  Lemma step_times_list_exists P lang th0 th1 e
        (STEPS: (@pred_step P lang) e th0 th1)
    :
      exists times,
        (@pred_step (P /1\ wf_time_evt (fun loc to => List.In to (times loc))) lang) e th0 th1.
  Proof.
    inv STEPS. destruct e.
    - exists (fun l => if Loc.eq_dec l loc then
                         [from; to] else []).
      econs; eauto.
      ss. splits; auto; des_ifs; ss; eauto.
    - exists (fun _ => []). econs; eauto. ss.
    - exists (fun _ => []). econs; eauto. ss.
    - exists (fun l => if Loc.eq_dec l loc then
                         [from; to] else []).
      econs; eauto.
      ss. splits; auto; des_ifs; ss; eauto.
    - exists (fun l => if Loc.eq_dec l loc then
                         [tsw] else []).
      econs; eauto.
      ss. splits; auto; des_ifs; ss; eauto.
    - exists (fun _ => []). econs; eauto. ss.
    - exists (fun _ => []). econs; eauto. ss.
    - exists (fun _ => []). econs; eauto. ss.
  Qed.

  Lemma times_list_exists P lang th0 th1
        (STEPS: rtc (tau (@pred_step P lang)) th0 th1)
    :
      exists times,
        rtc (tau (@pred_step (P /1\ wf_time_evt (fun loc to => List.In to (times loc))) lang)) th0 th1.
  Proof.
    ginduction STEPS.
    - exists (fun _ => []). refl.
    - dup H. inv H0.
      eapply step_times_list_exists in TSTEP. des.
      exists (fun loc => times loc ++ times0 loc). econs 2.
      + econs; eauto. eapply pred_step_mon; eauto.
        i. ss. des. split; auto.
        eapply wf_time_evt_mon; eauto.
        i. ss. eapply List.in_or_app; eauto.
      + eapply pred_step_rtc_mon; eauto.
        i. ss. des. split; auto.
        eapply wf_time_evt_mon; eauto.
        i. ss. eapply List.in_or_app; eauto.
  Qed.

  Inductive opt_pred_step P lang
    : ThreadEvent.t -> Thread.t lang -> Thread.t lang -> Prop :=
  | step_none t: opt_pred_step P ThreadEvent.silent t t
  | step_some
      e t0 t1
      (STEP: pred_step P e t0 t1)
    :
      opt_pred_step P e t0 t1.
  Hint Constructors opt_pred_step.

End PredStep.