Require Import RelationClasses.

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

Set Implicit Arguments.


Module Threads.
  Definition syntax := IdentMap.t {lang:language & (Language.syntax lang)}.
  Definition t := IdentMap.t ({lang:language & (Language.state lang)} * Local.t).

  Definition init (s:syntax): t :=
    IdentMap.map
      (fun s => (existT _ _ ((Language.init (projT1 s)) (projT2 s)), Local.init))
      s.

  Definition is_terminal (ths:t): Prop :=
    forall tid lang st lc (FIND: IdentMap.find tid ths = Some (existT _ lang st, lc)),
      <<STATE: (Language.is_terminal lang) st>> /\
      <<THREAD: Local.is_terminal lc>>.

  Inductive wf (ths:t) (mem:Memory.t): Prop :=
  | wf_intro
      (DISJOINT:
         forall tid1 lang1 st1 lc1
           tid2 lang2 st2 lc2
           (TID: tid1 <> tid2)
           (TH1: IdentMap.find tid1 ths = Some (existT _ lang1 st1, lc1))
           (TH2: IdentMap.find tid2 ths = Some (existT _ lang2 st2, lc2)),
           Local.disjoint lc1 lc2)
      (THREADS: forall tid lang st lc
                  (TH: IdentMap.find tid ths = Some (existT _ lang st, lc)),
          Local.wf lc mem)
  .

  Lemma init_wf syn: wf (init syn) Memory.init.
  Proof.
    econs.
    - i. unfold init in *. rewrite IdentMap.Facts.map_o in *.
      destruct (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) tid1 syn); inv TH1.
      destruct (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) tid2 syn); inv TH2.
      econs. ss. econs. i. rewrite Memory.bot_get in *. congr.
    - i. unfold init in *. rewrite IdentMap.Facts.map_o in *.
      destruct (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) tid syn); inv TH.
      econs; ss.
      + apply TView.bot_wf.
      + apply TView.bot_closed.
      + ii. rewrite Memory.bot_get in LHS. congr.
      + apply Memory.bot_finite.
      + ii. rewrite Memory.bot_get in GET. congr.
  Qed.

  Lemma terminal_consistent
        ths sc mem
        tid lang st lc
        (TERMINAL: is_terminal ths)
        (TH: IdentMap.find tid ths = Some (existT _ lang st, lc)):
    Thread.consistent (Thread.mk lang st lc sc mem).
  Proof.
    unfold is_terminal in *. exploit TERMINAL; eauto. i. des.
    inv THREAD. ii. esplits; eauto.
  Qed.

  Inductive is_promised tid (loc:Loc.t) (to:Time.t) (threads:t): Prop :=
  | is_promised_intro
      lang st lc from msg
      (TID: IdentMap.find tid threads = Some (existT _ lang st, lc))
      (PROMISES: Memory.get loc to (Local.promises lc) = Some (from, msg))
  .

  Definition tids (ths: t): IdentSet.t :=
    List.fold_right (fun p s => IdentSet.add (fst p) s) IdentSet.empty (IdentMap.elements ths).

  Lemma tids_o tid ths:
    IdentSet.mem tid (tids ths) = IdentMap.find tid ths.
  Proof.
    unfold tids. rewrite IdentMap.Facts.elements_o.
    induction (IdentMap.elements ths); ss. destruct a. s.
    rewrite IdentSet.Facts.add_b, IHl.
    unfold IdentSet.Facts.eqb, IdentMap.Facts.eqb.
    repeat match goal with
           | [|- context[if ?c then true else false]] => destruct c
           end; ss; congr.
  Qed.

  Lemma tids_add
        tid lang st lc ths:
    tids (IdentMap.add tid (existT _ lang st, lc) ths) = IdentSet.add tid (tids ths).
  Proof.
    apply IdentSet.ext. i.
    rewrite IdentSet.Facts.add_b, ? tids_o.
    rewrite IdentMap.Facts.add_o. unfold IdentSet.Facts.eqb.
    repeat condtac; ss.
  Qed.

  Lemma is_terminal_spec ths:
    Threads.is_terminal ths <->
    forall tid lang st lc
      (TIDS: IdentSet.mem tid (tids ths))
      (FIND: IdentMap.find tid ths = Some (existT _ lang st, lc)),
      (Language.is_terminal lang) st /\ Local.is_terminal lc.
  Proof.
    unfold Threads.is_terminal. econs; i.
    - eapply H. eauto.
    - destruct (IdentMap.find tid ths) eqn:X; inv FIND.
      eapply H; eauto. rewrite tids_o, X. ss.
  Qed.

  Lemma tids_find
        ths_src ths_tgt tid
        (TIDS: tids ths_src = tids ths_tgt):
    (exists lang_src st_src lc_src, IdentMap.find tid ths_src = Some (existT _ lang_src st_src, lc_src)) <->
    (exists lang_tgt st_tgt lc_tgt, IdentMap.find tid ths_tgt = Some (existT _ lang_tgt st_tgt, lc_tgt)).
  Proof.
    split; i; des.
    - destruct (IdentSet.mem tid (tids ths_src)) eqn:MEM.
      + rewrite TIDS in MEM.
        rewrite tids_o in MEM.
        destruct (IdentMap.find tid ths_tgt); ss.
        destruct p. destruct s. esplits; eauto.
      + rewrite tids_o in MEM.
        destruct (IdentMap.find tid ths_src); ss.
    - destruct (IdentSet.mem tid (tids ths_tgt)) eqn:MEM.
      + rewrite <- TIDS in MEM.
        rewrite tids_o in MEM.
        destruct (IdentMap.find tid ths_src); ss.
        destruct p. destruct s. esplits; eauto.
      + rewrite tids_o in MEM.
        destruct (IdentMap.find tid ths_tgt); ss.
  Qed.
End Threads.


Module Configuration.
  Structure t := mk {
    threads: Threads.t;
    sc: TimeMap.t;
    memory: Memory.t;
  }.

  Definition init (s:Threads.syntax): t := mk (Threads.init s) TimeMap.bot Memory.init.

  Definition is_terminal (conf:t): Prop := Threads.is_terminal (threads conf).

  Inductive wf (conf:t): Prop :=
  | wf_intro
      (WF: Threads.wf (threads conf) (memory conf))
      (SC: Memory.closed_timemap (sc conf) (memory conf))
      (MEM: Memory.closed (memory conf))
  .

  Lemma init_wf syn: wf (init syn).
  Proof.
    econs.
    - apply Threads.init_wf.
    - viewtac.
    - apply Memory.init_closed.
  Qed.

  Inductive step: forall (e:MachineEvent.t) (tid:Ident.t) (c1 c2:t), Prop :=
  | step_failure
      pf tid c1 lang st1 lc1 e2 st3 lc3 sc3 memory3
      (TID: IdentMap.find tid (threads c1) = Some (existT _ lang st1, lc1))
      (STEPS: rtc (@Thread.tau_step _) (Thread.mk _ st1 lc1 (sc c1) (memory c1)) e2)
      (STEP: Thread.step pf ThreadEvent.failure e2 (Thread.mk _ st3 lc3 sc3 memory3)):
      step MachineEvent.failure tid c1 (mk (IdentMap.add tid (existT _ _ st3, lc3) (threads c1)) sc3 memory3)
  | step_normal
      pf e tid c1 lang st1 lc1 e2 st3 lc3 sc3 memory3
      (TID: IdentMap.find tid (threads c1) = Some (existT _ lang st1, lc1))
      (STEPS: rtc (@Thread.tau_step _) (Thread.mk _ st1 lc1 (sc c1) (memory c1)) e2)
      (STEP: Thread.step pf e e2 (Thread.mk _ st3 lc3 sc3 memory3))
      (EVENT: e <> ThreadEvent.failure)
      (CONSISTENT: Thread.consistent (Thread.mk _ st3 lc3 sc3 memory3)):
      step (ThreadEvent.get_machine_event e) tid c1 (mk (IdentMap.add tid (existT _ _ st3, lc3) (threads c1)) sc3 memory3)
  .

  Inductive opt_step: forall (e: MachineEvent.t) (tid: Ident.t) (c1 c2: t), Prop :=
  | step_none
      tid c:
      opt_step MachineEvent.silent tid c c
  | step_some
      e tid c1 c2
      (STEP: step e tid c1 c2):
      opt_step e tid c1 c2
  .
  Hint Constructors opt_step.

  Definition tau_step := union (step MachineEvent.silent).

  Definition steps_failure (c1: t): Prop :=
    exists tid c2 c3,
      <<STEPS: rtc tau_step c1 c2>> /\
      <<FAILURE: step MachineEvent.failure tid c2 c3>>.
  Hint Unfold steps_failure.

  Inductive has_promise (c:t): Prop :=
  | has_promise_intro
      tid st lc loc from to msg
      (FIND: IdentMap.find tid (threads c) = Some (st, lc))
      (GET: Memory.get loc to (Local.promises lc) = Some (from, msg))
  .

  Lemma inj_option_pair
        A B
        (a1 a2: A)
        (b1 b2: B)
        (EQ: Some (a1, b1) = Some (a2, b2)):
    a1 = a2 /\ b1 = b2.
  Proof.
    inv EQ. ss.
  Qed.

  Ltac simplify :=
    repeat
      (try match goal with
           | [H: context[IdentMap.find _ (IdentMap.add _ _ _)] |- _] =>
             rewrite IdentMap.Facts.add_o in H
           | [H: context[if ?c then _ else _] |- _] =>
             destruct c
           | [H: Some _ = Some _ |- _] =>
             inv H
           | [H: (_, _) = (_, _) |- _] =>
             inv H
           | [H: existT ?P ?p _ = existT ?P ?p _ |- _] =>
             apply inj_pair2 in H
           | [H: existT ?P ?p _ = existT ?P ?q _ |- _] =>
             apply eq_sigT_sig_eq in H; inv H
           end;
       ss; subst).

  Ltac simplify2 :=
    repeat
      (try match goal with
           | [H: context[IdentMap.find _ (IdentMap.add _ _ _)] |- _] =>
             rewrite IdentMap.Facts.add_o in H
           | [H: context[if ?c then _ else _] |- _] =>
             destruct c
           | [H: Some (_, _) = Some (_, _) |- _] =>
             apply inj_option_pair in H; des
           | [H: existT ?P ?p _ = existT ?Q ?q _ |- _] =>
             apply inj_pair2 in H
           | [H: existT ?P ?p _ = existT ?Q ?q _ |- _] =>
             exploit eq_sigT_fst; try exact H; i; subst
           end;
       ss; subst).

  Lemma step_future
        e tid c1 c2
        (STEP: step e tid c1 c2)
        (WF1: wf c1):
    <<WF2: wf c2>> /\
    <<SC_FUTURE: TimeMap.le (sc c1) (sc c2)>> /\
    <<MEM_FUTURE: Memory.future (memory c1) (memory c2)>>.
  Proof.
    inv WF1. inv WF. inv STEP; s.
    - exploit THREADS; ss; eauto. i.
      exploit Thread.rtc_tau_step_future; eauto. s. i. des.
      exploit Thread.step_future; eauto. s. i. des.
      splits; [|by etrans; eauto|by etrans; eauto].
      econs; ss. econs.
      + i. simplify.
        * exploit THREADS; try apply TH1; eauto. i. des.
          exploit Thread.rtc_tau_step_disjoint; eauto. i. des.
          exploit Thread.step_disjoint; eauto. s. i. des.
          symmetry. auto.
        * exploit THREADS; try apply TH2; eauto. i. des.
          exploit Thread.rtc_tau_step_disjoint; eauto. i. des.
          exploit Thread.step_disjoint; eauto. i. des.
          auto.
        * eapply DISJOINT; [|eauto|eauto]. auto.
      + i. simplify.
        exploit THREADS; try apply TH; eauto. i.
        exploit Thread.rtc_tau_step_disjoint; eauto. i. des.
        exploit Thread.step_disjoint; eauto. s. i. des.
        auto.
    - exploit THREADS; ss; eauto. i.
      exploit Thread.rtc_tau_step_future; eauto. s. i. des.
      exploit Thread.step_future; eauto. s. i. des.
      splits; [|by etrans; eauto|by etrans; eauto].
      econs; ss. econs.
      + i. simplify.
        * exploit THREADS; try apply TH1; eauto. i. des.
          exploit Thread.rtc_tau_step_disjoint; eauto. i. des.
          exploit Thread.step_disjoint; eauto. s. i. des.
          symmetry. auto.
        * exploit THREADS; try apply TH2; eauto. i. des.
          exploit Thread.rtc_tau_step_disjoint; eauto. i. des.
          exploit Thread.step_disjoint; eauto. i. des.
          auto.
        * eapply DISJOINT; [|eauto|eauto]. auto.
      + i. simplify.
        exploit THREADS; try apply TH; eauto. i.
        exploit Thread.rtc_tau_step_disjoint; eauto. i. des.
        exploit Thread.step_disjoint; eauto. s. i. des.
        auto.
  Qed.

  Lemma opt_step_future
        e tid c1 c2
        (STEP: opt_step e tid c1 c2)
        (WF1: wf c1):
    <<WF2: wf c2>> /\
    <<SC_FUTURE: TimeMap.le (sc c1) (sc c2)>> /\
    <<MEM_FUTURE: Memory.future (memory c1) (memory c2)>>.
  Proof.
    inv STEP.
    - splits; auto; refl.
    - eapply step_future; eauto.
  Qed.

  Lemma rtc_step_future
        c1 c2
        (STEPS: rtc tau_step c1 c2)
        (WF1: wf c1):
    <<WF2: wf c2>> /\
    <<SC_FUTURE: TimeMap.le (sc c1) (sc c2)>> /\
    <<MEM_FUTURE: Memory.future (memory c1) (memory c2)>>.
  Proof.
    induction STEPS; i.
    - splits; auto; refl.
    - inv H.
      exploit step_future; eauto. i. des.
      exploit IHSTEPS; eauto. i. des.
      splits; eauto; etrans; eauto.
  Qed.
End Configuration.
