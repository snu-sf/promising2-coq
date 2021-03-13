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

Require Import PromotionDef.
Require Import SimCommon.
Require Import SimThreadPromotion.
Require Import SimThreadOther.

Set Implicit Arguments.


Module Promotion.
  Inductive sim_conf (p: Ident.t) (l: Loc.t) (r: Reg.t) (c_src c_tgt: Configuration.t): Prop :=
  | sim_conf_intro
      (TIDS: Threads.tids (Configuration.threads c_src) = Threads.tids (Configuration.threads c_tgt))
      (FIND_SRC: forall tid lang_src st_src lc_src
                   (FIND: IdentMap.find tid (Configuration.threads c_src) = Some (existT _ lang_src st_src, lc_src)),
          lang_src = lang)
      (FIND_TGT: forall tid lang_tgt st_tgt lc_tgt
                   (FIND: IdentMap.find tid (Configuration.threads c_tgt) = Some (existT _ lang_tgt st_tgt, lc_tgt)),
          lang_tgt = lang)
      (PROMOTION: exists st_src lc_src st_tgt lc_tgt,
          <<FIND_SRC: IdentMap.find p (Configuration.threads c_src) = Some (existT _ lang st_src, lc_src)>> /\
          <<FIND_TGT: IdentMap.find p (Configuration.threads c_tgt) = Some (existT _ lang st_tgt, lc_tgt)>> /\
          <<SIM_THREAD: SimThreadPromotion.sim_thread_reserve
                          l r
                          (Thread.mk lang st_src lc_src (Configuration.sc c_src) (Configuration.memory c_src))
                          (Thread.mk lang st_tgt lc_tgt (Configuration.sc c_tgt) (Configuration.memory c_tgt))>>)
      (OTHER: forall tid st_src lc_src st_tgt lc_tgt
                (TID: tid <> p)
                (FIND_SRC: IdentMap.find tid (Configuration.threads c_src) = Some (existT _ lang st_src, lc_src))
                (FIND_TGT: IdentMap.find tid (Configuration.threads c_tgt) = Some (existT _ lang st_tgt, lc_tgt)),
          <<SIM_THREAD: SimThreadOther.sim_thread
                          l
                          (Thread.mk lang st_src lc_src (Configuration.sc c_src) (Configuration.memory c_src))
                          (Thread.mk lang st_tgt lc_tgt (Configuration.sc c_tgt) (Configuration.memory c_tgt))>>)
  .
  Hint Constructors sim_conf.

  Lemma sim_conf_find
        p l r c_src c_tgt tid
        (SIM: sim_conf p l r c_src c_tgt):
    (exists lang_src st_src lc_src,
        IdentMap.find tid (Configuration.threads c_src) = Some (existT _ lang_src st_src, lc_src)) <->
    (exists lang_tgt st_tgt lc_tgt,
        IdentMap.find tid (Configuration.threads c_tgt) = Some (existT _ lang_tgt st_tgt, lc_tgt)).
  Proof.
    inv SIM. destruct c_src, c_tgt. ss.
    eapply Threads.tids_find; eauto.
  Qed.

  Lemma sim_conf_sim_thread_other
        p l r c_src c_tgt
        tid st_src lc_src st_tgt lc_tgt
        (SIM: sim_conf p l r c_src c_tgt)
        (TID: tid <> p)
        (FIND_SRC: IdentMap.find tid (Configuration.threads c_src) = Some (existT _ lang st_src, lc_src))
        (FIND_TGT: IdentMap.find tid (Configuration.threads c_tgt) = Some (existT _ lang st_tgt, lc_tgt)):
    SimThreadOther.sim_thread
      l
      (Thread.mk lang st_src lc_src (Configuration.sc c_src) (Configuration.memory c_src))
      (Thread.mk lang st_tgt lc_tgt (Configuration.sc c_tgt) (Configuration.memory c_tgt)).
  Proof.
    inv SIM. exploit OTHER; eauto.
  Qed.

  Lemma sim_conf_sim
        p l r c_src c_tgt
        (SIM: sim_conf p l r c_src c_tgt):
    sim c_src c_tgt.
  Proof.
    revert c_src c_tgt SIM.
    pcofix CIH. i. pfold. econs; ii.
    { (* terminal *)
      dup SIM. inv SIM0. des. ss.
      dup WF_SRC. inv WF_SRC0. inv WF.
      exploit THREADS; eauto. i. clear DISJOINT THREADS.
      exploit SimThreadPromotion.step_reserve_sim_thread; try exact SIM_THREAD; eauto. i. des.
      destruct e2_src.
      esplits.
      - econs 2; eauto. econs.
        replace MachineEvent.silent with
            (ThreadEvent.get_machine_event (ThreadEvent.promise l from to Message.reserve Memory.op_kind_cancel)) by ss.
        econs; eauto; ss.
        ii. right. esplits; eauto. s.
        exploit TERMINAL_TGT; eauto. i. des. inv THREAD.
        exploit SimThreadPromotion.sim_thread_promises_bot; eauto.
      - s. ii. destruct (Ident.eq_dec tid p).
        + subst. Configuration.simplify2.
          exploit TERMINAL_TGT; eauto. i. des.
          split.
          * exploit SimThreadPromotion.sim_thread_terminal; eauto.
          * inv THREAD. unnw. econs.
            exploit SimThreadPromotion.sim_thread_promises_bot; eauto.
        + Configuration.simplify2.
          clear st_src lc_src st_tgt lc_tgt x from to state local sc memory
                FIND_SRC0 FIND_TGT0 SIM_THREAD SC MEM STEP SIM2.
          exploit sim_conf_find; eauto. i. des.
          exploit x0; eauto. i. des.
          exploit FIND_SRC; eauto. i. subst.
          exploit FIND_TGT; eauto. i. subst.
          clear x0 x1 FIND_SRC FIND_TGT.
          exploit sim_conf_sim_thread_other; eauto. intro SIM_THREAD.
          exploit TERMINAL_TGT; eauto. i. des.
          split.
          * exploit SimThreadOther.sim_thread_terminal; eauto.
          * inv THREAD. unnw. econs.
            exploit SimThreadOther.sim_thread_promises_bot; eauto.
    }

    destruct (Ident.eq_dec tid p); subst; inv STEP_TGT.
    { (* promotion: failure *)
      destruct c_src as [ths1_src sc1_src mem1_src].
      destruct c_tgt as [ths1_tgt sc1_tgt mem1_tgt].
      dup SIM. inv SIM0. des. ss.
      clear FIND_SRC FIND_TGT OTHER.
      rewrite TID in FIND_TGT0. Configuration.simplify2.
      dup WF_SRC. inv WF_SRC0. inv WF. ss.
      exploit THREADS; eauto. intro WF1_SRC. clear DISJOINT THREADS.
      dup WF_TGT. inv WF_TGT0. inv WF. ss.
      exploit THREADS; eauto. intro WF1_TGT. clear DISJOINT THREADS.
      exploit SimThreadPromotion.sim_thread_reserve_plus_step; eauto. s. i. des.
      destruct e_src; ss. inv STEP_SRC. destruct e3_src. ss.
      assert (CSTEP: Configuration.step
                       MachineEvent.failure p
                       (Configuration.mk ths1_src sc1_src mem1_src)
                       (Configuration.mk
                          (IdentMap.add p (existT (fun (lang: language) => (Language.state lang)) lang state, local) ths1_src)
                          sc memory)).
      { econs 1; eauto. }
      esplits; [econs 2; eauto|].
      exploit Configuration.step_future; try exact CSTEP; eauto. s. i. des.
      hexploit Thread.rtc_all_step_prev_None.
      { eapply rtc_n1.
        - eapply rtc_implies; try exact STEPS_SRC. apply tau_union.
        - econs. econs. eapply STEP0. }
      i. des.
      right. apply CIH. econs; ss.
      - repeat rewrite Threads.tids_add.
        repeat rewrite IdentSet.add_mem; ss.
        + rewrite Threads.tids_o. rewrite TID. ss.
        + rewrite Threads.tids_o. rewrite FIND_SRC0. ss.
      - i. revert FIND. rewrite IdentMap.gsspec. condtac; ss; i.
        + inv FIND. ss.
        + inv SIM. eapply FIND_SRC; eauto.
      - i. revert FIND. rewrite IdentMap.gsspec. condtac; ss; i.
        + inv FIND. ss.
        + inv SIM. eapply FIND_TGT; eauto.
      - repeat rewrite IdentMap.gsspec. condtac; ss. esplits; eauto.
      - i. revert FIND_SRC. rewrite IdentMap.gsspec. condtac; ss; i.
        revert FIND_TGT. rewrite IdentMap.gsspec. condtac; ss; i.
        exploit sim_conf_sim_thread_other; eauto. s. i.
        eapply SimThreadOther.sim_thread_future; eauto; try apply SIM3.
        inv WF_SRC. inv WF. ss. exploit THREADS; eauto.
    }

    { (* promotion: normal *)
      destruct c_src as [ths1_src sc1_src mem1_src].
      destruct c_tgt as [ths1_tgt sc1_tgt mem1_tgt].
      dup SIM. inv SIM0. des. ss.
      clear FIND_SRC FIND_TGT OTHER.
      rewrite TID in FIND_TGT0. Configuration.simplify2.
      dup WF_SRC. inv WF_SRC0. inv WF. ss.
      exploit THREADS; eauto. intro WF1_SRC. clear DISJOINT THREADS.
      dup WF_TGT. inv WF_TGT0. inv WF. ss.
      exploit THREADS; eauto. intro WF1_TGT. clear DISJOINT THREADS.
      exploit SimThreadPromotion.sim_thread_reserve_plus_step; eauto. s. i. des.
      destruct e3_src. ss.
      assert (CSTEP: Configuration.opt_step
                       (ThreadEvent.get_machine_event e_src) p
                       (Configuration.mk ths1_src sc1_src mem1_src)
                       (Configuration.mk
                          (IdentMap.add p (existT (fun (lang: language) => (Language.state lang)) lang state, local) ths1_src)
                          sc memory)).
      { inv STEP_SRC.
        - destruct (rtc_tail STEPS_SRC).
          + des. inv H0. inv TSTEP. ss. rewrite <- EVENT1.
            econs 2. econs 2; eauto.
            * ii. subst. ss.
            * exploit Thread.rtc_tau_step_future; try exact STEPS; eauto. s. i. des.
              exploit Thread.step_future; try exact STEP; eauto. s. i. des.
              exploit Thread.rtc_tau_step_future; try exact STEPS_SRC; eauto. s. i. des.
              eapply SimThreadPromotion.sim_thread_reserve_consistent; eauto.
          + inv H.
            replace (IdentMap.add p (existT (fun lang : language => Language.state lang) lang state, local) ths1_src)
              with ths1_src; auto.
            apply IdentMap.eq_leibniz. ii.
            rewrite -> IdentMap.gsident; auto.
        - econs 2. econs 2; eauto.
          + ii. subst. ss. destruct e0; ss.
          + exploit Thread.rtc_tau_step_future; try exact STEPS; eauto. s. i. des.
            exploit Thread.step_future; try exact STEP; eauto. s. i. des.
            exploit Thread.rtc_tau_step_future; try exact STEPS_SRC; eauto. s. i. des.
            exploit Thread.step_future; try exact STEP0; eauto. s. i. des.
            eapply SimThreadPromotion.sim_thread_reserve_consistent; eauto.
      }
      rewrite <- EVENT0. esplits; eauto.
      exploit Configuration.opt_step_future; try exact CSTEP; eauto. s. i. des.
      hexploit Thread.rtc_all_step_prev_None; try eapply Thread.tau_opt_all; eauto. s. i. des.
      right. apply CIH. econs; ss.
      - repeat rewrite Threads.tids_add.
        repeat rewrite IdentSet.add_mem; ss.
        + rewrite Threads.tids_o. rewrite TID. ss.
        + rewrite Threads.tids_o. rewrite FIND_SRC0. ss.
      - i. revert FIND. rewrite IdentMap.gsspec. condtac; ss; i.
        + inv FIND. ss.
        + inv SIM. eapply FIND_SRC; eauto.
      - i. revert FIND. rewrite IdentMap.gsspec. condtac; ss; i.
        + inv FIND. ss.
        + inv SIM. eapply FIND_TGT; eauto.
      - repeat rewrite IdentMap.gsspec. condtac; ss. esplits; eauto.
      - i. revert FIND_SRC. rewrite IdentMap.gsspec. condtac; ss; i.
        revert FIND_TGT. rewrite IdentMap.gsspec. condtac; ss; i.
        exploit sim_conf_sim_thread_other; eauto. s. i.
        eapply SimThreadOther.sim_thread_future; eauto; try apply SIM3.
        inv WF_SRC. inv WF. ss. exploit THREADS; eauto.
    }

    { (* other: failure *)
      exploit sim_conf_find; eauto. i. des.
      exploit x1; eauto. i. des. clear x0 x1.
      destruct c_src as [ths1_src sc1_src mem1_src].
      destruct c_tgt as [ths1_tgt sc1_tgt mem1_tgt].
      dup SIM. inv SIM0. ss.
      exploit FIND_SRC; eauto. i. subst.
      exploit FIND_TGT; eauto. i. subst.
      clear FIND_SRC FIND_TGT PROMOTION OTHER.
      exploit sim_conf_sim_thread_other; eauto. s. intro SIM_TH.
      dup WF_SRC. inv WF_SRC0. inv WF. ss.
      exploit THREADS; eauto. intro WF1_SRC. clear DISJOINT THREADS.
      dup WF_TGT. inv WF_TGT0. inv WF. ss.
      exploit THREADS; eauto. intro WF1_TGT. clear DISJOINT THREADS.
      exploit SimThreadOther.sim_thread_plus_step; eauto. s. i. des.
      destruct e_src; ss. inv STEP_SRC. destruct e3_src. ss.
      assert (CSTEP: Configuration.step
                       MachineEvent.failure tid
                       (Configuration.mk ths1_src sc1_src mem1_src)
                       (Configuration.mk
                          (IdentMap.add tid (existT (fun (lang: language) => (Language.state lang)) lang state, local) ths1_src)
                          sc memory)).
      { econs 1; eauto. }
      esplits; [econs 2; eauto|].
      exploit Configuration.step_future; try exact CSTEP; eauto. s. i. des.
      hexploit Thread.rtc_all_step_prev_None.
      { eapply rtc_n1.
        - eapply rtc_implies; try exact STEPS_SRC. apply tau_union.
        - econs. econs. eapply STEP0. }
      i. des.
      right. apply CIH. econs; ss.
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
      - repeat rewrite IdentMap.gsspec. condtac; try congr.
        inv SIM. des. ss. esplits; eauto.
        eapply SimThreadPromotion.sim_thread_reserve_future; eauto; try apply SIM3.
        inv WF_SRC. inv WF. ss. exploit THREADS; eauto.
      - i. revert FIND_SRC. rewrite IdentMap.gsspec. condtac; ss; i.
        + subst. revert FIND_TGT. rewrite IdentMap.gsspec. condtac; ss; i. Configuration.simplify2.
        + revert FIND_TGT. rewrite IdentMap.gsspec. condtac; ss; i.
          exploit sim_conf_sim_thread_other; eauto. s. i.
          eapply SimThreadOther.sim_thread_future; eauto; try apply SIM3.
          inv WF_SRC. inv WF. ss. exploit THREADS; eauto.
    }

    { (* other: normal *)
      exploit sim_conf_find; eauto. i. des.
      exploit x1; eauto. i. des. clear x0 x1.
      destruct c_src as [ths1_src sc1_src mem1_src].
      destruct c_tgt as [ths1_tgt sc1_tgt mem1_tgt].
      dup SIM. inv SIM0. ss.
      exploit FIND_SRC; eauto. i. subst.
      exploit FIND_TGT; eauto. i. subst.
      clear FIND_SRC FIND_TGT PROMOTION OTHER.
      exploit sim_conf_sim_thread_other; eauto. s. intro SIM_TH.
      dup WF_SRC. inv WF_SRC0. inv WF. ss.
      exploit THREADS; eauto. intro WF1_SRC. clear DISJOINT THREADS.
      dup WF_TGT. inv WF_TGT0. inv WF. ss.
      exploit THREADS; eauto. intro WF1_TGT. clear DISJOINT THREADS.
      exploit SimThreadOther.sim_thread_plus_step; eauto. s. i. des.
      destruct e3_src. ss.
      assert (CSTEP: Configuration.opt_step
                       (ThreadEvent.get_machine_event e_src) tid
                       (Configuration.mk ths1_src sc1_src mem1_src)
                       (Configuration.mk
                          (IdentMap.add tid (existT (fun (lang: language) => (Language.state lang)) lang state, local) ths1_src)
                          sc memory)).
      { inv STEP_SRC.
        - destruct (rtc_tail STEPS_SRC).
          + des. inv H0. inv TSTEP. ss. rewrite <- EVENT1.
            econs 2. econs 2; eauto.
            * ii. subst. ss.
            * exploit Thread.rtc_tau_step_future; try exact STEPS; eauto. s. i. des.
              exploit Thread.step_future; try exact STEP; eauto. s. i. des.
              exploit Thread.rtc_tau_step_future; try exact STEPS_SRC; eauto. s. i. des.
              eapply SimThreadOther.sim_thread_consistent; eauto.
          + inv H.
            replace (IdentMap.add tid (existT (fun lang : language => Language.state lang) lang state, local) ths1_src)
              with ths1_src; auto.
            apply IdentMap.eq_leibniz. ii.
            rewrite -> IdentMap.gsident; auto.
        - econs 2. econs 2; eauto.
          + ii. subst. ss. destruct e0; ss.
          + exploit Thread.rtc_tau_step_future; try exact STEPS; eauto. s. i. des.
            exploit Thread.step_future; try exact STEP; eauto. s. i. des.
            exploit Thread.rtc_tau_step_future; try exact STEPS_SRC; eauto. s. i. des.
            exploit Thread.step_future; try exact STEP0; eauto. s. i. des.
            eapply SimThreadOther.sim_thread_consistent; eauto.
      }
      rewrite <- EVENT0. esplits; eauto.
      exploit Configuration.opt_step_future; try exact CSTEP; eauto. s. i. des.
      hexploit Thread.rtc_all_step_prev_None; try eapply Thread.tau_opt_all; eauto. s. i. des.
      right. apply CIH. econs; ss.
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
      - repeat rewrite IdentMap.gsspec. condtac; try congr.
        inv SIM. des. ss. esplits; eauto.
        eapply SimThreadPromotion.sim_thread_reserve_future; eauto; try apply SIM3.
        inv WF_SRC. inv WF. ss. exploit THREADS; eauto.
      - i. revert FIND_SRC. rewrite IdentMap.gsspec. condtac; ss; i.
        + subst. revert FIND_TGT. rewrite IdentMap.gsspec. condtac; ss; i. Configuration.simplify2.
        + revert FIND_TGT. rewrite IdentMap.gsspec. condtac; ss; i.
          exploit sim_conf_sim_thread_other; eauto. s. i.
          eapply SimThreadOther.sim_thread_future; eauto; try apply SIM3.
          inv WF_SRC. inv WF. ss. exploit THREADS; eauto.
    }
  Qed.


  (* promotion *)

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

  Inductive promote_program (p: Ident.t) (l: Loc.t) (r: Reg.t) (program_src program_tgt: Threads.syntax): Prop :=
  | promote_program_intro
      (TIDS: syntax_tids program_src = syntax_tids program_tgt)
      (FIND_SRC: forall tid lang_src syn_src
                   (FIND: IdentMap.find tid program_src = Some (existT _ lang_src syn_src)),
          lang_src = lang)
      (FIND_TGT: forall tid lang_tgt syn_tgt
                   (FIND: IdentMap.find tid program_tgt = Some (existT _ lang_tgt syn_tgt)),
          lang_tgt = lang)
      (PROMOTION: exists syn_src syn_tgt,
          <<FIND_SRC: IdentMap.find p program_src = Some (existT _ lang syn_src)>> /\
          <<FIND_TGT: IdentMap.find p program_tgt = Some (existT _ lang syn_tgt)>> /\
          <<REGFREE: reg_free_stmts r syn_src>> /\
          <<PROMOTE: syn_tgt = promote_stmts l r syn_src>>)
      (OTHER: forall tid syn_src syn_tgt
                (TID: tid <> p)
                (FIND_SRC: IdentMap.find tid program_src = Some (existT _ lang syn_src))
                (FIND_TGT: IdentMap.find tid program_tgt = Some (existT _ lang syn_tgt)),
          <<LOCFREE: loc_free_stmts l syn_src>> /\
          <<SYNTAX: syn_src = syn_tgt>>)
  .

  Inductive sim_conf_init (p: Ident.t) (l: Loc.t) (r: Reg.t) (c_src c_tgt: Configuration.t): Prop :=
  | sim_conf_init_intro
      (TIDS: Threads.tids (Configuration.threads c_src) = Threads.tids (Configuration.threads c_tgt))
      (FIND_SRC: forall tid lang_src st_src lc_src
                   (FIND: IdentMap.find tid (Configuration.threads c_src) = Some (existT _ lang_src st_src, lc_src)),
          lang_src = lang)
      (FIND_TGT: forall tid lang_tgt st_tgt lc_tgt
                   (FIND: IdentMap.find tid (Configuration.threads c_tgt) = Some (existT _ lang_tgt st_tgt, lc_tgt)),
          lang_tgt = lang)
      (PROMOTION: exists st_src lc_src st_tgt lc_tgt,
          <<FIND_SRC: IdentMap.find p (Configuration.threads c_src) = Some (existT _ lang st_src, lc_src)>> /\
          <<FIND_TGT: IdentMap.find p (Configuration.threads c_tgt) = Some (existT _ lang st_tgt, lc_tgt)>> /\
          <<SIM_THREAD: SimThreadPromotion.sim_thread
                          l r
                          (Thread.mk lang st_src lc_src (Configuration.sc c_src) (Configuration.memory c_src))
                          (Thread.mk lang st_tgt lc_tgt (Configuration.sc c_tgt) (Configuration.memory c_tgt))>>)
      (OTHER: forall tid st_src lc_src st_tgt lc_tgt
                (TID: tid <> p)
                (FIND_SRC: IdentMap.find tid (Configuration.threads c_src) = Some (existT _ lang st_src, lc_src))
                (FIND_TGT: IdentMap.find tid (Configuration.threads c_tgt) = Some (existT _ lang st_tgt, lc_tgt)),
          <<SIM_THREAD: SimThreadOther.sim_thread
                          l
                          (Thread.mk lang st_src lc_src (Configuration.sc c_src) (Configuration.memory c_src))
                          (Thread.mk lang st_tgt lc_tgt (Configuration.sc c_tgt) (Configuration.memory c_tgt))>>)
  .
  Hint Constructors sim_conf_init.

  Lemma init_sim_conf
        p l r program_src program_tgt
        (PROMOTE: promote_program p l r program_src program_tgt):
    exists c_src,
      <<STEP: Configuration.step MachineEvent.silent p (Configuration.init program_src) c_src>> /\
      <<SIM: sim_conf p l r c_src (Configuration.init program_tgt)>>.
  Proof.
    assert (INIT: sim_conf_init p l r (Configuration.init program_src) (Configuration.init program_tgt)).
    { inv PROMOTE. econs; ss; i.
      - apply IdentSet.ext. i.
        repeat rewrite Threads.tids_o.
        unfold Threads.init.
        repeat rewrite IdentMap.Facts.map_o.
        specialize (@syntax_tids_o i program_src). i.
        specialize (@syntax_tids_o i program_tgt). i.
        destruct (@UsualFMapPositive.UsualPositiveMap'.find
                    (@sigT _ (@Language.syntax ProgramEvent.t)) i program_src) eqn:SRC;
          destruct (@UsualFMapPositive.UsualPositiveMap'.find
                      (@sigT _ (@Language.syntax ProgramEvent.t)) i program_tgt) eqn:TGT; ss.
        + assert (@UsualFMapPositive.UsualPositiveMap'.find
                    (@sigT _ (@Language.syntax ProgramEvent.t)) i program_src = IdentMap.find i program_src) by ss.
          rewrite <- H1 in *. rewrite SRC in *. ss.
          assert (@UsualFMapPositive.UsualPositiveMap'.find
                    (@sigT _ (@Language.syntax ProgramEvent.t)) i program_tgt = IdentMap.find i program_tgt) by ss.
          rewrite <- H2 in *. rewrite TGT in *. ss.
          rewrite TIDS in *. congr.
        + assert (@UsualFMapPositive.UsualPositiveMap'.find
                    (@sigT _ (@Language.syntax ProgramEvent.t)) i program_src = IdentMap.find i program_src) by ss.
          rewrite <- H1 in *. rewrite SRC in *. ss.
          assert (@UsualFMapPositive.UsualPositiveMap'.find
                    (@sigT _ (@Language.syntax ProgramEvent.t)) i program_tgt = IdentMap.find i program_tgt) by ss.
          rewrite <- H2 in *. rewrite TGT in *. ss.
          rewrite TIDS in *. congr.
      - unfold Threads.init in *.
        rewrite IdentMap.Facts.map_o in *.
        destruct (@UsualFMapPositive.UsualPositiveMap'.find
                    (@sigT _ (@Language.syntax ProgramEvent.t)) tid program_src) eqn:SRC; ss.
        destruct s. ss. inv FIND. eapply FIND_SRC; eauto.
      - unfold Threads.init in *.
        rewrite IdentMap.Facts.map_o in *.
        destruct (@UsualFMapPositive.UsualPositiveMap'.find
                    (@sigT _ (@Language.syntax ProgramEvent.t)) tid program_tgt) eqn:SRC; ss.
        destruct s. ss. inv FIND. eapply FIND_TGT; eauto.
      - unfold Threads.init in *.
        repeat rewrite IdentMap.Facts.map_o in *. des.
        replace (@UsualFMapPositive.UsualPositiveMap'.find
                   (@sigT _ (@Language.syntax ProgramEvent.t)) p program_src) with
            (IdentMap.find p program_src) by ss.
        replace (@UsualFMapPositive.UsualPositiveMap'.find
                   (@sigT _ (@Language.syntax ProgramEvent.t)) p program_tgt) with
            (IdentMap.find p program_tgt) by ss.
        rewrite FIND_SRC0. rewrite FIND_TGT0. ss.
        esplits; eauto.
        unfold State.init. econs; ss; try refl.
        + instantiate (1 := 0). left. econs; eauto. refl.
        + ii. rewrite Memory.bot_get in *. ss.
        + replace (Memory.max_ts l Memory.init) with Time.bot by ss.
          unfold Memory.get, Memory.init, Cell.get, Cell.init, Cell.Raw.init. ss.
          rewrite DOMap.singleton_eq. unfold Message.elt. eauto.
        + i. rewrite Memory.bot_get. ss.
        + ii. unfold Memory.get, Memory.init, Cell.get, Cell.init in GET.
          apply DOMap.singleton_find_inv in GET. des. inv GET0.
      - unfold Threads.init in *.
        rewrite IdentMap.Facts.map_o in *.
        destruct (@UsualFMapPositive.UsualPositiveMap'.find
                    (@sigT _ (@Language.syntax ProgramEvent.t)) tid program_src) eqn:SRC;
          destruct (@UsualFMapPositive.UsualPositiveMap'.find
                      (@sigT _ (@Language.syntax ProgramEvent.t)) tid program_tgt) eqn:TGT; ss.
        destruct s, s0; ss.  Configuration.simplify2.
        exploit OTHER; eauto. i. des.
        unfold State.init. econs; ss; try refl.
        + f_equal. ss.
        + i. rewrite Memory.bot_get. ss.
        + ii. rewrite Memory.bot_get in *. ss.
    }
    inv INIT. des.
    specialize (Configuration.init_wf program_src). intro WF_SRC.
    specialize (Configuration.init_wf program_tgt). intro WF_TGT.
    dup WF_SRC. inv WF_SRC0. inv WF.
    exploit THREADS; eauto. intro WF_SRC1. clear DISJOINT THREADS.
    dup WF_TGT. inv WF_TGT0. inv WF.
    exploit THREADS; eauto. intro WF_TGT1. clear DISJOINT THREADS.
    exploit SimThreadPromotion.step_sim_thread_reserve; eauto; ss. i. des.
    destruct e2_src. ss.
    exploit Thread.step_future; eauto. s. i. des.
    esplits.
    - replace MachineEvent.silent with
          (ThreadEvent.get_machine_event (ThreadEvent.promise l from to Message.reserve Memory.op_kind_add)) by ss.
      econs 2; eauto; ss.
      eapply SimThreadPromotion.sim_thread_reserve_consistent; eauto. ii. ss.
      right. esplits; eauto. ss.
      unfold Threads.init in *.
      rewrite IdentMap.Facts.map_o in *.
      destruct (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) p program_tgt) eqn:TGT; ss.
      destruct s; ss. Configuration.simplify2.
    - econs; ss.
      + repeat rewrite Threads.tids_add.
        repeat rewrite IdentSet.add_mem; ss.
        rewrite Threads.tids_o. rewrite FIND_SRC0. ss.
      + i. revert FIND. rewrite IdentMap.gsspec. condtac; ss; i.
        * inv FIND. ss.
        * eauto.
      + repeat rewrite IdentMap.gsspec. condtac; ss. esplits; eauto.
      + i. revert FIND_SRC1. rewrite IdentMap.gsspec. condtac; ss; i.
        exploit OTHER; eauto. i.
        eapply SimThreadOther.sim_thread_future; eauto; try apply SIM2.
        * inv WF_SRC. inv WF. ss. exploit THREADS; eauto.
        * hexploit Thread.step_prev_None; eauto.
  Qed.

  Theorem promote_behavior
          p l r program_src program_tgt
          (PROMOTE: promote_program p l r program_src program_tgt):
    behaviors Configuration.step (Configuration.init program_tgt) <1=
    behaviors Configuration.step (Configuration.init program_src).
  Proof.
    exploit init_sim_conf; eauto. i. des.
    specialize (Configuration.init_wf program_src). intro WF_SRC.
    specialize (Configuration.init_wf program_tgt). intro WF_TGT.
    exploit Configuration.step_future; eauto. i. des.
    hexploit sim_conf_sim; eauto. i.
    exploit sim_adequacy; try exact H; eauto. i.
    econs 4; eauto.
  Qed.
End Promotion.