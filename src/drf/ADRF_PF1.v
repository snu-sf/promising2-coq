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

Require Import Pred.
Require Import AMemory.
Require Import ALocal.
Require Import AThread.
Require Import APredStep.
Require Import ADRF_PF0.


Set Implicit Arguments.



Section NOREADSELFPROMS.

  Lemma consistent_read_no_self_promise
        lang th_tgt th_tgt' st st' v v' prom prom' sc sc'
        mem_tgt mem_tgt' pf e_tgt
        (LOCALWF: Local.wf (Local.mk v prom) mem_tgt)
        (CLOSED: Memory.closed mem_tgt)
        (SC: Memory.closed_timemap sc mem_tgt)
        (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem_tgt)
        (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
        (CONSISTENT: Local.promise_consistent (Local.mk v' prom'))
        (STEP: AThread.step pf e_tgt th_tgt th_tgt')
    :
      no_read_msgs (promised prom) e_tgt.
  Proof.
    inv STEP; ss.
    - inv STEP0. ss.
    - inv STEP0. inv LOCAL; ss.
      + ii. inv H. destruct msg as [? []].
        * hexploit promise_consistent_promise_read; eauto; ss.
          ii. timetac.
        * inv LOCAL0. ss. clarify.
          inv LOCALWF. ss. eapply PROMISES in GET. clarify.
      + ii. destruct lc2.
        inv H. destruct msg as [? []].
        * hexploit promise_consistent_promise_read; eauto; ss.
          { eapply write_step_promise_consistent; eauto. }
          { ii. timetac. }
        * inv LOCAL1. ss. clarify.
          inv LOCALWF. ss. eapply PROMISES in GET. clarify.
  Qed.

End NOREADSELFPROMS.


Section NOSC.

  Lemma no_sc_any_sc
        P lang th_src th_tgt th_tgt' st st' v v' prom prom' sc sc_src sc'
        mem mem' e
        (STEP: (@pred_step P lang) e th_tgt th_tgt')
        (NOSC: P <1= no_sc)
        (TH_SRC: th_src = Thread.mk lang st (Local.mk v prom) sc_src mem)
        (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem)
        (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem')
  :
    exists sc_src',
      (<<STEP: (@pred_step P lang)
                 e th_src
                 (Thread.mk lang st' (Local.mk v' prom') sc_src' mem')>>).
  Proof.
    clarify. inv STEP. dup SAT. eapply NOSC in SAT.
    inv STEP0. des. inv STEP.
    - inv STEP0. inv LOCAL. ss. clarify.
      esplits. econs; eauto. econs; eauto. econs 1; eauto. econs; eauto.
    - inv STEP0. inv LOCAL; ss.
      + esplits. econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
      + esplits. econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
      + inv LOCAL0. ss. clarify. exists sc_src.
        econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
        econs; eauto. econs; eauto. ss.
        inv WRITABLE. econs; eauto.
      + inv LOCAL1. ss. inv LOCAL2. ss. clarify. exists sc_src.
        econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
        econs; eauto. econs; eauto. ss.
        inv WRITABLE. econs; eauto.
      + inv LOCAL0. ss. clarify.
        esplits. econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
        econs; eauto. econs; eauto. ss. f_equal.
        unfold TView.write_fence_tview. ss. des_ifs.
      + esplits. econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
  Qed.

  Lemma no_sc_any_sc_traced
        lang th_src th_tgt th_tgt' st st' lc lc' sc sc_src sc'
        mem mem' events
        (STEPS: traced_step events th_tgt th_tgt')
        (TH_SRC: th_src = Thread.mk lang st lc sc_src mem)
        (TH_TGT0: th_tgt = Thread.mk lang st lc sc mem)
        (TH_TGT1: th_tgt' = Thread.mk lang st' lc' sc' mem')
        (EVENTS: forall e (IN: List.In e events), <<SAT: no_sc (fst e)>>)
    :
      exists sc_src',
        (<<STEPS: traced_step events
                              th_src
                              (Thread.mk lang st' lc' sc_src' mem')>>).
  Proof.
    ginduction STEPS.
    - i. clarify. esplits; eauto. econs.
    - i. clarify. destruct th1. destruct local, lc, lc'. ss.
      exploit no_sc_any_sc; ss.
      { econs; eauto. instantiate (1:=no_sc).
        exploit EVENTS; eauto. }
      { ss. }
      i. des. inv STEP.
      exploit IHSTEPS; eauto. i. des. eexists. econs; eauto.
  Qed.

  Lemma no_sc_any_sc_rtc
        P lang th_src th_tgt th_tgt' st st' lc lc' sc sc_src sc'
        mem mem'
        (STEP: rtc (tau (@pred_step P lang)) th_tgt th_tgt')
        (TH_SRC: th_src = Thread.mk lang st lc sc_src mem)
        (TH_TGT0: th_tgt = Thread.mk lang st lc sc mem)
        (TH_TGT1: th_tgt' = Thread.mk lang st' lc' sc' mem')
        (PRED: P <1= no_sc)
    :
      exists sc_src',
        (<<STEP: rtc (tau (@pred_step P lang))
                     th_src
                     (Thread.mk lang st' lc' sc_src' mem')>>).
  Proof.
    ginduction STEP.
    - i. clarify. esplits; eauto.
    - i. clarify. destruct y. destruct local, lc, lc'. ss.
      inv H. exploit no_sc_any_sc; eauto. i. des.
      exploit IHSTEP; eauto. i. des.
      exists sc_src'0. esplits. econs; eauto.
  Qed.

End NOSC.



Section SELFPROMISEREMOVE.

  Lemma self_promise_remove_promise
        prom prom' mem_src mem_tgt mem_tgt' loc from to msg kind
        (MEM: forget_memory (promised prom) mem_src mem_tgt)
        (PROMISE: AMemory.promise prom mem_tgt loc from to msg prom' mem_tgt' kind)
  :
    forget_memory (promised prom') mem_src mem_tgt'.
  Proof.
    dup MEM. eapply forget_memory_le in MEM0. inv MEM. inv PROMISE.
    - econs; eauto.
      * i. rewrite COMPLETE.
        { symmetry. erewrite Memory.add_o; eauto. des_ifs.
          - ss. des. clarify. exfalso. apply NPROMS.
            apply Memory.add_get0 in PROMISES. des.
            econs; eauto. }
        { ii. inv H. eapply NPROMS.
          exploit Memory.add_o; try apply PROMISES; eauto. i.
          erewrite GET in *. des_ifs.
          - econs; eauto.
          - econs; eauto. }
      * i. inv PROMS. destruct msg0.
        erewrite Memory.add_o in GET; eauto. des_ifs.
        { ss. des. clarify.
          eapply memory_le_get_none; eauto.
          apply Memory.add_get0 in MEM. des. eauto. }
        { eapply FORGET. econs; eauto. }
    - econs; eauto.
      * i. rewrite COMPLETE.
        { symmetry. erewrite Memory.split_o; eauto. des_ifs.
          - ss. des. clarify. exfalso. apply NPROMS.
            apply Memory.split_get0 in PROMISES. des.
            econs; eauto.
          - ss. destruct a. clarify. exfalso. apply NPROMS.
            apply Memory.split_get0 in PROMISES.
            econs; des; eauto. }
        { ii. inv H. eapply NPROMS.
          exploit Memory.split_o; try apply PROMISES; eauto. i.
          erewrite GET in *. des_ifs.
          - econs; eauto.
          - econs; eauto.
          - econs; eauto. }
      * i. inv PROMS. destruct msg0.
        erewrite Memory.split_o in GET; eauto. des_ifs.
        { ss. des. clarify.
          eapply memory_le_get_none; eauto.
          apply Memory.split_get0 in MEM. des. eauto. }
        { ss. destruct a. clarify.
          eapply FORGET. apply Memory.split_get0 in PROMISES.
          econs. des; eauto. }
        { eapply FORGET. econs; eauto. }
    - econs; eauto.
      * i. rewrite COMPLETE.
        { symmetry. erewrite Memory.lower_o; eauto. des_ifs.
          - ss. des. clarify. exfalso. apply NPROMS.
            apply Memory.lower_get0 in PROMISES. des.
            econs; eauto. }
        { ii. inv H. eapply NPROMS.
          exploit Memory.lower_o; try apply PROMISES; eauto. i.
          erewrite GET in *. des_ifs.
          - econs; eauto.
          - econs; eauto. }
      * i. inv PROMS. destruct msg1.
        erewrite Memory.lower_o in GET; eauto. des_ifs.
        { ss. des. clarify. eapply FORGET.
          apply Memory.lower_get0 in PROMISES. des. econs. eauto. }
        { eapply FORGET. apply Memory.lower_get0 in PROMISES.
          econs. des; eauto. }
    - econs; eauto.
      * i. erewrite (@Memory.remove_o mem_tgt'); eauto. des_ifs.
        { ss. des. clarify. eapply FORGET. econs; eauto.
          eapply Memory.remove_get0 in PROMISES. des. eauto. }
        { eapply COMPLETE. ii. inv H. eapply NPROMS. econs; eauto.
          erewrite Memory.remove_o; eauto.
          des_ifs; ss; des; clarify; eauto. }
      * i. inv PROMS. erewrite Memory.remove_o in GET; eauto. des_ifs.
        eapply FORGET; eauto. econs; eauto.
  Qed.

  Lemma self_promise_remove_write v prom v' prom'
        loc from to val releasedm released ord sc sc' mem_src
        mem_tgt mem_tgt' kind
        (WRITE: ALocal.write_step
                  (Local.mk v prom) sc mem_tgt
                  loc from to val releasedm released ord
                  (Local.mk v' prom') sc' mem_tgt' kind)
        (MEM: forget_memory (promised prom) mem_src mem_tgt)
        (LCWF: Local.wf (Local.mk v prom) mem_tgt)
  :
    exists mem_src',
      (<<WRITE: ALocal.write_step
                  (Local.mk v Memory.bot) sc mem_src
                  loc from to val releasedm released ord
                  (Local.mk v' Memory.bot) sc' mem_src' Memory.op_kind_add>>) /\
      (<<MEM: forget_memory (promised prom') mem_src' mem_tgt'>>).
  Proof.
    dup MEM. eapply forget_memory_le in MEM0. inv MEM.
    inv WRITE. ss. clarify.
    (* inv WRITE0. *)
    exploit write_msg_wf; eauto. i. des.
    exploit write_succeed; eauto.
    { instantiate (1:=mem_src).
      ii. inv LCWF. exploit write_disjoint; try apply WRITE0; eauto.
      i. des.
      - inv PROMISED. inv COVER. dup GET0.
        assert (NPRM: ~ promised prom loc to1).
        { ii. erewrite FORGET in GET0; eauto. clarify. }
        erewrite COMPLETE in GET0; eauto. exploit Memory.get_disjoint.
        + eapply GET0.
        + eapply PROMISES in GET. eapply GET.
        + i. des; clarify; eauto.
          eapply NPRM. econs; eauto.
      - eapply NEWMSG. eapply memory_le_covered; try apply MEM0; eauto. }
    i. des. exists mem2. esplits; ss.
    - econs 1; ss; eauto.
      ii. rewrite Memory.bot_get in *. clarify.
    - inv WRITE0. inv WRITE. inv PROMISE0. inv PROMISE.
      + exploit MemoryFacts.MemoryFacts.add_remove_eq.
        { eapply PROMISES0. }
        { eapply REMOVE. } i. clarify.
        econs; i.
        * erewrite (@Memory.add_o mem2); eauto.
          erewrite (@Memory.add_o mem_tgt'); cycle 1; eauto.
          des_ifs. eauto.
        * erewrite (@Memory.add_o mem2); eauto.
          des_ifs; eauto. ss. des. clarify. exfalso.
          eapply Memory.add_get0 in PROMISES0. des. inv PROMS. clarify.
      + econs; i.
        * erewrite (@Memory.add_o mem2); eauto.
          erewrite (@Memory.split_o mem_tgt'); cycle 1; eauto.
          des_ifs.
          { ss. destruct a. clarify. des; clarify. exfalso. eapply NPROMS.
            eapply Memory.split_get0 in PROMISES0. des.
            econs. erewrite Memory.remove_o; eauto. des_ifs; eauto.
            des; ss; clarify. }
          { ss. eapply COMPLETE. ii. eapply NPROMS.
            inv H. econs. instantiate (1:=msg).
            erewrite Memory.remove_o; eauto.
            erewrite Memory.split_o; eauto. des_ifs; ss; des; clarify. }
        * erewrite (@Memory.add_o mem2); eauto. des_ifs.
          { ss. des. clarify. exfalso. inv PROMS.
            erewrite Memory.remove_o in GET; eauto.
            des_ifs. ss. des; clarify. }
          { eapply FORGET. inv PROMS.
            erewrite Memory.remove_o in GET; eauto.
            erewrite Memory.split_o in GET; eauto. des_ifs.
            - ss; des; clarify.
              eapply Memory.split_get0 in PROMISES0. des. econs; eauto.
            - econs; eauto. }
      + econs; i.
        * erewrite (@Memory.add_o mem2); eauto.
          erewrite (@Memory.lower_o mem_tgt'); cycle 1; eauto.
          des_ifs. eapply COMPLETE.
          ii. eapply NPROMS. inv H. econs. instantiate (1:=msg).
          erewrite Memory.remove_o; eauto.
          erewrite Memory.lower_o; eauto. des_ifs. ss; des; clarify.
        * erewrite (@Memory.add_o mem2); eauto. des_ifs.
          { ss. des. clarify. exfalso. inv PROMS.
            erewrite Memory.remove_o in GET; eauto.
            des_ifs. ss. des; clarify. }
          { eapply FORGET. inv PROMS. econs.
            erewrite Memory.remove_o in GET; eauto.
            erewrite Memory.lower_o in GET; eauto. des_ifs. eauto. }
      + clarify.
  Qed.

  Definition forget_event e_src e_tgt: Prop :=
    match e_tgt with
    | ThreadEvent.promise _ _ _ _ _ => e_src = ThreadEvent.silent
    | _ => e_src = e_tgt
    end.

  Lemma forget_event_same_machine_event
    :
      forget_event <2= same_machine_event.
  Proof.
    ii. unfold forget_event in *. des_ifs.
  Qed.

  Lemma self_promise_remove
        P lang th_src th_tgt th_tgt' st st' v v' prom prom' sc sc'
        mem_src mem_tgt mem_tgt' e_tgt
        (NOREAD: P <1= no_read_msgs (promised prom))
        (STEP: (@pred_step P lang) e_tgt th_tgt th_tgt')
        (TH_SRC: th_src = Thread.mk lang st (Local.mk v Memory.bot) sc mem_src)
        (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem_tgt)
        (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
        (MEM: forget_memory (promised prom) mem_src mem_tgt)
        (LCWF: Local.wf (Local.mk v prom) mem_tgt)
        (CLOSED: Memory.closed mem_tgt)
    :
      exists mem_src' e_src,
        (<<STEP: opt_pred_step
                   (P /1\ no_promise) e_src th_src
                   (Thread.mk lang st' (Local.mk v' Memory.bot) sc' mem_src')>>) /\
        (<<EVT: forget_event e_src e_tgt>>) /\
        (<<MEM: forget_memory (promised prom') mem_src' mem_tgt'>>).
  Proof.
    dup MEM. eapply forget_memory_le in MEM0.
    clarify. inv STEP. dup SAT. eapply NOREAD in SAT.
    des. inv STEP0. inv STEP.
    - inv STEP0. ss. inv LOCAL. clarify. ss.
      exists mem_src, ThreadEvent.silent. esplits; eauto.
      eapply self_promise_remove_promise; eauto.
    - inv STEP0. ss. inv LOCAL; clarify; ss.
      + exists mem_src, ThreadEvent.silent.
        esplits; eauto. econs. econs; ss; eauto. econs; eauto.
        econs 2; eauto. econs; eauto.
      + exists mem_src, (ThreadEvent.read loc ts val released ord).
        inv LOCAL0. ss. clarify.
        esplits; eauto. econs. econs; ss; eauto. econs; eauto.
        econs 2; eauto. econs; eauto. econs 2; eauto. econs; eauto.
        inv MEM. rewrite COMPLETE; eauto.
      + exploit self_promise_remove_write; eauto. i. des.
        exists mem_src', (ThreadEvent.write loc from to val released ord).
        esplits; eauto. econs. econs; eauto. econs; eauto.
        econs 2; eauto. econs; eauto.
      + exploit Local.read_step_future; eauto. i. des.
        inv LOCAL1. ss. exploit self_promise_remove_write; eauto. i. des.
        exists mem_src',
        (ThreadEvent.update loc tsr tsw valr valw releasedr releasedw ordr ordw).
        esplits; eauto. econs. econs; ss; eauto. econs; eauto.
        econs 2; eauto. econs; eauto. econs; eauto. econs; eauto.
        inv MEM. rewrite COMPLETE; eauto.
      + inv LOCAL0. ss. clarify.
        exists mem_src, (ThreadEvent.fence ordr ordw).
        esplits; eauto. econs. econs; ss; eauto. econs; eauto.
        econs 2; eauto. econs; eauto. econs; eauto. econs; eauto. ss.
        ii. rewrite Memory.bot_get in *. clarify.
      + inv LOCAL0. ss. clarify.
        exists mem_src, (ThreadEvent.syscall e).
        esplits; eauto. econs. econs; ss; eauto. econs; eauto.
        econs 2; eauto. econs; eauto. econs; eauto. econs; eauto. ss.
        ii. rewrite Memory.bot_get in *. clarify.
      + inv LOCAL0. ss. clarify.
        exists mem_src, ThreadEvent.failure. esplits; eauto.
        econs. econs; ss; eauto. econs; eauto.
        econs 2; eauto. econs; eauto. econs; eauto. econs; eauto.
        ii. ss. erewrite Memory.bot_get in *. clarify.
  Qed.


End SELFPROMISEREMOVE.




Section OTHERPROMISEREMOVE.

  Lemma other_promise_remove_write v v' prom'
        loc from to val releasedm released ord sc sc' mem_src
        mem_tgt mem_tgt' kind others
        (WRITE: ALocal.write_step
                  (Local.mk v Memory.bot) sc mem_tgt
                  loc from to val releasedm released ord
                  (Local.mk v' prom') sc' mem_tgt' kind)
        (MEM: forget_memory others mem_src mem_tgt)
        (OTHERS: ~ others loc to)
  :
    exists mem_src',
      (<<WRITE: ALocal.write_step
                  (Local.mk v Memory.bot) sc mem_src
                  loc from to val releasedm released ord
                  (Local.mk v' Memory.bot) sc' mem_src' Memory.op_kind_add>>) /\
      (<<MEM: forget_memory others mem_src' mem_tgt'>>).
  Proof.
    exploit write_msg_wf; eauto. i. des.
    inv WRITE. ss. clarify. exploit memory_write_bot_add; eauto. i. clarify.
    dup WRITE0. inv WRITE0. inv PROMISE.
    exploit write_succeed; eauto.
    { instantiate (1:=mem_src). i. eapply forget_memory_le in MEM.
      eapply memory_le_covered in COVER; eauto. ii.
      exploit write_disjoint; try apply WRITE1; eauto.
      { eapply Memory.bot_le. }
      i. des; eauto. inv PROMISED.
      erewrite Memory.bot_get in GET. clarify. }
    i. des. exists mem2. econs; eauto.
    inv MEM. inv WRITE. inv PROMISE. econs; i.
    - erewrite (@Memory.add_o mem2); eauto.
      erewrite (@Memory.add_o mem_tgt'); cycle 1; eauto. des_ifs. eauto.
    - erewrite (@Memory.add_o mem2); eauto. des_ifs; eauto.
      ss. des. clarify.
  Qed.

  Lemma other_promise_remove
        P lang th_src th_tgt th_tgt' st st' v v' prom' sc sc'
        mem_src mem_tgt mem_tgt' e_tgt others
        (PRED: P <1= (no_read_msgs others /1\ write_not_in others /1\ no_promise))
        (STEP: (@pred_step P) lang e_tgt th_tgt th_tgt')
        (TH_SRC: th_src = Thread.mk lang st (Local.mk v Memory.bot) sc mem_src)
        (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v Memory.bot) sc mem_tgt)
        (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
        (MEM: forget_memory others mem_src mem_tgt)
    :
      exists mem_src',
        (<<STEP: (@pred_step P lang)
                   e_tgt th_src
                   (Thread.mk lang st' (Local.mk v' Memory.bot) sc' mem_src')>>) /\
        (<<MEM: forget_memory others mem_src' mem_tgt'>>).
  Proof.
    dup MEM. eapply forget_memory_le in MEM0.
    clarify. inv STEP. des. inv STEP0.
    dup SAT. eapply PRED in SAT. des. inv STEP.
    { inv STEP0. ss; clarify. }
    inv STEP0. inv LOCAL; ss.
    - exists mem_src. esplits; eauto. econs; eauto. econs; eauto.
      econs 2; eauto. econs; eauto.
    - inv LOCAL0. ss. clarify.
      exists mem_src. esplits; eauto. econs; eauto. econs; eauto.
      econs 2; eauto. econs; eauto. econs; eauto. econs; eauto.
      inv MEM. erewrite COMPLETE; eauto.
    - ss. exploit other_promise_remove_write; eauto.
      { exploit write_msg_wf; eauto. i. des.
        eapply SAT2. econs; eauto. refl. }
      i. des. exists mem_src'. esplits; eauto.
      econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
    - ss. inv LOCAL1. ss.
      exploit other_promise_remove_write; eauto.
      { exploit write_msg_wf; eauto. i. des.
        eapply SAT2. econs; eauto. refl. }
      i. des. exists mem_src'. esplits; eauto.
      econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
      econs; eauto. econs; eauto. inv MEM. erewrite COMPLETE; eauto.
    - inv LOCAL0. ss. clarify. exists mem_src. esplits; eauto.
      econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
    - inv LOCAL0. ss. clarify. exists mem_src. esplits; eauto.
      econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
    - inv LOCAL0. ss. clarify. exists mem_src. esplits; eauto.
      econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
  Qed.

End OTHERPROMISEREMOVE.







Section SHORTERMEMORY.

  Inductive shorter_memory (mem_src mem_tgt: Memory.t): Prop :=
  | shorter_memory_intro
      (COMPLETE: forall loc to from_tgt val released
                        (GET: Memory.get loc to mem_tgt = Some (from_tgt, Message.full val released)),
          exists from_src,
            (<<GET: Memory.get loc to mem_src = Some (from_src, Message.full val released)>>))
      (COVER: forall l t (COV: covered l t mem_src), covered l t mem_tgt)
  .
  Global Program Instance shorter_memory_PreOrder: PreOrder shorter_memory.
  Next Obligation. ii. econs; eauto. Qed.
  Next Obligation.
    ii. inv H. inv H0. econs; eauto.
    ii. exploit COMPLETE0; eauto. i. des.
    exploit COMPLETE; eauto.
  Qed.

  Lemma shorter_attatched mem_src mem_tgt loc to
        (ATTATCH: ~ attatched_time mem_tgt loc to)
        (NCOV: ~ covered loc to mem_tgt)
        (NBOT: Time.lt Time.bot to)
        (SHORTER: shorter_memory mem_src mem_tgt)
    :
      ~ attatched_time mem_src loc to.
  Proof.
    ii. unfold attatched_time in *. des.
    hexploit (@closed_point mem_tgt loc to to').
    { eapply memory_get_ts_strong in GET. des; clarify. }
    { i. inv SHORTER. eapply COVER. econs; eauto. }
    i. des. destruct TS0.
    - eapply NCOV. econs; eauto. econs; ss.
      left. auto.
    - inv H. eapply ATTATCH. esplits; eauto.
  Qed.

  Lemma shorter_closed_timemap mem_src mem_tgt tm
        (CLOSED: Memory.closed_timemap tm mem_tgt)
        (SHORTER: shorter_memory mem_src mem_tgt)
    :
      Memory.closed_timemap tm mem_src.
  Proof.
    inv SHORTER. ii. specialize (CLOSED loc). des.
    eapply COMPLETE in CLOSED. des. eauto.
  Qed.

  Lemma shorter_closed_view mem_src mem_tgt vw
        (CLOSED: Memory.closed_view vw mem_tgt)
        (SHORTER: shorter_memory mem_src mem_tgt)
    :
      Memory.closed_view vw mem_src.
  Proof.
    inv CLOSED. econs; eapply shorter_closed_timemap; eauto.
  Qed.

  Lemma shorter_closed_message mem_src mem_tgt msg
        (CLOSED: Memory.closed_message msg mem_tgt)
        (SHORTER: shorter_memory mem_src mem_tgt)
    :
      Memory.closed_message msg mem_src.
  Proof.
    inv CLOSED; econs. inv CLOSED0; econs.
    eapply shorter_closed_view; eauto.
  Qed.

  Lemma shorter_memory_add mem_src mem_tgt loc from1 to1 msg mem_tgt' from'
        (SHORTER: shorter_memory mem_src mem_tgt)
        (ADD: Memory.add mem_tgt loc from1 to1 msg mem_tgt')
        (TO: Time.le from1 from')
        (FROM: Time.lt from' to1)
    :
      exists mem_src',
        (<<ADD: Memory.add mem_src loc from' to1 msg mem_src'>>) /\
        (<<SHORTER: shorter_memory mem_src' mem_tgt'>>).
  Proof.
    dup ADD. eapply add_succeed_wf in ADD0. des.
    inv SHORTER.
    exploit (@Memory.add_exists mem_src loc from' to1 msg); eauto.
    { ii. exploit COVER.
      { econs; eauto. }
      intros COV. inv COV. eapply DISJOINT; eauto.
      inv LHS. econs; ss.
      eapply TimeFacts.le_lt_lt; eauto. }
    i. des. esplits; eauto. econs.
    + i. erewrite Memory.add_o in GET; eauto.
      erewrite Memory.add_o; cycle 1; eauto. des_ifs; eauto.
    + i. erewrite add_covered in COV; eauto.
      erewrite add_covered; cycle 1; eauto. des; auto.
      right. split; auto.
      inv COV0. econs; ss. eapply TimeFacts.le_lt_lt; eauto.
  Qed.

  Lemma shorter_memory_add_write prom mem_src mem_tgt loc from1 to1 val released prom' mem_tgt' from'
        (MLE: Memory.le prom mem_src)
        (SHORTER: shorter_memory mem_src mem_tgt)
        (ADD: AMemory.write prom mem_tgt loc from1 to1 val released prom' mem_tgt' Memory.op_kind_add)
        (TO: Time.le from1 from')
        (FROM: Time.lt from' to1)
    :
      exists mem_src',
        (<<ADD: AMemory.write prom mem_src loc from' to1 val released prom' mem_src' Memory.op_kind_add>>) /\
        (<<SHORTER: shorter_memory mem_src' mem_tgt'>>).
  Proof.
    dup SHORTER. inv SHORTER. inv ADD. inv PROMISE.
    exploit MemoryFacts.MemoryFacts.add_remove_eq; try apply REMOVE; eauto. i. clarify.
    exploit shorter_memory_add; eauto. i. des.
    exploit Memory.add_exists_le; eauto. i. des.
    esplits; eauto. econs; eauto.
    - econs; eauto.
      + i. clarify.
      (* + i. clarify. *)
      (*   eapply (@shorter_attatched mem_src mem_tgt loc to1). *)
      (*   * unfold attatched_time. ii. des. eapply ATTACH; eauto. *)
      (*   * ii. inv H. inv MEM. inv ADD0. eapply DISJOINT. *)
      (*     { eapply GET0. } *)
      (*     { instantiate (1:=to1). econs; ss. refl. } *)
      (*     { eauto. } *)
      (*   * eapply TimeFacts.le_lt_lt. *)
      (*     { eapply Time.bot_spec. } *)
      (*     { eauto. } *)
      (*   * eauto. *)
      (*   * eexists; eauto. *)
    - exploit Memory.remove_exists.
      { eapply Memory.add_get0; eauto. }
      i. des.
      exploit MemoryFacts.MemoryFacts.add_remove_eq; eauto.
      i. clarify.
  Qed.

  Lemma shorter_memory_promise prom mem_src mem_tgt loc from1 to1 msg prom' mem_tgt' kind
        (MLE: Memory.le prom mem_src)
        (SHORTER: shorter_memory mem_src mem_tgt)
        (PROMISE: AMemory.promise prom mem_tgt loc from1 to1 msg prom' mem_tgt' kind)
    :
      exists mem_src',
        (<<PROMISE: AMemory.promise prom mem_src loc from1 to1 msg prom' mem_src' kind>>) /\
        (<<SHORTER: shorter_memory mem_src' mem_tgt'>>).
  Proof.
    dup SHORTER. inv SHORTER. inv PROMISE.
    - exploit shorter_memory_add; eauto.
      { refl. }
      { inv MEM. inv ADD. auto. }
      i. des. esplits; eauto.
      econs; eauto.
      + i. clarify. specialize (RESERVE eq_refl). des.
        eapply COMPLETE in RESERVE. des. esplits; eauto.
      (* + i. clarify. *)
      (*   eapply (@shorter_attatched mem_src mem_tgt loc to1). *)
      (*   * unfold attatched_time. ii. des. eapply ATTACH; eauto. *)
      (*   * ii. inv H. inv MEM. inv ADD0. eapply DISJOINT. *)
      (*     { eapply GET0. } *)
      (*     { instantiate (1:=to1). econs; ss. refl. } *)
      (*     { eauto. } *)
      (*   * eapply TimeFacts.le_lt_lt. *)
      (*     { eapply Time.bot_spec. } *)
      (*     { inv MEM. inv ADD0. eauto. } *)
      (*   * eauto. *)
      (*   * eexists; eauto. *)
    - exploit Memory.split_exists_le; eauto. i. des.
      exists mem2. splits.
      + econs; eauto.
      + econs; eauto.
        * dup x0. eapply Memory.split_get0 in x1. des.
          i. erewrite Memory.split_o in GET3; eauto.
          erewrite Memory.split_o; cycle 1; eauto.
          des_ifs; eauto.
        * ii. erewrite split_covered in COV; cycle 1; eauto.
          erewrite split_covered; cycle 1; eauto.
    - exploit Memory.lower_exists_le; eauto. i. des.
      exists mem2. splits.
      + econs; eauto.
      + econs; eauto.
        * dup x0. eapply Memory.lower_get0 in x1. des.
          i. erewrite Memory.lower_o in GET1; eauto.
          erewrite Memory.lower_o; cycle 1; eauto.
          des_ifs; eauto.
        * ii. erewrite lower_covered in COV; cycle 1; eauto.
          erewrite lower_covered; cycle 1; eauto.
    - exploit Memory.remove_exists.
      { eapply MLE. eapply Memory.remove_get0; eauto. }
      i. des. exists mem2. splits.
      + econs; eauto.
      + econs; eauto.
        * dup x0. eapply Memory.remove_get0 in x1. des.
          i. erewrite Memory.remove_o in GET1; eauto.
          erewrite Memory.remove_o; cycle 1; eauto.
          des_ifs; eauto.
        * ii. erewrite remove_covered in COV; cycle 1; eauto.
          erewrite remove_covered; cycle 1; eauto. des; auto.
  Qed.

  Lemma shorter_memory_write prom mem_src mem_tgt loc from1 to1 val released prom' mem_tgt' kind
        (MLE: Memory.le prom mem_src)
        (SHORTER: shorter_memory mem_src mem_tgt)
        (WRITE: AMemory.write prom mem_tgt loc from1 to1 val released prom' mem_tgt' kind)
    :
      exists mem_src',
        (<<WRITE: AMemory.write prom mem_src loc from1 to1 val released prom' mem_src' kind>>) /\
        (<<SHORTER: shorter_memory mem_src' mem_tgt'>>).
  Proof.
    inv WRITE.
    exploit shorter_memory_promise; eauto. i. des.
    esplits; eauto.
  Qed.

  Lemma shorter_memory_step
        P lang th_src th_tgt th_tgt' st st' v v' prom prom' sc sc'
        mem_tgt mem_tgt' mem_src e
        (STEP: (@pred_step P lang) e th_tgt th_tgt')
        (MLE: Memory.le prom mem_src)
        (TH_SRC: th_src = Thread.mk lang st (Local.mk v prom) sc mem_src)
        (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem_tgt)
        (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
        (SHORTER: shorter_memory mem_src mem_tgt)
    :
      exists mem_src',
        (<<STEP: (@pred_step P lang)
                   e th_src
                   (Thread.mk lang st' (Local.mk v' prom') sc' mem_src')>>) /\
        (<<SHORTER: shorter_memory mem_src' mem_tgt'>>).
  Proof.
    dup SHORTER. inv SHORTER. inv STEP.
    inv STEP0. inv STEP.
    - inv STEP0. inv LOCAL. ss. clarify.
      exploit shorter_memory_promise; eauto. i. des.
      esplits; eauto. econs; eauto. econs; eauto. econs 1; eauto. econs; eauto.
      econs; eauto. eapply shorter_closed_message; eauto.
    - inv STEP0. inv LOCAL.
      + exists mem_src; eauto. econs; eauto. econs; eauto.
        econs; eauto. econs 2; eauto. econs; eauto.
      + inv LOCAL0. ss. clarify. exploit COMPLETE; eauto. i. des.
        exists mem_src; eauto. econs; eauto. econs; eauto.
        econs; eauto. econs 2; eauto. econs; eauto.
      + exploit write_msg_wf; eauto. i. des.
        inv LOCAL0. ss. clarify.
        exploit shorter_memory_write; eauto. i. des.
        esplits; eauto. econs; eauto. econs; eauto. econs 2; eauto.
        econs; eauto.
      + inv LOCAL1. ss. exploit write_msg_wf; eauto. i. des.
        exploit COMPLETE; eauto. i. des.
        inv LOCAL2. ss. clarify.
        exploit shorter_memory_write; eauto. i. des.
        esplits; eauto. econs; eauto. econs; eauto. econs 2; eauto.
        econs; eauto.
      + inv LOCAL0. ss. clarify. esplits; eauto. econs; eauto.
        econs; eauto. econs 2; eauto. econs; eauto.
      + inv LOCAL0. ss. clarify. esplits; eauto. econs; eauto.
        econs; eauto. econs 2; eauto. econs; eauto.
      + inv LOCAL0. ss. clarify. esplits; eauto. econs; eauto.
        econs; eauto. econs 2; eauto. econs; eauto.
  Qed.

End SHORTERMEMORY.


Section NOTATTATCHED.

  Definition not_attatched (L: Loc.t -> Time.t -> Prop) (mem: Memory.t) :=
    forall loc to (SAT: L loc to),
      (<<CONCRETE: concrete_promised mem loc to>>) /\
      (<<NOATTATCH: exists to',
          (<<TLE: Time.lt to to'>>) /\
          (<<EMPTY: forall t (ITV: Interval.mem (to, to') t), ~ covered loc t mem>>)>>).

  Lemma not_attatched_sum L0 L1 mem
        (NOATTATCH0: not_attatched L0 mem)
        (NOATTATCH1: not_attatched L1 mem)
    :
      not_attatched (L0 \2/ L1) mem.
  Proof.
    ii. des; eauto.
  Qed.

  Lemma not_attatched_mon L0 L1 mem
        (NOATTATCH0: not_attatched L0 mem)
        (LE: L1 <2= L0)
    :
      not_attatched L1 mem.
  Proof.
    ii. eauto.
  Qed.

  Lemma attached_preserve_add updates mem0 loc from to msg mem1
        (ADD: Memory.add mem0 loc from to msg mem1)
        (NOATTATCHED: not_attatched updates mem1)
        (PROMISED: updates <2= concrete_promised mem0)
    :
      not_attatched updates mem0.
  Proof.
    ii. exploit NOATTATCHED; eauto. i. des. split.
    - auto.
    - esplits; eauto. ii. eapply EMPTY; eauto.
      eapply add_covered; eauto.
  Qed.

  Lemma attatched_preserve P updates lang (th0 th1: Thread.t lang) e
        (PRED: P <1= no_promise)
        (STEP: (@pred_step P lang) e th0 th1)
        (BOT: (Local.promises (Thread.local th0)) = Memory.bot)
        (NOATTATCHED: not_attatched updates (Thread.memory th1))
        (PROMISED: updates <2= concrete_promised (Thread.memory th0))
    :
      not_attatched updates (Thread.memory th0).
  Proof.
    inv STEP. inv STEP0. eapply PRED in SAT. inv STEP.
    - inv STEP0; des; clarify.
    - inv STEP0. ss. inv LOCAL; ss.
      + inv LOCAL0. destruct lc1. ss. clarify.
        exploit memory_write_bot_add; eauto. i. clarify.
        inv WRITE. inv PROMISE.
        eapply attached_preserve_add; eauto.
      + inv LOCAL1. inv LOCAL2. ss. destruct lc1. ss. clarify.
        exploit memory_write_bot_add; eauto. i. clarify.
        inv WRITE. inv PROMISE.
        eapply attached_preserve_add; eauto.
  Qed.

  Lemma update_not_attatched P lang (th0 th1: Thread.t lang)
        loc from to valr valw releasedr releasedw ordr ordw
        (STEP: (@pred_step P lang) (ThreadEvent.update loc from to valr valw releasedr releasedw ordr ordw) th0 th1)
        (BOT: (Local.promises (Thread.local th0)) = Memory.bot)
    :
      not_attatched (fun l t => l = loc /\ t = from) (Thread.memory th0).
  Proof.
    inv STEP. inv STEP0. inv STEP; ss.
    - inv STEP0; des; clarify.
    - inv STEP0. ss. inv LOCAL; ss. destruct lc1, lc3, lc2.
      exploit write_msg_wf; eauto. i. des. ss. clarify.
      inv LOCAL1. inv LOCAL2. ss. clarify.
      exploit memory_write_bot_add; eauto. i. clarify.
      ii. des. clarify. esplits; eauto.
      + econs; eauto.
      + ii. inv WRITE. inv PROMISE. eapply memory_add_cover_disjoint in MEM; eauto.
  Qed.

  Lemma attatched_preserve_rtc P updates lang (th0 th1: Thread.t lang)
        (PRED: P <1= no_promise)
        (STEP: rtc (tau (@pred_step P lang)) th0 th1)
        (BOT: (Local.promises (Thread.local th0)) = Memory.bot)
        (NOATTATCHED: not_attatched updates (Thread.memory th1))
        (PROMISED: updates <2= concrete_promised (Thread.memory th0))
    :
      not_attatched updates (Thread.memory th0).
  Proof.
    revert BOT PROMISED. induction STEP; auto.
    i. hexploit IHSTEP; eauto.
    - inv H. eapply promise_bot_no_promise; eauto.
    - i. inv H. inv TSTEP. inv STEP0. eapply concrete_promised_increase; eauto.
    - i. inv H. eapply attatched_preserve; eauto.
  Qed.

  Lemma not_attatch_promise L prom mem_src loc from1 to1 msg prom' mem_src' kind
        (PROMISE: AMemory.promise prom mem_src loc from1 to1 msg prom' mem_src' kind)
        (NOATTATCH: not_attatched L mem_src)
        (FROM: kind = Memory.op_kind_add -> ~ L loc from1)
    :
      (<<NOATTATCH: not_attatched L mem_src'>>).
  Proof.
    ii. exploit NOATTATCH; eauto. i. des.
    dup CONCRETE.
    eapply concrete_promised_increase_promise in CONCRETE0; eauto. inv CONCRETE.
    inv PROMISE.
    - clear PROMISES.
      destruct (Loc.eq_dec loc loc0); clarify.
      + esplit; eauto. clear CONCRETE0.
        exists (if (Time.le_lt_dec to from1)
                then (Time.meet to' from1)
                else to'). esplits; eauto.
        * unfold Time.meet. des_ifs.
          destruct l; eauto. inv H. exfalso. eapply FROM; auto.
        * ii. erewrite add_covered in H; eauto. des.
          { eapply EMPTY; eauto. unfold Time.meet in *. des_ifs.
            inv ITV. econs; ss; eauto.
            left. eapply TimeFacts.le_lt_lt; eauto. }
          { clarify. unfold Time.meet in *.
            dup ITV. dup H0. inv ITV. inv H0. ss. des_ifs.
            - clear - FROM1 TO l0.
              eapply Time.lt_strorder.
              instantiate (1:=from1).
              eapply TimeFacts.lt_le_lt; eauto.
            - eapply Time.lt_strorder.
              instantiate (1:=from1).
              eapply TimeFacts.lt_le_lt; eauto.
            - dup MEM. eapply Memory.add_get0 in MEM. des.
              exploit Memory.get_disjoint.
              { eapply GET1. }
              { eapply Memory.add_get1; try apply GET; eauto. }
              exploit memory_get_ts_strong; try apply GET. i. des; clarify.
              + exfalso. eapply Time.lt_strorder.
                eapply TimeFacts.lt_le_lt.
                * eapply l.
                * eapply Time.bot_spec.
              + eapply x1.
                { instantiate (1:=to).
                  econs; ss; eauto. etrans; eauto. left. auto. }
                { econs; ss; eauto. refl. }
          }
      + esplits; eauto. ii.
        erewrite add_covered in H; eauto. des; clarify.
        eapply EMPTY; eauto.
    - esplits; eauto. ii. erewrite split_covered in H; eauto.
      eapply EMPTY; eauto.
    - esplits; eauto. ii. erewrite lower_covered in H; eauto.
      eapply EMPTY; eauto.
    - esplits; eauto. ii. erewrite remove_covered in H; eauto.
      destruct H. eapply EMPTY; eauto.
  Qed.

  Lemma not_attatch_write L prom mem_src loc from1 to1 val released prom' mem_src' kind
        (PROMISE: AMemory.write prom mem_src loc from1 to1 val released prom' mem_src' kind)
        (NOATTATCH: not_attatched L mem_src)
        (FROM: kind = Memory.op_kind_add -> ~ L loc from1)
    :
      (<<NOATTATCH: not_attatched L mem_src'>>).
  Proof.
    inv PROMISE. eapply not_attatch_promise; eauto.
  Qed.

  Inductive shorter_event: ThreadEvent.t -> ThreadEvent.t -> Prop :=
  | shorter_event_read
      loc to val released ordr
    :
      shorter_event
        (ThreadEvent.read loc to val released ordr)
        (ThreadEvent.read loc to val released ordr)
  | shorter_event_write
      loc from ffrom to val released ordw
      (FROM: Time.le from ffrom)
    :
      shorter_event
        (ThreadEvent.write loc ffrom to val released ordw)
        (ThreadEvent.write loc from to val released ordw)
  | shorter_event_update
      loc from to valr valw releasedr releasedw ordr ordw
    :
      shorter_event
        (ThreadEvent.update loc from to valr valw releasedr releasedw ordr ordw)
        (ThreadEvent.update loc from to valr valw releasedr releasedw ordr ordw)
  | shorter_event_fence
      or ow
    :
      shorter_event
        (ThreadEvent.fence or ow)
        (ThreadEvent.fence or ow)
  | shorter_event_syscall
      e
    :
      shorter_event
        (ThreadEvent.syscall e)
        (ThreadEvent.syscall e)
  | shorter_event_silent
    :
      shorter_event
        (ThreadEvent.silent)
        (ThreadEvent.silent)
  | shorter_event_failure
    :
      shorter_event
        (ThreadEvent.failure)
        (ThreadEvent.failure)
  | shorter_event_promise
      loc from to msg kind
    :
      shorter_event
        (* (ThreadEvent.silent) *)
        (ThreadEvent.promise loc from to msg kind)
        (ThreadEvent.promise loc from to msg kind)
  .
  Global Program Instance shorter_event_PreOrder: PreOrder shorter_event.
  Next Obligation. ii. destruct x; econs. refl. Qed.
  Next Obligation.
    ii. inv H; inv H0; econs; eauto.
  Qed.

  Lemma shorter_event_shift L
        e_src e_tgt
        (SAT: (write_not_in L /1\ no_promise) e_tgt)
        (EVT: shorter_event e_src e_tgt)
    :
      (write_not_in L /1\ no_promise) e_src.
  Proof.
    ss. des. inv EVT; ss. split; auto. i.
    eapply SAT. inv IN. econs; ss.
    eapply TimeFacts.le_lt_lt; eauto.
  Qed.

  Lemma no_update_on_step
        P L lang th_src th_tgt th_tgt' st st' v v' prom prom' sc sc'
        mem_tgt mem_tgt' mem_src e_tgt
        (LCWF: Memory.le prom mem_src)
        (PRED: P <1= (no_update_on L /1\ promise_free))
        (STEP: (@pred_step P lang) e_tgt th_tgt th_tgt')
        (TH_SRC: th_src = Thread.mk lang st (Local.mk v prom) sc mem_src)
        (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem_tgt)
        (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
        (SHORTER: shorter_memory mem_src mem_tgt)
        (NOATTATCH: not_attatched L mem_src)
    :
      exists e_src mem_src',
        (<<STEP: AThread.step_allpf
                   e_src th_src
                   (Thread.mk lang st' (Local.mk v' prom') sc' mem_src')>>) /\
        (<<EVT: shorter_event e_src e_tgt>>) /\
        (<<SHORTER: shorter_memory mem_src' mem_tgt'>>) /\
        (<<NOATTATCH: not_attatched L mem_src'>>).
  Proof.
    dup SHORTER. inv SHORTER. inv STEP.
    eapply PRED in SAT. inv STEP0. des. inv STEP.
    - inv STEP0. inv LOCAL. ss. clarify.
      exploit shorter_memory_promise; eauto. i. des.
      exists (ThreadEvent.promise loc from to msg kind), mem_src'. splits; auto.
      + econs; eauto. econs 1; eauto. econs; eauto. econs; eauto.
        eapply shorter_closed_message; eauto.
      + econs.
      + eapply not_attatch_promise; eauto. i. clarify.
    - inv STEP0. inv LOCAL.
      + exists ThreadEvent.silent, mem_src; eauto. esplits; eauto.
        * econs; eauto. econs 2; eauto. econs; eauto.
        * econs.
      + inv LOCAL0. ss. clarify. exploit COMPLETE; eauto. i. des.
        exists (ThreadEvent.read loc ts val released ord). exists mem_src; eauto.
        econs; eauto.
        * econs; eauto. econs 2; eauto. econs; eauto.
        * esplits; eauto. econs.
      + exploit write_msg_wf; eauto. i. des. inv LOCAL0. ss. clarify.
        destruct (classic (kind = Memory.op_kind_add)); cycle 1.
        { exploit shorter_memory_write; eauto. i. des.
          exists (ThreadEvent.write loc from to val (TView.write_released v sc loc to None ord) ord), mem_src'.
          splits; auto.
          - econs; eauto. econs 2; eauto. econs; eauto.
          - refl.
          - eapply not_attatch_write; eauto. }
        clarify. dup WRITE. exploit Time.middle_spec; eauto. i. des.
        exploit shorter_memory_add_write.
        { eauto. }
        { eauto. }
        { eauto. }
        { instantiate (1:=Time.middle from to). left. auto. }
        { auto. }
        i. des.
        exists (ThreadEvent.write loc (Time.middle from to) to val (TView.write_released v sc loc to None ord) ord), mem_src'.
        splits; auto.
        * econs; eauto.
          { econs 2; eauto. econs; eauto. }
        * econs; eauto. left. eauto.
        * eapply not_attatch_write; eauto. ii.
          exploit NOATTATCH; eauto. i. des. inv CONCRETE.
          exploit memory_add_cover_disjoint; auto.
          { inv WRITE. inv PROMISE. eapply MEM. }
          { instantiate (1:=(Time.middle from to)).
            econs; eauto. ss. left. eauto. }
          { apply COVER. econs; eauto.
            econs; ss; eauto.
            - exploit memory_get_ts_strong; eauto. i. des; clarify.
              exfalso. rewrite x3 in *.
              eapply Time.lt_strorder.
              instantiate (1:=Time.bot).
              eapply TimeFacts.le_lt_lt; eauto.
              apply Time.bot_spec.
            - refl. }
      + inv LOCAL1. ss.
        exists (ThreadEvent.update loc tsr tsw valr valw releasedr releasedw ordr ordw).
        exploit write_msg_wf; eauto. i. des.
        exploit COMPLETE; eauto. i. des.
        inv LOCAL2. ss. clarify.
        exploit shorter_memory_write; eauto. i. des.
        exists mem_src'. splits; auto.
        * econs; eauto. econs 2; eauto. econs; eauto.
        * refl.
        * eapply not_attatch_write; eauto.
      + eexists. exists mem_src; eauto. esplits; eauto.
        * econs; eauto. econs 2; eauto. econs; eauto.
        * econs.
      + eexists. exists mem_src; eauto. esplits; eauto.
        * econs; eauto. econs 2; eauto. econs; eauto.
        * econs.
      + eexists. exists mem_src; eauto. esplits; eauto.
        * econs; eauto. econs 2; eauto. econs; eauto.
        * econs.
  Qed.

  Lemma no_update_on_steps
        P0 P1 L lang th_src th_tgt th_tgt' st st' v v' prom prom' sc sc'
        mem_tgt mem_tgt' mem_src
        (LCWF: Memory.le prom mem_src)
        (PRED: P0 <1= (no_update_on L /1\ promise_free))
        (STEPS: rtc (tau (@pred_step P0 lang)) th_tgt th_tgt')
        (TH_SRC: th_src = Thread.mk lang st (Local.mk v prom) sc mem_src)
        (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem_tgt)
        (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
        (SHORTER: shorter_memory mem_src mem_tgt)
        (NOATTATCH: not_attatched L mem_src)
        (SHIFT: te_pred_shift P1 P0 shorter_event)
    :
      exists mem_src',
        (<<STEPS: rtc (tau (@pred_step P1 lang)) th_src
                      (Thread.mk lang st' (Local.mk v' prom') sc' mem_src')>>) /\
        (<<SHORTER: shorter_memory mem_src' mem_tgt'>>) /\
        (<<NOATTATCH: not_attatched L mem_src'>>).
  Proof.
    ss. ginduction STEPS; i; ss; clarify.
    - esplits; eauto.
    - inv H. destruct y. destruct local.
      exploit no_update_on_step; try apply TSTEP; eauto. i. des.
      exploit IHSTEPS; cycle 1; eauto.
      + i. des. esplits; eauto. econs; eauto. econs.
        * econs; eauto. eapply SHIFT; eauto.
          inv TSTEP. eauto.
        * inv EVT; auto.
      + eapply step_promises_le in STEP; eauto.
  Qed.

  Lemma no_update_on_traced_step
        L lang th_src th_tgt th_tgt' st st' lc lc' sc sc'
        mem_tgt mem_tgt' mem_src tr_tgt
        (PRED: List.Forall (fun em => (no_update_on L /1\ promise_free) (fst em)) tr_tgt)
        (LCWF: Memory.le (Local.promises lc) mem_src)
        (STEPS: traced_step tr_tgt th_tgt th_tgt')
        (TH_SRC: th_src = Thread.mk lang st lc sc mem_src)
        (TH_TGT0: th_tgt = Thread.mk lang st lc sc mem_tgt)
        (TH_TGT1: th_tgt' = Thread.mk lang st' lc' sc' mem_tgt')
        (SHORTER: shorter_memory mem_src mem_tgt)
        (NOATTATCH: not_attatched L mem_src)
    :
      exists mem_src' tr_src,
        (<<STEPS: traced_step tr_src th_src (Thread.mk lang st' lc' sc' mem_src')>>) /\
        (<<SHORTER: shorter_memory mem_src' mem_tgt'>>) /\
        (<<NOATTATCH: not_attatched L mem_src'>>) /\
        (<<TRACE: List.Forall2 (fun em_src em_tgt => <<EVENT: shorter_event (fst em_src) (fst em_tgt)>> /\ <<MEM: shorter_memory (snd em_src) (snd em_tgt)>>) tr_src tr_tgt>>)
  .
  Proof.
    ss. ginduction STEPS; i; ss; clarify.
    - esplits; eauto. econs.
    - ss. destruct th1. destruct lc, local. ss. inv PRED. ss. des.
      exploit no_update_on_step; ss; eauto.
      { instantiate (1:= no_update_on L /1\ promise_free). ss. }
      { econs; eauto. }
      i. des.
      exploit IHSTEPS; eauto.
      { eapply step_promises_le in STEP; eauto. }
      i. des.
      esplits; eauto.
      + econs; eauto.
      + econs; eauto.
  Qed.

End NOTATTATCHED.


Section FORGET.

  Inductive forget_statelocal:
    sigT (@Language.state ProgramEvent.t) * Local.t -> sigT (@Language.state ProgramEvent.t) * Local.t -> Prop :=
  | forget_statelocal_intro
      st lc1 lc2
      (TVIEW : (Local.tview lc1) = (Local.tview lc2))
      (PROMS : (Local.promises lc1) = Memory.bot)
    :
      forget_statelocal (st, lc1) (st, lc2)
  .

  Inductive pf_sim_memory (proms: Loc.t -> Time.t -> Prop) (mem_src mem_tgt: Memory.t): Prop :=
  | pf_sim_memory_intro
      mem_inter
      (FORGET: forget_memory proms mem_inter mem_tgt)
      (SHORTER: shorter_memory mem_src mem_inter)
  .

  Inductive forget_thread others lang: Thread.t lang -> Thread.t lang -> Prop :=
  | forget_thread_intro
      st v prom sc mem_src mem_tgt
      (MEMP: pf_sim_memory (others \2/ promised prom) mem_src mem_tgt)
    :
      forget_thread
        others
        (Thread.mk lang st (Local.mk v Memory.bot) sc mem_src)
        (Thread.mk lang st (Local.mk v prom) sc mem_tgt)
  .

  Inductive all_promises (ths: Threads.t) (P: IdentMap.key -> Prop)
            (l: Loc.t) (t: Time.t) : Prop :=
  | all_promises_intro
      tid st lc
      (TID1: IdentMap.find tid ths = Some (st, lc))
      (PROMISED: promised (Local.promises lc) l t)
      (SAT: P tid)
  .

  Inductive forget_config csrc ctgt : Prop :=
  | forget_configuration_intro
      (THS : forall tid, option_rel
                           forget_statelocal
                           (IdentMap.find tid (Configuration.threads csrc))
                           (IdentMap.find tid (Configuration.threads ctgt)))
      (SC : (Configuration.sc csrc) = (Configuration.sc ctgt))
      (MEM : pf_sim_memory (all_promises (Configuration.threads ctgt) (fun _ => True))
                           (Configuration.memory csrc)
                           (Configuration.memory ctgt))
  .

End FORGET.



Definition memory_reserve_wf mem := Memory.reserve_wf mem mem.

Lemma memory_reserve_wf_promise
      prom0 mem0 loc from to msg prom1 mem1 kind
      (PROMISE: Memory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
      (RESERVE: memory_reserve_wf mem0)
  :
    memory_reserve_wf mem1.
Proof.
  inv PROMISE.
  - ii. erewrite Memory.add_o in GET; eauto. des_ifs.
    + ss; des; clarify. exploit RESERVE0; eauto.
      i. des. eapply Memory.add_get1 in x; eauto.
    + eapply RESERVE in GET; eauto. clear o. des.
      eapply Memory.add_get1 in GET; eauto.
  - ii. des. clarify. erewrite Memory.split_o in GET; eauto. des_ifs.
    + ss; des; clarify. eapply Memory.split_get0 in MEM. des.
      esplits; eauto.
    + eapply RESERVE in GET; eauto. clear o o0. des.
      eapply Memory.split_get1 in GET; eauto. des. esplits; eauto.
  - ii. erewrite Memory.lower_o in GET; eauto. des_ifs.
    + ss; des; clarify. inv MEM. inv LOWER. inv MSG_LE.
    + eapply RESERVE in GET; eauto. clear o. des.
      eapply Memory.lower_get1 in GET; eauto. des.
      inv MSG_LE. esplits; eauto.
  - ii. erewrite Memory.remove_o in GET; eauto. des_ifs. guardH o.
    dup MEM. eapply Memory.remove_get0 in MEM0. des.
    eapply RESERVE in GET; eauto. des. dup GET.
    eapply Memory.remove_get1 in GET2; eauto. ss. des; clarify.
    esplits; eauto.
Qed.

Lemma memory_reserve_wf_tstep lang (th0 th1: Thread.t lang) tf e
      (RESERVE: memory_reserve_wf (Thread.memory th0))
      (STEP: Thread.step tf e th0 th1)
  :
    memory_reserve_wf (Thread.memory th1).
Proof.
  inv STEP; inv STEP0; ss.
  - inv LOCAL. eapply memory_reserve_wf_promise; eauto.
  - inv LOCAL; eauto.
    + inv LOCAL0. inv WRITE.
      eapply memory_reserve_wf_promise; eauto.
    + inv LOCAL1. inv LOCAL2. inv WRITE.
      eapply memory_reserve_wf_promise; eauto.
Qed.

Lemma memory_reserve_wf_tsteps lang (th0 th1: Thread.t lang)
      (RESERVE: memory_reserve_wf (Thread.memory th0))
      (STEP: rtc (tau (@Thread.step_allpf lang)) th0 th1)
  :
    memory_reserve_wf (Thread.memory th1).
Proof.
  ginduction STEP; eauto.
  i. eapply IHSTEP; eauto. inv H. inv TSTEP.
  eapply memory_reserve_wf_tstep; eauto.
Qed.

Lemma memory_reserve_wf_init
  :
    memory_reserve_wf Memory.init.
Proof.
  ii. unfold Memory.get, Memory.init in *. ss.
  rewrite Cell.init_get in GET. des_ifs.
Qed.

Lemma memory_reserve_wf_configuration_step c0 c1 e tid
      (RESERVE: memory_reserve_wf (Configuration.memory c0))
      (STEP: Configuration.step e tid c0 c1)
  :
    memory_reserve_wf (Configuration.memory c1).
Proof.
  eapply configuration_step_equivalent in STEP. inv STEP. ss.
  eapply memory_reserve_wf_tstep in STEP0; eauto.
  eapply memory_reserve_wf_tsteps in STEPS; eauto.
Qed.

Lemma not_latest_reserve_le_max_full_ts loc mem ts to from msg
      (RESERVEWF : memory_reserve_wf mem)
      (INHABITED : Memory.inhabited mem)
      (MAX : Memory.max_full_ts mem loc ts)
      (GET: Memory.get loc to mem = Some (from, msg))
  :
    (<<TLE: Time.le to ts>>) \/
    ((<<TO: to = Memory.max_ts loc mem>>) /\
     (<<FROM: from = ts>>) /\
     (<<MSG: msg = Message.reserve>>)).
Proof.
  inv MAX. des.
  destruct msg.
  - left. eapply MAX0; eauto.
  - exploit RESERVEWF; eauto. i. des.
    destruct (TimeFacts.le_lt_dec to ts); auto.
    dup x. eapply MAX0 in x; eauto. destruct x.
    + exfalso. exploit memory_get_from_mon.
      { eapply GET0. }
      { eapply GET. }
      { auto. }
      i. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
      * eapply x1.
      * eapply H.
    + unfold Time.eq in *. subst. right. esplits; eauto.
      setoid_rewrite GET0 in x0. clarify.
      dup GET. eapply Memory.max_ts_spec in GET1. des.
      destruct MAX; auto. exfalso.
      destruct msg.
      * eapply MAX0 in GET2. eapply Time.lt_strorder.
        eapply TimeFacts.lt_le_lt.
        { etrans.
          - eapply l.
          - eapply H. }
        { eauto. }
      * dup GET2. eapply RESERVEWF in GET2. des.
        eapply MAX0 in GET2.
        exploit memory_get_from_mon.
        { eapply GET. }
        { eapply GET1. }
        { eapply H. }
        i. eapply Time.lt_strorder.
        eapply TimeFacts.lt_le_lt.
        { eapply l. }
        { etrans.
          - eapply x0.
          - eapply Memory.get_ts in GET1. des; clarify. }
Qed.

Lemma max_ts_reserve_from_full_ts mem0 loc from
      (INHABITED: Memory.inhabited mem0)
      (RESERVEWF0: memory_reserve_wf mem0)
      (GET: Memory.get loc (Memory.max_ts loc mem0) mem0 = Some (from, Message.reserve))
  :
    Memory.max_full_ts mem0 loc from.
Proof.
  exploit Memory.max_full_ts_exists; eauto. intros [max MAX].
  dup GET. eapply not_latest_reserve_le_max_full_ts in GET; eauto.
  des; clarify. exfalso.
  exploit Memory.max_full_ts_spec; eauto. i. des.
  exploit TimeFacts.antisym.
  { eapply TLE. }
  { eapply Memory.max_ts_spec; eauto. }
  i. clarify.
Qed.

Lemma max_full_ts_max_ts loc mem ts
      (RESERVEWF : memory_reserve_wf mem)
      (INHABITED : Memory.inhabited mem)
      (MAX : Memory.max_full_ts mem loc ts)
  :
    (<<FULL: ts = Memory.max_ts loc mem>>) \/
    ((<<TLT: Time.lt ts (Memory.max_ts loc mem)>>) /\
     (<<GET: Memory.get loc (Memory.max_ts loc mem) mem = Some (ts, Message.reserve)>>)).
Proof.
  dup MAX. inv MAX. des.
  eapply Memory.max_ts_spec in GET. des.
  dup GET0. eapply not_latest_reserve_le_max_full_ts in GET0; eauto.
  des; clarify.
  - left. eapply TimeFacts.antisym; eauto.
  - right. split; eauto. dup GET1.
    eapply memory_get_ts_strong in GET1. des; clarify.
    erewrite GET2 in *.
    erewrite INHABITED in GET0. clarify.
Qed.

Definition reserver_exists (c: Configuration.t) :=
  forall loc to from
         (RESERVE: Memory.get loc to (Configuration.memory c) = Some (from, Message.reserve)),
  exists tid st lc,
    (<<TIDSRC: IdentMap.find tid (Configuration.threads c) =
               Some (st, lc)>>) /\
    (<<PROM: Memory.get loc to (Local.promises lc) = Some (from, Message.reserve)>>).

Require Import APFPF.




Lemma promise_new_reserve prom0 mem0 loc from to msg prom1 mem1 kind
      (PROMISE: AMemory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
      loc0 to0 from0
      (GET: Memory.get loc0 to0 mem1 = Some (from0, Message.reserve))
      (NONE: Memory.get loc0 to0 prom1 <> Some (from0, Message.reserve))
  :
    (<<GET: Memory.get loc0 to0 mem0 = Some (from0, Message.reserve)>>) /\
    (<<NONE: Memory.get loc0 to0 prom0 <> Some (from0, Message.reserve)>>)
.
Proof.
  inv PROMISE.
  - erewrite Memory.add_o in GET; eauto.
    erewrite Memory.add_o in NONE; eauto. des_ifs.
  - erewrite Memory.split_o in GET; eauto.
    erewrite Memory.split_o in NONE; eauto. des_ifs.
  - erewrite Memory.lower_o in GET; eauto.
    erewrite Memory.lower_o in NONE; eauto. des_ifs.
  - erewrite Memory.remove_o in GET; eauto.
    erewrite Memory.remove_o in NONE; eauto. des_ifs.
Qed.

Lemma write_new_reserve prom0 mem0 loc from to val released prom1 mem1 kind
      (wRITE: AMemory.write prom0 mem0 loc from to val released prom1 mem1 kind)
      loc0 to0 from0
      (GET: Memory.get loc0 to0 mem1 = Some (from0, Message.reserve))
      (NONE: Memory.get loc0 to0 prom1 <> Some (from0, Message.reserve))
  :
    (<<GET: Memory.get loc0 to0 mem0 = Some (from0, Message.reserve)>>) /\
    (<<NONE: Memory.get loc0 to0 prom0 <> Some (from0, Message.reserve)>>)
.
Proof.
  inv wRITE. erewrite Memory.remove_o in NONE; eauto. des_ifs.
  - ss. des; clarify.
    destruct (Memory.op_kind_is_cancel kind) eqn:KIND.
    + inv PROMISE; ss; clarify.
    + eapply AMemory.promise_get2 in PROMISE; auto. des. clarify.
  - eapply promise_new_reserve; eauto.
Qed.

Lemma step_new_reserve lang (th0 th1: Thread.t lang) e
      (STEP: AThread.step_allpf e th0 th1)
      loc0 to0 from0
      (GET: Memory.get loc0 to0 (Thread.memory th1) = Some (from0, Message.reserve))
      (NONE: Memory.get loc0 to0 (Local.promises (Thread.local th1)) <> Some (from0, Message.reserve))
  :
    (<<GET: Memory.get loc0 to0 (Thread.memory th0) = Some (from0, Message.reserve)>>) /\
    (<<NONE: Memory.get loc0 to0 (Local.promises (Thread.local th0)) <> Some (from0, Message.reserve)>>)
.
Proof.
  inv STEP. inv STEP0; inv STEP.
  - inv LOCAL. ss.
    eapply promise_new_reserve in PROMISE; eauto.
  - inv LOCAL; ss; try by inv LOCAL0; ss.
    + inv LOCAL0. ss. eapply write_new_reserve in WRITE; eauto.
    + inv LOCAL1. inv LOCAL2. eapply write_new_reserve in WRITE; eauto.
Qed.

Lemma steps_new_reserve lang (th0 th1: Thread.t lang)
      (STEPS: rtc (tau (@AThread.step_allpf _)) th0 th1)
      loc0 to0 from0
      (GET: Memory.get loc0 to0 (Thread.memory th1) = Some (from0, Message.reserve))
      (NONE: Memory.get loc0 to0 (Local.promises (Thread.local th1)) <> Some (from0, Message.reserve))
  :
    (<<GET: Memory.get loc0 to0 (Thread.memory th0) = Some (from0, Message.reserve)>>) /\
    (<<NONE: Memory.get loc0 to0 (Local.promises (Thread.local th0)) <> Some (from0, Message.reserve)>>)
.
Proof.
  ginduction STEPS.
  - i. clarify.
  - i. exploit IHSTEPS; eauto. i. des.
    inv H. exploit step_new_reserve; eauto.
Qed.

Lemma step_reserver_exists_tgt c0 c1 tid e
      (RESERVES: reserver_exists c0)
      (STEP: Configuration.step e tid c0 c1)
  :
    reserver_exists c1.
Proof.
  apply configuration_step_equivalent in STEP. inv STEP. ii. ss.
  destruct (classic (Memory.get loc to (Local.promises lc3) = Some (from, Message.reserve))).
  - exists tid. erewrite IdentMap.gss. esplits; eauto.
  - exploit step_new_reserve.
    { eapply thread_step_athread_step. econs; eauto. } all: eauto.
    i. des.
    exploit steps_new_reserve.
    { eapply thread_steps_athread_steps. eauto. } all: eauto.
    i. des. ss.
    eapply RESERVES in GET0. des.
    assert (NEQ: tid <> tid0).
    { ii. clarify. }
    exists tid0. esplits; eauto.
    erewrite IdentMap.gso; eauto.
Qed.

Lemma step_reserver_exists_src c0 c1 tid e
      (RESERVES: reserver_exists c0)
      (STEP: APFConfiguration.step e tid c0 c1)
  :
    reserver_exists c1.
Proof.
  inv STEP. ii. ss.
  destruct (classic (Memory.get loc to (Local.promises lc3) = Some (from, Message.reserve))).
  - exists tid. erewrite IdentMap.gss. esplits; eauto.
  - exploit step_new_reserve.
    { econs. econs 2; eauto. } all: eauto.
    i. des.
    exploit steps_new_reserve.
    { eapply rtc_implies; try apply STEPS.
      eapply tau_mon. i. econs. econs 2; eauto. } all: eauto.
    i. des. ss.
    eapply RESERVES in GET0. des.
    assert (NEQ: tid <> tid0).
    { ii. clarify. }
    exists tid0. esplits; eauto.
    erewrite IdentMap.gso; eauto.
Qed.

Module Inv.

  Record t mem lang (st: Language.state lang) lc
         (proms: Memory.t)
         (spaces : Loc.t -> Time.t -> Prop)
         (updates : Loc.t -> Time.t -> Prop)
         (aupdates : Loc.t -> Time.t -> Prop)
         (mlast: Memory.t): Prop :=
    {
      SPACES: forall loc ts (IN: spaces loc ts), concrete_covered proms mem loc ts;
      AUPDATES: forall loc ts (IN: aupdates loc ts),
          exists to msg,
            (<<TS: Time.lt ts to>>) /\
            (<<GET: Memory.get loc to proms = Some (ts, msg)>>);
      PROMS: forall
          loc to m sc (PROM : concrete_promised proms loc to)
          (FUTURE: unchanged_on spaces mlast m)
          (UNCHANGED: not_attatched (updates \2/ aupdates) m),
          exists st' lc' sc' m',
            (<<STEPS : rtc (tau (@AThread.program_step _))
                           (Thread.mk _ st lc sc m)
                           (Thread.mk _ st' lc' sc' m')>>) /\
            (<<WRITING : is_writing _ st' loc Ordering.relaxed>>);
      UPDATE : forall
          loc to m sc (UPD : updates loc to)
          (FUTURE: unchanged_on spaces mlast m)
          (UNCHANGED: not_attatched (updates \2/ aupdates) m),
          exists st' lc' sc' m',
            (<<STEPS : rtc (tau (@AThread.program_step _))
                           (Thread.mk _ st lc sc m)
                           (Thread.mk _ st' lc' sc' m')>>) /\
            (<<READING : is_updating _ st' loc Ordering.strong_relaxed>>);
      AUPDATE : forall
          loc to m sc (UPD : aupdates loc to)
          (FUTURE: unchanged_on spaces mlast m)
          (UNCHANGED: not_attatched (updates \2/ aupdates) m),
          exists st' lc' sc' m',
            (<<STEPS : rtc (tau (@AThread.program_step _))
                           (Thread.mk _ st lc sc m)
                           (Thread.mk _ st' lc' sc' m')>>) /\
            (<<READING : is_updating _ st' loc Ordering.seqcst>>);
    }.

End Inv.



Section SIMPF.

  Inductive thread_wf lang (th: Thread.t lang): Prop :=
  | thread_wf_intro
      (SC: Memory.closed_timemap (Thread.sc th) (Thread.memory th))
      (CLOSED: Memory.closed (Thread.memory th))
      (LCWF: Local.wf (Thread.local th) (Thread.memory th))
  .

  Inductive sim_pf_one
            (tid: Ident.t)
            (mlast: Memory.t)
            (spaces : (Loc.t -> Time.t -> Prop))
            (updates: (Loc.t -> Time.t -> Prop))
            (aupdates: (Loc.t -> Time.t -> Prop))
            (c_src c_tgt: Configuration.t) : Prop :=
  | sim_pf_one_intro
      (FUTURE: unchanged_on spaces mlast (Configuration.memory c_src))
      (NOATTATCH: not_attatched (updates \2/ aupdates) (Configuration.memory c_src))
      (INV:
         forall
           lang_src st_src lc_src lang_tgt st_tgt lc_tgt
           (TIDSRC: IdentMap.find tid (Configuration.threads c_src) =
                    Some (existT _ lang_src st_src, lc_src))
           (TIDTGT: IdentMap.find tid (Configuration.threads c_tgt) =
                    Some (existT _ lang_tgt st_tgt, lc_tgt)),
           Inv.t (Configuration.memory c_tgt) _ st_src lc_src (Local.promises lc_tgt) spaces updates aupdates mlast)
      (INVBOT:
         forall
           (TIDSRC: IdentMap.find tid (Configuration.threads c_src) = None),
           (<<SPACESBOT: spaces <2= bot2>>) /\
           (<<UPDATESBOT: updates <2= bot2>>) /\
           (<<AUPDATESBOT: aupdates <2= bot2>>))
  .

  Inductive sim_pf
            (idents: Ident.t -> Prop)
            (mlast: Ident.t -> Memory.t)
            (spaces : Ident.t -> (Loc.t -> Time.t -> Prop))
            (updates: Ident.t -> (Loc.t -> Time.t -> Prop))
            (aupdates: Ident.t -> (Loc.t -> Time.t -> Prop))
            (c_src c_tgt: Configuration.t) : Prop :=
  | sim_pf_intro
      (FORGET: forget_config c_src c_tgt)
      (THREADS: forall tid (IDENT: idents tid),
          sim_pf_one tid (mlast tid) (spaces tid) (updates tid) (aupdates tid) c_src c_tgt)
      (RACEFREE: pf_racefree APFConfiguration.step c_src)
      (WFSRC: Configuration.wf c_src)
      (WFTGT: Configuration.wf c_tgt)
      (RESERVEWF: memory_reserve_wf (Configuration.memory c_tgt))
      (RESERVERTGT: reserver_exists c_tgt)
      (RESERVERSRC: reserver_exists c_src)
  .

  Definition sim_pf_minus_one
             (tid: Ident.t)
             (mlast: Ident.t -> Memory.t)
             (spaces : Ident.t -> (Loc.t -> Time.t -> Prop))
             (updates: Ident.t -> (Loc.t -> Time.t -> Prop))
             (aupdates: Ident.t -> (Loc.t -> Time.t -> Prop))
             (c_src c_tgt: Configuration.t) : Prop :=
    sim_pf (fun tid' => tid <> tid') mlast spaces updates aupdates c_src c_tgt.

  Inductive sim_pf_all c_src c_tgt: Prop :=
  | sim_pf_all_intro mlast spaces updates aupdates
                     (SIM : sim_pf (fun _ => True) mlast spaces updates aupdates c_src c_tgt)
  .

  Lemma init_pf s tid st lc
        (TID: IdentMap.find tid (Threads.init s) = Some (st, lc))
    :
      Local.promises lc = Memory.bot.
  Proof.
    unfold Threads.init in *. erewrite IdentMap.Properties.F.map_o in *.
    unfold option_map in *. des_ifs.
  Qed.

  Lemma sim_pf_init
        s
        (RACEFREE: pf_racefree APFConfiguration.step (Configuration.init s))
    :
      sim_pf_all (Configuration.init s) (Configuration.init s)
  .
  Proof.
    econs.
    instantiate (1:=fun _ _ _ => False).
    instantiate (1:=fun _ _ _ => False).
    instantiate (1:=fun _ _ _ => False).
    instantiate (1:=fun _ => Memory.init).
    econs; eauto; ss; i.
    - econs; i; ss.
      + unfold Threads.init in *. erewrite IdentMap.Properties.F.map_o in *.
        unfold option_map in *. des_ifs.
      + econs.
        * instantiate (1:= Memory.init). econs; ss; eauto.
          ii. inv PROMS. ss.
          exploit init_pf; eauto. i. rewrite x0 in *.
          inv PROMISED. rewrite Memory.bot_get in *. clarify.
        * refl.
    - econs; ss.
      + refl.
      + ii. des; clarify.
      + i. econs; eauto; ii; clarify.
        exploit init_pf; try apply TIDTGT; eauto. i.
        rewrite x0 in *. inv PROM.
        rewrite Memory.bot_get in *. clarify.
      + i; splits; i; clarify.
    - eapply Configuration.init_wf.
    - eapply Configuration.init_wf.
    - ii. unfold Memory.get in GET. rewrite Cell.init_get in GET.
      des_ifs.
    - ii. unfold Memory.get in RESERVE. rewrite Cell.init_get in RESERVE.
      des_ifs.
    - ii. unfold Memory.get in RESERVE. rewrite Cell.init_get in RESERVE.
      des_ifs.
  Qed.

  Lemma sim_pf_src_no_promise idents mlast spaces updates aupdates c_src c_tgt
        (SIM: sim_pf idents mlast spaces updates aupdates c_src c_tgt)
        tid st lc
        (TIDSRC: IdentMap.find tid (Configuration.threads c_src) =
                 Some (st, lc))
    :
      (Local.promises lc) = Memory.bot.
  Proof.
    inv SIM. inv FORGET. specialize (THS tid).
    unfold option_rel in THS. des_ifs. inv THS. auto.
  Qed.

  Lemma sim_pf_src_no_reserve idents mlast spaces updates aupdates c_src c_tgt
        (SIM: sim_pf idents mlast spaces updates aupdates c_src c_tgt)
        loc to from
        (RESERVE: Memory.get loc to (Configuration.memory c_src) = Some (from, Message.reserve))
    :
      False.
  Proof.
    dup SIM. inv SIM. eapply RESERVERSRC in RESERVE; eauto.
    des. eapply sim_pf_src_no_promise in TIDSRC; eauto.
    rewrite TIDSRC in *. erewrite Memory.bot_get in *; clarify.
  Qed.

  Lemma less_covered_max_ts mem0 mem1
        (INHABITED: Memory.inhabited mem0)
        (SHORTER: forall loc to (COVER: covered loc to mem0), covered loc to mem1)
        loc
    :
      Time.le (Memory.max_ts loc mem0) (Memory.max_ts loc mem1).
  Proof.
    specialize (INHABITED loc). eapply Memory.max_ts_spec in INHABITED.
    des. dup GET. eapply memory_get_ts_strong in GET. des; clarify.
    - erewrite GET1. eapply Time.bot_spec.
    - exploit SHORTER.
      { econs; eauto. econs; [|refl]. eauto. }
      intros COVER. inv COVER. inv ITV.
      eapply Memory.max_ts_spec in GET. des. ss.
      etrans; eauto.
  Qed.

  Lemma sim_pf_max_timemap idents mlast spaces updates aupdates c_src c_tgt max
        (SIM: sim_pf idents mlast spaces updates aupdates c_src c_tgt)
        (MAX: Memory.max_full_timemap (Configuration.memory c_tgt) max)
    :
      TimeMap.le (Memory.max_timemap (Configuration.memory c_src)) max.
  Proof.
    inv SIM. inv WFTGT. inv MEM. inv WFSRC. inv MEM. inv FORGET. ii.
    inv MEM. inv SHORTER. eapply less_covered_max_ts in COVER; eauto. etrans; eauto.
    exploit Memory.max_ts_spec.
    { inv FORGET. erewrite COMPLETE0.
      - eapply (INHABITED loc).
      - ii. inv H. destruct st as [lang st]. inv PROMISED. destruct msg.
        inv WF. exploit THREADS0; eauto. intros []. erewrite BOT in GET. clarify. }
    i. des. eapply forget_memory_get in GET; eauto. des. destruct msg.
    - eapply Memory.max_full_ts_spec in GET0; eauto. des. auto.
    - exfalso. eapply NOT.
      eapply RESERVERTGT in GET0. des. destruct st as [lang st].
      econs; eauto. econs; eauto.
  Qed.

  Lemma pf_sim_memory_exists_or_blank L mem_src mem_tgt
        (MEM: pf_sim_memory L mem_src mem_tgt)
        loc to from val released
        (GET: Memory.get loc to mem_tgt = Some (from, Message.full val released))
    :
      (exists from', (<<GET: Memory.get loc to mem_src = Some (from', Message.full val released)>>)) \/
      (<<BLANK: forall ts (ITV: Interval.mem (from, to) ts),
          (<<NCOVER: ~ covered loc ts mem_src>>) /\ (<<FORGET: L loc to>>)>>).
  Proof.
    inv MEM. dup FORGET. inv FORGET. destruct (classic (L loc to)).
    - right. ii. split; auto. ii.
      inv SHORTER. eapply COVER in H0. inv H0.
      eapply forget_memory_get in GET0; eauto. des; clarify.
      exploit Memory.get_disjoint.
      { eapply GET1. }
      { eapply GET. }
      i. des; clarify. eapply x0; eauto.
    - left. erewrite <- COMPLETE in GET; eauto.
      inv SHORTER. eapply COMPLETE0 in GET. des. eauto.
  Qed.


End SIMPF.


Inductive diff_after_promises (caps: Loc.t -> option (Time.t * Time.t * Message.t))
          (prom mem0 mem1: Memory.t): Prop :=
| diff_after_promises_intro
    (MLE: Memory.le mem0 mem1)

    (DIFF: forall loc to from msg
                  (GET: Memory.get loc to mem1 = Some (from, msg))
                  (NONE: Memory.get loc to mem0 = None),
        caps loc = Some (from, to, msg))

    (CAPS: forall loc to from msg
                  (CAP: caps loc = Some (from, to, msg)),
        (<<TGTGET: Memory.get loc to mem1 = Some (from, msg)>>) /\
        (<<PROMGET: Memory.get loc to prom = None>>) /\
        (<<SRCGET: forall (NONE: Memory.get loc to mem0 = None),
            exists from' to' val released,
              (<<PROM: Memory.get loc to' prom = Some (from', Message.full val released)>>)>>) /\
        (<<PROM: forall from' to' val released
                        (PROM: Memory.get loc to' prom = Some (from', Message.full val released)),
            (<<TLT: Time.lt to' to>>) /\ (<<GET: Memory.get loc to mem0 = None>>)>>))
.

Lemma diff_after_promise_unchangable caps prom0 mem_src0 mem_tgt0
      (MLE: Memory.le prom0 mem_src0)
      (DIFF: diff_after_promises caps prom0 mem_src0 mem_tgt0)
      loc from to msg
      (CAP: caps loc = Some (from, to, msg))
  :
    unchangable mem_tgt0 prom0 loc to from msg.
Proof.
  inv DIFF. eapply CAPS in CAP. des. econs; eauto.
Qed.

Lemma diff_after_promise_promise caps prom0 mem_src0 mem_tgt0
      loc from to msg kind prom1 mem_tgt1
      (DIFF: diff_after_promises caps prom0 mem_src0 mem_tgt0)
      (MLE: Memory.le prom0 mem_src0)
      (PROMISE: AMemory.promise prom0 mem_tgt0 loc from to msg prom1 mem_tgt1 kind)
      (PF: (Memory.op_kind_is_lower_full kind && Message.is_released_none msg
            || Memory.op_kind_is_cancel kind)%bool)
  :
    exists mem_src1,
      (<<PROMISE: AMemory.promise prom0 mem_src0 loc from to msg prom1 mem_src1 kind>>) /\
      (<<DIFF: diff_after_promises caps prom1 mem_src1 mem_tgt1>>).
Proof.
  generalize (unchangable_promise PROMISE). intros UNCH.
  dup DIFF. inv DIFF. inv PROMISE; ss.
  - unfold Message.is_released_none in *. des_ifs. des. clarify.
    dup MEM. eapply lower_succeed_wf in MEM0. des.
    exploit Memory.lower_exists.
    { eapply MLE. eapply lower_succeed_wf in PROMISES. des. eapply GET0. }
    { eauto. }
    { eauto. }
    { eauto. }
    i. des. exists mem2. split.
    + econs; eauto.
    + econs.
      * eapply memory_op_le; eauto.
      * i. erewrite Memory.lower_o in GET0; eauto.
        erewrite Memory.lower_o in NONE; eauto. des_ifs. guardH o.
        exploit DIFF1; eauto.
      * i. exploit UNCH.
        { eapply diff_after_promise_unchangable; eauto. } i. inv x.
        eapply CAPS in CAP. des. splits; eauto.
        { i. erewrite Memory.lower_o in NONE; eauto. des_ifs. guardH o.
          eapply SRCGET in NONE. des. eapply Memory.lower_get1 in PROM0; eauto.
          des. inv MSG_LE0. esplits; eauto. }
        { i. erewrite Memory.lower_o in PROM0; eauto. des_ifs.
          - ss. des; clarify. exploit PROM.
            + eapply Memory.lower_get0 in PROMISES. des. eauto.
            + i. des. split; auto. eapply Memory.lower_get0 in PROMISES.
              erewrite Memory.lower_o; eauto. des_ifs. ss; des; clarify.
          - guardH o. dup PROM0. eapply PROM in PROM0. des. split; auto.
            erewrite Memory.lower_o; eauto. des_ifs. ss. des; clarify.
            exfalso. eapply Memory.lower_get0 in PROMISES. des. clarify. }
  - exploit Memory.remove_exists.
    { eapply Memory.remove_get0 in PROMISES. des.
      eapply MLE. eauto. }
    i. des. exists mem2. split.
    + econs; eauto.
    + econs.
      * eapply memory_op_le; eauto.
      * i. erewrite Memory.remove_o in GET; eauto.
        erewrite Memory.remove_o in NONE; eauto. des_ifs. eauto.
      * i. exploit UNCH.
        { eapply diff_after_promise_unchangable; eauto. } i. inv x.
        eapply CAPS in CAP. des. splits; eauto.
        { i. erewrite Memory.remove_o in NONE; eauto. des_ifs.
          - ss. eapply Memory.remove_get0 in PROMISES. des; clarify.
          - guardH o. eapply SRCGET in NONE. des.
            exists from', to', val, released. erewrite Memory.remove_o; eauto.
            eapply Memory.remove_get0 in PROMISES. des_ifs. ss; des; clarify. }
        { i. erewrite Memory.remove_o in PROM0; eauto. des_ifs.
          guardH o. eapply PROM in PROM0. des. split; auto.
          erewrite Memory.remove_o; eauto. des_ifs. }
Qed.
