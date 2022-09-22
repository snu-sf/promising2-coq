Require Import Lia.
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

Require Import PF.
Require Import Race.
Require Import Behavior.
Require Import SimMemory.
Require Import yjtac.
Require Import Program.
Require Import Cell.
Require Import Time.
Require Import Pred.
Require Import PredStep.

Set Implicit Arguments.


Section GENERAL.

  Lemma list_filter_exists A (P: A -> Prop) (l: list A)
    :
      exists l',
        (<<COMPLETE: forall a, ((<<IN: List.In a l>>) /\ (<<SAT: P a>>))
                               <-> (<<IN: List.In a l'>>)>>).
  Proof.
    induction l.
    - exists []. ii. split; i; des.
      + inv IN.
      + inv H.
    - des. destruct (classic (P a)).
      + exists (a :: l'). split; i; ss; des; clarify; eauto.
        * right. eapply COMPLETE; eauto.
        * eapply COMPLETE in H0. des. eauto.
      + exists l'. split; i; ss; des; clarify; eauto.
        * eapply COMPLETE; eauto.
        * eapply COMPLETE in H0. des; eauto.
  Qed.

  Lemma or_strengthen A B
        (OR: A \/ B)
  :
    (A \/ ((<<NOT: ~ A>>) /\ (<<SAT: B>>))).
  Proof.
    destruct (classic A); eauto. des; eauto.
  Qed.

End GENERAL.


Section CELL.

  Inductive times_sorted: list Time.t -> Prop :=
  | times_sorted_nil
    :
      times_sorted []
  | times_sorted_cons
      hd tl
      (HD: List.Forall (Time.lt hd) tl)
      (TL: times_sorted tl)
    :
      times_sorted (hd :: tl)
  .
  #[local]
  Hint Constructors times_sorted: core.

  Fixpoint insert (to: Time.t) (l: list Time.t): list Time.t :=
    match l with
    | [] => [to]
    | hd :: tl =>
      match (Time.le_lt_dec to hd) with
      | left LE => match (Time.eq_dec to hd) with
                   | left EQ => hd :: tl
                   | right LT => to :: hd :: tl
                   end
      | right LT => hd :: (insert to tl)
      end
    end.

  Fixpoint sorting (l: list Time.t): list Time.t :=
    match l with
    | [] => []
    | hd :: tl => insert hd (sorting tl)
    end.

  Lemma insert_complete a l
    :
      forall b, List.In b (insert a l) <-> (a = b \/ List.In b l).
  Proof.
    ginduction l; ss. i. des_ifs; ss.
    - split; i; des; eauto.
    - split; i; des; eauto.
      + eapply IHl in H. des; eauto.
      + clarify. right. eapply IHl; eauto.
      + right. eapply IHl; eauto.
  Qed.

  Lemma insert_sorted a l
        (SORTED: times_sorted l)
    :
      times_sorted (insert a l).
  Proof.
    ginduction l; ss.
    - i. econs; ss.
    - i. des_ifs.
      + econs; eauto. inv SORTED. econs.
        * destruct l0; clarify.
        * eapply List.Forall_impl; cycle 1; eauto.
          i. eapply TimeFacts.le_lt_lt; eauto.
      + econs.
        * inv SORTED.
          eapply List.Forall_forall. i.
          eapply insert_complete in H. des; clarify.
          eapply List.Forall_forall in HD; eauto.
        * inv SORTED. eapply IHl; eauto.
  Qed.

  Lemma sorting_sorted l
    :
      (<<COMPLETE: forall a, List.In a l <-> List.In a (sorting l)>>) /\
      (<<SORTED: times_sorted (sorting l)>>).
  Proof.
    induction l; ss.
    - split; i; ss.
    - i. des. splits.
      + i. erewrite insert_complete.
        split; i; des; eauto.
        * right. eapply COMPLETE; eauto.
        * right. eapply COMPLETE; eauto.
      + eapply insert_sorted; eauto.
  Qed.

  Inductive disjoint_cell_msgs: list (Time.t * Time.t * Message.t) -> Prop :=
  | disjoint_cell_msgs_nil
    :
      disjoint_cell_msgs []
  | disjoint_cell_msgs_cons
      from to msg tl
      (HD: List.Forall (fun ftm =>
                          match ftm with
                          | (f, t, m) => Time.le to f
                          end) tl)
      (TL: disjoint_cell_msgs tl)
    :
      disjoint_cell_msgs ((from, to, msg) :: tl)
  .


  Definition wf_cell_msgs l :=
    (<<DISJOINT: disjoint_cell_msgs l>>) /\
    (<<MSGSWF: List.Forall (fun ftm =>
                              match ftm with
                              | (from, to, msg) =>
                                (<<MSGWF: Message.wf msg>>) /\
                                (<<TS: (from = Time.bot /\ to = Time.bot) \/ (Time.lt from to)>>)
                              end) l>>)
  .

  Lemma cell_finite_sound_exists c
    :
      exists dom,
        (<<COMPLETE: forall to,
            (List.In to dom <-> exists from msg,
                (<<GET: Cell.get to c = Some (from, msg)>>))>>).
  Proof.
    generalize (Cell.finite c). i. des.
    generalize (list_filter_exists (fun to => exists from msg, (<<GET: Cell.get to c = Some (from, msg)>>)) dom). i. des.
    exists l'. i. split; i.
    - eapply COMPLETE in H0. des. eauto.
    - eapply COMPLETE. splits; eauto.
      des. eapply H; eauto.
  Qed.

  Lemma wf_cell_msgs_exists c
    :
      exists l,
        (<<COMPLETE:
           forall from to msg,
             (<<GET: Cell.get to c = Some (from, msg)>>) <->
             (<<IN: List.In (from, to, msg) l>>)>>) /\
        (<<WFMSGS: wf_cell_msgs l>>).
  Proof.
    generalize (cell_finite_sound_exists c). i. des.
    generalize (sorting_sorted dom). i. des.
    assert (COMPLETE1: forall a, List.In a (sorting dom) <->
                                 exists from msg,
                                   (<<GET: Cell.get a c = Some (from, msg)>>)).
    { i. split; i.
      - eapply COMPLETE0 in H. eapply COMPLETE in H. eauto.
      - eapply COMPLETE0. eapply COMPLETE. eauto. }
    remember (sorting dom). clear - SORTED COMPLETE1.
    exists (List.map (fun to => match (Cell.get to c) with
                                | Some (from, msg) => (from, to, msg)
                                | None => (to, Time.bot, Message.reserve)
                                end) l).
    ginduction l; ss.
    - i. splits.
      + ii. split; clarify.
        i. eapply COMPLETE1. eauto.
      + econs.
        * econs.
        * econs.
    - i. hexploit (proj1 (COMPLETE1 a)); eauto. i. des.
      hexploit Cell.remove_exists; eauto. i. des.
      hexploit (IHl cell2).
      { inv SORTED. eauto. }
      { i. split; i.
        - hexploit (proj1 (COMPLETE1 a0)); eauto. i. des.
          exists from0, msg0. erewrite Cell.remove_o; eauto. des_ifs.
          exfalso. inv SORTED.
          eapply List.Forall_forall in H0; eauto.
          eapply Time.lt_strorder; eauto.
        - des. erewrite Cell.remove_o in GET0; eauto. des_ifs.
          hexploit (proj2 (COMPLETE1 a0)); eauto.
          i. des; clarify. }
      i. des. rewrite GET in *.
      replace (List.map
                 (fun to0 =>
                    match Cell.get to0 c with
                    | Some (from1, msg1) => (from1, to0, msg1)
                    | None => (to0, Time.bot, Message.reserve)
                    end) l) with
          (List.map
             (fun to0 =>
                match Cell.get to0 cell2 with
                | Some (from1, msg1) => (from1, to0, msg1)
                | None => (to0, Time.bot, Message.reserve)
                end) l); cycle 1.
      { eapply List.map_ext_in. i.
        erewrite (@Cell.remove_o cell2); eauto.
        des_ifs. exfalso. inv SORTED.
        eapply List.Forall_forall in H0; eauto.
        eapply Time.lt_strorder; eauto. }
      assert (COMPLETE2:
                forall from0 to msg0,
                  Cell.get to c = Some (from0, msg0) <->
                  (from, a, msg) = (from0, to, msg0) \/
                  List.In (from0, to, msg0)
                          (List.map
                             (fun to0 =>
                                match Cell.get to0 cell2 with
                                | Some (from1, msg1) => (from1, to0, msg1)
                                | None => (to0, Time.bot, Message.reserve)
                                end) l)).
      { i. split; i.
        - generalize (Cell.remove_o to H). intros GET0.
          des_ifs; eauto. right.
          rewrite H0 in GET0. eapply COMPLETE in GET0. eauto.
        - des; clarify.
          eapply (proj2 (COMPLETE from0 to msg0)) in H0.
          erewrite Cell.remove_o in H0; eauto. des_ifs. }
      splits; auto.
      unfold wf_cell_msgs in WFMSGS. des. econs; eauto.
      + econs; eauto. inv SORTED.
        eapply List.Forall_forall. i.
        eapply List.in_map_iff in H0. des.
        erewrite Cell.remove_o in H0; eauto. des_ifs.
        * dup GET. eapply Cell.get_ts in GET0. des; clarify.
          { eapply Time.bot_spec. }
          destruct (Time.le_lt_dec a t0); auto. exfalso.
          exploit Cell.get_disjoint.
          { eapply GET. }
          { eapply Heq0. }
          i. des; clarify. eapply x0.
          { instantiate (1:=a). econs; ss. refl. }
          { econs; ss.
            eapply List.Forall_forall in HD; eauto. left. auto. }
        * refl.
        * exfalso. hexploit (proj1 (COMPLETE1 t0)); eauto.
          i. des. clarify.
      + econs; eauto. splits.
        { eapply Cell.get_opt_wf; eauto. }
        { eapply Cell.get_ts; eauto. }
  Qed.

  Lemma finite_greatest P (l: list Time.t)
    :
      (exists to,
          (<<SAT: P to>>) /\
          (<<IN: List.In to l>>) /\
          (<<GREATEST: forall to'
                              (IN: List.In to' l)
                              (SAT: P to'),
              Time.le to' to>>)) \/
      (<<EMPTY: forall to (IN: List.In to l), ~ P to>>).
  Proof.
    induction l.
    - right. ii. inv IN.
    - destruct (classic (P a)).
      + des.
        * destruct (Time.le_lt_dec to a).
          { left. exists a. esplits; ss; eauto.
            i. des; clarify; eauto. refl. }
          { left. exists to. esplits; ss; eauto.
            i. des; clarify; eauto. left. eauto. }
        * left. exists a. esplits; ss; eauto.
          i. des; clarify.
          { refl. }
          { exfalso. eapply EMPTY; eauto. }
      + des.
        * left. esplits; ss; eauto.
          i. des; clarify. eapply GREATEST; eauto.
        * right. ii. ss. des; clarify.
          eapply EMPTY; eauto.
  Qed.

  Lemma cell_elements_greatest cell P
    :
      (exists to from msg,
          (<<GET: Cell.get to cell = Some (from, msg)>>) /\
          (<<SAT: P to>>) /\
          (<<GREATEST: forall to' from' msg'
                              (GET': Cell.get to' cell = Some (from', msg'))
                              (SAT: P to'),
              Time.le to' to>>)) \/
      (<<EMPTY: forall to from msg
                       (GET: Cell.get to cell = Some (from, msg)),
          ~ P to>>).
  Proof.
    hexploit (Cell.finite cell). i. des.
    hexploit (finite_greatest (fun to => P to /\ exists from msg, Cell.get to cell = Some (from, msg)) dom).
    i. des.
    - left. esplits; eauto. i.
      dup GET'. eapply H in GET'. eauto.
    - right. ii. dup GET. eapply H in GET0.
      eapply EMPTY in GET0. eapply GET0.
      esplits; eauto.
  Qed.

  Lemma finite_least P (l: list Time.t)
    :
      (exists to,
          (<<SAT: P to>>) /\
          (<<IN: List.In to l>>) /\
          (<<LEAST: forall to'
                           (IN: List.In to' l)
                           (SAT: P to'),
              Time.le to to'>>)) \/
      (<<EMPTY: forall to (IN: List.In to l), ~ P to>>).
  Proof.
    induction l.
    - right. ii. inv IN.
    - destruct (classic (P a)).
      + des.
        * destruct (Time.le_lt_dec a to).
          { left. exists a. esplits; ss; eauto.
            i. des; clarify; eauto. refl. }
          { left. exists to. esplits; ss; eauto.
            i. des; clarify; eauto. left. eauto. }
        * left. exists a. esplits; ss; eauto.
          i. des; clarify.
          { refl. }
          { exfalso. eapply EMPTY; eauto. }
      + des.
        * left. esplits; ss; eauto.
          i. des; clarify. eapply LEAST; eauto.
        * right. ii. ss. des; clarify.
          eapply EMPTY; eauto.
  Qed.

  Lemma cell_elements_least cell P
    :
      (exists to from msg,
          (<<GET: Cell.get to cell = Some (from, msg)>>) /\
          (<<SAT: P to>>) /\
          (<<LEAST: forall to' from' msg'
                           (GET': Cell.get to' cell = Some (from', msg'))
                           (SAT: P to'),
              Time.le to to'>>)) \/
      (<<EMPTY: forall to from msg
                       (GET: Cell.get to cell = Some (from, msg)),
          ~ P to>>).
  Proof.
    hexploit (Cell.finite cell). i. des.
    hexploit (finite_least (fun to => P to /\ exists from msg, Cell.get to cell = Some (from, msg)) dom).
    i. des.
    - left. esplits; eauto. i.
      dup GET'. eapply H in GET'. eauto.
    - right. ii. dup GET. eapply H in GET0.
      eapply EMPTY in GET0. eapply GET0.
      esplits; eauto.
  Qed.


End CELL.



Section FORGETMEMORY.

  Inductive forget_memory P msrc mtgt : Prop :=
  | forget_memory_intro
      (COMPLETE: forall l t (NPROMS: ~ P l t),
          Memory.get l t msrc = Memory.get l t mtgt)
      (FORGET: forall l t (PROMS: P l t), Memory.get l t msrc = None)
  .

  Lemma forget_compose P0 P1 m0 m1 m2
        (FORGET0: forget_memory P0 m0 m1)
        (FORGET1: forget_memory P1 m1 m2)
    :
      forget_memory (P0 \2/ P1) m0 m2.
  Proof.
    inv FORGET0. inv FORGET1. econs; eauto.
    - ii. apply not_or_and in NPROMS. des.
      erewrite COMPLETE; eauto.
    - i. destruct (classic (P0 l t)); auto.
      des; clarify. erewrite COMPLETE; eauto.
  Qed.

  Lemma forget_compose_middle P0 P1 m0 m1 m2
        (FORGET: forget_memory (P0 \2/ P1) m0 m2)
        (FORGET1: forget_memory P1 m1 m2)
    :
      forget_memory P0 m0 m1.
  Proof.
    inv FORGET. inv FORGET1. econs; eauto.
    ii. destruct (classic (P1 l t)).
    - erewrite FORGET; eauto.
    - erewrite COMPLETE; eauto.
      + erewrite COMPLETE0; eauto.
      + ii. des; clarify.
  Qed.

  Lemma forget_memory_le P msrc mtgt
        (FORGET: forget_memory P msrc mtgt)
    :
      Memory.le msrc mtgt.
  Proof.
    inv FORGET. ii.
    destruct (classic (P loc to)).
    - exploit FORGET0; eauto.
      i. clarify.
    - exploit COMPLETE; eauto.
      i. rewrite LHS in *. auto.
  Qed.

  Inductive forget_cell (P: Time.t -> Prop) cell_src cell_tgt : Prop :=
  | forget_cell_intro
      (COMPLETE: forall t (NPROMS: ~ P t),
          Cell.get t cell_src = Cell.get t cell_tgt)
      (FORGET: forall t (PROMS: P t), Cell.get t cell_src = None)
  .

  Lemma forget_exists_list l cell_tgt:
    exists cell_src,
      (<<FORGET: forget_cell (fun to => List.In to l) cell_src cell_tgt>>).
  Proof.
    induction l; ss.
    - exists cell_tgt. econs; ss.
    - des. destruct (Cell.get a cell_src) as [[from msg]|] eqn:GET.
      + exploit Cell.remove_exists; eauto. i. des. exists cell2.
        inv FORGET. econs; i.
        * erewrite Cell.remove_o; eauto. des_ifs; eauto.
          ss; des; clarify. exfalso. eauto.
        * erewrite Cell.remove_o; eauto. des_ifs; clarify.
          eapply FORGET0; eauto. ss. des; clarify; eauto.
      + exists cell_src. inv FORGET.
        econs; eauto. i. des; clarify; eauto.
  Qed.

  Lemma forget_cell_exists P cell_tgt:
    exists cell_src, (<<FORGET: forget_cell P cell_src cell_tgt>>).
  Proof.
    hexploit (cell_finite_sound_exists cell_tgt); eauto. i. des.
    hexploit (list_filter_exists P dom). i. des.
    hexploit (forget_exists_list l' cell_tgt). i. des.
    exists cell_src. inv FORGET. econs; eauto.
    - i. eapply COMPLETE1. ii. apply COMPLETE0 in H. des. clarify.
    - i. destruct (classic (List.In t dom)).
      + eapply FORGET0; eauto. eapply COMPLETE0; eauto.
      + rewrite COMPLETE1; eauto.
        * destruct (Cell.get t cell_tgt) as [[from msg]|] eqn:GET; auto.
          exfalso. eapply H. eapply COMPLETE; eauto.
        * ii. eapply COMPLETE0 in H0. des; clarify.
  Qed.

  Lemma forget_exists P mem_tgt:
    exists mem_src, (<<FORGET: forget_memory P mem_src mem_tgt>>).
  Proof.
    hexploit (choice (fun loc cell => forget_cell (P loc) cell (mem_tgt loc))).
    { i. eapply forget_cell_exists. } i. des.
    exists f. econs.
    - i. destruct (H l). eapply COMPLETE; eauto.
    - i. destruct (H l). eapply FORGET; eauto.
  Qed.

  Lemma forget_unique P mem_tgt mem_src0 mem_src1
        (FORGET0: forget_memory P mem_src0 mem_tgt)
        (FORGET1: forget_memory P mem_src1 mem_tgt)
    :
      mem_src0 = mem_src1.
  Proof.
    inv FORGET0. inv FORGET1.
    eapply Memory.ext. i. destruct (classic (P loc ts)).
    - erewrite FORGET; auto. erewrite FORGET0; auto.
    - erewrite COMPLETE; auto. erewrite COMPLETE0; auto.
  Qed.

  Lemma forget_memory_get P mem0 mem1 loc to msg
        (FORGET: forget_memory P mem0 mem1)
        (GET: Memory.get loc to mem0 = Some msg)
    :
      (<<NOT: ~ P loc to>>) /\ (<<GET: Memory.get loc to mem1 = Some msg>>).
  Proof.
    inv FORGET. destruct (classic (P loc to)).
    - exfalso. rewrite FORGET0 in GET; auto. clarify.
    - esplits; eauto.
      rewrite <- COMPLETE; auto.
  Qed.

  Lemma bot_forget P mem0
        (BOT: P <2= bot2)
    :
      forget_memory P mem0 mem0.
  Proof.
    econs; eauto. i. eapply BOT in PROMS. clarify.
  Qed.


End FORGETMEMORY.


Section MEMORYLEMMAS.

  Lemma disjoint_equivalent from0 to0 from1 to1
  :
    (<<INTERSECT: ~ Interval.disjoint (from0, to0) (from1, to1)>>) <->
    ((<<TS0: Time.lt from0 to0>>) /\ (<<TS1: Time.lt from1 to1>>) /\
     (<<TS0: Time.lt (Time.join from0 from1) (Time.meet to0 to1)>>)).
  Proof.
    split; i. des.
    - unfold Interval.disjoint in H.
      eapply not_all_ex_not in H. des.
      dup H. eapply not_imply_elim in H. eapply not_imply_elim2 in H0.
      apply NNPP in H0.
      destruct H. destruct H0. ss. splits.
      + eapply TimeFacts.lt_le_lt; eauto.
      + eapply TimeFacts.lt_le_lt; eauto.
      + unfold Time.join, Time.meet. des_ifs.
        * eapply TimeFacts.lt_le_lt; eauto.
        * eapply TimeFacts.lt_le_lt; eauto.
        * eapply TimeFacts.lt_le_lt; eauto.
        * eapply TimeFacts.lt_le_lt; eauto.
    - des. ii. eapply H.
      + instantiate (1:=Time.meet to0 to1). econs; ss.
        * unfold Time.join, Time.meet in *. des_ifs.
          eapply TimeFacts.le_lt_lt; eauto.
        * eapply Time.meet_l.
      + econs; ss.
        * unfold Time.join, Time.meet in *. des_ifs.
          etrans; eauto.
        * eapply Time.meet_r.
  Qed.

  Lemma disjoint_equivalent2 from0 to0 from1 to1
    :
      (<<DISJOINT: Interval.disjoint (from0, to0) (from1, to1)>>) <->
      ((<<TS0: ~ Time.lt from0 to0>>) \/ (<<TS1: ~ Time.lt from1 to1>>) \/
       (<<TS0: Time.le (Time.meet to0 to1) (Time.join from0 from1)>>)).
  Proof.
    set (disjoint_equivalent from0 to0 from1 to1).
    eapply not_iff_compat in i. split; i.
    - des. hexploit i.
      { ii. clarify. } i.
      apply not_and_or in H0. des; eauto.
      apply not_and_or in H0. des; eauto.
      right. right. red.
      destruct (Time.le_lt_dec (Time.meet to0 to1) (Time.join from0 from1)); eauto.
      exfalso. eauto.
    - destruct i. hexploit H1.
      { ii. des; eauto. eapply Time.lt_strorder.
        eapply TimeFacts.lt_le_lt; eauto. }
      ii. eauto.
  Qed.

  Lemma memory_get_ts_strong loc to mem from msg
        (GET: Memory.get loc to mem = Some (from, msg))
    :
      (from = Time.bot /\ to = Time.bot) \/
      ((<<TS: Time.lt from to>>) /\ (<<TO: to <> Time.bot>>)).
  Proof.
    apply Memory.get_ts in GET.
    destruct (classic (to = Time.bot)); clarify.
    - des; clarify; eauto.
      exfalso. eapply Time.lt_strorder.
      eapply TimeFacts.lt_le_lt; eauto. eapply Time.bot_spec.
    - des; clarify. right. eauto.
  Qed.

  Lemma memory_get_from_inj mem loc from to0 to1 msg0 msg1
        (GET0: Memory.get loc to0 mem = Some (from, msg0))
        (GET1: Memory.get loc to1 mem = Some (from, msg1))
    :
      (<<TO: to0 = to1>>) \/
      (((<<BOT: to0 = Time.bot>>) \/ (<<BOT: to1 = Time.bot>>)) /\ (<<BOT: from = Time.bot>>) /\
       (<<TO: to0 <> to1>>)).
  Proof.
    exploit Memory.get_disjoint.
    - eapply GET0.
    - eapply GET1.
    - i. des; clarify; eauto.
      eapply memory_get_ts_strong in GET0.
      eapply memory_get_ts_strong in GET1.
      des; clarify; eauto.
      { right. esplits; eauto. }
      { right. esplits; eauto. }
      exfalso. eapply x0.
      + instantiate (1:=Time.meet to0 to1). econs; ss; eauto.
        * unfold Time.meet. des_ifs.
        * eapply Time.meet_l.
      + econs; ss; eauto.
        * unfold Time.meet. des_ifs.
        * eapply Time.meet_r.
  Qed.

  Lemma memory_get_to_mon mem loc from0 from1 to0 to1 msg0 msg1
        (GET0: Memory.get loc to0 mem = Some (from0, msg0))
        (GET1: Memory.get loc to1 mem = Some (from1, msg1))
        (TO: Time.lt from0 from1)
    :
      Time.lt to0 to1.
  Proof.
    exploit Memory.get_disjoint.
    - eapply GET0.
    - eapply GET1.
    - i. des; clarify.
      + exfalso. eapply Time.lt_strorder. eauto.
      + dup GET0. dup GET1.
        eapply memory_get_ts_strong in GET0.
        eapply memory_get_ts_strong in GET1.
        des; clarify.
        * exfalso. eapply Time.lt_strorder.
          eapply TimeFacts.lt_le_lt; eauto. eapply Time.bot_spec.
        * hexploit (Time.bot_spec from1). i.
          destruct H; eauto.
        * eapply disjoint_equivalent2 in x0. des; clarify.
          unfold Time.meet, Time.join in *. des_ifs; eauto.
          { destruct l; eauto. destruct H; eauto. clarify.
            exfalso. eapply Time.lt_strorder; eauto. }
          { destruct l; eauto. destruct H; eauto. clarify.
            exfalso. eapply Time.lt_strorder; eauto. }
          { exfalso. eapply Time.lt_strorder.
            eapply TimeFacts.le_lt_lt; eauto. }
          { exfalso. eapply Time.lt_strorder.
            eapply TimeFacts.le_lt_lt; eauto. }
  Qed.

  Lemma memory_get_from_mon mem loc from0 from1 to0 to1 msg0 msg1
        (GET0: Memory.get loc to0 mem = Some (from0, msg0))
        (GET1: Memory.get loc to1 mem = Some (from1, msg1))
        (TO: Time.lt to0 to1)
    :
      Time.le to0 from1.
  Proof.
    exploit Memory.get_disjoint.
    - eapply GET0.
    - eapply GET1.
    - i. des; clarify.
      + exfalso. eapply Time.lt_strorder. eauto.
      + dup GET0. dup GET1.
        eapply memory_get_ts_strong in GET0.
        eapply memory_get_ts_strong in GET1.
        des; clarify.
        * exfalso. eapply Time.lt_strorder.
          eapply TimeFacts.lt_le_lt; eauto. eapply Time.bot_spec.
        * exfalso. eapply Time.lt_strorder.
          eapply TimeFacts.lt_le_lt; eauto. eapply Time.bot_spec.
        * apply Time.bot_spec.
        * destruct (Time.le_lt_dec to0 from1); auto. exfalso.
          eapply x0.
          { instantiate (1:=to0).
            econs; ss. refl. }
          { econs; ss. left. auto. }
  Qed.

  Lemma closed_point mem loc from
        to
        (TS: Time.lt from to)
        (COVERED: forall t (ITV: Interval.mem (from, to) t), covered loc t mem)
    :
      exists from' to' msg,
        (<<GET: Memory.get loc to' mem = Some (from', msg)>>) /\
        (<<TS0: Time.le from' from>>) /\
        (<<TS1: Time.lt from to'>>).
  Proof.
    hexploit (cell_elements_least
                (mem loc)
                (fun to' =>
                   exists from' msg',
                     (<<GET: Memory.get loc to' mem = Some (from', msg')>>) /\
                     (<<FROMLE: Time.lt from to'>>))). i. des.
    - destruct (Time.le_lt_dec from' from).
      + esplits; eauto.
      + exfalso. exploit (COVERED (Time.meet from' to)).
        * unfold Time.meet. des_ifs; econs; ss. refl.
        * i. inv x0. inv ITV. ss.
          exploit LEAST; try apply GET1; eauto.
          { esplits; try apply GET1.
            eapply TimeFacts.lt_le_lt; [|apply TO].
            unfold Time.meet. des_ifs. }
          { i. setoid_rewrite GET0 in GET. clarify.
            exploit memory_get_to_mon.
            - eapply GET1.
            - eapply GET0.
            - unfold Time.meet in FROM. des_ifs. etrans; eauto.
            - i. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto. }
    - exfalso. exploit (COVERED to).
      + econs; ss. refl.
      + i. inv x0. inv ITV. ss.
        eapply EMPTY; eauto. esplits; eauto.
        eapply TimeFacts.lt_le_lt; eauto.
  Qed.

  Lemma memory_get_ts_le loc to mem from msg
        (GET: Memory.get loc to mem = Some (from, msg))
    :
      Time.le from to.
  Proof.
    eapply Memory.get_ts in GET. des; clarify.
    - refl.
    - left. auto.
  Qed.

  Lemma max_full_timemap_get mem tm loc to from val released
        (MAX: Memory.max_full_timemap mem tm)
        (GET: Memory.get loc to mem = Some (from, Message.full val released))
    :
      Time.le to (tm loc).
  Proof.
    specialize (MAX loc). inv MAX. eapply MAX0; eauto.
  Qed.

  Lemma le_inhabited mem0 mem1
        (INHABITED: Memory.inhabited mem0)
        (MLE: Memory.le mem0 mem1)
    :
      Memory.inhabited mem1.
  Proof.
    ii. eapply MLE; eauto.
  Qed.

  Lemma remove_le mem0 loc from to msg mem1
        (REMOVE: Memory.remove mem0 loc from to msg mem1)
  :
    Memory.le mem1 mem0.
  Proof.
    ii. erewrite Memory.remove_o in LHS; eauto. des_ifs.
  Qed.

  Lemma step_promises_le lang (th0 th1: Thread.t lang) e
        (MLE: Memory.le (Local.promises (Thread.local th0)) (Thread.memory th0))
        (STEP: Thread.step_allpf e th0 th1)
  :
    Memory.le (Local.promises (Thread.local th1)) (Thread.memory th1).
  Proof.
    inv STEP. inv STEP0.
    - inv STEP. inv LOCAL. ss.
      eapply Memory.promise_le; eauto.
    - inv STEP. inv LOCAL; ss.
      + inv LOCAL0; ss.
      + inv LOCAL0. ss. inv WRITE.
        eapply Memory.promise_le in PROMISE; eauto. red in PROMISE.
        eapply remove_le in REMOVE.
        etrans; eauto.
      + inv LOCAL1. inv LOCAL2. ss. inv WRITE.
        eapply Memory.promise_le in PROMISE; eauto. red in PROMISE.
        eapply remove_le in REMOVE.
        etrans; eauto.
      + inv LOCAL0; ss.
      + inv LOCAL0; ss.
  Qed.

  Lemma traced_step_promises_le lang tr (th0 th1: Thread.t lang)
        (MLE: Memory.le (Local.promises (Thread.local th0)) (Thread.memory th0))
        (STEP: traced_step tr th0 th1)
  :
    Memory.le (Local.promises (Thread.local th1)) (Thread.memory th1).
  Proof.
    ginduction STEP; ss.
    i. eapply IHSTEP. eapply step_promises_le; eauto.
  Qed.

  Lemma steps_promises_le P lang (th0 th1: Thread.t lang)
        (MLE: Memory.le (Local.promises (Thread.local th0)) (Thread.memory th0))
        (STEP: rtc (tau (@pred_step P lang)) th0 th1)
  :
    Memory.le (Local.promises (Thread.local th1)) (Thread.memory th1).
  Proof.
    ginduction STEP; ss.
    i. eapply IHSTEP.
    inv H. inv TSTEP. eapply step_promises_le; eauto.
  Qed.

  Lemma traced_steps_promises_le lang (th0 th1: Thread.t lang) events
        (MLE: Memory.le (Local.promises (Thread.local th0)) (Thread.memory th0))
        (STEP: traced_step events th0 th1)
  :
    Memory.le (Local.promises (Thread.local th1)) (Thread.memory th1).
  Proof.
    ginduction STEP; ss.
    i. eapply IHSTEP. eapply step_promises_le; eauto.
  Qed.

  Lemma inhabited_future mem1 mem2
        (FUTURE: Memory.future mem1 mem2)
        (INHABITED: Memory.inhabited mem1)
  :
    Memory.inhabited mem2.
  Proof.
    induction FUTURE; auto. apply IHFUTURE.
    inv H. hexploit Memory.op_inhabited; eauto.
  Qed.

  Lemma memory_le_get_none msrc mtgt loc to
        (MLE: Memory.le msrc mtgt)
        (NONE: Memory.get loc to mtgt = None)
    :
      Memory.get loc to msrc = None.
  Proof.
    destruct (Memory.get loc to msrc) eqn:GET; auto.
    destruct p. eapply MLE in GET. clarify.
  Qed.

  Lemma memory_le_covered msrc mtgt loc to
        (MLE: Memory.le msrc mtgt)
        (COVERED: covered loc to msrc)
    :
      covered loc to mtgt.
  Proof.
    inv COVERED. econs; eauto.
  Qed.

  Lemma memory_add_cover_disjoint mem0 loc from to msg mem1
        (ADD: Memory.add mem0 loc from to msg mem1)
        t
        (IN: Interval.mem (from, to) t)
    :
      ~ covered loc t mem0.
  Proof.
    ii. inv H. dup ADD. eapply Memory.add_get0 in ADD. des.
    exploit Memory.get_disjoint.
    + eapply Memory.add_get1; eauto.
    + eauto.
    + i. des; clarify. eauto.
  Qed.

  Definition attatched_time (mem: Memory.t) (loc: Loc.t) (to: Time.t) :=
    exists to' msg, <<GET: Memory.get loc to' mem = Some (to, msg)>>.

  Lemma write_succeed_valid prom mem1 loc from1 to1 val released
        (MLE: Memory.le prom mem1)
        (NCOVER: forall t (COVER: covered loc t mem1),
            ~ Interval.mem (from1, to1) t)
        (TO: Time.le (View.rlx (View.unwrap released) loc) to1)
        (FROMTO: Time.lt from1 to1)
        (NOATTATCH: ~ attatched_time mem1 loc to1)
        (MSGWF: Message.wf (Message.full val released))
    :
      exists mem2,
        (<<WRITE: Memory.write prom mem1 loc from1 to1 val released prom mem2 Memory.op_kind_add>>).
  Proof.
    exploit Memory.add_exists; eauto.
    { instantiate (1:=mem1). instantiate (1:=loc).
      ii. eapply NCOVER; eauto. econs; eauto. }
    i. des. exists mem2.
    exploit Memory.add_exists_le; eauto. i. des.
    econs.
    - econs; eauto; ss.
      i. eapply NOATTATCH; eauto. econs; eauto.
    - exploit Memory.remove_exists; eauto.
      { eapply Memory.add_get0 in x1. des. eauto. } i. des.
      exploit MemoryFacts.MemoryFacts.add_remove_eq; eauto.
      i. clarify.
  Qed.

  Lemma write_disjoint promises1 mem1 loc from1 to1 val released promises3 mem2 kind
        (MLE: Memory.le promises1 mem1)
        (WRITE: Memory.write
                  promises1 mem1 loc from1 to1 val released promises3 mem2 kind)
        to
        (INT: Interval.mem (from1, to1) to)
    :
      (<<PROMISED: covered loc to promises1>>) \/
      (<<NEWMSG: ~ covered loc to mem1>>).
  Proof.
    inv WRITE. inv PROMISE.
    - right. ii. inv H. inv MEM. inv ADD.
      exploit DISJOINT; eauto.
    - left. dup PROMISES. eapply Memory.split_get0 in PROMISES. des.
      econs; eauto.
      inv INT. inv PROMISES0. inv SPLIT. econs; ss.
      etrans; eauto. left. auto.
    - left. dup PROMISES. eapply Memory.lower_get0 in PROMISES. des.
      econs; eauto.
    - clarify.
  Qed.

  Lemma write_msg_wf v prom v' prom'
        loc from to val releasedm released ord sc sc' mem_tgt mem_tgt' kind
        (WRITE: Local.write_step
                  (Local.mk v prom) sc mem_tgt
                  loc from to val releasedm released ord
                  (Local.mk v' prom') sc' mem_tgt' kind)
    :
      (<<TLE: Time.le
                (View.rlx (View.unwrap (TView.write_released v sc loc to releasedm ord)) loc) to>>) /\
      (<<FROMTO: Time.lt from to>>) /\
      (<<MSGWF: Message.wf (Message.full val (TView.write_released v sc loc to releasedm ord))>>) /\
      (<<NOATTATCH: forall (KIND: kind = Memory.op_kind_add), ~ attatched_time mem_tgt loc to>>)
  .
  Proof.
    inv WRITE. inv WRITE0. inv PROMISE.
    - inv TS. inv MEM. inv ADD. esplits; eauto. ii. clarify.
      unfold attatched_time in *. des. exploit ATTACH; eauto.
    - inv TS. inv MEM. inv SPLIT. esplits; eauto. ii. clarify.
    - inv TS. inv MEM. inv LOWER. esplits; eauto. ii. clarify.
    - clarify.
  Qed.

  Lemma memory_write_bot_add
        mem1 loc from1 to1 val released promises3 mem2 kind
        (WRITE: Memory.write
                  Memory.bot mem1 loc from1 to1 val released promises3 mem2 kind)
    :
      kind = Memory.op_kind_add.
  Proof.
    inv WRITE. inv PROMISE; auto.
    - exfalso. eapply Memory.split_get0 in PROMISES. des.
      rewrite Memory.bot_get in *. clarify.
    - exfalso. eapply Memory.lower_get0 in PROMISES. des.
      rewrite Memory.bot_get in *. clarify.
    - clarify.
  Qed.

  Lemma promise_bot_no_promise P lang (th0 th1: Thread.t lang) e
        (STEP: (@pred_step P lang) e th0 th1)
        (NOPROMISE: P <1= no_promise)
        (BOT: (Local.promises (Thread.local th0)) = Memory.bot)
    :
      (Local.promises (Thread.local th1)) = Memory.bot.
  Proof.
    inv STEP. eapply NOPROMISE in SAT. inv STEP0. inv STEP.
    - inv STEP0; des; clarify.
    - inv STEP0. ss. inv LOCAL; try inv LOCAL0; ss.
      + rewrite BOT in *. exploit memory_write_bot_add; eauto. i. clarify.
        exploit MemoryFacts.MemoryFacts.write_add_promises; eauto.
      + inv LOCAL1. inv LOCAL2. ss. rewrite BOT in *.
        exploit memory_write_bot_add; eauto. i. clarify.
        exploit MemoryFacts.MemoryFacts.write_add_promises; eauto.
  Qed.

  Lemma promise_bot_no_promise_rtc P lang (th0 th1: Thread.t lang)
        (STEP: rtc (tau (@pred_step P lang)) th0 th1)
        (NOPROMISE: P <1= no_promise)
        (BOT: (Local.promises (Thread.local th0)) = Memory.bot)
    :
      (Local.promises (Thread.local th1)) = Memory.bot.
  Proof.
    induction STEP; auto. erewrite IHSTEP; auto.
    inv H. eapply promise_bot_no_promise; eauto.
  Qed.

  Lemma add_succeed_wf mem1 loc from to msg mem2
        (ADD: Memory.add mem1 loc from to msg mem2)
    :
      (<<DISJOINT: forall to2 from2 msg2
                          (GET2: Memory.get loc to2 mem1 = Some (from2, msg2)),
          Interval.disjoint (from, to) (from2, to2)>>) /\
      (<<TO1: Time.lt from to>>) /\
      (<<MSG_WF: Message.wf msg>>).
  Proof.
    inv ADD. inv ADD0. esplits; eauto.
  Qed.

  Lemma lower_succeed_wf mem1 loc from to msg1 msg2 mem2
        (LOWER: Memory.lower mem1 loc from to msg1 msg2 mem2)
    :
      (<<GET: Memory.get loc to mem1 = Some (from, msg1)>>) /\
      (<<TS: Time.lt from to>>) /\
      (<<MSG_WF: Message.wf msg2>>) /\
      (<<MSG_LE: Message.le msg2 msg1>>).
  Proof.
    inv LOWER. inv LOWER0. esplits; eauto.
  Qed.

  Lemma split_succeed_wf mem1 loc ts1 ts2 ts3 msg2 msg3 mem2
        (SPLIT: Memory.split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2)
    :
      (<<GET2: Memory.get loc ts3 mem1 = Some (ts1, msg3)>>) /\
      (<<TS12: Time.lt ts1 ts2>>) /\
      (<<TS23: Time.lt ts2 ts3>>) /\
      (<<MSG_WF: Message.wf msg2>>).
  Proof.
    inv SPLIT. inv SPLIT0. esplits; eauto.
  Qed.

  Lemma promise_include_boundary prom0 mem0 loc from to msg prom1 mem1 kind
        (PROMISE: Memory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
        (BOTNONE: Memory.bot_none prom0)
    :
      Interval.mem (from, to) to.
  Proof.
    econs; ss; [|refl]. inv PROMISE.
    - eapply add_succeed_wf in MEM. des. auto.
    - eapply split_succeed_wf in MEM. des. auto.
    - eapply Memory.lower_get0 in PROMISES. des.
      dup GET. eapply Memory.get_ts in GET1. des; clarify.
      rewrite BOTNONE in *. clarify.
    - eapply Memory.remove_get0 in PROMISES. des.
      dup GET. eapply Memory.get_ts in GET1. des; clarify.
      rewrite BOTNONE in *. clarify.
  Qed.

  Lemma step_write_not_in_boundary
        MSGS lang (th0 th1: Thread.t lang) pf e
        (STEP: Thread.step pf e th0 th1)
        (WRITENOTIN: write_not_in MSGS e)
        (LCWF0: Local.wf (Thread.local th0) (Thread.memory th0))
    :
      write_not_to MSGS e.
  Proof.
    inv LCWF0. inv STEP.
    - inv STEP0. inv LOCAL. ii. ss. des_ifs. eapply WRITENOTIN; eauto.
      eapply promise_include_boundary; eauto.
    - inv STEP0; ss. inv LOCAL; ss.
      + inv LOCAL0. inv WRITE. eapply WRITENOTIN; eauto.
        eapply promise_include_boundary; eauto.
      + inv LOCAL1. inv LOCAL2. inv WRITE. eapply WRITENOTIN; eauto.
        eapply promise_include_boundary; eauto.
  Qed.

  Lemma promise_wf_event prom0 mem0 loc from to msg prom1 mem1 kind
        (PROMISE: Memory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
        (INHABITED: Memory.inhabited mem0)
    :
      Time.lt from to.
  Proof.
    inv PROMISE.
    - eapply add_succeed_wf in PROMISES. des. eauto.
    - eapply split_succeed_wf in PROMISES. des. eauto.
    - eapply lower_succeed_wf in PROMISES. des. eauto.
    - eapply Memory.remove_get0 in MEM. des. dup GET.
      eapply memory_get_ts_strong in GET. des; auto.
      clarify. erewrite INHABITED in GET1. clarify.
  Qed.

  Lemma write_wf_event prom0 mem0 loc from to val released prom1 mem1 kind
        (WRITE: Memory.write prom0 mem0 loc from to val released prom1 mem1 kind)
        (INHABITED: Memory.inhabited mem0)
    :
      Time.lt from to.
  Proof.
    inv WRITE. eapply promise_wf_event; eauto.
  Qed.

  Lemma step_wf_event lang P (th0 th1: Thread.t lang) e
        (INHABITED: Memory.inhabited (Thread.memory th0))
        (STEP: pred_step P e th0 th1)
    :
      wf_event e.
  Proof.
    inv STEP. inv STEP0. inv STEP.
    - inv STEP0. inv LOCAL. ss.
      eapply promise_wf_event; eauto.
    - inv STEP0. inv LOCAL; ss.
      + inv LOCAL0. eapply write_wf_event; eauto.
      + inv LOCAL1. inv LOCAL2. eapply write_wf_event; eauto.
  Qed.

  Lemma steps_wf_event lang P (th0 th1: Thread.t lang)
        (INHABITED: Memory.inhabited (Thread.memory th0))
        (STEP: rtc (tau (@pred_step P lang)) th0 th1)
    :
      rtc (tau (@pred_step (P /1\ wf_event) lang)) th0 th1.
  Proof.
    ginduction STEP.
    - i. refl.
    - i. inv H. hexploit step_wf_event; eauto. i. inv TSTEP. econs.
      + econs; eauto. econs; eauto.
      + eapply IHSTEP; eauto. inv STEP0. eapply Thread.step_inhabited; eauto.
  Qed.


  Lemma lower_remove_exists mem1 loc from to msg1 msg2
        (GET: Memory.get loc to mem1 = Some (from, msg1))
        (TLT: Time.lt from to)
        (MSGWF: Message.wf msg2)
        (MSGLE: Message.le msg2 msg1)
    :
      exists mem2 mem3,
        (<<LOWER: Memory.lower mem1 loc from to msg1 msg2 mem2>>) /\
        (<<REMOVE: Memory.remove mem2 loc from to msg2 mem3>>) /\
        (<<SPEC: forall l t,
             Memory.get l t mem3 =
             if loc_ts_eq_dec (l, t) (loc, to) then None else Memory.get l t mem1>>).
  Proof.
    exploit Memory.lower_exists; eauto. i. des.
    dup x0. eapply Memory.lower_get0 in x0. des.
    exploit Memory.remove_exists.
    { eapply GET1. }
    i. des.
    esplits; eauto.
    i. erewrite (@Memory.remove_o mem0 mem2); eauto.
    erewrite (@Memory.lower_o mem2 mem1); eauto. des_ifs.
  Qed.

  Lemma lower_remove_remove mem1 mem2 mem3 loc from to msg1 msg2
        (LOWER: Memory.lower mem1 loc from to msg1 msg2 mem2)
        (REMOVE: Memory.remove mem2 loc from to msg2 mem3)
    :
      Memory.remove mem1 loc from to msg1 mem3.
  Proof.
    dup LOWER. eapply Memory.lower_get0 in LOWER0. des.
    exploit Memory.remove_exists.
    { eapply GET. }
    i. des.
    replace mem3 with mem0; auto.
    eapply Memory.ext. i.
    erewrite (@Memory.remove_o mem0 mem1); eauto.
    erewrite (@Memory.remove_o mem3 mem2); eauto.
    erewrite (@Memory.lower_o mem2 mem1); eauto.
    des_ifs.
  Qed.

  Lemma split_remove_exists mem1 loc ts1 ts2 ts3 msg2 msg3
        (GET: Memory.get loc ts3 mem1 = Some (ts1, msg3))
        (TS12: Time.lt ts1 ts2)
        (TS23: Time.lt ts2 ts3)
        (MSGWF: Message.wf msg2)
    :
      exists mem2 mem3,
        (<<SPLIT: Memory.split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2>>) /\
        (<<REMOVE: Memory.remove mem2 loc ts1 ts2 msg2 mem3>>).
  Proof.
    exploit Memory.split_exists; eauto. i. des.
    dup x0. eapply Memory.split_get0 in x0. des.
    exploit Memory.remove_exists.
    { eapply GET2. }
    i. des. esplits; eauto.
  Qed.

  Lemma split_remove_shorten mem1 loc ts1 ts2 ts3 msg2 msg3 mem2 mem3
        (REMOVE: Memory.remove mem2 loc ts1 ts2 msg2 mem3)
        (SPLIT: Memory.split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2)
    :
      forall l t,
        Memory.get l t mem3 =
        if loc_ts_eq_dec (l, t) (loc, ts3) then Some (ts2, msg3) else Memory.get l t mem1.
  Proof.
    exploit Memory.split_get0; eauto. i. des.
    i. erewrite (@Memory.remove_o mem3 mem2); eauto.
    erewrite (@Memory.split_o mem2 mem1); eauto. des_ifs; ss; des; clarify.
  Qed.

  Lemma memory_op_le mem_src0 mem_tgt0 loc from to msg mem_src1 mem_tgt1 kind
        (MLE: Memory.le mem_src0 mem_tgt0)
        (OPSRC: Memory.op mem_src0 loc from to msg mem_src1 kind)
        (OPTGT: Memory.op mem_tgt0 loc from to msg mem_tgt1 kind)
    :
      Memory.le mem_src1 mem_tgt1.
  Proof.
    inv OPSRC; inv OPTGT.
    - ii. erewrite Memory.add_o in LHS; eauto.
      erewrite Memory.add_o; cycle 1; eauto. des_ifs; eauto.
    - ii. erewrite Memory.split_o in LHS; eauto.
      erewrite Memory.split_o; cycle 1; eauto. des_ifs; eauto.
    - ii. erewrite Memory.lower_o in LHS; eauto.
      erewrite Memory.lower_o; cycle 1; eauto. des_ifs; eauto.
    - ii. erewrite Memory.remove_o in LHS; eauto.
      erewrite Memory.remove_o; cycle 1; eauto. des_ifs; eauto.
  Qed.

  Lemma max_full_ts_le_max_ts mem loc ts
        (MAX: Memory.max_full_ts mem loc ts)
    :
      Time.le ts (Memory.max_ts loc mem).
  Proof.
    inv MAX. des.
    eapply Memory.max_ts_spec in GET. des; auto.
  Qed.

End MEMORYLEMMAS.

Section VIEW.


  Lemma time_join_mon t0 t1 t0' t1'
        (TS0: Time.le t0 t0')
        (TS1: Time.le t1 t1')
    :
      Time.le (Time.join t0 t1) (Time.join t0' t1').
  Proof.
    unfold Time.join. des_ifs.
    - left. eapply TimeFacts.le_lt_lt; eauto.
    - etrans; eauto.
  Qed.

  Lemma timemap_join_mon tm0 tm1 tm0' tm1'
        (TM0: TimeMap.le tm0 tm0')
        (TM1: TimeMap.le tm1 tm1')
    :
      TimeMap.le (TimeMap.join tm0 tm1) (TimeMap.join tm0' tm1').
  Proof.
    unfold TimeMap.join. ii.
    eapply time_join_mon; eauto.
  Qed.

  Lemma view_join_mon vw0 vw1 vw0' vw1'
        (VW0: View.le vw0 vw0')
        (VW1: View.le vw1 vw1')
    :
      View.le (View.join vw0 vw1) (View.join vw0' vw1').
  Proof.
    inv VW0. inv VW1. econs.
    - eapply timemap_join_mon; eauto.
    - eapply timemap_join_mon; eauto.
  Qed.

  Lemma view_ur_rw_le loc ts
    :
      View.le (View.singleton_rw loc ts) (View.singleton_ur loc ts).
  Proof.
    unfold View.singleton_rw, View.singleton_ur. econs; ss; eauto.
    - eapply TimeMap.bot_spec.
    - refl.
  Qed.

  Lemma read_tview_mon
        tview1 tview2 loc ts released1 released2 ord1 ord2
        (TVIEW: TView.le tview1 tview2)
        (REL: View.opt_le released1 released2)
        (ORD: Ordering.le ord1 ord2):
    TView.le
      (TView.read_tview tview1 loc ts released1 ord1)
      (TView.read_tview tview2 loc ts released2 ord2).
  Proof.
    unfold TView.read_tview, View.singleton_ur_if.
    inv TVIEW. econs; ss.
    - eapply view_join_mon.
      + eapply view_join_mon; eauto. inv ORD.
        des_ifs; eauto.
        * refl.
        * exfalso. destruct ord1, ord2; ss.
        * apply view_ur_rw_le.
        * refl.
      + des_ifs.
        * eapply View.unwrap_opt_le; eauto.
        * exfalso. destruct ord1, ord2; ss.
        * apply View.bot_spec.
        * refl.
    - eapply view_join_mon.
      + eapply view_join_mon; eauto. inv ORD.
        des_ifs; eauto.
        * refl.
        * exfalso. destruct ord1, ord2; ss.
        * apply view_ur_rw_le.
        * refl.
      + des_ifs.
        * eapply View.unwrap_opt_le; eauto.
        * exfalso. destruct ord1, ord2; ss.
        * apply View.bot_spec.
        * refl.
  Qed.

  Lemma write_tview_mon_same_ord
        tview1 tview2 sc1 sc2 loc ts ord
        (TVIEW: TView.le tview1 tview2)
        (SC: TimeMap.le sc1 sc2)
    :
      TView.le
        (TView.write_tview tview1 sc1 loc ts ord)
        (TView.write_tview tview2 sc1 loc ts ord).
  Proof.
    unfold TView.write_tview.
    inv TVIEW. econs; ss.
    - i. unfold LocFun.find, LocFun.add. des_ifs.
      + eapply view_join_mon; eauto. refl.
      + eapply view_join_mon; eauto. refl.
    - eapply view_join_mon; eauto. refl.
    - eapply view_join_mon; eauto. refl.
  Qed.

  Lemma read_fence_tview_mon_same_ord
        tview1 tview2 ord
        (TVIEW: TView.le tview1 tview2)
    :
      TView.le
        (TView.read_fence_tview tview1 ord)
        (TView.read_fence_tview tview2 ord).
  Proof.
    unfold TView.read_fence_tview.
    inv TVIEW. econs; ss.
    des_ifs.
  Qed.

  Lemma write_fence_fc_mon_same_ord
        tview1 tview2 ord sc1 sc2
        (SC: TimeMap.le sc1 sc2)
        (TVIEW: TView.le tview1 tview2)
    :
      TimeMap.le
        (TView.write_fence_sc tview1 sc1 ord)
        (TView.write_fence_sc tview2 sc2 ord).
  Proof.
    inv TVIEW. inv CUR.
    unfold TView.write_fence_sc. des_ifs.
    eapply timemap_join_mon; eauto.
  Qed.

  Lemma write_fence_tview_mon_same_ord
        tview1 tview2 ord sc1 sc2
        (SC: TimeMap.le sc1 sc2)
        (TVIEW: TView.le tview1 tview2)
    :
      TView.le
        (TView.write_fence_tview tview1 sc1 ord)
        (TView.write_fence_tview tview2 sc2 ord).
  Proof.
    unfold TView.write_fence_tview.
    dup TVIEW. inv TVIEW. econs; ss.
    - i. unfold LocFun.find, LocFun.add. des_ifs; eauto.
      econs; ss.
      + eapply write_fence_fc_mon_same_ord; eauto.
      + eapply write_fence_fc_mon_same_ord; eauto.
    - des_ifs.
      econs; ss.
      + eapply write_fence_fc_mon_same_ord; eauto.
      + eapply write_fence_fc_mon_same_ord; eauto.
    - des_ifs.
      + eapply view_join_mon; eauto.
        econs; ss.
        * eapply write_fence_fc_mon_same_ord; eauto.
        * eapply write_fence_fc_mon_same_ord; eauto.
      + eapply view_join_mon; eauto. refl.
  Qed.

End VIEW.

Section PROMISED.

  Inductive promised (mem: Memory.t) (loc: Loc.t) (to: Time.t) : Prop :=
  | promised_intro
      msg
      (GET: Memory.get loc to mem = Some msg)
    :
      promised mem loc to
  .

  Inductive concrete_promised (mem: Memory.t) (loc: Loc.t) (to: Time.t) : Prop :=
  | concrete_promised_intro
      from val released
      (GET: Memory.get loc to mem = Some (from, Message.full val released))
  .

  Inductive concrete_covered (prom mem: Memory.t) (loc: Loc.t) (to: Time.t): Prop :=
  | concrete_covered_intro
      max
      (MAX: Memory.max_full_ts mem loc max)
      (COVERED: covered loc to prom)
      (TS: Time.le to max)
  .

  Lemma concrete_covered_covered prom mem loc to
        (COVERED: concrete_covered prom mem loc to)
    :
      covered loc to prom.
  Proof.
    inv COVERED. auto.
  Qed.

  Lemma concrete_promised_increase_promise promises1 mem1 loc from to msg promises2 mem2 kind
        (STEP: Memory.promise promises1 mem1 loc from to msg promises2 mem2 kind)
    :
      concrete_promised mem1 <2= concrete_promised mem2.
  Proof.
    inv STEP.
    - ii. inv PR.
      exploit Memory.add_get1; eauto. i.
      econs; eauto.
    - ii. inv PR.
      exploit Memory.split_get1; eauto. i. des.
      econs; eauto.
    - ii. inv PR.
      exploit Memory.lower_get1; eauto. i. des.
      inv MSG_LE. econs; eauto.
    - ii. inv PR. econs; eauto.
      erewrite Memory.remove_o; eauto. des_ifs; eauto.
      eapply Memory.remove_get0 in MEM. ss; des; clarify.
  Qed.

  Lemma concrete_promised_increase lang (th0 th1: Thread.t lang) pf e
        (STEP: Thread.step pf e th0 th1)
    :
      concrete_promised (Thread.memory th0) <2= concrete_promised (Thread.memory th1).
  Proof.
    i. inv STEP.
    - inv STEP0. ss. inv LOCAL.
      eapply concrete_promised_increase_promise; eauto.
    - inv STEP0; ss. inv LOCAL; ss.
      + inv LOCAL0. inv WRITE.
        eapply concrete_promised_increase_promise; eauto.
      + inv LOCAL1. inv LOCAL2. inv WRITE.
        eapply concrete_promised_increase_promise; eauto.
  Qed.

End PROMISED.

Inductive opt_pred_step P lang
  : ThreadEvent.t -> Thread.t lang -> Thread.t lang -> Prop :=
| step_none t: opt_pred_step P ThreadEvent.silent t t
| step_some
    e t0 t1
    (STEP: pred_step P e t0 t1)
  :
    opt_pred_step P e t0 t1.
#[export]
Hint Constructors opt_pred_step: core.


Section UNCHANGABLES.

  Inductive unchangable (mem prom: Memory.t) (l: Loc.t) (t: Time.t) (from: Time.t) (msg: Message.t): Prop :=
  | unchangable_intro
      (GET: Memory.get l t mem = Some (from, msg))
      (NPROM: Memory.get l t prom = None)
  .

  Inductive unwritable (mem prom: Memory.t) (l: Loc.t) (t: Time.t): Prop :=
  | unwritable_intro
      to from msg
      (UNCH: unchangable mem prom l to from msg)
      (ITV: Interval.mem (from, to) t)
  .

  Lemma unwritable_covered prom mem loc to
        (UNWRITABLE: unwritable mem prom loc to)
    :
      covered loc to mem.
  Proof.
    inv UNWRITABLE. inv UNCH. econs; eauto.
  Qed.

  Inductive unchangable_ts (mem prom: Memory.t) (l: Loc.t) (t: Time.t): Prop :=
  | unchangable_ts_intro
      from msg
      (UNCH: unchangable mem prom l t from msg)
  .

  Lemma unchangable_promise mem0 prom0 loc from to msg prom1 mem1 kind
        (PROMISE: Memory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
    :
      unchangable mem0 prom0 <4= unchangable mem1 prom1.
  Proof.
    ii. inv PR. inv PROMISE.
    - econs.
      + eapply Memory.add_get1; eauto.
      + eapply Memory.add_get0 in MEM. erewrite Memory.add_o; eauto.
        des_ifs. ss. des. clarify.
    - econs.
      + erewrite Memory.split_o; eauto. eapply Memory.split_get0 in MEM.
        des. des_ifs.
        * ss. des. clarify.
        * ss. destruct a. clarify. eapply Memory.split_get0 in PROMISES. des; clarify.
      + eapply Memory.split_get0 in MEM. des.
        erewrite Memory.split_o; eauto.
        eapply Memory.split_get0 in PROMISES.
        des_ifs; ss; des; clarify.
    - econs.
      + erewrite Memory.lower_o; eauto. eapply Memory.lower_get0 in MEM.
        des. des_ifs. ss. des. clarify. exfalso.
        eapply Memory.lower_get0 in PROMISES. des. clarify.
      + erewrite Memory.lower_o; eauto.
        eapply Memory.lower_get0 in PROMISES.
        des_ifs. ss. des. clarify.
    - econs.
      + erewrite Memory.remove_o; eauto. eapply Memory.remove_get0 in MEM.
        des. des_ifs. ss. des. clarify. exfalso.
        eapply Memory.remove_get0 in PROMISES. des. clarify.
      + erewrite Memory.remove_o; eauto.
        eapply Memory.remove_get0 in PROMISES. des_ifs.
  Qed.

  Lemma unchangable_remove mem prom0 loc from to msg prom1
        (PROMISE: Memory.remove prom0 loc from to msg prom1)
    :
      unchangable mem prom0 <4= unchangable mem prom1.
  Proof.
    ii. inv PR. econs; eauto.
    erewrite Memory.remove_o; eauto. des_ifs.
  Qed.

  Lemma unchangable_increase pf e lang (th0 th1: Thread.t lang)
        (STEP: Thread.step pf e th0 th1)
    :
      unchangable (Thread.memory th0) (Local.promises (Thread.local th0)) <4=
      unchangable (Thread.memory th1) (Local.promises (Thread.local th1)).
  Proof.
    inv STEP.
    - inv STEP0; ss. inv LOCAL. i.
      hexploit unchangable_promise; eauto.
    - i. inv STEP0; ss. inv LOCAL; try inv LOCAL0; ss.
      + inv WRITE. exploit unchangable_promise; eauto.
        eapply unchangable_remove; eauto.
      + inv LOCAL1. inv LOCAL2. ss. inv WRITE.
        exploit unchangable_promise; eauto.
        eapply unchangable_remove; eauto.
  Qed.

  Lemma unchangable_rtc_increase P lang (th0 th1: Thread.t lang)
        (STEPS: rtc (tau (@pred_step P lang))th0 th1)
    :
      unchangable (Thread.memory th0) (Local.promises (Thread.local th0)) <4=
      unchangable (Thread.memory th1) (Local.promises (Thread.local th1)).
  Proof.
    ginduction STEPS; ss. i.
    eapply IHSTEPS.
    inv H. inv TSTEP. inv STEP. eapply unchangable_increase; eauto.
  Qed.

  Lemma other_promise_unchangable c tid1 tid2 st1 st2 lc1 lc2
        (CWF: Configuration.wf c)
        (TID1: IdentMap.find tid1 (Configuration.threads c) = Some (st1, lc1))
        (TID2: IdentMap.find tid2 (Configuration.threads c) = Some (st2, lc2))
        (DIFF: tid1 <> tid2)
        l t from msg
        (GET: Memory.get l t (Local.promises lc2) = Some (from, msg))
    :
      unchangable (Configuration.memory c) (Local.promises lc1) l t from msg.
  Proof.
    inv CWF. inv WF. destruct st1, st2. econs; eauto.
    - exploit THREADS; try apply TID2; eauto. intros LCWF. inv LCWF. eauto.
    - destruct (Memory.get l t (Local.promises lc1)) eqn:GET0; eauto. exfalso.
      exploit DISJOINT; eauto. intros LCDISJ. inv LCDISJ. destruct p.
      inv DISJOINT0. exploit DISJOINT1; eauto. i. des.
      eapply Memory.get_ts in GET. eapply Memory.get_ts in GET0. des; clarify.
      eapply x2; eauto.
      + instantiate (1:=t). econs; ss; eauto. refl.
      + econs; ss; eauto. refl.
  Qed.

  Definition promise_not_in (MSGS : Loc.t -> Time.t -> Prop)
             (e : ThreadEvent.t) : Prop :=
    match e with
    | ThreadEvent.promise loc from to _ _ =>
      forall t (IN: Interval.mem (from, to) t), ~ (MSGS loc t)
    | _ => True
    end.

  Lemma step_promise_not_in_other_msgs
        promises1 mem1 loc from1 to1 msg promises3 mem2 kind
        (PROMISE: Memory.promise promises1 mem1 loc from1 to1 msg promises3 mem2 kind)
    :
      ~ unchangable_ts mem1 promises1 loc to1.
  Proof.
    ii. inv H. inv UNCH. inv PROMISE.
    - dup GET. eapply Memory.add_get1 in GET; eauto.
      eapply Memory.add_get0 in MEM. des. clarify.
    - dup GET. eapply Memory.split_get1 in GET; eauto.
      eapply Memory.split_get0 in MEM. des. clarify.
    - dup GET. eapply Memory.lower_get1 in GET; eauto.
      eapply Memory.lower_get0 in MEM. des. clarify.
      eapply Memory.lower_get0 in PROMISES. des. clarify.
    - eapply Memory.remove_get0 in PROMISES. des. clarify.
  Qed.

  Definition unwritable2 (mem prom: Memory.t) (l: Loc.t) (t: Time.t) :=
    (<<COV: covered l t mem>>) /\
    (<<NCOV: ~ covered l t prom>>).

  Lemma unwritable_eq mem prom
        (MLE: Memory.le prom mem)
        l t
    :
      unwritable mem prom l t <-> unwritable2 mem prom l t.
  Proof.
    split; i.
    - inv H. inv UNCH. econs.
      + econs; eauto.
      + ii. inv H.
        exploit Memory.get_disjoint.
        { eapply MLE. eapply GET0. }
        { eapply GET. }
        i. des; clarify.
        eapply x0; eauto.
    - inv H. inv H0. econs; eauto. econs; eauto.
      destruct (Memory.get l to prom) eqn:GET0; auto. destruct p. exfalso.
      dup GET0. eapply MLE in GET0. clarify. eapply H1. econs; eauto.
  Qed.

  Lemma step_write_not_in_promise promises1 mem1 loc from1 to1 msg promises3 mem2 kind
        (MLE: Memory.le promises1 mem1)
        (PROMISE: Memory.promise promises1 mem1 loc from1 to1 msg promises3 mem2 kind)
        t
        (IN: Interval.mem (from1, to1) t)
    :
      ~ unwritable mem1 promises1 loc t.
  Proof.
    rewrite unwritable_eq; auto.
    unfold unwritable2. apply or_not_and. inv PROMISE.
    - left. ii. inv H. dup GET. eapply Memory.add_get1 in GET; eauto.
      eapply Memory.add_get0 in MEM. des.
      exploit Memory.get_disjoint.
      + eapply GET.
      + eapply GET2.
      + i. des; clarify. eauto.
    - right. eapply Memory.split_get0 in PROMISES. des. ii. apply H.
      econs; eauto. inv IN. econs; ss; eauto. etrans; eauto.
      inv MEM. inv SPLIT. left. eauto.
    - right. eapply Memory.lower_get0 in PROMISES. des. ii. apply H.
      econs; eauto.
    - right. eapply Memory.remove_get0 in PROMISES. des. ii. apply H.
      econs; eauto.
  Qed.

  Lemma step_write_not_in_write promises1 mem1 loc from1 to1 val released promises3 mem2 kind
        (MLE: Memory.le promises1 mem1)
        (WRITE: Memory.write promises1 mem1 loc from1 to1 val released promises3 mem2 kind)
        t
        (IN: Interval.mem (from1, to1) t)
    :
      ~ unwritable mem1 promises1 loc t.
  Proof.
    inv WRITE. eapply step_write_not_in_promise; eauto.
  Qed.

  Lemma step_write_not_in lang (th_tgt th_tgt': Thread.t lang) e_tgt pf
        (MLE: Memory.le (Local.promises (Thread.local th_tgt)) (Thread.memory th_tgt))
        (STEP: Thread.step pf e_tgt th_tgt th_tgt')
    :
      write_not_in (unwritable (Thread.memory th_tgt) (Local.promises (Thread.local th_tgt)))
                   e_tgt.
  Proof.
    inv STEP.
    - inv STEP0; ss. inv LOCAL.
      ii. des_ifs. ii. eapply step_write_not_in_promise in PROMISE; eauto.
    - inv STEP0; ss. inv LOCAL; ss.
      + inv LOCAL0. ii. exploit step_write_not_in_write; eauto.
      + inv LOCAL1. inv LOCAL2. ss. ii. exploit step_write_not_in_write; eauto.
  Qed.

  Lemma unwritable_increase pf e lang (th0 th1: Thread.t lang)
        (STEP: Thread.step pf e th0 th1)
    :
      unwritable (Thread.memory th0) (Local.promises (Thread.local th0)) <2=
      unwritable (Thread.memory th1) (Local.promises (Thread.local th1)).
  Proof.
    ii. inv PR.
    eapply unchangable_increase in UNCH; eauto.
    econs; eauto.
  Qed.

  Lemma rtc_unwritable_increase lang (th0 th1: Thread.t lang)
        (STEP: rtc (Thread.tau_step (lang:=lang)) th0 th1)
    :
      unwritable (Thread.memory th0) (Local.promises (Thread.local th0)) <2=
      unwritable (Thread.memory th1) (Local.promises (Thread.local th1)).
  Proof.
    induction STEP; eauto.
    i. inv H. inv TSTEP. eapply IHSTEP. eapply unwritable_increase; eauto.
  Qed.

  Lemma steps_write_not_in P lang (th_tgt th_tgt': Thread.t lang)
        (MLE: Memory.le (Local.promises (Thread.local th_tgt)) (Thread.memory th_tgt))
        (STEP: rtc (tau (@pred_step P lang)) th_tgt th_tgt')
    :
      rtc (tau (@pred_step (P /1\ write_not_in (unwritable (Thread.memory th_tgt) (Local.promises (Thread.local th_tgt)))) lang)) th_tgt th_tgt'.
  Proof.
    ginduction STEP.
    - i. refl.
    - i. inv H. inv TSTEP. econs 2.
      + econs; eauto. econs; eauto.
        split; auto. inv STEP0. eapply step_write_not_in; eauto.
      + inv STEP0. exploit IHSTEP.
        * eapply step_promises_le in MLE; eauto. econs; eauto.
        * i. eapply pred_step_rtc_mon; eauto.
          i. ss. des. split; auto. eapply write_not_in_mon; eauto.
          i. eapply unwritable_increase; eauto.
  Qed.

  Lemma other_promise_unwritable c tid1 tid2 st1 st2 lc1 lc2
        (CWF: Configuration.wf c)
        (TID1: IdentMap.find tid1 (Configuration.threads c) = Some (st1, lc1))
        (TID2: IdentMap.find tid2 (Configuration.threads c) = Some (st2, lc2))
        (DIFF: tid1 <> tid2)
        l t
        (COV: covered l t (Local.promises lc2))
    :
      unwritable (Configuration.memory c) (Local.promises lc1) l t.
  Proof.
    inv CWF. inv WF. inv COV. destruct st1, st2.
    rewrite unwritable_eq; cycle 1.
    { exploit THREADS; try apply TID1. intro x1. inv x1. auto. }
    unfold unwritable2. esplits; eauto.
    - exploit THREADS; try apply TID2; eauto. intros LCWF. inv LCWF.
      econs; eauto.
    - ii. inv H. exploit DISJOINT; eauto. intros LCDISJ. inv LCDISJ.
      inv DISJOINT0. exploit DISJOINT1; eauto. intro x1. des.
      eapply x1; eauto.
  Qed.

End UNCHANGABLES.


Section UNCHANGEDON.

  Inductive unchanged_on (P: Loc.t -> Time.t -> Prop) m0 m1 : Prop :=
  | unchanged_on_intro
      (NCOV: forall l t (IN: P l t) (COV: covered l t m1), covered l t m0)
      (FUTURE : Memory.le m0 m1)
  .
  Global Program Instance le_PreOrder P: PreOrder (unchanged_on P).
  Next Obligation. ii. econs; eauto. refl. Qed.
  Next Obligation. ii. inv H. inv H0. econs; eauto. etrans; eauto. Qed.

  Lemma unchanged_on_mon L0 L1
        m0 m1
        (NOTIN: unchanged_on L1 m0 m1)
        (LE: L0 <2= L1)
    :
      unchanged_on L0 m0 m1.
  Proof.
    inv NOTIN. econs; eauto.
  Qed.

  Lemma write_not_in_unchanged_on_write L v v' prom'
        loc from to val releasedm released ord sc sc'
        mem_tgt mem_tgt' kind
        (WRITE: Local.write_step
                  (Local.mk v Memory.bot) sc mem_tgt
                  loc from to val releasedm released ord
                  (Local.mk v' prom') sc' mem_tgt' kind)
        (NOTIN: forall t (IN: Interval.mem (from, to) t), ~ (L loc t))
    :
      unchanged_on L mem_tgt mem_tgt'.
  Proof.
    inv WRITE. ss. clarify.
    exploit memory_write_bot_add; eauto. i. clarify.
    inv WRITE0. inv PROMISE. econs.
    - i. rewrite add_covered in COV; eauto. des; auto.
      clarify. exfalso. eapply NOTIN; eauto.
    - ii. eapply Memory.add_get1; eauto.
  Qed.

  Lemma write_not_in_unchanged_on P L e lang (th0 th1: Thread.t lang)
        (STEP: pred_step P e th0 th1)
        (PRED: P <1= (write_not_in L /1\ no_promise))
        (BOT: (Local.promises (Thread.local th0)) = Memory.bot)
    :
      unchanged_on L (Thread.memory th0) (Thread.memory th1).
  Proof.
    inv STEP. eapply PRED in SAT. des. inv STEP0. inv STEP.
    - inv STEP0; ss; des; clarify.
    - des. inv STEP0. ss. inv LOCAL; try refl.
      + destruct lc1, lc2. ss. clarify. exploit write_not_in_unchanged_on_write; eauto.
      + inv LOCAL1. ss.
        destruct lc1, lc2. ss. clarify. exploit write_not_in_unchanged_on_write; eauto.
  Qed.

End UNCHANGEDON.

Lemma promise_memory_le prom0 mem0 loc from to msg prom1 mem1 kind
      (MLE: Memory.le prom0 mem0)
      (PROMISE: Memory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
  :
    Memory.le prom1 mem1.
Proof.
  inv PROMISE.
  - ii. erewrite Memory.add_o in LHS; eauto.
    erewrite Memory.add_o; cycle 1; eauto. des_ifs; eauto.
  - ii. erewrite Memory.split_o in LHS; eauto.
    erewrite Memory.split_o; cycle 1; eauto. des_ifs; eauto.
  - ii. erewrite Memory.lower_o in LHS; eauto.
    erewrite Memory.lower_o; cycle 1; eauto. des_ifs; eauto.
  - ii. erewrite Memory.remove_o in LHS; eauto.
    erewrite Memory.remove_o; cycle 1; eauto. des_ifs; eauto.
Qed.

Lemma write_memory_le prom0 mem0 loc from to val released prom1 mem1 kind
      (MLE: Memory.le prom0 mem0)
      (PROMISE: Memory.write prom0 mem0 loc from to val released prom1 mem1 kind)
  :
    Memory.le prom1 mem1.
Proof.
  inv PROMISE. etrans.
  - eapply remove_le; eauto.
  - eapply promise_memory_le; eauto.
Qed.

Lemma step_memory_le lang (th0 th1: Thread.t lang) pf e
      (STEP: Thread.step pf e th0 th1)
      (MLE: Memory.le (Local.promises (Thread.local th0)) (Thread.memory th0))
  :
    Memory.le (Local.promises (Thread.local th1)) (Thread.memory th1).
Proof.
  inv STEP.
  - inv STEP0. ss. inv LOCAL.
    eapply promise_memory_le; eauto.
  - inv STEP0. ss. inv LOCAL; ss; try (inv LOCAL0; ss).
    + eapply write_memory_le; eauto.
    + inv LOCAL1. inv LOCAL2. ss.
      eapply write_memory_le; eauto.
Qed.

Lemma pf_step_memory_le lang (th0 th1: Thread.t lang) e
      (STEP: pred_step no_promise e th0 th1)
      (BOT: (Local.promises (Thread.local th0)) = Memory.bot)
  :
    Memory.le (Thread.memory th0) (Thread.memory th1).
Proof.
  exploit write_not_in_unchanged_on; eauto.
  - i. instantiate (1:=fun _ _ => False).
    ss. splits; eauto. unfold write_not_in. des_ifs.
  - i. inv x0. auto.
Qed.

Inductive configuration_step: forall (e:MachineEvent.t) (tid:Ident.t) (c1 c2:Configuration.t), Prop :=
| configuration_step_intro
    pf e tid c1 lang st1 lc1 e2 st3 lc3 sc3 memory3
    (TID: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st1, lc1))
    (STEPS: rtc (@Thread.tau_step _) (Thread.mk _ st1 lc1 (Configuration.sc c1) (Configuration.memory c1)) e2)
    (STEP: Thread.step pf e e2 (Thread.mk _ st3 lc3 sc3 memory3))
    (CONSISTENT: forall (EVENT: e <> ThreadEvent.failure),
        Thread.consistent (Thread.mk _ st3 lc3 sc3 memory3))
  :
    configuration_step (ThreadEvent.get_machine_event e) tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st3, lc3) (Configuration.threads c1)) sc3 memory3)
.

Lemma configuration_step_equivalent e tid c1 c2
  :
    Configuration.step e tid c1 c2 <-> configuration_step e tid c1 c2.
Proof.
  split.
  - i. inv H.
    + replace MachineEvent.failure with (ThreadEvent.get_machine_event ThreadEvent.failure); auto.
      econs; eauto. i. clarify.
    + econs; eauto.
  - i. inv H. destruct (classic (e0 = ThreadEvent.failure)).
    + clarify. econs 1; eauto.
    + econs 2; eauto.
Qed.

Definition no_reserves (proms: Memory.t): Prop :=
  forall loc to from msg (GET: Memory.get loc to proms = Some (from, msg)),
    msg <> Message.reserve.


Definition memory_concrete_le (lhs rhs: Memory.t): Prop :=
  forall loc to from val released
         (GET: Memory.get loc to lhs = Some (from, Message.full val released)),
    Memory.get loc to rhs = Some (from, Message.full val released).
Global Program Instance concrete_le_PreOrder: PreOrder memory_concrete_le.
Next Obligation. ii. ss. Qed.
Next Obligation. ii. eauto. Qed.

Lemma memory_concrete_le_le
  :
    Memory.le <2= memory_concrete_le.
Proof.
  ii. eauto.
Qed.
#[export]
Hint Resolve memory_concrete_le_le: core.

Lemma memory_concrete_le_closed_timemap tm mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (TM: Memory.closed_timemap tm mem0)
  :
    Memory.closed_timemap tm mem1.
Proof.
  ii. hexploit (TM loc). i. des.
  esplits; eauto.
Qed.

Lemma memory_concrete_le_closed_view vw mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (VW: Memory.closed_view vw mem0)
  :
    Memory.closed_view vw mem1.
Proof.
  inv VW. econs.
  - eapply memory_concrete_le_closed_timemap; eauto.
  - eapply memory_concrete_le_closed_timemap; eauto.
Qed.

Lemma memory_concrete_le_closed_opt_view vw mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (VW: Memory.closed_opt_view vw mem0)
  :
    Memory.closed_opt_view vw mem1.
Proof.
  inv VW; econs.
  eapply memory_concrete_le_closed_view; eauto.
Qed.

Lemma memory_concrete_le_closed_msg msg mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (MSG: Memory.closed_message msg mem0)
  :
    Memory.closed_message msg mem1.
Proof.
  inv MSG; econs.
  eapply memory_concrete_le_closed_opt_view; eauto.
Qed.

Lemma memory_concrete_le_closed_tview vw mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (VW: TView.closed vw mem0)
  :
    TView.closed vw mem1.
Proof.
  inv VW. econs.
  - i. eapply memory_concrete_le_closed_view; eauto.
  - eapply memory_concrete_le_closed_view; eauto.
  - eapply memory_concrete_le_closed_view; eauto.
Qed.

Lemma memory_concrete_le_reserve_wf prom mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (RESERVE: Memory.reserve_wf prom mem0)
  :
    Memory.reserve_wf prom mem1.
Proof.
  ii. eapply RESERVE in GET. des.
  esplits; eauto.
Qed.

Lemma memory_concrete_le_local_wf lc mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (PROM: Memory.le (Local.promises lc) mem1)
      (LOCAL: Local.wf lc mem0)
  :
    Local.wf lc mem1.
Proof.
  inv LOCAL. econs; eauto.
  - eapply memory_concrete_le_closed_tview; eauto.
  - eapply memory_concrete_le_reserve_wf; eauto.
Qed.
