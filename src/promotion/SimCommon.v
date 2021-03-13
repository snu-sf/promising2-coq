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

Require Import Syntax.
Require Import Semantics.

Require Import PromiseConsistent.
Require Import MemoryMerge.
Require Import MemoryReorder.

Require Import FulfillStep.

Set Implicit Arguments.


Module SimCommon.
  (* sim_view *)

  Definition sim_timemap (l: Loc.t) (tm_src tm_tgt: TimeMap.t): Prop :=
    forall loc (LOC: loc <> l), tm_src loc = tm_tgt loc.

  Program Instance sim_timemap_Equivalence: forall l, Equivalence (sim_timemap l).
  Next Obligation.
    ii. ss.
  Qed.
  Next Obligation.
    ii. rewrite H; eauto.
  Qed.
  Next Obligation.
    ii. rewrite H; eauto.
  Qed.

  Inductive sim_view (l: Loc.t) (view_src view_tgt: View.t): Prop :=
  | sim_view_intro
      (PLN: sim_timemap l (View.pln view_src) (View.pln view_tgt))
      (RLX: sim_timemap l (View.rlx view_src) (View.rlx view_tgt))
  .
  Hint Constructors sim_view.

  Program Instance sim_view_Equivalence: forall l, Equivalence (sim_view l).
  Next Obligation.
    ii. ss.
  Qed.
  Next Obligation.
    ii. inv H. symmetry in PLN, RLX. econs; ss.
  Qed.
  Next Obligation.
    ii. inv H. inv H0. econs; etrans; eauto.
  Qed.

  Inductive sim_opt_view (l: Loc.t): forall (view_src view_tgt: option View.t), Prop :=
  | sim_opt_view_some
      view_src view_tgt
      (SIM: sim_view l view_src view_tgt):
      sim_opt_view l (Some view_src) (Some view_tgt)
  | sim_opt_view_none:
      sim_opt_view l None None
  .
  Hint Constructors sim_opt_view.

  Program Instance sim_opt_view_Equivalence: forall l, Equivalence (sim_opt_view l).
  Next Obligation.
    ii. destruct x; ss. econs; ss.
  Qed.
  Next Obligation.
    ii. inv H; ss. econs. symmetry. ss.
  Qed.
  Next Obligation.
    ii. inv H; inv H0; ss. econs; etrans; eauto.
  Qed.

  Inductive sim_tview (l: Loc.t) (tview_src tview_tgt: TView.t): Prop :=
  | sim_tview_intro
      (REL: forall loc (LOC: loc <> l),
          sim_view l ((TView.rel tview_src) loc) ((TView.rel tview_tgt) loc))
      (CUR: sim_view l (TView.cur tview_src) (TView.cur tview_tgt))
      (ACQ: sim_view l (TView.acq tview_src) (TView.acq tview_tgt))
  .
  Hint Constructors sim_tview.

  Program Instance sim_tview_Equivalence: forall l, Equivalence (sim_tview l).
  Next Obligation.
    ii. destruct x; ss.
  Qed.
  Next Obligation.
    ii. inv H. symmetry in REL, CUR, ACQ. econs; ss.
  Qed.
  Next Obligation.
    ii. inv H. inv H0. econs; etrans; eauto.
  Qed.


  (* lemmas on sim view *)

  Lemma sim_view_bot l: sim_view l View.bot View.bot.
  Proof.
    econs; ss.
  Qed.

  Lemma sim_view_join
        l
        v1_src v2_src
        v1_tgt v2_tgt
        (SIM1: sim_view l v1_src v1_tgt)
        (SIM2: sim_view l v2_src v2_tgt):
    sim_view l (View.join v1_src v2_src) (View.join v1_tgt v2_tgt).
  Proof.
    inv SIM1. inv SIM2.
    unfold View.join, TimeMap.join.
    econs; ss; ii.
    - exploit PLN; eauto. i.
      exploit PLN0; eauto. i.
      rewrite x. rewrite x0. refl.
    - exploit RLX; eauto. i.
      exploit RLX0; eauto. i.
      rewrite x. rewrite x0. refl.
  Qed.

  Lemma sim_opt_view_unwrap
        l view_src view_tgt
        (SIM: sim_opt_view l view_src view_tgt):
    sim_view l (View.unwrap view_src) (View.unwrap view_tgt).
  Proof.
    inv SIM; ss.
  Qed.

  Lemma sim_readable
        l
        tview_src released_src
        tview_tgt loc to released_tgt ord
        (TVIEW: sim_tview l tview_src tview_tgt)
        (RELEASED: sim_opt_view l released_src released_tgt)
        (LOC: loc <> l)
        (READABLE_TGT: TView.readable (TView.cur tview_tgt) loc to released_tgt ord):
    TView.readable (TView.cur tview_src) loc to released_src ord.
  Proof.
    inv TVIEW. inv CUR. inv READABLE_TGT. econs; i.
    - exploit PLN; eauto. i. rewrite x. ss.
    - exploit RLX0; eauto. i.
      exploit RLX; eauto. i. rewrite x0. ss.
  Qed.

  Lemma sim_read_tview
        l
        tview_src released_src
        tview_tgt loc to released_tgt ord
        (TVIEW: sim_tview l tview_src tview_tgt)
        (RELEASED: sim_opt_view l released_src released_tgt)
        (LOC: loc <> l):
    sim_tview l
              (TView.read_tview tview_src loc to released_src ord)
              (TView.read_tview tview_tgt loc to released_tgt ord).
  Proof.
    inv TVIEW. econs; ss.
    - condtac; ss.
      + apply sim_view_join; eauto using sim_opt_view_unwrap.
        apply sim_view_join; ss.
      + apply sim_view_join; eauto using sim_opt_view_unwrap.
        apply sim_view_join; ss.
        apply sim_view_bot.
    - condtac; ss.
      + apply sim_view_join; eauto using sim_opt_view_unwrap.
        apply sim_view_join; ss.
      + apply sim_view_join; eauto using sim_opt_view_unwrap.
        apply sim_view_join; ss.
        apply sim_view_bot.
  Qed.

  Lemma sim_write_released
        l
        tview_src sc_src releasedm_src
        tview_tgt sc_tgt releasedm_tgt
        loc to ord
        (LOC: loc <> l)
        (TVIEW: sim_tview l tview_src tview_tgt)
        (RELEASEDM: sim_opt_view l releasedm_src releasedm_tgt):
    sim_opt_view l
                 (TView.write_released tview_src sc_src loc to releasedm_src ord)
                 (TView.write_released tview_tgt sc_tgt loc to releasedm_tgt ord).
  Proof.
    inv TVIEW. inv CUR.
    exploit REL; eauto. i. inv x.
    unfold TView.write_released. condtac; ss.
    econs. apply sim_view_join; eauto using sim_opt_view_unwrap.
    condtac; econs; ss; ii; unfold LocFun.add;
      condtac; ss; unfold TimeMap.join.
    - exploit PLN; eauto. i. rewrite x. refl.
    - exploit RLX; eauto. i. rewrite x. refl.
    - exploit PLN0; eauto. i. rewrite x. refl.
    - exploit RLX0; eauto. i. rewrite x. refl.
  Qed.

  Lemma sim_writable
        l
        tview_src sc_src
        tview_tgt sc_tgt
        loc to ord
        (LOC: loc <> l)
        (TVIEW: sim_tview l tview_src tview_tgt)
        (WRITABLE_TGT: TView.writable (TView.cur tview_tgt) sc_tgt loc to ord):
    TView.writable (TView.cur tview_src) sc_src loc to ord.
  Proof.
    inv TVIEW. inv CUR. inv WRITABLE_TGT. econs; i.
    exploit RLX; eauto. i. rewrite x. ss.
  Qed.

  Lemma sim_write_tview
        l
        tview_src sc_src
        tview_tgt sc_tgt
        loc to ord
        (LOC: loc <> l)
        (TVIEW: sim_tview l tview_src tview_tgt):
    sim_tview l
              (TView.write_tview tview_src sc_src loc to ord)
              (TView.write_tview tview_tgt sc_tgt loc to ord).
  Proof.
    inv TVIEW. econs; ss.
    - i. condtac; ss.
      + unfold LocFun.add, LocFun.find. condtac; ss; eauto.
        subst. apply sim_view_join; eauto.
        econs; ss.
      + unfold LocFun.add, LocFun.find. condtac; ss; eauto.
        subst. apply sim_view_join; eauto.
        econs; ss.
    - apply sim_view_join; eauto. econs; ss.
    - apply sim_view_join; eauto. econs; ss.
  Qed.

  Lemma sim_read_fence_tview
        l tview_src tview_tgt ordr
        (TVIEW: sim_tview l tview_src tview_tgt):
    sim_tview l
              (TView.read_fence_tview tview_src ordr)
              (TView.read_fence_tview tview_tgt ordr).
  Proof.
    inv TVIEW. econs; ss. condtac; ss.
  Qed.

  Lemma sim_write_fence_sc
        l
        tview_src sc_src
        tview_tgt sc_tgt
        ordw
        (TVIEW: sim_tview l tview_src tview_tgt)
        (SC: sim_timemap l sc_src sc_tgt):
    sim_timemap l
                (TView.write_fence_sc tview_src sc_src ordw)
                (TView.write_fence_sc tview_tgt sc_tgt ordw).
  Proof.
    inv TVIEW. inv CUR.
    unfold TView.write_fence_sc. condtac; ss.
    ii. unfold TimeMap.join.
    exploit SC; eauto. i.
    exploit RLX; eauto. i.
    rewrite x. rewrite x0. refl.
  Qed.

  Lemma sim_write_fence_tview
        l
        tview_src sc_src
        tview_tgt sc_tgt
        ordw
        (TVIEW: sim_tview l tview_src tview_tgt)
        (SC: sim_timemap l sc_src sc_tgt):
    sim_tview l
              (TView.write_fence_tview tview_src sc_src ordw)
              (TView.write_fence_tview tview_tgt sc_tgt ordw).
  Proof.
    inv TVIEW. econs; ss; i.
    - repeat (condtac; ss; eauto).
      econs; eauto using sim_write_fence_sc.
    - repeat (condtac; ss).
      econs; eauto using sim_write_fence_sc.
    - repeat (condtac; ss).
      + apply sim_view_join; ss.
        econs; eauto using sim_write_fence_sc.
      + apply sim_view_join; ss.
  Qed.

  Lemma sim_fence_tview
        l
        tview_src sc_src
        tview_tgt sc_tgt
        ordr ordw
        (TVIEW: sim_tview l tview_src tview_tgt)
        (SC: sim_timemap l sc_src sc_tgt):
    sim_tview l
              (TView.write_fence_tview (TView.read_fence_tview tview_src ordr) sc_src ordw)
              (TView.write_fence_tview (TView.read_fence_tview tview_tgt ordr) sc_tgt ordw).
  Proof.
    eapply sim_write_fence_tview; eauto.
    eapply sim_read_fence_tview; eauto.
  Qed.


  (* sim_memory *)

  Inductive sim_message (l: Loc.t): forall (msg_src msg_tgt: Message.t), Prop :=
  | sim_message_full
      val released_src released_tgt
      (RELEASED: sim_opt_view l released_src released_tgt):
      sim_message l (Message.full val released_src) (Message.full val released_tgt)
  | sim_message_reserve:
      sim_message l Message.reserve Message.reserve
  .
  Hint Constructors sim_message.

  Program Instance sim_message_Equivalence: forall l, Equivalence (sim_message l).
  Next Obligation.
    ii. destruct x; ss. econs. refl.
  Qed.
  Next Obligation.
    ii. inv H; ss. econs. symmetry. ss.
  Qed.
  Next Obligation.
    ii. inv H; ss. inv H0. econs; etrans; eauto.
  Qed.

  Inductive sim_memory (l: Loc.t) (mem_src mem_tgt: Memory.t): Prop :=
  | sim_memory_intro
      (SOUND: forall loc from to msg_src
                (LOC: loc <> l)
                (GET_SRC: Memory.get loc to mem_src = Some (from, msg_src)),
          exists msg_tgt,
            <<GET_TGT: Memory.get loc to mem_tgt = Some (from, msg_tgt)>> /\
            <<MSG: sim_message l msg_src msg_tgt>>)
      (COMPLETE: forall loc from to msg_tgt
                   (LOC: loc <> l)
                   (GET_TGT: Memory.get loc to mem_tgt = Some (from, msg_tgt)),
          exists msg_src,
            <<GET_SRC: Memory.get loc to mem_src = Some (from, msg_src)>> /\
            <<MSG: sim_message l msg_src msg_tgt>>)
  .
  Hint Constructors sim_memory.

  Program Instance sim_memory_Equivalence: forall l, Equivalence (sim_memory l).
  Next Obligation.
    ii. econs; i.
    - esplits; eauto. refl.
    - esplits; eauto. refl.
  Qed.
  Next Obligation.
    ii. inv H. econs; i.
    - exploit COMPLETE; eauto. i. des.
      esplits; eauto. symmetry. ss.
    - exploit SOUND; eauto. i. des.
      esplits; eauto. symmetry. ss.
  Qed.
  Next Obligation.
    ii. inv H. inv H0. econs; i.
    - exploit SOUND; eauto. i. des.
      exploit SOUND0; eauto. i. des.
      esplits; eauto. etrans; eauto.
    - exploit COMPLETE0; eauto. i. des.
      exploit COMPLETE; eauto. i. des.
      esplits; eauto. etrans; eauto.
  Qed.

  Inductive sim_local (l: Loc.t) (lc_src lc_tgt: Local.t): Prop :=
  | sim_local_intro
      (TVIEW: sim_tview l (Local.tview lc_src) (Local.tview lc_tgt))
      (PROMISES1: sim_memory l (Local.promises lc_src) (Local.promises lc_tgt))
  .
  Hint Constructors sim_local.

  Program Instance sim_local_Equivalence: forall l, Equivalence (sim_local l).
  Next Obligation.
    ii. econs; refl.
  Qed.
  Next Obligation.
    ii. inv H. econs; symmetry; ss.
  Qed.
  Next Obligation.
    ii. inv H. inv H0. econs; etrans; eauto.
  Qed.


  (* lemmas on sim_memory *)

  Lemma sim_memory_remove
        l mem1_src mem1_tgt mem2_src mem2_tgt
        loc from to msg_src msg_tgt
        (SIM: sim_memory l mem1_src mem1_tgt)
        (REMOVE_SRC: Memory.remove mem1_src loc from to msg_src mem2_src)
        (REMOVE_TGT: Memory.remove mem1_tgt loc from to msg_tgt mem2_tgt):
    sim_memory l mem2_src mem2_tgt.
  Proof.
    inv SIM. econs; i.
    - revert GET_SRC.
      erewrite Memory.remove_o; eauto.
      erewrite (@Memory.remove_o mem2_tgt); eauto.
      condtac; ss; eauto.
    - revert GET_TGT.
      erewrite Memory.remove_o; eauto.
      erewrite (@Memory.remove_o mem2_src); eauto.
      condtac; ss; eauto.
  Qed.


  (* fulfillable *)

  Definition view_le_loc (l: Loc.t) (view1 view2: View.t): Prop :=
    <<PLN: Time.le ((View.pln view1) l) ((View.pln view2) l)>> /\
    <<RLX: Time.le ((View.rlx view1) l) ((View.rlx view2) l)>>.

  Global Program Instance view_le_loc_PreOrder: forall l, PreOrder (view_le_loc l).
  Next Obligation.
    ii. econs; unnw; refl.
  Qed.
  Next Obligation.
    ii. inv H. inv H0.
    econs; unnw; etrans; eauto.
  Qed.

  Definition tview_released_le_loc (l loc: Loc.t) (tview: TView.t) (released: View.t): Prop :=
    view_le_loc l ((TView.rel tview) loc) released.

  Definition prev_released_le_loc (l loc: Loc.t) (from: Time.t) (mem: Memory.t) (released: View.t): Prop :=
    match Memory.get loc from mem with
    | Some (_, Message.full _ (Some r)) => view_le_loc l r released
    | _ => True
    end.

  Definition fulfillable (l: Loc.t) (tview: TView.t) (mem promises: Memory.t): Prop :=
    forall loc from to val released
      (GETP: Memory.get loc to promises =
             Some (from, Message.full val (Some released))),
      <<TVIEW: tview_released_le_loc l loc tview released>> /\
      <<PREV: prev_released_le_loc l loc from mem released>>.


  (* generating source message *)

  Definition get_released_src (strong: bool) (l loc: Loc.t) (released_tgt: View.t)
             (tview_src: TView.t) (released_prev: View.t): View.t :=
    if strong
    then
      View.mk
        (LocFun.add
           l (Time.join ((View.pln (TView.cur tview_src)) l) ((View.pln released_prev) l))
           (View.pln released_tgt))
        (LocFun.add
           l (Time.join ((View.rlx (TView.cur tview_src)) l) ((View.rlx released_prev) l))
           (View.rlx released_tgt))
    else
      View.mk
        (LocFun.add
           l (Time.join (((TView.rel tview_src) loc).(View.pln) l) ((View.pln released_prev) l))
           (View.pln released_tgt))
        (LocFun.add
           l (Time.join (((TView.rel tview_src) loc).(View.rlx) l) ((View.rlx released_prev) l))
           (View.rlx released_tgt)).

  Definition get_message_src (strong: bool) (l loc: Loc.t) (msg_tgt: Message.t)
             (tview_src: TView.t) (from: Time.t) (mem_src: Memory.t): Message.t :=
    match msg_tgt with
    | Message.full val (Some released_tgt) =>
      match (Memory.get loc from mem_src) with
      | Some (_, Message.full _ (Some released_prev)) =>
        Message.full val (Some (get_released_src strong l loc released_tgt tview_src released_prev))
      | _ =>
        Message.full val (Some (get_released_src strong l loc released_tgt tview_src View.bot))
      end
    | _ => msg_tgt
    end.

  Lemma get_released_src_tview_released_le_loc
        strong l loc released_tgt tview_src released_prev
        (TVIEW: TView.wf tview_src):
    <<TVIEW: tview_released_le_loc l loc tview_src (get_released_src strong l loc released_tgt tview_src released_prev)>>.
  Proof.
    unfold get_released_src. condtac; ss.
    - inv TVIEW. destruct (REL_CUR loc).
      econs; ss.
      + unfold LocFun.add. condtac; ss. unnw.
        etrans; try eapply PLN. eapply Time.join_l.
      + unfold LocFun.add. condtac; ss. unnw.
        etrans; try eapply RLX. eapply Time.join_l.
    - econs; ss.
      + unfold LocFun.add. condtac; ss. eapply Time.join_l.
      + unfold LocFun.add. condtac; ss. eapply Time.join_l.
  Qed.

  Lemma get_released_src_prev_released_le_loc
        strong l loc released_tgt tview_src released_prev
        from mem_src from' val
        (GET: Memory.get loc from mem_src = Some (from', Message.full val (Some released_prev))):
    <<PREV: prev_released_le_loc l loc from mem_src (get_released_src strong l loc released_tgt tview_src released_prev)>>.
  Proof.
    unfold prev_released_le_loc. rewrite GET.
    unfold get_released_src, LocFun.add. 
    econs; repeat (condtac; ss); eauto using Time.join_r.
  Qed.

  Lemma get_released_src_sim_view
        strong l loc released_tgt tview_src released_prev:
    <<SIM: sim_view l (get_released_src strong l loc released_tgt tview_src released_prev) released_tgt>>.
  Proof.
    unfold get_released_src. econs; ss.
    - unfold sim_timemap, LocFun.add. i. repeat (condtac; ss).
    - unfold sim_timemap, LocFun.add. i. repeat (condtac; ss).
  Qed.

  Lemma get_released_src_wf
        strong l loc released_tgt tview_src released_prev
        (RELEASED_TGT: View.wf released_tgt)
        (TVIEW_SRC: TView.wf tview_src)
        (RELEASED_PREV: View.wf released_prev):
    View.wf (get_released_src strong l loc released_tgt tview_src released_prev).
  Proof.
    econs. ii.
    unfold get_released_src, LocFun.add. repeat (condtac; ss).
    - subst. inv TVIEW_SRC. inv CUR.
      inv RELEASED_PREV.
      apply Time.join_spec.
      + etrans; eauto. apply Time.join_l.
      + etrans; eauto. apply Time.join_r.
    - inv RELEASED_TGT. apply PLN_RLX.
    - subst. inv TVIEW_SRC. destruct (REL loc).
      inv RELEASED_PREV.
      apply Time.join_spec.
      + etrans; eauto. apply Time.join_l.
      + etrans; eauto. apply Time.join_r.
    - inv RELEASED_TGT. apply PLN_RLX.
  Qed.

  Lemma get_released_src_closed
        strong l loc released_tgt tview_src released_prev
        mem_src mem_tgt
        (SIM: sim_memory l mem_src mem_tgt)
        (MSG_TGT: Memory.closed_view released_tgt mem_tgt)
        (TVIEW_SRC: TView.closed tview_src mem_src)
        (PREV_SRC: Memory.closed_view released_prev mem_src):
    Memory.closed_view (get_released_src strong l loc released_tgt tview_src released_prev) mem_src.
  Proof.
    inv MSG_TGT. inv TVIEW_SRC. inv PREV_SRC.
    unfold get_released_src. condtac; ss.
    - econs; ss; ii.
      + unfold LocFun.add. condtac; ss.
        * subst. inv CUR.
          edestruct Time.join_cases; rewrite H; eauto.
        * specialize (PLN loc0). des. inv SIM.
          exploit COMPLETE; eauto. i. des.
          inv MSG. inv RELEASED; eauto.
      + unfold LocFun.add. condtac; ss.
        * subst. inv CUR.
          edestruct Time.join_cases; rewrite H; eauto.
        * specialize (RLX loc0). des. inv SIM.
          exploit COMPLETE; eauto. i. des.
          inv MSG. inv RELEASED; eauto.
    - econs; ss; ii.
      + unfold LocFun.add. condtac; ss.
        * subst. destruct (REL loc).
          edestruct Time.join_cases; rewrite H; eauto.
        * specialize (PLN loc0). des. inv SIM.
          exploit COMPLETE; eauto. i. des.
          inv MSG. inv RELEASED; eauto.
      + unfold LocFun.add. condtac; ss.
        * subst. destruct (REL loc).
          edestruct Time.join_cases; rewrite H; eauto.
        * specialize (RLX loc0). des. inv SIM.
          exploit COMPLETE; eauto. i. des.
          inv MSG. inv RELEASED; eauto.
  Qed.

  Lemma get_message_src_fulfillable
        strong l loc msg_tgt tview_src from mem_src
        val released
        (TVIEW: TView.wf tview_src)
        (MSG: get_message_src strong l loc msg_tgt tview_src from mem_src =
              Message.full val (Some released)):
    <<TVIEW: tview_released_le_loc l loc tview_src released>> /\
    <<PREV: prev_released_le_loc l loc from mem_src released>>.
  Proof.
    unfold get_message_src.
    destruct msg_tgt; ss. destruct released0; ss.
    destruct (Memory.get loc from mem_src) as [[? [? []|]]|] eqn:GET;
      inv MSG; split;
        eauto using get_released_src_tview_released_le_loc;
        eauto using get_released_src_prev_released_le_loc;
        unfold prev_released_le_loc; rewrite GET; ss.
  Qed.

  Lemma get_message_src_sim_message
        strong l loc msg_tgt tview_src from mem_src:
    <<SIM: sim_message l (get_message_src strong l loc msg_tgt tview_src from mem_src) msg_tgt>>.
  Proof.
    unfold get_message_src.
    destruct msg_tgt; ss. destruct released; ss.
    - destruct (Memory.get loc from mem_src) as [[? [? []|]]|];
        econs; econs; eapply get_released_src_sim_view.
    - econs. econs.
  Qed.

  Lemma get_message_src_wf
        strong l loc msg_tgt tview_src from mem_src
        (MSG_TGT: Message.wf msg_tgt)
        (TVIEW_SRC: TView.wf tview_src)
        (CLOSED_SRC: Memory.closed mem_src):
    Message.wf (get_message_src strong l loc msg_tgt tview_src from mem_src).
  Proof.
    unfold get_message_src.
    destruct msg_tgt; ss. destruct released; ss.
    inv MSG_TGT. inv WF.
    specialize View.bot_wf. i.
    destruct (Memory.get loc from mem_src) as [[? [? []|]]|] eqn:GET;
      econs; econs; eauto using get_released_src_wf.
    inv CLOSED_SRC. exploit CLOSED; eauto. i. des.
    inv MSG_WF. inv WF.
    eauto using get_released_src_wf.
  Qed.

  Lemma get_message_src_message_to
        strong l loc to msg_tgt tview_src from mem_src
        (MSG_TGT: Memory.message_to msg_tgt loc to)
        (LOC: loc <> l):
    Memory.message_to (get_message_src strong l loc msg_tgt tview_src from mem_src) loc to.
  Proof.
    unfold get_message_src.
    destruct msg_tgt; ss. destruct released; ss.
    inv MSG_TGT.
    destruct (Memory.get loc from mem_src) as [[? [? []|]]|] eqn:GET;
      econs; ss; unfold get_released_src, LocFun.add; repeat (condtac; ss).
  Qed.

  Lemma get_message_src_closed
        strong l loc msg_tgt tview_src from mem1_src mem2_src mem2_tgt
        (SIM: sim_memory l mem2_src mem2_tgt)
        (MSG_TGT: Memory.closed_message msg_tgt mem2_tgt)
        (TVIEW1_SRC: TView.closed tview_src mem1_src)
        (MEM1_SRC: Memory.closed mem1_src)
        (OP_SRC: forall v (CLOSED: Memory.closed_view v mem1_src),
            Memory.closed_view v mem2_src):
    Memory.closed_message (get_message_src strong l loc msg_tgt tview_src from mem1_src) mem2_src.
  Proof.
    inv MSG_TGT; ss. inv CLOSED; eauto.
    exploit Memory.closed_view_bot; try eapply MEM1_SRC. i.
    exploit OP_SRC; eauto. i.
    assert (TVIEW2_SRC: TView.closed tview_src mem2_src).
    { inv TVIEW1_SRC. econs; eauto. }
    destruct (Memory.get loc from mem1_src) as [[? [? []|]]|] eqn:GET;
      econs; econs; eapply get_released_src_closed; eauto.
    inv MEM1_SRC. exploit CLOSED; eauto. i. des.
    inv MSG_CLOSED. inv CLOSED1. eauto.
  Qed.

  Lemma get_message_src_full
        strong l loc msg_tgt tview_src from mem_src
        val released
        (MSG: get_message_src strong l loc msg_tgt tview_src from mem_src = Message.full val released):
    exists released_tgt, msg_tgt = Message.full val released_tgt.
  Proof.
    destruct msg_tgt; ss.
    destruct released0; try by inv MSG; eauto.
    destruct (Memory.get loc from mem_src) as [[? [? []|]]|]; inv MSG; eauto.
  Qed.

  Lemma get_message_src_reserve
        strong l loc msg_tgt tview_src from mem_src
        (MSG: get_message_src strong l loc msg_tgt tview_src from mem_src = Message.reserve):
    msg_tgt = Message.reserve.
  Proof.
    destruct msg_tgt; ss.
    destruct released; ss.
    destruct (Memory.get loc from mem_src) as [[? [? []|]]|]; ss.
  Qed.


  (* promise *)

  Lemma promise
        l tview_src
        promises1_src mem1_src
        promises1_tgt mem1_tgt loc from to msg_tgt promises2_tgt mem2_tgt kind_tgt
        (PROMISES1: sim_memory l promises1_src promises1_tgt)
        (MEM1: sim_memory l mem1_src mem1_tgt)
        (FULFILL1: fulfillable l tview_src mem1_src promises1_src)
        (TVIEW_SRC: TView.wf tview_src)
        (LE1_SRC: Memory.le promises1_src mem1_src)
        (LE1_TGT: Memory.le promises1_tgt mem1_tgt)
        (MEM1_SRC: Memory.closed mem1_src)
        (PROMISE_TGT: Memory.promise promises1_tgt mem1_tgt loc from to msg_tgt promises2_tgt mem2_tgt kind_tgt)
        (LOC: loc <> l):
    exists promises2_src mem2_src kind_src,
      <<PROMISE_SRC: Memory.promise promises1_src mem1_src loc from to
                                    (get_message_src false l loc msg_tgt tview_src from mem1_src)
                                    promises2_src mem2_src kind_src>> /\
      <<PROMISES2: sim_memory l promises2_src promises2_tgt>> /\
      <<MEM2: sim_memory l mem2_src mem2_tgt>> /\
      <<FULFILL2: fulfillable l tview_src mem2_src promises2_src>>.
  Proof.
    inv PROMISES1. inv MEM1. inv PROMISE_TGT.
    { (* add *)
      exploit (@Memory.add_exists mem1_src loc from to
                                  (get_message_src false l loc msg_tgt tview_src from mem1_src)).
      { ii. exploit SOUND0; eauto. i. des.
        exploit Memory.add_get1; try exact GET_TGT; eauto. i.
        exploit Memory.add_get0; try exact MEM. i. des.
        exploit Memory.get_disjoint; [exact x1|exact GET0|..]. i. des.
        { subst. congr. }
        apply (x2 x); eauto. }
      { inv MEM. inv ADD. ss. }
      { eapply get_message_src_wf; eauto.
        inv MEM. inv ADD. ss. }
      i. des.
      exploit Memory.add_exists_le; try exact x0; eauto. i. des.
      esplits.
      - econs; eauto.
        + eapply get_message_src_message_to; eauto.
        + i. exploit get_message_src_reserve; eauto. i. subst.
          exploit RESERVE; eauto. i. des.
          exploit COMPLETE0; try exact x; eauto. i. des.
          inv MSG. eauto.
        + i. exploit SOUND0; try exact GET; eauto. i. des.
          destruct msg_tgt; ss. eauto.
      - econs; i.
        + revert GET_SRC. erewrite Memory.add_o; eauto. condtac; ss; i.
          * des. subst. inv GET_SRC.
            exploit Memory.add_get0; try exact PROMISES. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o.
            exploit SOUND; eauto. i. des.
            exploit Memory.add_get1; try exact GET_TGT; eauto.
        + revert GET_TGT. erewrite Memory.add_o; eauto. condtac; ss; i.
          * des. subst. inv GET_TGT.
            exploit Memory.add_get0; try exact x1. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o.
            exploit COMPLETE; eauto. i. des.
            exploit Memory.add_get1; try exact GET_SRC; eauto.
      - econs; i.
        + revert GET_SRC. erewrite Memory.add_o; eauto. condtac; ss; i.
          * des. subst. inv GET_SRC.
            exploit Memory.add_get0; try exact MEM. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o.
            exploit SOUND0; eauto. i. des.
            exploit Memory.add_get1; try exact GET_TGT; eauto.
        + revert GET_TGT. erewrite Memory.add_o; eauto. condtac; ss; i.
          * des. subst. inv GET_TGT.
            exploit Memory.add_get0; try exact x0. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o.
            exploit COMPLETE0; eauto. i. des.
            exploit Memory.add_get1; try exact GET_SRC; eauto.
      - ii. revert GETP. erewrite Memory.add_o; eauto. condtac; ss; i.
        + des. subst. inv GETP.
          exploit get_message_src_fulfillable; eauto. i. des.
          split; auto.
          unfold prev_released_le_loc.
          erewrite Memory.add_o; eauto. condtac; ss.
          des. subst. inv x0. inv ADD. timetac.
        + guardH o.
          exploit FULFILL1; eauto. i. des. split; auto.
          unfold prev_released_le_loc.
          erewrite Memory.add_o; eauto. condtac; ss. des. subst.
          destruct (get_message_src false l loc msg_tgt tview_src from mem1_src) eqn:GET; ss.
          exploit get_message_src_full; eauto. i. des. subst.
          exploit LE1_SRC; try exact GETP. i.
          exploit SOUND0; try exact x; eauto. i. des. inv MSG.
          exploit ATTACH; eauto; ss.
    }

    { (* split *)
      guardH RESERVE.
      exploit Memory.split_get0; try exact PROMISES. i. des.
      clear GET GET1 GET2.
      exploit COMPLETE; eauto. i. des.
      exploit (@Memory.split_exists promises1_src loc from to ts3
                                    (get_message_src false l loc msg_tgt tview_src from mem1_src) msg_src); eauto.
      { inv MEM. inv SPLIT. ss. }
      { inv MEM. inv SPLIT. ss. }
      { eapply get_message_src_wf; eauto.
        inv MEM. inv SPLIT. ss. }
      i. des.
      exploit Memory.split_exists_le; try exact x0; eauto. i. des.
      esplits.
      - econs 2; eauto.
        + eapply get_message_src_message_to; eauto.
        + unguard. des. subst.
          unfold get_message_src.
          destruct released'; eauto.
          destruct (Memory.get loc from mem1_src) as [[? [? []|]]|]; eauto.
      - econs; i.
        + revert GET_SRC0. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          * des. subst. inv GET_SRC0.
            exploit Memory.split_get0; try exact PROMISES. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o. des. subst. inv GET_SRC0.
            exploit Memory.split_get0; try exact PROMISES. i. des.
            esplits; eauto.
          * guardH o. guardH o0.
            exploit SOUND; eauto. i. des.
            erewrite Memory.split_o; eauto. repeat condtac; ss.
            esplits; eauto.
        + revert GET_TGT. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          * des. subst. inv GET_TGT.
            exploit Memory.split_get0; try exact x0. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o. des. subst. inv GET_TGT.
            exploit Memory.split_get0; try exact x0. i. des.
            esplits; eauto.
          * guardH o. guardH o0.
            exploit COMPLETE; eauto. i. des.
            erewrite Memory.split_o; eauto. repeat condtac; ss.
            esplits; eauto.
      - econs; i.
        + revert GET_SRC0. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          * des. subst. inv GET_SRC0.
            exploit Memory.split_get0; try exact MEM. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o. des. subst. inv GET_SRC0.
            exploit Memory.split_get0; try exact MEM. i. des.
            esplits; eauto.
          * guardH o. guardH o0.
            exploit SOUND0; eauto. i. des.
            erewrite Memory.split_o; eauto. repeat condtac; ss.
            esplits; eauto.
        + revert GET_TGT. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          * des. subst. inv GET_TGT.
            exploit Memory.split_get0; try exact x1. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o. des. subst. inv GET_TGT.
            exploit Memory.split_get0; try exact x1. i. des.
            esplits; eauto.
          * guardH o. guardH o0.
            exploit COMPLETE0; eauto. i. des.
            erewrite Memory.split_o; eauto. repeat condtac; ss.
            esplits; eauto.
      - ii. revert GETP. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
        + des. subst. inv GETP.
          exploit get_message_src_fulfillable; eauto. i. des.
          split; auto.
          unfold prev_released_le_loc.
          erewrite Memory.split_o; eauto. repeat condtac; ss.
          * des. subst. inv x0. inv SPLIT. timetac.
          * guardH o. des. subst.
            inv x0. inv SPLIT. rewrite TS12 in TS23. timetac.
        + guardH o. des. subst. inv GETP.
          exploit FULFILL1; try exact GET_SRC. i. des. split; auto.
          exploit Memory.split_get0; try exact x1. i. des.
          unfold prev_released_le_loc. rewrite GET2.
          destruct msg_tgt as [? []|]; ss.
          assert (BOT: view_le_loc l (get_released_src false l loc t tview_src View.bot) released).
          { exploit FULFILL1; try exact GET_SRC. i. des.
            inv TVIEW0. econs; ss.
            - unfold LocFun.add. condtac; ss.
              eapply Time.join_spec; eauto.
              unfold TimeMap.bot. apply Time.bot_spec.
            - unfold LocFun.add. condtac; ss.
              eapply Time.join_spec; eauto.
              unfold TimeMap.bot. apply Time.bot_spec.
          }
          destruct (Memory.get loc from mem1_src) as [[? [? []|]]|] eqn:GET_PREV; ss.
          exploit FULFILL1; try exact GET_SRC. i. des.
          unfold prev_released_le_loc in PREV0. rewrite GET_PREV in *.
          inv TVIEW0. inv PREV0. econs; ss.
          * unfold LocFun.add. condtac; ss.
            eapply Time.join_spec; eauto.
          * unfold LocFun.add. condtac; ss.
            eapply Time.join_spec; eauto.
        + guardH o. guardH o0.
          exploit FULFILL1; eauto. i. des. split; auto.
          unfold prev_released_le_loc.
          erewrite Memory.split_o; eauto. repeat condtac; ss.
          * des. subst. exfalso.
            exploit Memory.split_get0; try exact x0. i. des.
            exploit Memory.get_ts; try exact GETP. i. des.
            { subst. inv x0. inv SPLIT. inv TS12. }
            exploit Memory.get_ts; try exact GET1. i. des.
            { subst. inv x0. inv SPLIT. inv TS23. }
            exploit Memory.get_disjoint; [exact GETP|exact GET1|..]. i. des.
            { subst. inv x0. inv SPLIT. timetac. }
            destruct (TimeFacts.le_lt_dec to0 ts3).
            { apply (x4 to0); econs; ss; try refl.
              inv x0. inv SPLIT. etrans; eauto. }
            { apply (x4 ts3); econs; ss; try refl.
              - inv x0. inv SPLIT. ss.
              - econs. ss. }
          * guardH o1. des. subst.
            exploit Memory.split_get0; try exact x1. i. des.
            unfold prev_released_le_loc in PREV.
            rewrite GET1 in *. ss.
    }

    { (* lower *)
      guardH RESERVE.
      exploit Memory.lower_get0; try exact PROMISES. i. des.
      exploit COMPLETE; eauto. i. des. clear GET GET0.
      exploit (@Memory.lower_exists promises1_src loc from to msg_src
                                    (get_message_src false l loc msg_tgt tview_src from mem1_src)); eauto.
      { inv MEM. inv LOWER. ss. }
      { eapply get_message_src_wf; eauto.
        inv MEM. inv LOWER. ss. }
      { unguard. des. subst.
        destruct released; cycle 1.
        - inv MSG_LE. inv RELEASED. inv MSG. inv RELEASED. ss. refl.
        - exploit Memory.lower_get0; try exact PROMISES. i. des.
          exploit SOUND; eauto. i. des.
          rewrite GET_TGT in *. inv GET. inv MSG. inv RELEASED.
          inv MSG_LE. inv RELEASED; [econs|]; ss.
          exploit FULFILL1; eauto. i. des.
          assert (BOT: View.le (get_released_src false l loc lhs tview_src View.bot) view_src).
          { inv SIM. inv TVIEW. econs; ss.
            - unfold TimeMap.bot.
              ii. unfold LocFun.add. condtac; ss.
              + subst. eapply Time.join_spec; eauto using Time.bot_spec.
              + exploit PLN; try eapply n. i. rewrite x. apply LE.
            - unfold TimeMap.bot.
              ii. unfold LocFun.add. condtac; ss.
              + subst. eapply Time.join_spec; eauto using Time.bot_spec.
              + exploit RLX; try eapply n. i. rewrite x. apply LE.
          }
          destruct (Memory.get loc from mem1_src) as [[? [? []|]]|] eqn:GET_PREV; econs; econs; ss.
          unfold prev_released_le_loc in PREV. rewrite GET_PREV in *.
          inv SIM. inv TVIEW. inv PREV. econs; ss.
          + ii. unfold LocFun.add. condtac; ss.
            * subst. eapply Time.join_spec; eauto.
            * exploit PLN; try eapply n. i. rewrite x. apply LE.
          + ii. unfold LocFun.add. condtac; ss.
            * subst. eapply Time.join_spec; eauto.
            * exploit RLX; try eapply n. i. rewrite x. apply LE.
      }
      i. des.
      exploit Memory.lower_exists_le; try exact x0; eauto. i. des.
      esplits.
      - econs 3; eauto.
        + eapply get_message_src_message_to; eauto.
        + unguard. des. subst. inv MSG_LE. inv MSG. eauto.
      - econs; i.
        + revert GET_SRC0. erewrite Memory.lower_o; eauto. condtac; ss; i.
          * des. subst. inv GET_SRC0.
            exploit Memory.lower_get0; try exact PROMISES. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o.
            exploit SOUND; eauto. i. des.
            erewrite Memory.lower_o; eauto. condtac; ss.
            esplits; eauto.
        + revert GET_TGT. erewrite Memory.lower_o; eauto. condtac; ss; i.
          * des. subst. inv GET_TGT.
            exploit Memory.lower_get0; try exact x0. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o.
            exploit COMPLETE; eauto. i. des.
            erewrite Memory.lower_o; eauto. condtac; ss.
            esplits; eauto.
      - econs; i.
        + revert GET_SRC0. erewrite Memory.lower_o; eauto. condtac; ss; i.
          * des. subst. inv GET_SRC0.
            exploit Memory.lower_get0; try exact MEM. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o.
            exploit SOUND0; eauto. i. des.
            erewrite Memory.lower_o; eauto. condtac; ss.
            esplits; eauto.
        + revert GET_TGT. erewrite Memory.lower_o; eauto. condtac; ss; i.
          * des. subst. inv GET_TGT.
            exploit Memory.lower_get0; try exact x1. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o.
            exploit COMPLETE0; eauto. i. des.
            erewrite Memory.lower_o; eauto. condtac; ss.
            esplits; eauto.
      - ii. revert GETP. erewrite Memory.lower_o; eauto. condtac; ss; i.
        + des. subst. inv GETP.
          exploit get_message_src_fulfillable; eauto. i. des.
          split; auto.
          unfold prev_released_le_loc.
          erewrite Memory.lower_o; eauto. condtac; ss. des. subst.
          inv x0. inv LOWER. timetac.
        + guardH o.
          exploit FULFILL1; eauto. i. des. split; auto.
          unfold prev_released_le_loc.
          erewrite Memory.lower_o; eauto. condtac; ss.
          des. subst.
          exploit Memory.lower_get0; try exact x1. i. des.
          unfold prev_released_le_loc in PREV. rewrite GET in *.
          inv x1. inv MSG_LE0; ss.
          * inv RELEASED; ss.
            unnw. etrans; try exact PREV.
            inv LE. econs; eauto.
          * exploit SOUND0; try exact GET; eauto. i. des. inv MSG0.
            exploit Memory.lower_get0; try exact MEM. i. des.
            rewrite GET1 in *. inv GET_TGT.
            unguardH RESERVE. des. ss.
    }

    { (* cancel *)
      exploit Memory.remove_get0; try exact PROMISES. i. des.
      exploit COMPLETE; eauto. i. des. inv MSG.
      exploit Memory.remove_exists; try exact GET_SRC. i. des.
      exploit Memory.remove_exists_le; try exact x0; eauto. i. des.
      esplits.
      - econs 4; eauto.
      - econs; i.
        + revert GET_SRC0. erewrite Memory.remove_o; eauto. condtac; ss; i.
          guardH o.
          exploit SOUND; eauto. i. des.
          erewrite Memory.remove_o; eauto. condtac; ss.
          esplits; eauto.
        + revert GET_TGT. erewrite Memory.remove_o; eauto. condtac; ss; i.
          guardH o.
          exploit COMPLETE; eauto. i. des.
          erewrite Memory.remove_o; eauto. condtac; ss.
          esplits; eauto.
      - econs; i.
        + revert GET_SRC0. erewrite Memory.remove_o; eauto. condtac; ss; i.
          guardH o.
          exploit SOUND0; eauto. i. des.
          erewrite Memory.remove_o; eauto. condtac; ss.
          esplits; eauto.
        + revert GET_TGT. erewrite Memory.remove_o; eauto. condtac; ss; i.
          guardH o.
          exploit COMPLETE0; eauto. i. des.
          erewrite Memory.remove_o; eauto. condtac; ss.
          esplits; eauto.
      - ii. revert GETP. erewrite Memory.remove_o; eauto. condtac; ss. i.
        guardH o.
        exploit FULFILL1; eauto. i. des. split; auto.
        unfold prev_released_le_loc in *.
        erewrite Memory.remove_o; eauto. condtac; ss.
    }
  Qed.

  Lemma promise_strong_relaxed
        l tview_src
        promises1_src mem1_src
        promises1_tgt mem1_tgt loc from to msg_tgt promises2_tgt mem2_tgt kind_tgt
        (PROMISES1: sim_memory l promises1_src promises1_tgt)
        (MEM1: sim_memory l mem1_src mem1_tgt)
        (FULFILL1: fulfillable l tview_src mem1_src promises1_src)
        (TVIEW_SRC: TView.wf tview_src)
        (LE1_SRC: Memory.le promises1_src mem1_src)
        (LE1_TGT: Memory.le promises1_tgt mem1_tgt)
        (MEM1_SRC: Memory.closed mem1_src)
        (PROMISE_TGT: Memory.promise promises1_tgt mem1_tgt loc from to msg_tgt promises2_tgt mem2_tgt kind_tgt)
        (KIND_TGT: negb (Memory.op_kind_is_lower kind_tgt) /\ negb (Memory.op_kind_is_cancel kind_tgt))
        (SPLIT_TGT: Memory.op_kind_is_split kind_tgt ->
                         (exists ts3 val, kind_tgt = Memory.op_kind_split ts3 (Message.full val None)) \/
                         (exists ts3, kind_tgt = Memory.op_kind_split ts3 Message.reserve))
        (LOC: loc <> l):
    exists promises2_src mem2_src kind_src,
      <<PROMISE_SRC: Memory.promise promises1_src mem1_src loc from to
                                    (get_message_src true l loc msg_tgt tview_src from mem1_src)
                                    promises2_src mem2_src kind_src>> /\
      <<PROMISES2: sim_memory l promises2_src promises2_tgt>> /\
      <<MEM2: sim_memory l mem2_src mem2_tgt>> /\
      <<FULFILL2: fulfillable l tview_src mem2_src promises2_src>>.
  Proof.
    des. inv PROMISES1. inv MEM1. inv PROMISE_TGT; ss.
    { (* add *)
      exploit (@Memory.add_exists mem1_src loc from to
                                  (get_message_src true l loc msg_tgt tview_src from mem1_src)).
      { ii. exploit SOUND0; eauto. i. des.
        exploit Memory.add_get1; try exact GET_TGT; eauto. i.
        exploit Memory.add_get0; try exact MEM. i. des.
        exploit Memory.get_disjoint; [exact x1|exact GET0|..]. i. des.
        { subst. congr. }
        apply (x2 x); eauto. }
      { inv MEM. inv ADD. ss. }
      { eapply get_message_src_wf; eauto.
        inv MEM. inv ADD. ss. }
      i. des.
      exploit Memory.add_exists_le; try exact x0; eauto. i. des.
      esplits.
      - econs; eauto.
        + eapply get_message_src_message_to; eauto.
        + i. exploit get_message_src_reserve; eauto. i. subst.
          exploit RESERVE; eauto. i. des.
          exploit COMPLETE0; try exact x; eauto. i. des.
          inv MSG. eauto.
        + i. exploit SOUND0; try exact GET; eauto. i. des.
          destruct msg_tgt; ss. eauto.
      - econs; i.
        + revert GET_SRC. erewrite Memory.add_o; eauto. condtac; ss; i.
          * des. subst. inv GET_SRC.
            exploit Memory.add_get0; try exact PROMISES. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o.
            exploit SOUND; eauto. i. des.
            exploit Memory.add_get1; try exact GET_TGT; eauto.
        + revert GET_TGT. erewrite Memory.add_o; eauto. condtac; ss; i.
          * des. subst. inv GET_TGT.
            exploit Memory.add_get0; try exact x1. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o.
            exploit COMPLETE; eauto. i. des.
            exploit Memory.add_get1; try exact GET_SRC; eauto.
      - econs; i.
        + revert GET_SRC. erewrite Memory.add_o; eauto. condtac; ss; i.
          * des. subst. inv GET_SRC.
            exploit Memory.add_get0; try exact MEM. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o.
            exploit SOUND0; eauto. i. des.
            exploit Memory.add_get1; try exact GET_TGT; eauto.
        + revert GET_TGT. erewrite Memory.add_o; eauto. condtac; ss; i.
          * des. subst. inv GET_TGT.
            exploit Memory.add_get0; try exact x0. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o.
            exploit COMPLETE0; eauto. i. des.
            exploit Memory.add_get1; try exact GET_SRC; eauto.
      - ii. revert GETP. erewrite Memory.add_o; eauto. condtac; ss; i.
        + des. subst. inv GETP.
          exploit get_message_src_fulfillable; eauto. i. des.
          split; auto.
          unfold prev_released_le_loc.
          erewrite Memory.add_o; eauto. condtac; ss.
          des. subst. inv x0. inv ADD. timetac.
        + guardH o.
          exploit FULFILL1; eauto. i. des. split; auto.
          unfold prev_released_le_loc.
          erewrite Memory.add_o; eauto. condtac; ss. des. subst.
          destruct (get_message_src true l loc msg_tgt tview_src from mem1_src) eqn:GET; ss.
          exploit get_message_src_full; eauto. i. des. subst.
          exploit LE1_SRC; try exact GETP. i.
          exploit SOUND0; try exact x; eauto. i. des. inv MSG.
          exploit ATTACH; eauto; ss.
    }

    { (* split *)
      guardH RESERVE.
      exploit Memory.split_get0; try exact PROMISES. i. des.
      clear GET GET1 GET2.
      exploit COMPLETE; eauto. i. des.
      exploit (@Memory.split_exists promises1_src loc from to ts3
                                    (get_message_src true l loc msg_tgt tview_src from mem1_src) msg_src); eauto.
      { inv MEM. inv SPLIT. ss. }
      { inv MEM. inv SPLIT. ss. }
      { eapply get_message_src_wf; eauto.
        inv MEM. inv SPLIT. ss. }
      i. des.
      exploit Memory.split_exists_le; try exact x0; eauto. i. des.
      esplits.
      - econs 2; eauto.
        + eapply get_message_src_message_to; eauto.
        + unguard. des. subst.
          unfold get_message_src.
          destruct released'; eauto.
          destruct (Memory.get loc from mem1_src) as [[? [? []|]]|]; eauto.
      - econs; i.
        + revert GET_SRC0. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          * des. subst. inv GET_SRC0.
            exploit Memory.split_get0; try exact PROMISES. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o. des. subst. inv GET_SRC0.
            exploit Memory.split_get0; try exact PROMISES. i. des.
            esplits; eauto.
          * guardH o. guardH o0.
            exploit SOUND; eauto. i. des.
            erewrite Memory.split_o; eauto. repeat condtac; ss.
            esplits; eauto.
        + revert GET_TGT. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          * des. subst. inv GET_TGT.
            exploit Memory.split_get0; try exact x0. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o. des. subst. inv GET_TGT.
            exploit Memory.split_get0; try exact x0. i. des.
            esplits; eauto.
          * guardH o. guardH o0.
            exploit COMPLETE; eauto. i. des.
            erewrite Memory.split_o; eauto. repeat condtac; ss.
            esplits; eauto.
      - econs; i.
        + revert GET_SRC0. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          * des. subst. inv GET_SRC0.
            exploit Memory.split_get0; try exact MEM. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o. des. subst. inv GET_SRC0.
            exploit Memory.split_get0; try exact MEM. i. des.
            esplits; eauto.
          * guardH o. guardH o0.
            exploit SOUND0; eauto. i. des.
            erewrite Memory.split_o; eauto. repeat condtac; ss.
            esplits; eauto.
        + revert GET_TGT. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          * des. subst. inv GET_TGT.
            exploit Memory.split_get0; try exact x1. i. des.
            esplits; eauto.
            eapply get_message_src_sim_message; eauto.
          * guardH o. des. subst. inv GET_TGT.
            exploit Memory.split_get0; try exact x1. i. des.
            esplits; eauto.
          * guardH o. guardH o0.
            exploit COMPLETE0; eauto. i. des.
            erewrite Memory.split_o; eauto. repeat condtac; ss.
            esplits; eauto.
      - ii. revert GETP. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
        + des. subst. inv GETP.
          exploit get_message_src_fulfillable; eauto. i. des.
          split; auto.
          unfold prev_released_le_loc.
          erewrite Memory.split_o; eauto. repeat condtac; ss.
          * des. subst. inv x0. inv SPLIT. timetac.
          * guardH o. des. subst.
            inv x0. inv SPLIT. rewrite TS12 in TS23. timetac.
        + guardH o. des. subst. inv GETP.
          exploit LE1_SRC; eauto. i.
          exploit SOUND0; eauto. i. des. inv MSG0. inv RELEASED.
          exploit SPLIT_TGT; eauto. i. des.
          * inv x2. exploit LE1_TGT; eauto. i. congr.
          * inv x2. exploit LE1_TGT; eauto. i. congr.
        + guardH o. guardH o0.
          exploit FULFILL1; eauto. i. des. split; auto.
          unfold prev_released_le_loc.
          erewrite Memory.split_o; eauto. repeat condtac; ss.
          * des. subst. exfalso.
            exploit Memory.split_get0; try exact x0. i. des.
            exploit Memory.get_ts; try exact GETP. i. des.
            { subst. inv x0. inv SPLIT. inv TS12. }
            exploit Memory.get_ts; try exact GET1. i. des.
            { subst. inv x0. inv SPLIT. inv TS23. }
            exploit Memory.get_disjoint; [exact GETP|exact GET1|..]. i. des.
            { subst. inv x0. inv SPLIT. timetac. }
            destruct (TimeFacts.le_lt_dec to0 ts3).
            { apply (x4 to0); econs; ss; try refl.
              inv x0. inv SPLIT. etrans; eauto. }
            { apply (x4 ts3); econs; ss; try refl.
              - inv x0. inv SPLIT. ss.
              - econs. ss. }
          * guardH o1. des. subst.
            exploit Memory.split_get0; try exact x1. i. des.
            unfold prev_released_le_loc in PREV.
            rewrite GET1 in *. ss.
    }
  Qed.

  Lemma promise_loc
        l
        promises1_src mem1_src
        promises1_tgt mem1_tgt from to msg_tgt promises2_tgt mem2_tgt kind_tgt
        (PROMISES1: sim_memory l promises1_src promises1_tgt)
        (MEM1: sim_memory l mem1_src mem1_tgt)
        (PROMISE_TGT: Memory.promise promises1_tgt mem1_tgt l from to msg_tgt promises2_tgt mem2_tgt kind_tgt):
    <<PROMISES2: sim_memory l promises1_src promises2_tgt>> /\
    <<MEM2: sim_memory l mem1_src mem2_tgt>>.
  Proof.
    inv PROMISES1. inv MEM1. inv PROMISE_TGT.
    { (* add *)
      splits.
      - econs; i.
        + erewrite Memory.add_o; eauto.
          condtac; [des|]; ss; i; eauto.
        + revert GET_TGT. erewrite Memory.add_o; eauto.
          condtac; [des|]; ss; i; eauto.
      - econs; i.
        + erewrite Memory.add_o; eauto.
          condtac; [des|]; ss; i; eauto.
        + revert GET_TGT. erewrite Memory.add_o; eauto.
          condtac; [des|]; ss; i; eauto.
    }
    { (* split *)
      splits.
      - econs; i.
        + erewrite Memory.split_o; eauto.
          repeat condtac; [des|des|]; ss; i; eauto.
        + revert GET_TGT. erewrite Memory.split_o; eauto.
          repeat condtac; [des|des|]; ss; i; eauto.
      - econs; i.
        + erewrite Memory.split_o; eauto.
          repeat condtac; [des|des|]; ss; i; eauto.
        + revert GET_TGT. erewrite Memory.split_o; eauto.
          repeat condtac; [des|des|]; ss; i; eauto.
    }
    { (* lower *)
      splits.
      - econs; i.
        + erewrite Memory.lower_o; eauto.
          condtac; [des|]; ss; i; eauto.
        + revert GET_TGT. erewrite Memory.lower_o; eauto.
          condtac; [des|]; ss; i; eauto.
      - econs; i.
        + erewrite Memory.lower_o; eauto.
          condtac; [des|]; ss; i; eauto.
        + revert GET_TGT. erewrite Memory.lower_o; eauto.
          condtac; [des|]; ss; i; eauto.
    }
    { (* cancel *)
      splits.
      - econs; i.
        + erewrite Memory.remove_o; eauto.
          condtac; [des|]; ss; i; eauto.
        + revert GET_TGT. erewrite Memory.remove_o; eauto.
          condtac; [des|]; ss; i; eauto.
      - econs; i.
        + erewrite Memory.remove_o; eauto.
          condtac; [des|]; ss; i; eauto.
        + revert GET_TGT. erewrite Memory.remove_o; eauto.
          condtac; [des|]; ss; i; eauto.
    }
  Qed.

  Lemma promise_eq_promises
        l
        promises1 mem1 loc from to msg promises2 mem2 kind
        (PROMISE: Memory.promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (LOC: loc <> l):
    forall to, Memory.get l to promises1 = Memory.get l to promises2.
  Proof.
    i. inv PROMISE.
    - erewrite (@Memory.add_o promises2); eauto. condtac; ss. des. subst. ss.
    - erewrite (@Memory.split_o promises2); eauto. repeat condtac; ss.
      { des. subst. ss. }
      { des; subst; ss. }
    - erewrite (@Memory.lower_o promises2); eauto. condtac; ss. des. subst. ss.
    - erewrite (@Memory.remove_o promises2); eauto. condtac; ss. des. subst. ss.
  Qed.

  Lemma promise_eq_mem
        l
        promises1 mem1 loc from to msg promises2 mem2 kind
        (PROMISE: Memory.promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (LOC: loc <> l):
    forall to, Memory.get l to mem1 = Memory.get l to mem2.
  Proof.
    i. inv PROMISE.
    - erewrite (@Memory.add_o mem2); eauto. condtac; ss. des. subst. ss.
    - erewrite (@Memory.split_o mem2); eauto. repeat condtac; ss.
      { des. subst. ss. }
      { des; subst; ss. }
    - erewrite (@Memory.lower_o mem2); eauto. condtac; ss. des. subst. ss.
    - erewrite (@Memory.remove_o mem2); eauto. condtac; ss. des. subst. ss.
  Qed.


  (* local steps *)

  Lemma promise_step
        l
        lc1_src mem1_src
        lc1_tgt mem1_tgt loc from to msg_tgt lc2_tgt mem2_tgt kind_tgt
        (LC1: sim_local l lc1_src lc1_tgt)
        (MEM1: sim_memory l mem1_src mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (FULFILLABLE1: fulfillable l (Local.tview lc1_src) mem1_src (Local.promises lc1_src))
        (LOC: loc <> l)
        (STEP_TGT: Local.promise_step lc1_tgt mem1_tgt loc from to msg_tgt lc2_tgt mem2_tgt kind_tgt):
    exists msg_src lc2_src mem2_src kind_src,
      <<STEP_SRC: Local.promise_step lc1_src mem1_src loc from to msg_src lc2_src mem2_src kind_src>> /\
      <<LC2: sim_local l lc2_src lc2_tgt>> /\
      <<MEM2: sim_memory l mem2_src mem2_tgt>> /\
      <<FULFILLABLE2: fulfillable l (Local.tview lc2_src) mem2_src (Local.promises lc2_src)>>.
  Proof.
    inv STEP_TGT.
    exploit promise; try exact PROMISE; try apply LC1;
      try apply WF1_SRC; try apply WF1_TGT; eauto.
    i. des.
    esplits.
    - econs; eauto.
      eapply get_message_src_closed; eauto; try apply WF1_SRC. i.
      exploit Memory.promise_op; try exact PROMISE_SRC. i.
      eapply Memory.op_closed_view; eauto.
    - inv LC1. econs; eauto.
    - ss.
    - ss.
  Qed.

  Lemma promise_step_release
        l
        lc1_src mem1_src
        lc1_tgt mem1_tgt loc from to val released_tgt lc2_tgt mem2_tgt kind_tgt
        (LC1: sim_local l lc1_src lc1_tgt)
        (MEM1: sim_memory l mem1_src mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (FULFILLABLE1: fulfillable l (Local.tview lc1_src) mem1_src (Local.promises lc1_src))
        (LOC: loc <> l)
        (STEP_TGT: Local.promise_step lc1_tgt mem1_tgt loc from to
                                      (Message.full val (Some (released_tgt))) lc2_tgt mem2_tgt kind_tgt)
        (KIND_TGT: negb (Memory.op_kind_is_lower kind_tgt) /\ negb (Memory.op_kind_is_cancel kind_tgt))
        (SPLIT_TGT: Memory.op_kind_is_split kind_tgt ->
                         (exists ts3 val, kind_tgt = Memory.op_kind_split ts3 (Message.full val None)) \/
                         (exists ts3, kind_tgt = Memory.op_kind_split ts3 Message.reserve)):
    exists released_src lc2_src mem2_src kind_src,
      <<STEP_SRC: Local.promise_step lc1_src mem1_src loc from to
                                     (Message.full val (Some (released_src))) lc2_src mem2_src kind_src>> /\
      <<LC2: sim_local l lc2_src lc2_tgt>> /\
      <<MEM2: sim_memory l mem2_src mem2_tgt>> /\
      <<FULFILLABLE2: fulfillable l (Local.tview lc2_src) mem2_src (Local.promises lc2_src)>> /\
      <<STRONG: view_le_loc l (TView.cur (Local.tview lc1_src)) released_src>>.
  Proof.
    inv STEP_TGT.
    exploit promise_strong_relaxed; try exact PROMISE; try apply LC1;
      try apply WF1_SRC; try apply WF1_TGT; eauto.
    i. des.
    exploit (@get_message_src_closed true l loc (Message.full val (Some released_tgt))
                                     (Local.tview lc1_src) from mem1_src mem2_src mem2_tgt); eauto.
    { apply WF1_SRC. }
    { exploit Memory.promise_op; try exact PROMISE_SRC. i.
      eapply Memory.op_closed_view; eauto. }
    i. ss.
    destruct (Memory.get loc from mem1_src) as [[? [? []|]]|]; ss.
    - esplits.
      + econs; eauto.
      + inv LC1. econs; eauto.
      + ss.
      + ss.
      + econs; ss.
        * unfold LocFun.add. condtac; ss. unnw.
          etrans; [|eapply Time.join_l]. refl.
        * unfold LocFun.add. condtac; ss. unnw.
          etrans; [|eapply Time.join_l]. refl.
    - esplits.
      + econs; eauto.
      + inv LC1. econs; eauto.
      + ss.
      + ss.
      + econs; ss.
        * unfold LocFun.add. condtac; ss. unnw.
          etrans; [|eapply Time.join_l]. refl.
        * unfold LocFun.add. condtac; ss. unnw.
          etrans; [|eapply Time.join_l]. refl.
    - esplits.
      + econs; eauto.
      + inv LC1. econs; eauto.
      + ss.
      + ss.
      + econs; ss.
        * unfold LocFun.add. condtac; ss. unnw.
          etrans; [|eapply Time.join_l]. refl.
        * unfold LocFun.add. condtac; ss. unnw.
          etrans; [|eapply Time.join_l]. refl.
    - esplits.
      + econs; eauto.
      + inv LC1. econs; eauto.
      + ss.
      + ss.
      + econs; ss.
        * unfold LocFun.add. condtac; ss. unnw.
          etrans; [|eapply Time.join_l]. refl.
        * unfold LocFun.add. condtac; ss. unnw.
          etrans; [|eapply Time.join_l]. refl.
  Qed.

  Lemma read_step
        l
        lc1_src mem1_src
        lc1_tgt mem1_tgt loc to val released_tgt ord lc2_tgt
        (LC1: sim_local l lc1_src lc1_tgt)
        (MEM1: sim_memory l mem1_src mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (FULFILLABLE1: fulfillable l (Local.tview lc1_src) mem1_src (Local.promises lc1_src))
        (LOC: loc <> l)
        (STEP_TGT: Local.read_step lc1_tgt mem1_tgt loc to val released_tgt ord lc2_tgt):
    exists released_src lc2_src,
      <<STEP_SRC: Local.read_step lc1_src mem1_src loc to val released_src ord lc2_src>> /\
      <<LC2: sim_local l lc2_src lc2_tgt>> /\
      <<FULFILLABLE2: fulfillable l (Local.tview lc2_src) mem1_src (Local.promises lc2_src)>>.
  Proof.
    inv STEP_TGT.
    inv MEM1. exploit COMPLETE; eauto. i. des. inv MSG.
    esplits.
    - econs; eauto.
      eapply sim_readable; eauto. apply LC1.
    - econs; s; try apply LC1.
      eapply sim_read_tview; eauto. apply LC1.
    - ss.
  Qed.

  Lemma fulfill_step_relaxed
        l
        lc1_src sc1_src mem1_src releasedm_src
        lc1_tgt sc1_tgt mem1_tgt loc from to val releasedm_tgt released_tgt ord lc2_tgt sc2_tgt
        (LC1: sim_local l lc1_src lc1_tgt)
        (MEM1: sim_memory l mem1_src mem1_tgt)
        (REL: sim_opt_view l releasedm_src releasedm_tgt)
        (REL_WF: View.opt_wf releasedm_src)
        (REL_GET: __guard__ (
                      Time.le ((View.rlx (View.unwrap releasedm_src)) loc) to /\
                      (releasedm_src = None \/
                       exists from' val',
                         Memory.get loc from mem1_src = Some (from', Message.full val' releasedm_src))))
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (FULFILLABLE1: fulfillable l (Local.tview lc1_src) mem1_src (Local.promises lc1_src))
        (LOC: loc <> l)
        (ORD: Ordering.le ord Ordering.strong_relaxed)
        (RELEASED_TGT: __guard__ (
                           released_tgt =
                           TView.write_released (Local.tview lc1_tgt) sc1_tgt loc to releasedm_tgt ord))
        (STEP_TGT: fulfill_step lc1_tgt sc1_tgt loc from to val releasedm_tgt released_tgt ord lc2_tgt sc2_tgt):
    exists released_src promises2_src mem2_src,
      <<WRITE_SRC: Memory.write (Local.promises lc1_src) mem1_src loc from to
                                val (TView.write_released (Local.tview lc1_src) sc1_src loc to releasedm_src ord)
                                promises2_src mem2_src
                                (Memory.op_kind_lower (Message.full val released_src))>> /\
      <<PROMISES2: sim_memory l promises2_src (Local.promises lc2_tgt)>> /\
      <<MEM2: sim_memory l mem2_src mem1_tgt>>.
  Proof.
    inv STEP_TGT.
    exploit Memory.remove_get0; eauto. i. des.
    destruct lc1_src as [tview1_src promises1_src]. ss.
    dup LC1. inv LC0. inv PROMISES1. ss.
    exploit COMPLETE; eauto. i. des. inv MSG.
    clear TVIEW SOUND COMPLETE.
    exploit (@Memory.lower_exists promises1_src loc from to
                                  (Message.full val released_src)
                                  (Message.full val (TView.write_released tview1_src sc1_src loc to releasedm_src ord))); ss.
    { econs.
      eapply TViewFacts.write_future0; try eapply WF1_SRC; eauto. }
    { econs. destruct released_src; ss.
      - revert REL_LE. unfold TView.write_released.
        condtac; ss. repeat condtac; ss; i.
        { destruct ord; ss. }
        inv REL_LE. econs.
        exploit View.join_l. i. erewrite LE in x0.
        exploit View.join_r. i. erewrite LE in x1.
        clear LE. eapply View.join_spec.
        + unguard. des; subst; eauto using View.bot_spec.
          inv REL; eauto using View.bot_spec. inv SIM.
          inv RELEASED. inv SIM. inv x0. ss.
          exploit FULFILLABLE1; eauto. i. des.
          unfold prev_released_le_loc in *.
          rewrite REL_GET0 in PREV. inv PREV.
          econs; ii.
          * destruct (Loc.eq_dec loc0 l); subst; ss.
            exploit PLN; eauto. i.
            exploit PLN0; eauto. i.
            rewrite x. rewrite x0. ss.
          * destruct (Loc.eq_dec loc0 l); subst; ss.
            exploit RLX; eauto. i.
            exploit RLX0; eauto. i.
            rewrite x. rewrite x0. ss.
        + revert x1. unfold LocFun.add. condtac; ss. i.
          inv RELEASED. inv SIM. inv LC1. inv TVIEW. destruct (REL0 loc). ss.
          exploit View.join_l. i. erewrite x1 in x2.
          exploit View.join_r. i. erewrite x1 in x3.
          inv x2. inv x3. ss.
          exploit FULFILLABLE1; eauto. i. des. inv TVIEW.
          eapply View.join_spec.
          { econs; ii.
            - destruct (Loc.eq_dec loc0 l); subst; ss.
              exploit PLN; eauto. i.
              exploit PLN0; eauto. i.
              rewrite x. rewrite x2. ss.
            - destruct (Loc.eq_dec loc0 l); subst; ss.
              exploit RLX; eauto. i.
              exploit RLX0; eauto. i.
              rewrite x. rewrite x2. ss. }
          { econs; ss; ii.
            - specialize (PLN2 loc0). revert PLN2.
              unfold TimeMap.singleton, LocFun.add. condtac; ss; i.
              + subst. exploit PLN; eauto. i. rewrite x. ss.
              + unfold LocFun.find, LocFun.init. apply Time.bot_spec.
            - specialize (RLX2 loc0). revert RLX2.
              unfold TimeMap.singleton, LocFun.add. condtac; ss; i.
              + subst. exploit RLX; eauto. i. rewrite x. ss.
              + unfold LocFun.find, LocFun.init. apply Time.bot_spec. }
      - inv RELEASED. inv REL_LE.
        revert H0. unfold TView.write_released. condtac; ss. }
    i. des.
    exploit Memory.lower_get0; try exact x0. i. des.
    exploit Memory.remove_exists; try exact GET2. i. des.
    exploit Memory.lower_exists_le; try eapply WF1_SRC; eauto. i. des.
    esplits.
    - econs; eauto; ss. econs 3; eauto.
      econs. unfold TView.write_released.
      repeat (condtac; ss); try by (destruct ord; ss).
      + unfold TimeMap.join.
        unfold LocFun.add. condtac; ss.
        unfold TimeMap.join.
        unfold TimeMap.singleton, LocFun.add. condtac; ss.
        eapply Time.join_spec.
        * unguard. des; ss.
        * eapply Time.join_spec; try refl.
          inv LC1. inv TVIEW.
          exploit REL0; eauto. i. inv x. ss.
          exploit RLX; eauto. i. rewrite x.
          inv WRITABLE. etrans; [|econs; eauto].
          inv WF1_TGT. inv TVIEW_WF. destruct (REL_CUR loc). ss.
      + unfold TimeMap.bot. apply Time.bot_spec.
    - exploit MemoryReorder.lower_remove_same; try exact x0; eauto. i. des.
      eapply sim_memory_remove; try apply LC1; eauto.
    - unguardH RELEASED_TGT. subst.
      exploit Memory.remove_get0; try exact REMOVE. i. des.
      dup WF1_TGT. inv WF1_TGT0. exploit PROMISES; try exact GET3. i.
      clear GET4 TVIEW_WF TVIEW_CLOSED PROMISES FINITE BOT RESERVE.
      inv MEM1. econs; i.
      + revert GET_SRC0.
        erewrite Memory.lower_o; eauto. condtac; ss; eauto.
        i. des. subst. inv GET_SRC0.
        esplits; eauto. econs.
        eapply sim_write_released; eauto. apply LC1.
      + erewrite Memory.lower_o; eauto. condtac; ss; eauto.
        des. subst. rewrite GET_TGT in *. inv x.
        esplits; eauto. econs.
        eapply sim_write_released; eauto. apply LC1.
  Qed.

  Lemma fulfill_step_release
        l
        lc1_src sc1_src mem1_src releasedm_src val released_src
        lc1_tgt sc1_tgt mem1_tgt loc from to releasedm_tgt released_tgt ord lc2_tgt sc2_tgt
        (LC1: sim_local l lc1_src lc1_tgt)
        (MEM1: sim_memory l mem1_src mem1_tgt)
        (REL: sim_opt_view l releasedm_src releasedm_tgt)
        (REL_WF: View.opt_wf releasedm_src)
        (REL_GET: __guard__ (
                      Time.le ((View.rlx (View.unwrap releasedm_src)) loc) to /\
                      (releasedm_src = None \/
                       exists from' val',
                         Memory.get loc from mem1_src = Some (from', Message.full val' releasedm_src))))
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (FULFILLABLE1: fulfillable l (Local.tview lc1_src) mem1_src (Local.promises lc1_src))
        (GET_SRC: Memory.get loc to (Local.promises lc1_src) = Some (from, Message.full val (Some released_src)))
        (STRONG: view_le_loc l (TView.cur (Local.tview lc1_src)) released_src)
        (LOC: loc <> l)
        (ORD: Ordering.le Ordering.acqrel ord)
        (RELEASED_TGT: __guard__ (
                           released_tgt =
                           TView.write_released (Local.tview lc1_tgt) sc1_tgt loc to releasedm_tgt ord))
        (STEP_TGT: fulfill_step lc1_tgt sc1_tgt loc from to val releasedm_tgt released_tgt ord lc2_tgt sc2_tgt):
    exists released_src promises2_src mem2_src,
      <<WRITE_SRC: Memory.write (Local.promises lc1_src) mem1_src loc from to
                                val (TView.write_released (Local.tview lc1_src) sc1_src loc to releasedm_src ord)
                                promises2_src mem2_src
                                (Memory.op_kind_lower (Message.full val (Some released_src)))>> /\
      <<PROMISES2: sim_memory l promises2_src (Local.promises lc2_tgt)>> /\
      <<MEM2: sim_memory l mem2_src mem1_tgt>>.
  Proof.
    inv STEP_TGT.
    exploit Memory.remove_get0; eauto. i. des.
    destruct lc1_src as [tview1_src promises1_src]. ss.
    dup LC1. inv LC0. inv PROMISES1. ss.
    exploit COMPLETE; eauto. i. des.
    rewrite GET_SRC in *. inv GET_SRC0. inv MSG. inv RELEASED.
    clear TVIEW SOUND COMPLETE.
    exploit (@Memory.lower_exists promises1_src loc from to
                                  (Message.full val (Some released_src))
                                  (Message.full val (TView.write_released tview1_src sc1_src loc to releasedm_src ord))); ss.
    { econs.
      eapply TViewFacts.write_future0; try eapply WF1_SRC; eauto. }
    { econs.
      revert REL_LE. unfold TView.write_released.
      condtac; try by (destruct ord; ss). ss.
      repeat condtac; ss. i.
      inv REL_LE. econs.
      exploit View.join_l. i. erewrite LE in x0.
      exploit View.join_r. i. erewrite LE in x1.
      clear LE. eapply View.join_spec.
      - unguard. des; subst; eauto using View.bot_spec.
        inv REL; eauto using View.bot_spec. inv SIM.
        inv SIM0. inv x0. ss.
        exploit FULFILLABLE1; eauto. i. des.
        unfold prev_released_le_loc in *.
        rewrite REL_GET0 in PREV. inv PREV.
        econs; ii.
        + destruct (Loc.eq_dec loc0 l); subst; ss.
          exploit PLN; eauto. i.
          exploit PLN0; eauto. i.
          rewrite x. rewrite x0. ss.
        + destruct (Loc.eq_dec loc0 l); subst; ss.
          exploit RLX; eauto. i.
          exploit RLX0; eauto. i.
          rewrite x. rewrite x0. ss.
      - revert x1. unfold LocFun.add. condtac; ss. i.
        inv SIM. inv LC1. inv TVIEW. inv CUR. inv STRONG. ss.
        exploit View.join_l. i. erewrite x1 in x2.
        exploit View.join_r. i. erewrite x1 in x3.
        inv x2. inv x3. ss.
        exploit FULFILLABLE1; eauto. i. des. inv TVIEW.
        eapply View.join_spec.
        + econs; ii.
          * destruct (Loc.eq_dec loc0 l); subst; ss.
            exploit PLN; eauto. i.
            exploit PLN0; eauto. i.
            rewrite x. rewrite x2. ss.
          * destruct (Loc.eq_dec loc0 l); subst; ss.
            exploit RLX; eauto. i.
            exploit RLX0; eauto. i.
            rewrite x. rewrite x2. ss.
        + econs; ss; ii.
          * specialize (PLN2 loc0). revert PLN2.
            unfold TimeMap.singleton, LocFun.add. condtac; ss; i.
            { subst. exploit PLN; eauto. i. rewrite x. ss. }
            { unfold LocFun.find, LocFun.init. apply Time.bot_spec. }
          * specialize (RLX2 loc0). revert RLX2.
            unfold TimeMap.singleton, LocFun.add. condtac; ss; i.
            { subst. exploit RLX; eauto. i. rewrite x. ss. }
            { unfold LocFun.find, LocFun.init. apply Time.bot_spec. }
    }
    i. des.
    exploit Memory.lower_get0; try exact x0. i. des.
    exploit Memory.remove_exists; try exact GET2. i. des.
    exploit Memory.lower_exists_le; try eapply WF1_SRC; eauto. i. des.
    esplits.
    - econs; eauto; ss. econs 3; eauto.
      econs. unfold TView.write_released.
      repeat (condtac; ss; try by (destruct ord; ss)).
      unfold TimeMap.join.
      unfold LocFun.add. condtac; ss.
      unfold TimeMap.join.
      unfold TimeMap.singleton, LocFun.add. condtac; ss.
      eapply Time.join_spec.
      + unguard. des; ss.
      + eapply Time.join_spec; try refl.
        inv LC1. inv TVIEW. inv CUR. ss.
        exploit RLX; eauto. i. rewrite x.
        inv WRITABLE. etrans; [|econs; eauto]. refl.
    - exploit MemoryReorder.lower_remove_same; try exact x0; eauto. i. des.
      eapply sim_memory_remove; try apply LC1; eauto.
    - unguardH RELEASED_TGT.
      exploit Memory.remove_get0; try exact REMOVE. i. des.
      dup WF1_TGT. inv WF1_TGT0. exploit PROMISES; try exact GET3. i.
      clear GET4 TVIEW_WF TVIEW_CLOSED PROMISES FINITE BOT RESERVE.
      inv MEM1. econs; i.
      + revert GET_SRC0.
        erewrite Memory.lower_o; eauto. condtac; ss; eauto.
        i. des. subst. inv GET_SRC0.
        esplits; eauto. econs. rewrite RELEASED_TGT.
        eapply sim_write_released; eauto. apply LC1.
      + erewrite Memory.lower_o; eauto. condtac; ss; eauto.
        des. subst. rewrite GET_TGT in *. inv x.
        esplits; eauto. econs. rewrite RELEASED_TGT.
        eapply sim_write_released; eauto. apply LC1.
  Qed.

  Lemma write_step
        l
        lc1_src sc1_src mem1_src releasedm_src
        lc1_tgt sc1_tgt mem1_tgt loc from to val releasedm_tgt released_tgt
                                    ord lc2_tgt sc2_tgt mem2_tgt kind_tgt
        (LC1: sim_local l lc1_src lc1_tgt)
        (SC1: sim_timemap l sc1_src sc1_tgt)
        (MEM1: sim_memory l mem1_src mem1_tgt)
        (RELEASED: sim_opt_view l releasedm_src releasedm_tgt)
        (REL_WF_SRC: View.opt_wf releasedm_src)
        (REL_CLOSED_SRC: Memory.closed_opt_view releasedm_src mem1_src)
        (REL_WF_TGT: View.opt_wf releasedm_tgt)
        (REL_CLOSED_TGT: Memory.closed_opt_view releasedm_tgt mem1_tgt)
        (REL_GET: __guard__ (
                      Time.le ((View.rlx (View.unwrap releasedm_src)) loc) to /\
                      (releasedm_src = None \/
                       exists from' val',
                         Memory.get loc from mem1_src = Some (from', Message.full val' releasedm_src))))
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
        (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (FULFILLABLE1: fulfillable l (Local.tview lc1_src) mem1_src (Local.promises lc1_src))
        (LOC: loc <> l)
        (STEP_TGT: Local.write_step lc1_tgt sc1_tgt mem1_tgt loc from to val releasedm_tgt released_tgt
                                    ord lc2_tgt sc2_tgt mem2_tgt kind_tgt):
    exists released_src lc2_src sc2_src mem2_src kind_src,
      <<STEP_SRC: Local.write_step lc1_src sc1_src mem1_src loc from to val releasedm_src released_src
                                    ord lc2_src sc2_src mem2_src kind_src>> /\
      <<LC2: sim_local l lc2_src lc2_tgt>> /\
      <<SC2: sim_timemap l sc2_src sc2_tgt>> /\
      <<MEM2: sim_memory l mem2_src mem2_tgt>> /\
      <<FULFILLABLE2: fulfillable l (Local.tview lc2_src) mem2_src (Local.promises lc2_src)>>.
  Proof.
    destruct (Ordering.le ord Ordering.strong_relaxed) eqn:ORD.
    { (* relaxed *)
      exploit write_promise_fulfill; eauto. i. des.
      exploit promise_step; try exact STEP1; eauto. i. des.
      exploit Local.promise_step_future; try exact STEP_SRC; eauto. i. des.
      exploit Local.promise_step_future; try exact STEP1; eauto. i. des.
      exploit fulfill_step_relaxed; try exact STEP2; eauto.
      { unguard. des; eauto. split; auto. right.
        inv STEP_SRC. inv PROMISE.
        - erewrite Memory.add_o; eauto. condtac; ss; eauto.
          des. subst. inv MEM. inv ADD. timetac.
        - erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
          + des. subst. inv MEM. inv SPLIT. timetac.
          + guardH o. des. subst.
            inv MEM. inv SPLIT. rewrite TS12 in TS23. timetac.
        - erewrite Memory.lower_o; eauto. condtac; ss; eauto.
          des. subst. inv MEM. inv LOWER. timetac.
        - erewrite Memory.remove_o; eauto. condtac; ss; eauto.
          des. subst. exploit Memory.remove_get0; try exact MEM. i. des. congr. }
      { inv STEP1. ss. }
      i. des.
      inv STEP_SRC; ss.
      replace msg_src with (Message.full val released_src) in *; cycle 1.
      { inv WRITE_SRC. inv PROMISE0.
        exploit Memory.lower_get0; try exact MEM. i. des.
        exploit Memory.promise_get2; try exact PROMISE.
        { destruct kind_src; ss. inv PROMISE.
          exploit Memory.remove_get0; try exact MEM3. i. des. congr. }
        i. des.
        rewrite GET in *. inv GET_MEM. ss. }
      exploit MemoryMerge.promise_write_write; try exact PROMISE; eauto. i.
      esplits.
      - econs; eauto.
        + inv STEP_TGT. eapply sim_writable; eauto. apply LC1.
        + inv STEP_TGT. ii. destruct msg; ss.
          inv LC1. inv PROMISES1.
          exploit SOUND; try exact GET; eauto. i. des. inv MSG.
          exploit RELEASE; eauto. s. i. subst.
          inv RELEASED1. ss.
      - inv STEP_TGT. econs; ss.
        eapply sim_write_tview; eauto. apply LC1.
      - by inv STEP_TGT.
      - ss.
      - s. ii. inv WRITE_SRC. inv PROMISE0. revert GETP.
        erewrite Memory.remove_o; eauto. condtac; ss.
        erewrite Memory.lower_o; eauto. condtac; ss. i.
        guardH o. guardH o0.
        exploit FULFILLABLE2; eauto. i. des. split.
        + unfold TView.write_tview. condtac; try by destruct ord; ss.
          inv TVIEW. econs; ss.
          * unfold LocFun.add. condtac; ss.
            subst. unfold TimeMap.join, TimeMap.singleton, LocFun.add. condtac; subst; ss.
            unfold LocFun.find, LocFun.init.
            eapply Time.join_spec; ss. apply Time.bot_spec.
          * unfold LocFun.add. condtac; ss.
            subst. unfold TimeMap.join, TimeMap.singleton, LocFun.add. condtac; subst; ss.
            unfold LocFun.find, LocFun.init.
            eapply Time.join_spec; ss. apply Time.bot_spec.
        + unfold prev_released_le_loc.
          destruct (Memory.get loc0 from0 mem2_src0) as [[? [? []|]]|] eqn:GET; ss.
          revert GET.
          erewrite Memory.lower_o; eauto. condtac; ss; cycle 1.
          { i. unfold prev_released_le_loc in PREV.
            rewrite GET in *. ss. }
          i. des. subst. inv GET.
          exploit Memory.lower_get0; try exact MEM. i. des.
          unfold prev_released_le_loc in PREV.
          rewrite GET in *.
          rewrite H2 in MSG_LE. inv MSG_LE. inv RELEASED0.
          unnw. etrans; try exact PREV.
          inv LE. econs; eauto.
    }

    { (* release *)
      destruct released_tgt as [released_tgt|]; cycle 1.
      { inv STEP_TGT. revert RELEASED0.
        unfold TView.write_released. condtac; ss.
        destruct ord; ss. }
      exploit write_promise_fulfill; eauto. i. des.
      exploit promise_step_release; try exact STEP1; eauto.
      { exploit Local.write_step_strong_relaxed; eauto; try by destruct ord. i.
        exploit Local.write_step_non_cancel; eauto. }
      { i. destruct kind_tgt; ss. inv STEP_TGT.
        hexploit RELEASE; try by destruct ord. i.
        destruct msg3 as [? []|]; eauto.
        inv WRITE. inv PROMISE.
        exploit Memory.split_get0; try exact PROMISES. i. des.
        exploit H0; eauto; ss. }
      i. des.
      exploit Local.promise_step_future; try exact STEP_SRC; eauto. i. des.
      exploit Local.promise_step_future; try exact STEP1; eauto. i. des.
      dup STEP_SRC. inv STEP_SRC0. clear CLOSED.
      exploit Memory.promise_get2; try exact PROMISE; try by inv PROMISE. i. des.
      exploit fulfill_step_release; try exact STEP2; eauto.
      { unguard. des; eauto. split; auto. right.
        inv STEP_SRC. inv PROMISE.
        - erewrite Memory.add_o; eauto. condtac; ss; eauto.
          des. subst. inv MEM. inv ADD. timetac.
        - erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
          + des. subst. inv MEM. inv SPLIT. timetac.
          + guardH o. des. subst.
            inv MEM. inv SPLIT. rewrite TS12 in TS23. timetac.
        - erewrite Memory.lower_o; eauto. condtac; ss; eauto.
          des. subst. inv MEM. inv LOWER. timetac.
        - erewrite Memory.remove_o; eauto. condtac; ss; eauto. }
      { destruct ord; ss. }
      { inv STEP1. ss. }
      i. des.
      replace released_src0 with released_src in *; cycle 1.
      { inv WRITE_SRC. inv PROMISE0.
        exploit Memory.lower_get0; try exact MEM. i. des.
        rewrite GET in *. inv GET_MEM. ss. }
      exploit MemoryMerge.promise_write_write; try exact PROMISE; eauto. i.
      esplits.
      - econs; eauto.
        + inv STEP_TGT. eapply sim_writable; eauto. apply LC1.
        + inv STEP_TGT. ii. destruct msg; ss.
          inv LC1. inv PROMISES1.
          exploit SOUND; try exact GET; eauto. i. des. inv MSG.
          exploit RELEASE; eauto. s. i. subst.
          inv RELEASED1. ss.
      - inv STEP_TGT. econs; ss.
        eapply sim_write_tview; eauto. apply LC1.
      - by inv STEP_TGT.
      - ss.
      - s. ii. inv WRITE_SRC. inv PROMISE0. revert GETP.
        erewrite Memory.remove_o; eauto. condtac; ss.
        erewrite Memory.lower_o; eauto. condtac; ss. i.
        guardH o. guardH o0.
        exploit FULFILLABLE2; eauto. i. des. split.
        + unfold TView.write_tview. condtac; try by destruct ord; ss.
          inv TVIEW. econs; ss.
          * unfold LocFun.add. condtac; ss.
            subst. unfold TimeMap.join, TimeMap.singleton, LocFun.add. condtac; subst; ss.
            unfold LocFun.find, LocFun.init.
            eapply Time.join_spec; eauto using Time.bot_spec.
            inv LC2. inv PROMISES1. ss.
            exploit SOUND; try exact GETP; eauto. i. des.
            inv MSG. inv RELEASED0. inv STEP1. ss.
            clear - COND1 ORD0 PROMISE0 o GET_TGT.
            exfalso. revert GET_TGT. inv PROMISE0.
            { erewrite Memory.add_o; eauto. condtac; ss; i.
              - des. subst. unguard. des; ss.
              - guardH o0. exploit ORD0; eauto; ss.
                destruct ord; ss. }
            { erewrite Memory.split_o; eauto. repeat condtac; ss; i.
              - des. subst. unguard. des; ss.
              - guardH o0. des. subst. inv GET_TGT. inv RESERVE.
                exploit Memory.split_get0; try exact PROMISES. i. des.
                exploit ORD0; eauto; ss.
                destruct ord; ss.
              - guardH o0. guardH o1.
                exploit ORD0; eauto; ss.
                destruct ord; ss. }
            { erewrite Memory.lower_o; eauto. condtac; ss; i.
              - des. subst. unguard. des; ss.
              - guardH o0. exploit ORD0; eauto; ss.
                destruct ord; ss. }
            { erewrite Memory.remove_o; eauto. condtac; ss. }
          * unfold LocFun.add. condtac; ss.
            subst. unfold TimeMap.join, TimeMap.singleton, LocFun.add. condtac; subst; ss.
            unfold LocFun.find, LocFun.init.
            eapply Time.join_spec; eauto using Time.bot_spec.
            inv LC2. inv PROMISES1. ss.
            exploit SOUND; try exact GETP; eauto. i. des.
            inv MSG. inv RELEASED0. inv STEP1. ss.
            clear - COND1 ORD0 PROMISE0 o GET_TGT.
            exfalso. revert GET_TGT. inv PROMISE0.
            { erewrite Memory.add_o; eauto. condtac; ss; i.
              - des. subst. unguard. des; ss.
              - guardH o0. exploit ORD0; eauto; ss.
                destruct ord; ss. }
            { erewrite Memory.split_o; eauto. repeat condtac; ss; i.
              - des. subst. unguard. des; ss.
              - guardH o0. des. subst. inv GET_TGT. inv RESERVE.
                exploit Memory.split_get0; try exact PROMISES. i. des.
                exploit ORD0; eauto; ss.
                destruct ord; ss.
              - guardH o0. guardH o1.
                exploit ORD0; eauto; ss.
                destruct ord; ss. }
            { erewrite Memory.lower_o; eauto. condtac; ss; i.
              - des. subst. unguard. des; ss.
              - guardH o0. exploit ORD0; eauto; ss.
                destruct ord; ss. }
            { erewrite Memory.remove_o; eauto. condtac; ss. }
        + unfold prev_released_le_loc.
          destruct (Memory.get loc0 from0 mem2_src0) as [[? [? []|]]|] eqn:GET; ss.
          revert GET.
          erewrite Memory.lower_o; eauto. condtac; ss; cycle 1.
          { i. unfold prev_released_le_loc in PREV.
            rewrite GET in *. ss. }
          i. des. subst. inv GET.
          exploit Memory.lower_get0; try exact MEM. i. des.
          unfold prev_released_le_loc in PREV.
          rewrite GET in *.
          rewrite H2 in MSG_LE. inv MSG_LE. inv RELEASED0.
          unnw. etrans; try exact PREV.
          inv LE. econs; eauto.
    }
  Qed.

  Lemma fence_step
        l
        lc1_src sc1_src mem1_src
        lc1_tgt sc1_tgt mem1_tgt ordr ordw lc2_tgt sc2_tgt
        (LC1: sim_local l lc1_src lc1_tgt)
        (SC1: sim_timemap l sc1_src sc1_tgt)
        (MEM1: sim_memory l mem1_src mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (PROMISES1: forall to, Memory.get l to (Local.promises lc1_src) = None)
        (FULFILLABLE1: fulfillable l (Local.tview lc1_src) mem1_src (Local.promises lc1_src))
        (STEP_TGT: Local.fence_step lc1_tgt sc1_tgt ordr ordw lc2_tgt sc2_tgt):
    exists lc2_src sc2_src,
      <<STEP_SRC: Local.fence_step lc1_src sc1_src ordr ordw lc2_src sc2_src>> /\
      <<LC2: sim_local l lc2_src lc2_tgt>> /\
      <<SC2: sim_timemap l sc2_src sc2_tgt>> /\
      <<FULFILLABLE2: fulfillable l (Local.tview lc2_src) mem1_src (Local.promises lc2_src)>>.
  Proof.
    inv STEP_TGT. esplits.
    - econs; eauto. ii.
      hexploit RELEASE; eauto.
      inv LC1. inv PROMISES0. exploit SOUND; eauto.
      { ii. subst. congr. }
      i. des. inv MSG; ss.
      exploit H0; eauto. i. inv RELEASED; ss.
    - econs; try apply LC1; s.
      eapply sim_fence_tview; eauto. apply LC1.
    - eapply sim_write_fence_sc; eauto.
      eapply sim_read_fence_tview; eauto. apply LC1.
    - unfold TView.write_fence_tview. repeat condtac; ss; ii.
      + destruct ordw; ss.
        inv LC1. inv PROMISES0. exploit SOUND; eauto.
        { ii. subst. congr. }
        i. des. inv MSG. inv RELEASED.
        exploit RELEASE; eauto. ss.
      + destruct ordw; ss.
        inv LC1. inv PROMISES0. exploit SOUND; eauto.
        { ii. subst. congr. }
        i. des. inv MSG. inv RELEASED.
        exploit RELEASE; eauto. ss.
  Qed.

  Lemma failure_step
        l
        lc1_src
        lc1_tgt
        (LC1: sim_local l lc1_src lc1_tgt)
        (PROMISES1: forall to, Memory.get l to (Local.promises lc1_src) = None)
        (STEP_TGT: Local.failure_step lc1_tgt):
    <<STEP_SRC: Local.failure_step lc1_src>>.
  Proof.
    inv STEP_TGT. econs. ii.
    assert (LOC: loc <> l) by (ii; subst; congr).
    inv LC1. inv PROMISES0.
    exploit SOUND; eauto. i. des. inv MSG.
    exploit CONSISTENT; eauto. i.
    inv TVIEW. inv CUR. exploit RLX; eauto. i.
    rewrite x0. ss.
  Qed.

  Lemma program_step
        l
        lc1_src sc1_src mem1_src
        e_tgt lc1_tgt sc1_tgt mem1_tgt lc2_tgt sc2_tgt mem2_tgt
        (LC1: sim_local l lc1_src lc1_tgt)
        (SC1: sim_timemap l sc1_src sc1_tgt)
        (MEM1: sim_memory l mem1_src mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
        (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (PROMISES1: forall to, Memory.get l to (Local.promises lc1_src) = None)
        (FULFILLABLE1: fulfillable l (Local.tview lc1_src) mem1_src (Local.promises lc1_src))
        (LOC: ~ ThreadEvent.is_accessing_loc l e_tgt)
        (STEP_TGT: Local.program_step e_tgt lc1_tgt sc1_tgt mem1_tgt lc2_tgt sc2_tgt mem2_tgt):
    exists e_src lc2_src sc2_src mem2_src,
      <<STEP_SRC: Local.program_step e_src lc1_src sc1_src mem1_src lc2_src sc2_src mem2_src>> /\
      <<EVENT1: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>> /\
      <<EVENT2: ThreadEvent.get_program_event e_src = ThreadEvent.get_program_event e_tgt>> /\
      <<LC2: sim_local l lc2_src lc2_tgt>> /\
      <<SC2: sim_timemap l sc2_src sc2_tgt>> /\
      <<MEM2: sim_memory l mem2_src mem2_tgt>> /\
      <<FULFILLABLE2: fulfillable l (Local.tview lc2_src) mem2_src (Local.promises lc2_src)>>.
  Proof.
    unfold ThreadEvent.is_accessing_loc in *.
    inv STEP_TGT; ss.
    - esplits; eauto.
    - exploit read_step; eauto. i. des.
      esplits; [econs 2|..]; eauto.
    - hexploit write_step; eauto.
      { unguard. split; eauto. ss.
        unfold TimeMap.bot. apply Time.bot_spec. }
      i. des.
      esplits; [econs 3|..]; eauto.
    - exploit read_step; eauto. i. des.
      exploit Local.read_step_future; try exact LOCAL1; eauto. i. des.
      exploit Local.read_step_future; try exact STEP_SRC; eauto. i. des.
      hexploit write_step; try exact LOCAL2; eauto.
      { inv MEM1. inv LOCAL1. inv STEP_SRC. ss.
        exploit SOUND; eauto. i. des. inv MSG.
        rewrite GET_TGT in *. inv GET. ss. }
      { unguard. inv STEP_SRC. ss. split; eauto.
        inv CLOSED1_SRC. exploit CLOSED; eauto. i. des.
        inv MSG_TS. etrans; eauto. econs.
        inv LOCAL2. inv WRITE. inv PROMISE; inv MEM.
        - by inv ADD.
        - by inv SPLIT.
        - by inv LOWER.
        - by inv REMOVE. }
      i. des.
      esplits; [econs 4|..]; eauto.
    - exploit fence_step; eauto. i. des.
      esplits; [econs 5|..]; eauto.
    - exploit fence_step; eauto. i. des.
      esplits; [econs 6|..]; eauto; refl.
    - exploit failure_step; eauto. i. des.
      esplits; [econs 7|..]; eauto.
  Qed.

  Lemma program_step_eq_promises
        l
        e lc1 sc1 mem1 lc2 sc2 mem2
        (STEP: Local.program_step e lc1 sc1 mem1 lc2 sc2 mem2)
        (LOC: ~ ThreadEvent.is_accessing_loc l e):
    forall to, Memory.get l to (Local.promises lc1) = Memory.get l to (Local.promises lc2).
  Proof.
    unfold ThreadEvent.is_accessing_loc in *.
    inv STEP; ss; try by inv LOCAL.
    - i. inv LOCAL. inv WRITE. ss.
      erewrite (@Memory.remove_o promises2); eauto. condtac; ss.
      + des. subst. ss.
      + guardH o. inv PROMISE.
        * erewrite (@Memory.add_o promises0); eauto. condtac; ss.
        * erewrite (@Memory.split_o promises0); eauto. repeat condtac; ss.
          guardH o0. des. subst. ss.
        * erewrite (@Memory.lower_o promises0); eauto. condtac; ss.
        * erewrite (@Memory.remove_o promises0); eauto. condtac; ss.
    - i. inv LOCAL1. inv LOCAL2. inv WRITE. ss.
      erewrite (@Memory.remove_o promises2); eauto. condtac; ss.
      + des. subst. ss.
      + guardH o. inv PROMISE.
        * erewrite (@Memory.add_o promises0); eauto. condtac; ss.
        * erewrite (@Memory.split_o promises0); eauto. repeat condtac; ss.
          guardH o0. des. subst. ss.
        * erewrite (@Memory.lower_o promises0); eauto. condtac; ss.
        * erewrite (@Memory.remove_o promises0); eauto. condtac; ss.
  Qed.

  Lemma program_step_eq_mem
        l
        e lc1 sc1 mem1 lc2 sc2 mem2
        (STEP: Local.program_step e lc1 sc1 mem1 lc2 sc2 mem2)
        (LOC: ~ ThreadEvent.is_accessing_loc l e):
    forall to, Memory.get l to mem1 = Memory.get l to mem2.
  Proof.
    unfold ThreadEvent.is_accessing_loc in *.
    inv STEP; ss; try by inv LOCAL.
    - i. inv LOCAL. inv WRITE. ss.
      inv PROMISE.
      + erewrite (@Memory.add_o mem2); eauto. condtac; ss.
        des. subst. ss.
      + erewrite (@Memory.split_o mem2); eauto. repeat condtac; ss.
        * des. subst. ss.
        * guardH o. des. subst. ss.
      + erewrite (@Memory.lower_o mem2); eauto. condtac; ss.
        des. subst. ss.
      + erewrite (@Memory.remove_o mem2); eauto. condtac; ss.
    - i. inv LOCAL1. inv LOCAL2. inv WRITE. ss.
      inv PROMISE.
      + erewrite (@Memory.add_o mem2); eauto. condtac; ss.
        des. subst. ss.
      + erewrite (@Memory.split_o mem2); eauto. repeat condtac; ss.
        * des. subst. ss.
        * guardH o. des. subst. ss.
      + erewrite (@Memory.lower_o mem2); eauto. condtac; ss.
        des. subst. ss.
      + erewrite (@Memory.remove_o mem2); eauto. condtac; ss.
  Qed.


  (* max_timemap *)

  Lemma sim_memory_max_full_ts
        l loc
        mem_src mem_tgt
        max_src max_tgt
        (SIM: sim_memory l mem_src mem_tgt)
        (LOC: loc <> l)
        (MAX_SRC: Memory.max_full_ts mem_src loc max_src)
        (MAX_TGT: Memory.max_full_ts mem_tgt loc max_tgt):
    <<TS: max_src = max_tgt>>.
  Proof.
    inv SIM. inv MAX_SRC. inv MAX_TGT. des.
    apply TimeFacts.antisym.
    - exploit SOUND; eauto. i. des. inv MSG.
      exploit MAX0; try eapply GET_TGT. ss.
    - exploit COMPLETE; eauto. i. des. inv MSG.
      exploit MAX; try eapply GET_SRC. ss.
  Qed.

  Lemma sim_memory_max_full_timemap
        l
        mem_src mem_tgt
        max_src max_tgt
        (SIM: sim_memory l mem_src mem_tgt)
        (MAX_SRC: Memory.max_full_timemap mem_src max_src)
        (MAX_TGT: Memory.max_full_timemap mem_tgt max_tgt):
    <<SIM_TIMEMAP: sim_timemap l max_src max_tgt>>.
  Proof.
    ii. specialize (MAX_SRC loc). specialize (MAX_TGT loc).
    eapply sim_memory_max_full_ts; eauto.
  Qed.

  Lemma sim_memory_max_full_view
        l
        mem_src mem_tgt
        max_src max_tgt
        (SIM: sim_memory l mem_src mem_tgt)
        (MAX_SRC: Memory.max_full_view mem_src max_src)
        (MAX_TGT: Memory.max_full_view mem_tgt max_tgt):
    <<SIM_VIEW: sim_view l max_src max_tgt>>.
  Proof.
    inv MAX_SRC. inv MAX_TGT.
    econs; eapply sim_memory_max_full_timemap; eauto.
  Qed.


  (* cap *)

  Lemma sim_memory_get_None_src
        l mem_src mem_tgt
        loc to
        (SIM: sim_memory l mem_src mem_tgt)
        (LOC: loc <> l)
        (GET_SRC: Memory.get loc to mem_src = None):
    Memory.get loc to mem_tgt = None.
  Proof.
    inv SIM.
    destruct (Memory.get loc to mem_tgt) as [[]|] eqn:GET; ss.
    exploit COMPLETE; eauto. i. des. congr.
  Qed.

  Lemma sim_memory_get_None_tgt
        l mem_src mem_tgt
        loc to
        (SIM: sim_memory l mem_src mem_tgt)
        (LOC: loc <> l)
        (GET_TGT: Memory.get loc to mem_tgt = None):
    Memory.get loc to mem_src = None.
  Proof.
    symmetry in SIM.
    eapply sim_memory_get_None_src; eauto.
  Qed.

  Lemma sim_memory_adjacent_src
      l mem_src mem_tgt
      loc from1 to1 from2 to2
      (SIM: sim_memory l mem_src mem_tgt)
      (LOC: loc <> l)
      (ADJ: Memory.adjacent loc from1 to1 from2 to2 mem_src):
    Memory.adjacent loc from1 to1 from2 to2 mem_tgt.
  Proof.
    dup SIM. inv SIM0. inv ADJ.
    exploit SOUND; try exact GET1; eauto. i. des.
    exploit SOUND; try exact GET2; eauto. i. des.
    econs; eauto. i.
    exploit EMPTY; eauto. i.
    eapply sim_memory_get_None_src; eauto.
  Qed.

  Lemma sim_memory_adjacent_tgt
        l mem_src mem_tgt
        loc from1 to1 from2 to2
        (SIM: sim_memory l mem_src mem_tgt)
        (LOC: loc <> l)
        (ADJ: Memory.adjacent loc from1 to1 from2 to2 mem_tgt):
    Memory.adjacent loc from1 to1 from2 to2 mem_src.
  Proof.
    symmetry in SIM.
    eapply sim_memory_adjacent_src; eauto.
  Qed.

  Lemma sim_memory_max_ts
        l loc
        mem_src mem_tgt
        (SIM: sim_memory l mem_src mem_tgt)
        (INHABITED_SRC: Memory.inhabited mem_src)
        (INHABITED_TGT: Memory.inhabited mem_tgt)
        (LOC: loc <> l):
    <<TS: Memory.max_ts loc mem_src = Memory.max_ts loc mem_tgt>>.
  Proof.
    inv SIM. apply TimeFacts.antisym.
    - exploit Memory.max_ts_spec; try exact (INHABITED_SRC loc). i. des.
      exploit SOUND; eauto. i. des.
      exploit Memory.max_ts_spec; try exact GET_TGT. i. des. ss.
    - exploit Memory.max_ts_spec; try exact (INHABITED_TGT loc). i. des.
      exploit COMPLETE; eauto. i. des.
      exploit Memory.max_ts_spec; try exact GET_SRC. i. des. ss.
  Qed.

  Lemma sim_memory_latest_reserve_src
        l
        promises_src promises_tgt
        mem_src mem_tgt
        loc
        (PROMISES: sim_memory l promises_src promises_tgt)
        (MEM: sim_memory l mem_src mem_tgt)
        (INHABITED_SRC: Memory.inhabited mem_src)
        (INHABITED_TGT: Memory.inhabited mem_tgt)
        (LOC: loc <> l)
        (LATEST: Memory.latest_reserve loc promises_src mem_src):
    Memory.latest_reserve loc promises_tgt mem_tgt.
  Proof.
    unfold Memory.latest_reserve in *. des_ifs.
    - inv PROMISES.
      erewrite <- sim_memory_max_ts in Heq; eauto.
      exploit SOUND; eauto. i. des. inv MSG. congr.
    - erewrite <- sim_memory_max_ts in Heq; eauto.
      exploit sim_memory_get_None_src; try exact Heq0; eauto. i. congr.
  Qed.

  Lemma sim_memory_latest_reserve_tgt
        l
        promises_src promises_tgt
        mem_src mem_tgt
        loc
        (PROMISES: sim_memory l promises_src promises_tgt)
        (MEM: sim_memory l mem_src mem_tgt)
        (INHABITED_SRC: Memory.inhabited mem_src)
        (INHABITED_TGT: Memory.inhabited mem_tgt)
        (LOC: loc <> l)
        (LATEST: Memory.latest_reserve loc promises_tgt mem_tgt):
    Memory.latest_reserve loc promises_src mem_src.
  Proof.
    symmetry in PROMISES, MEM.
    eapply sim_memory_latest_reserve_src; eauto.
  Qed.

  Lemma sim_memory_latest_val_src
        l mem_src mem_tgt
        loc val
        (MEM: sim_memory l mem_src mem_tgt)
        (INHABITED_SRC: Memory.inhabited mem_src)
        (INHABITED_TGT: Memory.inhabited mem_tgt)
        (LOC: loc <> l)
        (LATEST: Memory.latest_val loc mem_src val):
    Memory.latest_val loc mem_tgt val.
  Proof.
    inv MEM. inv LATEST.
    exploit SOUND; eauto. i. des. inv MSG.
    exploit Memory.max_full_ts_exists; try exact INHABITED_TGT. i. des.
    exploit sim_memory_max_full_ts; eauto. i. des. subst.
    econs; eauto.
  Qed.

  Lemma sim_memory_latest_val_tgt
        l mem_src mem_tgt
        loc val
        (MEM: sim_memory l mem_src mem_tgt)
        (INHABITED_SRC: Memory.inhabited mem_src)
        (INHABITED_TGT: Memory.inhabited mem_tgt)
        (LOC: loc <> l)
        (LATEST: Memory.latest_val loc mem_tgt val):
    Memory.latest_val loc mem_src val.
  Proof.
    symmetry in MEM.
    eapply sim_memory_latest_val_src; eauto.
  Qed.

  Lemma sim_memory_cap
        l
        promises_src promises_tgt
        mem_src mem_tgt
        cap_src cap_tgt
        (PROMISES: sim_memory l promises_src promises_tgt)
        (MEM: sim_memory l mem_src mem_tgt)
        (CLOSED_SRC: Memory.closed mem_src)
        (CLOSED_TGT: Memory.closed mem_tgt)
        (CAP_SRC: Memory.cap promises_src mem_src cap_src)
        (CAP_TGT: Memory.cap promises_tgt mem_tgt cap_tgt):
    <<SIM_CAP: sim_memory l cap_src cap_tgt>>.
  Proof.
    inv PROMISES. inv MEM. econs; ii.
    - exploit Memory.cap_inv; try exact CAP_SRC; eauto. i. des.
      + inv CAP_TGT.
        exploit SOUND0; eauto. i. des. eauto.
      + subst. inv CAP_TGT.
        exploit sim_memory_adjacent_src; eauto. i.
        exploit MIDDLE; eauto.
      + subst. inv CAP_TGT.
        exploit sim_memory_latest_reserve_src; try exact x1; eauto;
          try apply CLOSED_SRC; try apply CLOSED_TGT; i.
        exploit sim_memory_latest_val_src; try exact x1; eauto;
          try apply CLOSED_SRC; try apply CLOSED_TGT; i.
        exploit Memory.max_full_view_exists; try eapply CLOSED_TGT. i. des.
        exploit sim_memory_max_full_view; try exact MEM; eauto. i. des.
        exploit BACK; eauto. i.
        erewrite sim_memory_max_ts; eauto.
        esplits; eauto.
        * apply CLOSED_SRC.
        * apply CLOSED_TGT.
    - exploit Memory.cap_inv; try exact CAP_TGT; eauto. i. des.
      + inv CAP_SRC.
        exploit COMPLETE0; eauto. i. des. eauto.
      + subst. inv CAP_SRC.
        exploit sim_memory_adjacent_tgt; eauto. i.
        exploit MIDDLE; eauto.
      + subst. inv CAP_SRC.
        exploit sim_memory_latest_reserve_tgt; try exact x1; eauto;
          try apply CLOSED_SRC; try apply CLOSED_TGT; i.
        exploit sim_memory_latest_val_tgt; try exact x1; eauto;
          try apply CLOSED_SRC; try apply CLOSED_TGT; i.
        exploit Memory.max_full_view_exists; try eapply CLOSED_SRC. i. des.
        exploit sim_memory_max_full_view; try exact MEM; eauto. i. des.
        exploit BACK; eauto. i.
        erewrite <- sim_memory_max_ts; eauto.
        esplits; eauto.
        * apply CLOSED_SRC.
        * apply CLOSED_TGT.
  Qed.

  Lemma cap_fulfillable
        l tview promises mem1 mem2
        (CAP: Memory.cap promises mem1 mem2)
        (LE: Memory.le promises mem1)
        (CLOSED: Memory.closed mem1)
        (FULFILLABLE: fulfillable l tview mem1 promises):
    <<FULFILLABLE: fulfillable l tview mem2 promises>>.
  Proof.
    ii. exploit FULFILLABLE; eauto. i. des. split; ss.
    unfold prev_released_le_loc in *.
    destruct (Memory.get loc from mem2) as [[? [? []|]]|] eqn:GET2; ss.
    exploit Memory.cap_inv; try exact CAP; eauto. i. des; ss.
    - rewrite x0 in *. ss.
    - subst. exploit LE; eauto. i.
      specialize (Time.incr_spec (Memory.max_ts loc mem1)). i.
      exploit Memory.get_ts; try exact x. i. des.
      { subst. rewrite x3 in *. inv H. }
      exploit Memory.max_ts_spec; try exact x. i. des.
      exploit TimeFacts.lt_le_lt; try exact x3; eauto. i.
      rewrite x7 in H. timetac.
  Qed.
End SimCommon.
