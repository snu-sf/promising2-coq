Require Import RelationClasses.

From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.

Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.

Set Implicit Arguments.


Module MemoryDomain.
  Definition t := Loc.t -> DOSet.t.

  Definition mem loc ts (dom:t) := DOSet.mem ts (dom loc).

  Lemma ext lhs rhs
        (EXT: forall loc ts, mem loc ts lhs = mem loc ts rhs):
    lhs = rhs.
  Proof.
    apply LocFun.ext. unfold LocFun.find. i.
    apply DOSet.eq_leibniz. ii.
    specialize (EXT i a). unfold mem in *. econs; i.
    - apply DOSet.mem_spec. erewrite <- EXT.
      apply DOSet.mem_spec. auto.
    - apply DOSet.mem_spec. erewrite EXT.
      apply DOSet.mem_spec. auto.
  Qed.

  Definition bot: t := fun _ => DOSet.empty.

  Lemma bot_spec loc ts: mem loc ts bot = false.
  Proof.
    unfold mem, bot. apply DOSet.Facts.empty_b.
  Qed.

  Definition le (lhs rhs:t): Prop :=
    forall loc ts, mem loc ts lhs -> mem loc ts rhs.

  Definition join (lhs rhs:t): t :=
    fun loc => DOSet.union (lhs loc) (rhs loc).

  Lemma join_comm lhs rhs: join lhs rhs = join rhs lhs.
  Proof.
    apply LocFun.ext. unfold LocFun.find, join. i.
    apply DOSet.eq_leibniz. ii.
    rewrite ? DOSet.union_spec. econs; i; des; auto.
  Qed.

  Lemma join_assoc a b c: join (join a b) c = join a (join b c).
  Proof.
    apply LocFun.ext. unfold LocFun.find, join. i.
    apply DOSet.eq_leibniz. ii.
    rewrite ? DOSet.union_spec. econs; i; des; auto.
  Qed.

  Lemma join_l lhs rhs: le lhs (join lhs rhs).
  Proof.
    unfold join. ii. unfold mem in *.
    rewrite DOSet.Facts.union_b, H. auto.
  Qed.

  Lemma join_r lhs rhs: le rhs (join lhs rhs).
  Proof. rewrite join_comm. apply join_l. Qed.

  Lemma join_spec lhs rhs o
        (LHS: le lhs o)
        (RHS: le rhs o):
    le (join lhs rhs) o.
  Proof.
    unfold join. ii.
    unfold mem in *. rewrite DOSet.Facts.union_b in *.
    apply Bool.orb_true_iff in H. des; eauto.
  Qed.

  Definition set (loc:Loc.t) (ts:Time.t) (dom:t) :=
    LocFun.add loc (DOSet.add ts (dom loc)) dom.

  Lemma set_o loc1 ts1 loc2 ts2 dom:
    mem loc1 ts1 (set loc2 ts2 dom) =
    if loc_ts_eq_dec (loc1, ts1) (loc2, ts2)
    then true
    else mem loc1 ts1 dom.
  Proof.
    unfold mem, set, LocFun.add, LocFun.find.
    repeat (try condtac; ss; des; subst; try congr).
    - rewrite DOSet.Facts.add_b.
      unfold DOSet.Facts.eqb. rewrite Time.eq_dec_eq. auto.
    - rewrite DOSet.Facts.add_b.
      unfold DOSet.Facts.eqb. rewrite Time.eq_dec_neq; auto.
  Qed.

  Lemma set_eq loc ts dom:
    mem loc ts (set loc ts dom) = true.
  Proof.
    rewrite set_o. condtac; ss. des; congr.
  Qed.

  Lemma set_inv loc1 ts1 loc2 ts2 dom
        (MEM: mem loc1 ts1 (set loc2 ts2 dom)):
    (loc1 = loc2 /\ ts1 = ts2) \/ mem loc1 ts1 dom.
  Proof.
    revert MEM. rewrite set_o. repeat condtac; ss; auto.
  Qed.

  Definition unset (loc:Loc.t) (ts:Time.t) (dom:t) :=
    LocFun.add loc (DOSet.remove ts (dom loc)) dom.

  Lemma unset_o loc1 ts1 loc2 ts2 dom:
    mem loc1 ts1 (unset loc2 ts2 dom) =
    if loc_ts_eq_dec (loc1, ts1) (loc2, ts2)
    then false
    else mem loc1 ts1 dom.
  Proof.
    unfold mem, unset, LocFun.add, LocFun.find.
    repeat (try condtac; ss; des; subst; try congr).
    - rewrite DOSet.Facts.remove_b.
      unfold DOSet.Facts.eqb. rewrite Time.eq_dec_eq.
      apply Bool.andb_false_iff. auto.
    - rewrite DOSet.Facts.remove_b.
      unfold DOSet.Facts.eqb. rewrite Time.eq_dec_neq; auto.
      apply Bool.andb_true_r.
  Qed.

  Lemma unset_eq loc ts dom:
    mem loc ts (unset loc ts dom) = false.
  Proof.
    rewrite unset_o. condtac; ss. des; congr.
  Qed.

  Lemma unset_inv loc1 ts1 loc2 ts2 dom
        (MEM: mem loc1 ts1 (unset loc2 ts2 dom)):
    ~ (loc1 = loc2 /\ ts1 = ts2) /\ mem loc1 ts1 dom.
  Proof.
    revert MEM. rewrite unset_o. condtac; ss. i.
    splits; auto. ii. des; auto.
  Qed.

  Lemma unset_set loc to inv
        (MEM: mem loc to inv = false):
    unset loc to (set loc to inv) = inv.
  Proof.
    apply ext. i.
    rewrite unset_o, set_o.  condtac; ss. des. subst. auto.
  Qed.

  Lemma unset_bot loc to:
    unset loc to bot = bot.
  Proof.
    apply ext. i. rewrite unset_o. condtac; ss.
  Qed.

  Inductive disjoint (lhs rhs:t): Prop :=
  | disjoint_intro
      (DISJOINT: forall loc ts
                   (LHS: mem loc ts lhs)
                   (RHS: mem loc ts rhs),
          False).

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    econs. ii. eapply H; eauto.
  Qed.

  Definition sound (dom: t) (promises: Memory.t): Prop :=
    forall loc ts (MEM: mem loc ts dom),
      exists from msg, Memory.get loc ts promises = Some (from, msg).
End MemoryDomain.
