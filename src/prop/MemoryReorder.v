Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

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
Require Import MemoryFacts.

Require Import Cover.

Set Implicit Arguments.


Module MemoryReorder.
  Lemma add_add
        mem0 loc1 from1 to1 msg1
        mem1 loc2 from2 to2 msg2
        mem2
        (ADD1: Memory.add mem0 loc1 from1 to1 msg1 mem1)
        (ADD2: Memory.add mem1 loc2 from2 to2 msg2 mem2):
    exists mem1',
      <<ADD1: Memory.add mem0 loc2 from2 to2 msg2 mem1'>> /\
      <<ADD2: Memory.add mem1' loc1 from1 to1 msg1 mem2>> /\
      <<LOCTS: (loc1, to1) <> (loc2, to2)>>.
  Proof.
    exploit (@Memory.add_exists mem0 loc2 from2 to2).
    { i. inv ADD2. inv ADD. eapply DISJOINT.
      etrans; [eapply Memory.add_o; eauto|]. condtac; ss; eauto.
      des. subst. exploit Memory.add_get0; eauto. i. des. congr.
    }
    { inv ADD2. inv ADD. auto. }
    { inv ADD2. inv ADD. eauto. }
    i. des.
    exploit (@Memory.add_exists mem3 loc1 from1 to1).
    { i. revert GET2. erewrite Memory.add_o; eauto. condtac; ss.
      - des. subst. i. inv GET2.
        exploit Memory.add_get0; try exact ADD2; eauto.
        inv ADD2. inv ADD. symmetry. eapply DISJOINT.
        etrans; [eapply Memory.add_o; eauto|]. condtac; ss. des; congr.
      - guardH o. i. inv ADD1. inv ADD. eapply DISJOINT; eauto.
    }
    { inv ADD1. inv ADD. auto. }
    { inv ADD1. inv ADD. eauto. }
    i. des.
    esplits; eauto; cycle 1.
    { ii. inv H.
      exploit Memory.add_get0; try exact ADD2; eauto.
      erewrite Memory.add_o; eauto. condtac; s; i; des; congr.
    }
    cut (mem4 = mem2); [by i; subst; eauto|].
    apply Memory.ext. i.
    setoid_rewrite Memory.add_o; cycle 1; eauto.
    erewrite (@Memory.add_o mem3); eauto. erewrite (@Memory.add_o mem1); eauto.
    repeat (condtac; ss). des. subst.
    exploit Memory.add_get0; try exact ADD1; eauto. i. des.
    exploit Memory.add_get0; try exact ADD2; eauto. i. des.
    congr.
  Qed.

  Lemma add_split_same
        mem0 loc ts1 ts2 ts3 msg2 msg3 mem1 mem2
        (ADD1: Memory.add mem0 loc ts1 ts3 msg3 mem1)
        (SPLIT2: Memory.split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2):
    exists mem1',
      <<ADD1: Memory.add mem0 loc ts1 ts2 msg2 mem1'>> /\
      <<ADD2: Memory.add mem1' loc ts2 ts3 msg3 mem2>>.
  Proof.
    exploit (@Memory.add_exists mem0 loc ts1 ts2 msg2); eauto.
    { i. inv ADD1. inv ADD. hexploit DISJOINT; eauto. i.
      eapply Interval.le_disjoint; eauto. econs; [refl|].
      inv SPLIT2. inv SPLIT. left. auto.
    }
    { inv SPLIT2. inv SPLIT. auto. }
    { inv SPLIT2. inv SPLIT. auto. }
    i. des.
    exploit (@Memory.add_exists mem3 loc ts2 ts3 msg3); eauto.
    { i. revert GET2. erewrite Memory.add_o; eauto. condtac; ss.
      - des. subst. i. inv GET2.
        symmetry. apply Interval.disjoint_imm.
      - i. inv ADD1. inv ADD. hexploit DISJOINT; eauto. i.
        eapply Interval.le_disjoint; eauto. econs; [|refl].
        inv SPLIT2. inv SPLIT. left. auto.
    }
    { inv SPLIT2. inv SPLIT. auto. }
    { inv ADD1. inv ADD. auto. }
    i. des.
    cut (mem4 = mem2); [by i; subst; eauto|].
    apply Memory.ext. i.
    erewrite Memory.add_o; eauto. erewrite Memory.add_o; eauto.
    erewrite (@Memory.split_o mem2); eauto. erewrite (@Memory.add_o mem1); eauto.
    repeat (condtac; ss). des. repeat subst.
    inv SPLIT2. inv SPLIT. exfalso. eapply Time.lt_strorder. eauto.
  Qed.

  Lemma add_split
        mem0 loc1 from1 to1 msg1
        mem1 loc2 ts21 ts22 ts23 msg22 msg23
        mem2
        (ADD1: Memory.add mem0 loc1 from1 to1 msg1 mem1)
        (SPLIT2: Memory.split mem1 loc2 ts21 ts22 ts23 msg22 msg23 mem2):
    (loc1 = loc2 /\ from1 = ts21 /\ to1 = ts23 /\ msg1 = msg23 /\
     exists mem1',
       <<ADD1: Memory.add mem0 loc2 ts21 ts22 msg22 mem1'>> /\
       <<ADD2: Memory.add mem1' loc2 ts22 ts23 msg23 mem2>>) \/
    (<<LOCTS1: (loc1, to1) <> (loc2, ts23)>> /\
     exists mem1',
       <<SPLIT1: Memory.split mem0 loc2 ts21 ts22 ts23 msg22 msg23 mem1'>> /\
       <<ADD2: Memory.add mem1' loc1 from1 to1 msg1 mem2>>).
  Proof.
    exploit Memory.split_get0; eauto. i. des.
    revert GET0. erewrite Memory.add_o; eauto. condtac; ss.
    { des. i. inv GET0. left. splits; eauto.
      eapply add_split_same; eauto.
    }
    guardH o. i. right. splits.
    { ii. inv H. unguardH o. des; congr. }
    exploit (@Memory.split_exists mem0 loc2 ts21 ts22 ts23);
      try by inv SPLIT2; inv SPLIT; eauto.
    i. des.
    exploit (@Memory.add_exists mem3 loc1 from1 to1);
      try by inv ADD1; inv ADD; eauto.
    { i. revert GET3. erewrite Memory.split_o; eauto. repeat condtac; ss.
      - des. subst. i. inv GET3.
        inv ADD1. inv ADD. hexploit DISJOINT; eauto. i. symmetry in H.
        symmetry. eapply Interval.le_disjoint; eauto. econs; [refl|].
        inv SPLIT2. inv SPLIT. left. auto.
      - guardH o0. i. des. inv GET3.
        inv ADD1. inv ADD. hexploit DISJOINT; eauto. i. symmetry in H.
        symmetry. eapply Interval.le_disjoint; eauto. econs; [|refl].
        inv SPLIT2. inv SPLIT. left. auto.
      - guardH o0. i. inv ADD1. inv ADD. eapply DISJOINT; eauto.
    }
    i. des.
    esplits; eauto.
    cut (mem4 = mem2); [by i; subst; eauto|].
    apply Memory.ext. i.
    erewrite Memory.add_o; eauto. erewrite Memory.split_o; eauto.
    setoid_rewrite Memory.split_o; cycle 1; eauto.
    erewrite (@Memory.add_o mem1); eauto.
    repeat (condtac; ss).
    - des. repeat subst.
      exploit Memory.add_get0; try exact ADD1; eauto. i. des.
      exploit Memory.split_get0; try exact SPLIT2; eauto. i. des.
      congr.
    - guardH o0. des. repeat subst. unguardH o. des; congr.
  Qed.

  Lemma add_lower
        mem0 loc1 from1 to1 msg1
        mem1 loc2 from2 to2 msg2 msg2'
        mem2
        (ADD1: Memory.add mem0 loc1 from1 to1 msg1 mem1)
        (LOWER2: Memory.lower mem1 loc2 from2 to2 msg2 msg2' mem2):
    (loc1 = loc2 /\ from1 = from2 /\ to1 = to2 /\ msg1 = msg2 /\
     Memory.add mem0 loc1 from1 to1 msg2' mem2) \/
    (<<LOCTS1: (loc1, to1) <> (loc2, to2)>> /\
     exists mem1',
       <<LOWER1: Memory.lower mem0 loc2 from2 to2 msg2 msg2' mem1'>> /\
       <<ADD2: Memory.add mem1' loc1 from1 to1 msg1 mem2>>).
  Proof.
    exploit Memory.lower_get0; eauto.
    erewrite Memory.add_o; eauto. condtac; ss.
    - des. subst. i. des. inv GET. left. splits; eauto.
      inv ADD1. inv ADD. inv LOWER2. inv LOWER.
      rewrite LocFun.add_add_eq. econs; auto.
      unfold Cell.add in *.
      destruct r, r0. ss. subst.
      unfold LocFun.add. condtac; [|congr]. s.
      rewrite DOMap.add_add_eq. econs; auto.
    - guardH o. i. des. right. splits.
      { ii. inv H. unguardH o. des; congr. }
      exploit (@Memory.lower_exists mem0 loc2 from2 to2);
        try by inv LOWER2; inv LOWER; eauto.
      i. des.
      exploit (@Memory.add_exists mem3 loc1 from1 to1).
      { i. revert GET2. erewrite Memory.lower_o; eauto. condtac; ss.
        - des. subst. i. inv GET2.
          exploit Memory.lower_get0; eauto. i. des.
          inv ADD1. inv ADD. eapply DISJOINT. eauto.
        - guardH o0. i. inv ADD1. inv ADD. eapply DISJOINT; eauto.
      }
      { inv ADD1. inv ADD. auto. }
      { inv ADD1. inv ADD. eauto. }
      i. des.
      esplits; eauto.
      cut (mem4 = mem2); [by i; subst; eauto|].
      apply Memory.ext. i.
      erewrite Memory.add_o; eauto. erewrite Memory.lower_o; eauto.
      setoid_rewrite Memory.lower_o; cycle 1; eauto.
      erewrite (@Memory.add_o mem1); eauto.
      repeat (condtac; ss). des. repeat subst.
      unguardH o. des; congr.
  Qed.

  Lemma add_remove
        mem0 loc1 from1 to1 msg1
        mem1 loc2 from2 to2 msg2
        mem2
        (LOCTS1: (loc1, to1) <> (loc2, to2))
        (ADD1: Memory.add mem0 loc1 from1 to1 msg1 mem1)
        (REMOVE2: Memory.remove mem1 loc2 from2 to2 msg2 mem2):
    exists mem1',
      <<REMOVE1: Memory.remove mem0 loc2 from2 to2 msg2 mem1'>> /\
      <<ADD2: Memory.add mem1' loc1 from1 to1 msg1 mem2>>.
  Proof.
    exploit (@Memory.remove_exists mem0 loc2 from2 to2).
    { hexploit Memory.remove_get0; eauto.
      erewrite Memory.add_o; eauto. condtac; ss; i; des; subst; eauto. congr.
    }
    i. des.
    exploit (@Memory.add_exists mem3 loc1 from1 to1);
      try by inv ADD1; inv ADD; eauto.
    { i. revert GET2. erewrite Memory.remove_o; eauto. condtac; ss.
      inv ADD1. inv ADD. eauto.
    }
    i. des.
    cut (mem4 = mem2); [by i; subst; eauto|].
    apply Memory.ext. i.
    erewrite Memory.add_o; eauto. erewrite Memory.remove_o; eauto.
    erewrite (@Memory.remove_o mem2); eauto. erewrite (@Memory.add_o mem1); eauto.
    repeat (condtac; ss). des. repeat subst. congr.
  Qed.

  Lemma add_remove_same
        mem0 loc1 from1 to1 msg1
        mem1 from2 msg2
        mem2
        (ADD1: Memory.add mem0 loc1 from1 to1 msg1 mem1)
        (REMOVE2: Memory.remove mem1 loc1 from2 to1 msg2 mem2):
    from1 = from2 /\ msg1 = msg2 /\ mem0 = mem2.
  Proof.
    exploit Memory.add_get0; eauto. i. des.
    exploit Memory.remove_get0; eauto. i. des.
    rewrite GET0 in *. inv GET1. splits; auto.
    apply Memory.ext. i.
    erewrite (@Memory.remove_o mem2); eauto. condtac; ss.
    - des. subst. ss.
    - erewrite (@Memory.add_o mem1); eauto. condtac; ss.
  Qed.

  Lemma split_add
        mem0 loc1 ts11 ts12 ts13 msg12 msg13
        mem1 loc2 from2 to2 msg2
        mem2
        (SPLIT1: Memory.split mem0 loc1 ts11 ts12 ts13 msg12 msg13 mem1)
        (ADD2: Memory.add mem1 loc2 from2 to2 msg2 mem2):
    <<LOCTS1: (loc1, ts12) <> (loc2, to2)>> /\
    <<LOCTS2: (loc1, ts13) <> (loc2, to2)>> /\
    exists mem1',
      <<ADD1: Memory.add mem0 loc2 from2 to2 msg2 mem1'>> /\
      <<SPLIT2: Memory.split mem1' loc1 ts11 ts12 ts13 msg12 msg13 mem2>>.
  Proof.
    exploit (@Memory.add_exists mem0 loc2 from2 to2);
      try by inv ADD2; inv ADD; eauto.
    { apply covered_disjoint_get_disjoint. i. rewrite <- split_covered in H; eauto.
      eapply get_disjoint_covered_disjoint; eauto. inv ADD2. inv ADD. auto.
    }
    i. des.
    exploit (@Memory.split_exists mem3 loc1 ts11 ts12 ts13);
      try by inv SPLIT1; inv SPLIT; eauto.
    { erewrite Memory.add_o; eauto. condtac; ss.
      - des. subst.
        hexploit Memory.add_get0; try exact ADD2; eauto. i. des.
        revert GET. erewrite Memory.split_o; eauto. repeat condtac; ss.
      - guardH o. hexploit Memory.split_get0; eauto. i. des. eauto.
    }
    i. des.
    splits.
    { ii. inv H.
      hexploit Memory.add_get0; try exact ADD2; eauto. i. des.
      revert GET. erewrite Memory.split_o; eauto. repeat condtac; ss.
      guardH o0. des; congr.
    }
    { ii. inv H.
      hexploit Memory.add_get0; try exact ADD2; eauto. i. des.
      revert GET. erewrite Memory.split_o; eauto. repeat condtac; ss.
      guardH o. des; congr.
    }
    cut (mem4 = mem2); [by i; subst; eauto|].
    apply Memory.ext. i.
    erewrite Memory.split_o; eauto. erewrite Memory.add_o; eauto.
    erewrite (@Memory.add_o mem2); eauto. erewrite (@Memory.split_o mem1); eauto.
    repeat (condtac; ss).
    - des. repeat subst.
      hexploit Memory.add_get0; try exact ADD2; eauto. i. des.
      revert GET. erewrite Memory.split_o; eauto. repeat condtac; ss.
    - guardH o. des. repeat subst.
      hexploit Memory.add_get0; try exact ADD2; eauto. i. des.
      revert GET. erewrite Memory.split_o; eauto. repeat condtac; ss.
  Qed.

  Lemma split_split
        mem0 loc1 ts11 ts12 ts13 msg12 msg13
        mem1 loc2 ts21 ts22 ts23 msg22 msg23
        mem2
        (LOCTS1: (loc1, ts13) <> (loc2, ts23))
        (SPLIT1: Memory.split mem0 loc1 ts11 ts12 ts13 msg12 msg13 mem1)
        (SPLIT2: Memory.split mem1 loc2 ts21 ts22 ts23 msg22 msg23 mem2):
    (loc1 = loc2 /\ ts21 = ts11 /\ ts23 = ts12 /\
     exists mem1',
       <<SPLIT1: Memory.split mem0 loc2 ts21 ts22 ts13 msg22 msg13 mem1'>> /\
       <<SPLIT2: Memory.split mem1' loc1 ts22 ts12 ts13 msg12 msg13 mem2>>) \/
    ((loc2, ts21, ts23) <> (loc1, ts11, ts12) /\
     exists mem1',
       <<SPLIT1: Memory.split mem0 loc2 ts21 ts22 ts23 msg22 msg23 mem1'>> /\
       <<SPLIT2: Memory.split mem1' loc1 ts11 ts12 ts13 msg12 msg13 mem2>>).
  Proof.
    exploit Memory.split_get0; try exact SPLIT2; eauto. i. des.
    revert GET0. erewrite Memory.split_o; eauto. repeat condtac; ss.
    - i. des. inv GET0. left. splits; auto.
      exploit Memory.split_get0; try exact SPLIT1; eauto. i. des.
      exploit Memory.split_get0; try exact SPLIT2; eauto. i. des.
      revert GET4. erewrite Memory.split_o; eauto. condtac; ss.
      exploit (@Memory.split_exists mem0 loc1 ts21 ts22 ts13);
        try by inv SPLIT2; inv SPLIT; eauto.
      { etrans.
        - inv SPLIT2. inv SPLIT. eauto.
        - inv SPLIT1. inv SPLIT. eauto.
      }
      i. des.
      exploit (@Memory.split_exists mem3 loc1 ts22 ts12 ts13);
        (try by inv SPLIT1; inv SPLIT; eauto);
        (try by inv SPLIT2; inv SPLIT; eauto).
      { erewrite Memory.split_o; eauto. repeat condtac; ss.
        - des. subst. inv x0. inv SPLIT.
          exfalso. eapply Time.lt_strorder. eauto.
        - guardH o. des; congr.
      }
      i. des.
      cut (mem4 = mem2); [by i; subst; eauto|].
      apply Memory.ext. i.
      erewrite Memory.split_o; eauto. erewrite Memory.split_o; eauto.
      erewrite (@Memory.split_o mem2); eauto. erewrite (@Memory.split_o mem1); eauto.
      repeat (condtac; ss).
      + des. repeat subst. inv x1. inv SPLIT.
        exfalso. eapply Time.lt_strorder. eauto.
      + guardH o. des. repeat subst. inv x0. inv SPLIT.
        exfalso. eapply Time.lt_strorder. eauto.
    - guardH o. i. des. inv GET0. congr.
    - guardH o. guardH o0. i. right.
      exploit (@Memory.split_exists mem0 loc2 ts21 ts22 ts23);
        try by inv SPLIT2; inv SPLIT; eauto. i. des.
      exploit (@Memory.split_exists mem3 loc1 ts11 ts12 ts13);
        try by inv SPLIT1; inv SPLIT; eauto.
      { erewrite Memory.split_o; eauto. repeat condtac; ss.
        - des. subst. hexploit Memory.split_get0; try exact SPLIT2; eauto. i. des.
          revert GET3. erewrite Memory.split_o; eauto. repeat condtac; ss.
        - guardH o1. des. subst. unguardH o0. des; congr.
        - guardH o1. guardH o2. hexploit Memory.split_get0; try exact SPLIT1; eauto. i. des. eauto.
      }
      i. des. splits.
      { ii. inv H. unguardH o. des; congr. }
      cut (mem4 = mem2); [by i; subst; eauto|].
      apply Memory.ext. i.
      erewrite Memory.split_o; eauto. erewrite Memory.split_o; eauto.
      erewrite (@Memory.split_o mem2); eauto. erewrite (@Memory.split_o mem1); eauto.
      repeat (condtac; ss).
      + des. repeat subst.
        exploit Memory.split_get0; try exact SPLIT2; eauto. i. des.
        revert GET3. erewrite Memory.split_o; eauto. repeat condtac; ss.
      + guardH o1. des. repeat subst. unguardH o. des; congr.
      + guardH o1. des. repeat subst.
        exploit Memory.split_get0; try exact SPLIT2; eauto. i. des.
        revert GET3. erewrite Memory.split_o; eauto. repeat condtac; ss.
      + guardH o1. guardH o2. des. repeat subst. unguardH o0. des; congr.
  Qed.

  Lemma split_lower_diff
        mem0 loc1 ts11 ts12 ts13 msg12 msg13
        mem1 loc2 from2 to2 msg2 msg2'
        mem2
        (LOCTS1: (loc1, ts13) <> (loc2, to2))
        (SPLIT1: Memory.split mem0 loc1 ts11 ts12 ts13 msg12 msg13 mem1)
        (LOWER2: Memory.lower mem1 loc2 from2 to2 msg2 msg2' mem2):
    (loc1 = loc2 /\ ts11 = from2 /\ ts12 = to2 /\ msg12 = msg2 /\
     Memory.split mem0 loc1 ts11 ts12 ts13 msg2' msg13 mem2) \/
    ((loc1, ts12) <> (loc2, to2) /\
     exists mem1',
        <<LOWER1: Memory.lower mem0 loc2 from2 to2 msg2 msg2' mem1'>> /\
        <<SPLIT2: Memory.split mem1' loc1 ts11 ts12 ts13 msg12 msg13 mem2>>).
  Proof.
    exploit Memory.lower_get0; eauto. i. des.
    revert GET. erewrite Memory.split_o; eauto. repeat condtac; ss.
    - des. subst. i. inv GET. left. splits; auto.
      inv SPLIT1. inv SPLIT. inv LOWER2. inv LOWER.
      rewrite LocFun.add_add_eq. econs; auto.
      unfold Cell.split in *.
      destruct r, r0. ss. subst.
      unfold LocFun.add. condtac; [|congr]. s.
      rewrite DOMap.add_add_eq. econs; auto.
    - guardH o. des. subst. congr.
    - guardH o. guardH o0. i. right.
      exploit (@Memory.lower_exists mem0 loc2 from2 to2);
        try by inv LOWER2; inv LOWER; eauto. i. des.
      exploit (@Memory.split_exists mem3 loc1 ts11 ts12 ts13);
        try by inv SPLIT1; inv SPLIT; eauto.
      { erewrite Memory.lower_o; eauto. condtac; ss.
        - des. subst. congr.
        - guardH o1. hexploit Memory.split_get0; try exact SPLIT1; eauto. i. des. eauto.
      }
      i. des.
      splits.
      { ii. inv H. exploit Memory.split_get0; try exact SPLIT1; eauto. i. des.
        exploit Memory.lower_get0; eauto. i. des. congr.
      }
      cut (mem4 = mem2); [by i; subst; eauto|].
      apply Memory.ext. i.
      erewrite Memory.split_o; eauto. erewrite Memory.lower_o; eauto.
      erewrite (@Memory.lower_o mem2); eauto. erewrite (@Memory.split_o mem1); eauto.
      repeat (condtac; ss).
      + des. repeat subst. congr.
      + guardH o1. des. repeat subst. congr.
  Qed.

  Lemma split_lower_same
        loc
        mem0 ts11 ts12 ts13 msg12 msg13
        mem1 from2 msg2 msg2'
        mem2
        (SPLIT1: Memory.split mem0 loc ts11 ts12 ts13 msg12 msg13 mem1)
        (LOWER2: Memory.lower mem1 loc from2 ts13 msg2 msg2' mem2):
    from2 = ts12 /\ msg13 = msg2 /\
    exists mem1',
      <<LOWER1: Memory.lower mem0 loc ts11 ts13 msg2 msg2' mem1'>> /\
      <<SPLIT2: Memory.split mem1' loc ts11 ts12 ts13 msg12 msg2' mem2>>.
  Proof.
    exploit Memory.lower_get0; eauto. erewrite Memory.split_o; eauto. repeat condtac; ss; cycle 2.
    { clear -o0. des; congr. }
    { des. subst. inv SPLIT1. inv SPLIT. exfalso. eapply Time.lt_strorder. eauto. }
    clear o a COND COND0. i. des. inv GET. splits; ss.
    exploit Memory.split_get0; eauto. i. des.
    exploit (@Memory.lower_exists mem0 loc ts11 ts13);
      try by inv LOWER2; inv LOWER; eauto.
    { inv SPLIT1. inv SPLIT. etrans; eauto. }
    i. des.
    exploit (@Memory.split_exists mem3 loc ts11 from2 ts13);
      try by inv SPLIT1; inv SPLIT; eauto.
    { erewrite Memory.lower_o; eauto. condtac; ss. des; congr. }
    i. des.
    cut (mem4 = mem2); [by i; subst; esplits; eauto|].
    apply Memory.ext. i.
    erewrite Memory.split_o; eauto. erewrite Memory.lower_o; eauto.
    erewrite (@Memory.lower_o mem2); eauto. erewrite (@Memory.split_o mem1); eauto.
    repeat (condtac; ss).
    des. repeat subst. congr.
  Qed.

  Lemma split_remove
        mem0 loc1 ts11 ts12 ts13 msg12 msg13
        mem1 loc2 from2 to2 msg2
        mem2
        (LOCTS1: (loc1, ts12) <> (loc2, to2))
        (LOCTS2: (loc1, ts13) <> (loc2, to2))
        (SPLIT1: Memory.split mem0 loc1 ts11 ts12 ts13 msg12 msg13 mem1)
        (REMOVE2: Memory.remove mem1 loc2 from2 to2 msg2 mem2):
    exists mem1',
      <<REMOVE1: Memory.remove mem0 loc2 from2 to2 msg2 mem1'>> /\
      <<SPLIT2: Memory.split mem1' loc1 ts11 ts12 ts13 msg12 msg13 mem2>>.
  Proof.
    exploit (@Memory.remove_exists mem0 loc2 from2 to2).
    { hexploit Memory.remove_get0; eauto.
      erewrite Memory.split_o; eauto. repeat condtac; ss.
      { des. subst. congr. }
      { guardH o. des. subst. congr. }
      guardH o. guardH o0. i. des. eauto.
    }
    i. des.
    exploit (@Memory.split_exists mem3 loc1 ts11 ts12 ts13);
      try by inv SPLIT1; inv SPLIT; eauto.
    { erewrite Memory.remove_o; eauto. condtac; ss.
      { des. subst. congr. }
      guardH o. hexploit Memory.split_get0; eauto. i. des. eauto.
    }
    i. des.
    cut (mem4 = mem2); [by i; subst; eauto|].
    apply Memory.ext. i.
    erewrite Memory.split_o; eauto. erewrite Memory.remove_o; eauto.
    erewrite (@Memory.remove_o mem2); eauto. erewrite (@Memory.split_o mem1); eauto.
    repeat (condtac; ss).
    - des. repeat subst. congr.
    - guardH o. des. repeat subst. congr.
  Qed.

  Lemma split_remove_same
        mem0 loc1 ts11 ts12 ts13 msg12 msg13
        mem1 from2 msg2
        mem2
        (SPLIT1: Memory.split mem0 loc1 ts11 ts12 ts13 msg12 msg13 mem1)
        (REMOVE2: Memory.remove mem1 loc1 from2 ts13 msg2 mem2):
    from2 = ts12 /\ msg13 = msg2 /\
    exists mem1',
      <<REMOVE1: Memory.remove mem0 loc1 ts11 ts13 msg13 mem1'>> /\
      <<ADD2: Memory.add mem1' loc1 ts11 ts12 msg12 mem2>>.
  Proof.
    exploit Memory.split_get0; eauto. i. des.
    exploit Memory.remove_get0; eauto. i. des.
    rewrite GET3 in *. inv GET2. splits; auto.
    exploit (@Memory.remove_exists mem0 loc1 ts11 ts13 msg13); eauto. i. des.
    exploit (@Memory.add_exists mem3 loc1 ts11 ts12 msg12); eauto.
    { ii. revert GET2.
      erewrite Memory.remove_o; eauto. condtac; ss. i. des; ss.
      exploit Memory.get_disjoint; [exact GET0|exact GET2|..]. i. des.
      { subst. ss. }
      inv LHS. inv RHS. ss.
      apply (x2 x); econs; ss.
      inv SPLIT1. inv SPLIT.
      etrans; try exact TO. econs; ss. }
    { inv SPLIT1. inv SPLIT. ss. }
    { inv SPLIT1. inv SPLIT. ss. }
    i. des. esplits; eauto.
    cut (mem4 = mem2); [i; subst; eauto|].
    apply Memory.ext. i.
    erewrite Memory.add_o; eauto. erewrite Memory.remove_o; eauto.
    erewrite (@Memory.remove_o mem2); eauto. erewrite (@Memory.split_o mem1); eauto.
    repeat (condtac; ss).
    des. subst. congr.
  Qed.

  Lemma lower_add
        mem0 loc1 from1 to1 msg1 msg1'
        mem1 loc2 from2 to2 msg2
        mem2
        (LOWER1: Memory.lower mem0 loc1 from1 to1 msg1 msg1' mem1)
        (ADD2: Memory.add mem1 loc2 from2 to2 msg2 mem2):
    exists mem1',
      <<ADD1: Memory.add mem0 loc2 from2 to2 msg2 mem1'>> /\
      <<LOWER2: Memory.lower mem1' loc1 from1 to1 msg1 msg1' mem2>> /\
      <<LOCTS: (loc1, to1) <> (loc2, to2)>>.
  Proof.
    exploit (@Memory.add_exists mem0 loc2 from2 to2);
      try by inv ADD2; inv ADD; eauto.
    { apply covered_disjoint_get_disjoint. i. rewrite <- lower_covered in H; eauto.
      eapply get_disjoint_covered_disjoint; eauto. inv ADD2. inv ADD. auto.
    }
    i. des.
    exploit (@Memory.lower_exists mem3 loc1 from1 to1);
      try by inv LOWER1; inv LOWER; eauto.
    { erewrite Memory.add_o; eauto. condtac; ss.
      - des. subst. hexploit Memory.lower_get0; eauto. i. des.
        hexploit Memory.add_get0; eauto. i. des. congr.
      - guardH o. hexploit Memory.lower_get0; eauto. i. des. eauto.
    }
    i. des.
    esplits; eauto; cycle 1.
    { ii. inv H.
      exploit Memory.lower_get0; try exact LOWER1; eauto. i. des.
      exploit Memory.add_get0; eauto. i. des. congr.
    }
    cut (mem4 = mem2); [by i; subst; eauto|].
    apply Memory.ext. i.
    erewrite Memory.lower_o; eauto. erewrite Memory.add_o; eauto.
    erewrite (@Memory.add_o mem2); eauto. erewrite (@Memory.lower_o mem1); eauto.
    repeat (condtac; ss). des. repeat subst.
    exploit Memory.add_get0; try exact ADD2; eauto. i. des.
    revert GET. erewrite Memory.lower_o; eauto. condtac; ss.
  Qed.

  Lemma lower_split
        mem0 loc1 from1 to1 msg1 msg1'
        mem1 loc2 ts21 ts22 ts23 msg22 msg23
        mem2
        (LOWER1: Memory.lower mem0 loc1 from1 to1 msg1 msg1' mem1)
        (SPLIT2: Memory.split mem1 loc2 ts21 ts22 ts23 msg22 msg23 mem2):
    exists from1' msg23' mem1',
      <<SPLIT1: Memory.split mem0 loc2 ts21 ts22 ts23 msg22 msg23' mem1'>> /\
      <<LOWER2: Memory.lower mem1' loc1 from1' to1 msg1 msg1' mem2>> /\
      <<FROM1: __guard__ ((loc1, to1, from1', msg1', msg23') = (loc2, ts23, ts22, msg23, msg1) \/
                          ((loc1, to1) <> (loc2, ts23) /\ (from1', msg23') = (from1, msg23)))>>.
  Proof.
    destruct (loc_ts_eq_dec (loc1, to1) (loc2, ts23)); ss.
    - des. subst.
      exploit Memory.split_get0; eauto. i. des.
      revert GET0. erewrite Memory.lower_o; eauto. condtac; ss; cycle 1.
      { des; congr. }
      i. inv GET0.
      exploit (@Memory.split_exists mem0 loc2 ts21 ts22 ts23);
        try by inv SPLIT2; inv SPLIT; eauto.
      { hexploit Memory.lower_get0; eauto. i. des. eauto. }
      i. des.
      exploit (@Memory.lower_exists mem3 loc2 ts22 ts23);
        try by inv LOWER1; inv LOWER; eauto.
      { erewrite Memory.split_o; eauto. repeat condtac; ss.
        ss. des. subst. inv SPLIT2. inv SPLIT.
        exfalso. eapply Time.lt_strorder. eauto.
      }
      { inv SPLIT2. inv SPLIT. auto. }
      i. des.
      esplits; eauto; cycle 1.
      { left. eauto. }
      cut (mem4 = mem2); [by i; subst; eauto|].
      apply Memory.ext. i.
      erewrite Memory.lower_o; eauto. erewrite Memory.split_o; eauto.
      erewrite (@Memory.split_o mem2); eauto. erewrite (@Memory.lower_o mem1); eauto.
      repeat (condtac; ss).
      des. repeat subst.
      revert GET. erewrite Memory.lower_o; eauto. condtac; ss.
    - guardH o.
      exploit Memory.split_get0; eauto. i. des.
      exploit (@Memory.split_exists mem0 loc2 ts21 ts22 ts23);
        try by inv SPLIT2; inv SPLIT; eauto.
      { revert GET0. erewrite Memory.lower_o; eauto. condtac; eauto.
        ss. i. des. inv GET0. unguardH o. des; congr.
      }
      i. des.
      exploit (@Memory.lower_exists mem3 loc1 from1 to1);
        try by inv LOWER1; inv LOWER; eauto.
      { erewrite Memory.split_o; eauto. repeat condtac; ss.
        - des. subst. hexploit Memory.split_get0; eauto.
          hexploit Memory.lower_get0; eauto. i. des. congr.
        - guardH o0. des. subst.
          unguardH o. des; congr.
        - guardH o0. guardH o1. hexploit Memory.lower_get0; eauto. i. des. eauto.
      }
      i. des.
      esplits; eauto; cycle 1.
      { right. splits; eauto. ii. inv H. unguardH o. des; congr. }
      cut (mem4 = mem2); [by i; subst; eauto|].
      apply Memory.ext. i.
      erewrite Memory.lower_o; eauto. erewrite Memory.split_o; eauto.
      erewrite (@Memory.split_o mem2); eauto. erewrite (@Memory.lower_o mem1); eauto.
      repeat (condtac; ss).
      + des. repeat subst.
        revert GET. erewrite Memory.lower_o; eauto. condtac; ss.
      + guardH o0. des. repeat subst. unguardH o. des; congr.
  Qed.

  Lemma lower_lower
        mem0 loc1 from1 to1 msg1 msg1'
        mem1 loc2 from2 to2 msg2 msg2'
        mem2
        (LOWER1: Memory.lower mem0 loc1 from1 to1 msg1 msg1' mem1)
        (LOWER2: Memory.lower mem1 loc2 from2 to2 msg2 msg2' mem2):
    (loc1 = loc2 /\ from1 = from2 /\ to1 = to2 /\ msg1' = msg2 /\
     Memory.lower mem0 loc1 from1 to1 msg1 msg2' mem2) \/
    (<<LOCTS1: (loc1, to1) <> (loc2, to2)>> /\
     exists mem1',
       <<LOWER1: Memory.lower mem0 loc2 from2 to2 msg2 msg2' mem1'>> /\
       <<LOWER2: Memory.lower mem1' loc1 from1 to1 msg1 msg1' mem2>>).
  Proof.
    exploit Memory.lower_get0; eauto. i. des.
    revert GET. erewrite Memory.lower_o; eauto. condtac; ss.
    - des. subst. i. inv GET. left. splits; eauto.
      inv LOWER1. inv LOWER. inv LOWER2. inv LOWER.
      rewrite LocFun.add_add_eq. econs; auto.
      unfold Cell.lower in *.
      destruct r, r0. ss. subst.
      unfold LocFun.add. condtac; [|congr]. s.
      rewrite DOMap.add_add_eq. econs; auto.
      etrans; eauto.
    - guardH o. i. right. splits.
      { ii. inv H. unguardH o. des; congr. }
      exploit (@Memory.lower_exists mem0 loc2 from2 to2);
        try by inv LOWER2; inv LOWER; eauto.
      i. des.
      exploit (@Memory.lower_exists mem3 loc1 from1 to1);
        try by inv LOWER1; inv LOWER; eauto.
      { erewrite Memory.lower_o; eauto. condtac; ss.
        - des. subst. unguardH o. des; congr.
        - guardH o0. hexploit Memory.lower_get0; try exact LOWER1; eauto. i. des. eauto.
      }
      i. des.
      esplits; eauto.
      cut (mem4 = mem2); [by i; subst; eauto|].
      apply Memory.ext. i.
      erewrite Memory.lower_o; eauto. erewrite Memory.lower_o; eauto.
      erewrite (@Memory.lower_o mem2); eauto. erewrite (@Memory.lower_o mem1); eauto.
      repeat (condtac; ss). des. repeat subst.
      unguardH o. des; congr.
  Qed.

  Lemma lower_remove
        mem0 loc1 from1 to1 msg1 msg1'
        mem1 loc2 from2 to2 msg2
        mem2
        (LOCTS1: (loc1, to1) <> (loc2, to2))
        (LOWER1: Memory.lower mem0 loc1 from1 to1 msg1 msg1' mem1)
        (REMOVE2: Memory.remove mem1 loc2 from2 to2 msg2 mem2):
    exists mem1',
      <<REMOVE1: Memory.remove mem0 loc2 from2 to2 msg2 mem1'>> /\
      <<LOWER2: Memory.lower mem1' loc1 from1 to1 msg1 msg1' mem2>>.
  Proof.
    exploit (@Memory.remove_exists mem0 loc2 from2 to2).
    { hexploit Memory.remove_get0; eauto. i. des.
      revert GET. erewrite Memory.lower_o; eauto. condtac; ss.
      { des. subst. congr. }
      eauto.
    }
    i. des.
    exploit (@Memory.lower_exists mem3 loc1 from1 to1);
      try by inv LOWER1; inv LOWER; eauto.
    { erewrite Memory.remove_o; eauto. condtac; ss.
      { des. subst. congr. }
      inv LOWER1. inv LOWER. eauto.
    }
    i. des.
    cut (mem4 = mem2); [by i; subst; eauto|].
    apply Memory.ext. i.
    erewrite Memory.lower_o; eauto. erewrite Memory.remove_o; eauto.
    erewrite (@Memory.remove_o mem2); eauto. erewrite (@Memory.lower_o mem1); eauto.
    repeat (condtac; ss). des. repeat subst. congr.
  Qed.

  Lemma lower_remove_same
        mem0 loc1 from1 to1 msg1 msg1'
        mem1 from2 msg2
        mem2
        (LOWER1: Memory.lower mem0 loc1 from1 to1 msg1 msg1' mem1)
        (REMOVE2: Memory.remove mem1 loc1 from2 to1 msg2 mem2):
    from1 = from2 /\ msg1' = msg2 /\
    <<REMOVE1: Memory.remove mem0 loc1 from1 to1 msg1 mem2>>.
  Proof.
    exploit Memory.lower_get0; eauto. i. des.
    exploit Memory.remove_get0; eauto. i. des.
    rewrite GET1 in *. inv GET0. splits; auto.
    exploit (@Memory.remove_exists mem0 loc1 from1 to1 msg1); eauto. i. des.
    cut (mem3 = mem2); [i; subst; eauto|].
    apply Memory.ext. i.
    erewrite Memory.remove_o; eauto.
    erewrite (@Memory.remove_o mem2); try exact REMOVE2.
    erewrite (@Memory.lower_o mem1); eauto.
    repeat (condtac; ss).
  Qed.

  Lemma remove_add
        mem0 loc1 from1 to1 msg1
        mem1 loc2 from2 to2 msg2
        mem2
        mem1'
        (REMOVE1: Memory.remove mem0 loc1 from1 to1 msg1 mem1)
        (ADD2: Memory.add mem1 loc2 from2 to2 msg2 mem2)
        (ADD1: Memory.add mem0 loc2 from2 to2 msg2 mem1'):
    Memory.remove mem1' loc1 from1 to1 msg1 mem2.
  Proof.
    exploit Memory.remove_get0; try eexact REMOVE1; eauto. i. des.
    exploit (@Memory.remove_exists mem1' loc1 from1 to1 msg1); eauto.
    { erewrite Memory.add_o; eauto. condtac; ss; eauto.
      des. subst. exploit Memory.add_get0; eauto. i. des. congr.
    }
    i. des.
    cut (mem3 = mem2); [by i; subst|].
    apply Memory.ext. i.
    erewrite Memory.remove_o; eauto. erewrite Memory.add_o; eauto.
    erewrite (@Memory.add_o mem2); eauto. erewrite (@Memory.remove_o mem1); eauto.
    repeat (condtac; ss). des. subst. subst.
    exploit Memory.add_get0; try eexact ADD1; eauto. i. des. congr.
  Qed.

  Lemma remove_split
        mem0 loc1 from1 to1 msg1
        mem1 loc2 ts21 ts22 ts23 msg22 msg23
        mem2
        mem1'
        (REMOVE1: Memory.remove mem0 loc1 from1 to1 msg1 mem1)
        (SPLIT2: Memory.split mem1 loc2 ts21 ts22 ts23 msg22 msg23 mem2)
        (SPLIT1: Memory.split mem0 loc2 ts21 ts22 ts23 msg22 msg23 mem1'):
    Memory.remove mem1' loc1 from1 to1 msg1 mem2.
  Proof.
    exploit Memory.remove_get0; try eexact REMOVE1; eauto. i. des.
    exploit Memory.split_get0; try exact SPLIT1; eauto. i. des.
    exploit (@Memory.remove_exists mem1' loc1 from1 to1 msg1); eauto.
    { erewrite Memory.split_o; eauto. repeat condtac; ss.
      - des. subst. congr.
      - guardH o. des. subst. rewrite GET0 in GET0. inv GET0.
        exploit Memory.split_get0; try exact SPLIT2; eauto. i. des.
        revert GET5. erewrite Memory.remove_o; eauto. condtac; ss.
    }
    i. des.
    cut (mem3 = mem2); [by i; subst|].
    apply Memory.ext. i.
    erewrite Memory.remove_o; eauto. erewrite Memory.split_o; eauto.
    erewrite (@Memory.split_o mem2); eauto. erewrite (@Memory.remove_o mem1); eauto.
    repeat (condtac; ss).
    - des; congr.
    - guardH o. des. subst. rewrite GET in GET2. inv GET2.
      exploit Memory.remove_get0; try exact GET1; eauto. i. des.
      revert GET2. erewrite Memory.split_o; eauto. repeat condtac; ss. i. inv GET2.
      inv SPLIT1. inv SPLIT. exfalso. eapply Time.lt_strorder. eauto.
  Qed.

  Lemma remove_lower
        mem0 loc1 from1 to1 msg1
        mem1 loc2 from2 to2 msg2' msg2
        mem2
        mem1'
        (REMOVE1: Memory.remove mem0 loc1 from1 to1 msg1 mem1)
        (LOWER2: Memory.lower mem1 loc2 from2 to2 msg2' msg2 mem2)
        (LOWER1: Memory.lower mem0 loc2 from2 to2 msg2' msg2 mem1'):
    Memory.remove mem1' loc1 from1 to1 msg1 mem2.
  Proof.
    exploit Memory.remove_get0; try eexact REMOVE1; eauto. i. des.
    exploit (@Memory.remove_exists mem1' loc1 from1 to1 msg1); eauto.
    { erewrite Memory.lower_o; eauto. condtac; ss.
      des. subst.
      exploit Memory.lower_get0; try exact LOWER2; eauto. i. des.
      revert GET1. erewrite Memory.remove_o; eauto. condtac; ss.
    }
    i. des.
    cut (mem3 = mem2); [by i; subst|].
    apply Memory.ext. i.
    erewrite Memory.remove_o; eauto. erewrite Memory.lower_o; eauto.
    erewrite (@Memory.lower_o mem2); eauto. erewrite (@Memory.remove_o mem1); eauto.
    repeat (condtac; ss). des. repeat subst.
    exploit Memory.lower_get0; try exact LOWER2; eauto. i. des.
    revert GET1. erewrite Memory.remove_o; eauto. condtac; ss.
  Qed.

  Lemma remove_remove
        promises0 loc1 from1 to1 msg1
        promises1 loc2 from2 to2 msg2
        promises2
        (REMOVE1: Memory.remove promises0 loc1 from1 to1 msg1 promises1)
        (REMOVE2: Memory.remove promises1 loc2 from2 to2 msg2 promises2):
    exists promises1',
      <<REMOVE1: Memory.remove promises0 loc2 from2 to2 msg2 promises1'>> /\
      <<REMOVE2: Memory.remove promises1' loc1 from1 to1 msg1 promises2>>.
  Proof.
    exploit Memory.remove_get0; try apply REMOVE2; eauto. i. des.
    revert GET. erewrite Memory.remove_o; eauto. condtac; ss. guardH o. i.
    exploit Memory.remove_exists; eauto. i. des.
    hexploit Memory.remove_get0; try apply REMOVE1; eauto. i. des.
    exploit (@Memory.remove_exists mem2 loc1 from1 to1 msg1); eauto.
    { erewrite Memory.remove_o; eauto. condtac; ss. des. subst. congr. }
    i. des.
    esplits; eauto.
    cut (mem0 = promises2); [by i; subst|].
    apply Memory.ext. i.
    erewrite Memory.remove_o; eauto. erewrite Memory.remove_o; eauto.
    erewrite (@Memory.remove_o promises2); eauto. erewrite (@Memory.remove_o promises1); eauto.
    repeat (condtac; ss).
  Qed.


  (* Lemmas on promise *)

  Lemma promise_add_remove
        loc1 from1 to1 msg1
        loc2 from2 to2 msg2
        promises0 mem0
        promises1 mem1
        promises2
        (LOCTS1: (loc1, to1) <> (loc2, to2))
        (PROMISE1: Memory.promise promises0 mem0 loc1 from1 to1 msg1 promises1 mem1 Memory.op_kind_add)
        (REMOVE2: Memory.remove promises1 loc2 from2 to2 msg2 promises2):
    exists promises1',
      <<REMOVE1: Memory.remove promises0 loc2 from2 to2 msg2 promises1'>> /\
      <<PROMISE2: Memory.promise promises1' mem0 loc1 from1 to1 msg1 promises2 mem1 Memory.op_kind_add>>.
  Proof.
    inv PROMISE1.
    exploit add_remove; try exact PROMISES; eauto. i. des.
    esplits; eauto.
  Qed.

  Lemma promise_split_remove
        loc1 from1 to1 msg1
        loc2 from2 to2 msg2
        to3 msg3
        promises0 mem0
        promises1 mem1
        promises2
        (LOCTS1: (loc1, to1) <> (loc2, to2))
        (LOCTS2: (loc1, to3) <> (loc2, to2))
        (PROMISE1: Memory.promise promises0 mem0 loc1 from1 to1 msg1 promises1 mem1 (Memory.op_kind_split to3 msg3))
        (REMOVE2: Memory.remove promises1 loc2 from2 to2 msg2 promises2):
    exists promises1',
      <<REMOVE1: Memory.remove promises0 loc2 from2 to2 msg2 promises1'>> /\
      <<PROMISE2: Memory.promise promises1' mem0 loc1 from1 to1 msg1 promises2 mem1 (Memory.op_kind_split to3 msg3)>>.
  Proof.
    inv PROMISE1.
    exploit split_remove; try exact PROMISES; eauto. i. des.
    esplits; eauto.
  Qed.

  Lemma promise_lower_remove
        loc1 from1 to1 msg0 msg1
        loc2 from2 to2 msg2
        promises0 mem0
        promises1 mem1
        promises2
        (LOCTS1: (loc1, to1) <> (loc2, to2))
        (PROMISE1: Memory.promise promises0 mem0 loc1 from1 to1 msg1 promises1 mem1 (Memory.op_kind_lower msg0))
        (REMOVE2: Memory.remove promises1 loc2 from2 to2 msg2 promises2):
    exists promises1',
      <<REMOVE1: Memory.remove promises0 loc2 from2 to2 msg2 promises1'>> /\
      <<PROMISE2: Memory.promise promises1' mem0 loc1 from1 to1 msg1 promises2 mem1 (Memory.op_kind_lower msg0)>>.
  Proof.
    inv PROMISE1.
    exploit lower_remove; try exact PROMISES; eauto. i. des.
    esplits; eauto.
  Qed.

  Lemma remove_promise
        promises1 loc1 from1 to1 msg1
        promises2 loc2 from2 to2 msg2
        promises3
        mem1 mem3
        kind
        (LE: Memory.le promises1 mem1)
        (REMOVE: Memory.remove promises1 loc1 from1 to1 msg1 promises2)
        (PROMISE: Memory.promise promises2 mem1 loc2 from2 to2 msg2 promises3 mem3 kind):
    exists promises2',
      Memory.promise promises1 mem1 loc2 from2 to2 msg2 promises2' mem3 kind /\
      Memory.remove promises2' loc1 from1 to1 msg1 promises3.
  Proof.
    inv PROMISE.
    - exploit Memory.add_exists_le; eauto. i. des.
      exploit remove_add; eauto.
    - exploit Memory.split_get0; try eexact PROMISES; eauto. i. des.
      revert GET0. erewrite Memory.remove_o; eauto. condtac; ss. i. guardH o.
      exploit Memory.split_exists; try exact GET0; try by inv PROMISES; inv SPLIT; eauto. i. des.
      exploit remove_split; eauto. i.
      esplits; eauto.
    - exploit Memory.lower_get0; try eexact PROMISES; eauto. i. des.
      revert GET. erewrite Memory.remove_o; eauto. condtac; ss. i. guardH o.
      exploit Memory.lower_exists; try exact GET; try by inv PROMISES; inv LOWER; eauto. i. des.
      exploit remove_lower; eauto. i.
      esplits; eauto.
    - exploit remove_remove; try exact REMOVE; eauto. i. des. eauto.
  Qed.

  Lemma promise_add_promise_split_same
        promises0 mem0 loc ts1 ts2 ts3 msg2 msg3
        promises1 mem1
        promises2 mem2
        (ADD1: Memory.promise promises0 mem0 loc ts1 ts3 msg3 promises1 mem1 Memory.op_kind_add)
        (SPLIT2: Memory.promise promises1 mem1 loc ts1 ts2 msg2 promises2 mem2 (Memory.op_kind_split ts3 msg3)):
    exists promises1' mem1',
      <<ADD1: Memory.promise promises0 mem0 loc ts1 ts2 msg2 promises1' mem1' Memory.op_kind_add>> /\
      <<ADD2: Memory.promise promises1' mem1' loc ts2 ts3 msg3 promises2 mem2 Memory.op_kind_add>>.
  Proof.
    inv ADD1. inv SPLIT2.
    exploit add_split; try exact PROMISES; eauto. i. des; [|congr].
    exploit add_split; try exact MEM; eauto. i. des; [|congr].
    esplits.
    - econs; eauto.
      + i. subst. congr.
      + i. exploit Memory.add_get0; try exact MEM. i. des.
        exploit Memory.add_get1; try exact GET; try exact MEM. i.
        exploit Memory.get_ts; try exact GET1. i. des.
        { subst. inv ADD3. inv ADD. inv TO. }
        exploit Memory.get_ts; try exact x8. i. des.
        { subst. inv ADD0. inv ADD. inv TO. }
        exploit Memory.get_disjoint; [exact GET1|exact x8|..]. i. des.
        { subst. inv ADD0. inv ADD. timetac. }
        destruct (TimeFacts.le_lt_dec ts3 to').
        * apply (x11 ts3); econs; ss; try refl.
          inv ADD3. inv ADD. ss.
        * apply (x11 to'); econs; ss; try refl.
          { etrans; try exact x10. inv ADD0. inv ADD. ss. }
          { econs. ss. }
    - econs; eauto.
      + i. subst.
        exploit Memory.add_get0; try exact ADD0. i. des. eauto.
      + i. revert GET.
        erewrite Memory.add_o; eauto. condtac; ss; eauto.
        i. des. subst. inv GET. inv MEM. inv ADD. timetac.
  Qed.

  Lemma promise_split_promise_split_same
        promises0 mem0 loc ts1 ts2 ts3 ts4 val2 released2 msg3 msg4
        promises1 mem1
        promises2 mem2
        (SPLIT1: Memory.promise promises0 mem0 loc ts1 ts3 msg3 promises1 mem1 (Memory.op_kind_split ts4 msg4))
        (SPLIT2: Memory.promise promises1 mem1 loc ts1 ts2 (Message.full val2 released2) promises2 mem2 (Memory.op_kind_split ts3 msg3)):
    exists promises1' mem1',
      <<SPLIT1: Memory.promise promises0 mem0 loc ts1 ts2 (Message.full val2 released2) promises1' mem1' (Memory.op_kind_split ts4 msg4)>> /\
      <<SPLIT2: Memory.promise promises1' mem1' loc ts2 ts3 msg3 promises2 mem2 (Memory.op_kind_split ts4 msg4)>>.
  Proof.
    assert (LOCTS: (loc, ts4) <> (loc, ts3)).
    { intro X. inv X. inv SPLIT1. inv MEM. inv SPLIT. timetac. }
    inv SPLIT1. inv SPLIT2.
    exploit split_split; try exact PROMISES; eauto. i. des; [|congr].
    exploit split_split; try exact MEM; eauto. i. des; [|congr].
    esplits.
    - econs; eauto; congr.
    - econs; eauto.
  Qed.

  Lemma promise_lower_promise_split_same
        promises0 mem0 loc ts1 ts2 ts3 msg0 val2 released2 msg3
        promises1 mem1
        promises2 mem2
        (LOWER1: Memory.promise promises0 mem0 loc ts1 ts3 msg3 promises1 mem1 (Memory.op_kind_lower msg0))
        (SPLIT2: Memory.promise promises1 mem1 loc ts1 ts2 (Message.full val2 released2) promises2 mem2 (Memory.op_kind_split ts3 msg3)):
    exists promises1' mem1',
      <<SPLIT1: Memory.promise promises0 mem0 loc ts1 ts2 (Message.full val2 released2) promises1' mem1' (Memory.op_kind_split ts3 msg0)>> /\
      <<LOWER2: Memory.promise promises1' mem1' loc ts2 ts3 msg3 promises2 mem2 (Memory.op_kind_lower msg0)>>.
  Proof.
    inv LOWER1. inv SPLIT2.
    exploit lower_split; try exact PROMISES; eauto. i. des.
    unguard. des; [|congr]. inv FROM1.
    exploit lower_split; try exact MEM; eauto. i. des.
    unguard. des; [|congr]. inv FROM1.
    esplits.
    - econs; eauto; congr.
    - econs; eauto.
  Qed.
End MemoryReorder.
