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

Set Implicit Arguments.


(* promotion *)

Fixpoint promote_stmt (l: Loc.t) (r: Reg.t) (stmt: Stmt.t): list Stmt.t :=
  match stmt with
  | Stmt.instr (Instr.load lhs rhs _) =>
    if Loc.eq_dec rhs l
    then [Stmt.instr (Instr.assign lhs (Instr.expr_val (Value.reg r)))]
    else [stmt]
  | Stmt.instr (Instr.store lhs rhs _) =>
    if Loc.eq_dec lhs l
    then [Stmt.instr (Instr.assign r rhs)]
    else [stmt]
  | Stmt.instr (Instr.update lhs loc (Instr.fetch_add addendum) _ _) =>
    if Loc.eq_dec loc l
    then [Stmt.instr (Instr.assign r (Instr.expr_op2 Op2.add (Value.reg r) addendum));
            Stmt.instr (Instr.assign lhs (Instr.expr_val (Value.reg r)))]
    else [stmt]
  | Stmt.instr (Instr.update lhs loc (Instr.cas old new) _ _) =>
    if Loc.eq_dec loc l
    then [Stmt.ite
            (Instr.expr_op2 Op2.eq (Value.reg r) old)
            [Stmt.instr (Instr.assign r new);
               Stmt.instr (Instr.assign lhs (Instr.expr_val (Value.const 1)))]
            [Stmt.instr (Instr.assign lhs (Instr.expr_val (Value.const 0)))]
         ]
    else [stmt]
  | Stmt.ite cond stmts1 stmts2 =>
    [Stmt.ite cond
              (List.fold_right (@List.app _) [] (List.map (promote_stmt l r) stmts1))
              (List.fold_right (@List.app _) [] (List.map (promote_stmt l r) stmts2))]
  | Stmt.dowhile stmts cond =>
    [Stmt.dowhile
       (List.fold_right (@List.app _) [] (List.map (promote_stmt l r) stmts))
       cond]
  | _ => [stmt]
  end.

Definition promote_stmts (l: Loc.t) (r: Reg.t) (stmts: list Stmt.t): list Stmt.t :=
  List.fold_right (@List.app _) [] (List.map (promote_stmt l r) stmts).


(* loc_free *)

Definition loc_free_instr (l: Loc.t) (i: Instr.t): Prop :=
  match i with
  | Instr.load _ loc _
  | Instr.store loc _ _
  | Instr.update _ loc _ _ _ => loc <> l
  | _ => true
  end.

Inductive loc_free_stmt (l: Loc.t): forall (stmt: Stmt.t), Prop :=
| loc_free_stmt_instr
    i
    (LOCFREE: loc_free_instr l i):
    loc_free_stmt l (Stmt.instr i)
| loc_free_stmt_ite
    cond stmts1 stmts2
    (LOCFREE1: List.Forall (loc_free_stmt l) stmts1)
    (LOCFREE2: List.Forall (loc_free_stmt l) stmts2):
    loc_free_stmt l (Stmt.ite cond stmts1 stmts2)
| loc_free_stmt_dowhile
    stmts cond
    (LOCFREE: List.Forall (loc_free_stmt l) stmts):
    loc_free_stmt l (Stmt.dowhile stmts cond)
.
Hint Constructors loc_free_stmt.

Definition loc_free_stmts (l: Loc.t) (stmts: list Stmt.t): Prop :=
  List.Forall (loc_free_stmt l) stmts.


(* reg_free *)

Inductive reg_free_stmt (r: Reg.t): forall (stmt: Stmt.t), Prop :=
| reg_free_stmt_instr
    i
    (REGFREE: RegSet.disjoint (RegSet.singleton r) (Instr.regs_of i)):
    reg_free_stmt r (Stmt.instr i)
| reg_free_stmt_ite
    cond stmts1 stmts2
    (REGFREE0: RegSet.disjoint (RegSet.singleton r) (Instr.regs_of_expr cond))
    (REGFREE1: List.Forall (reg_free_stmt r) stmts1)
    (REGFREE2: List.Forall (reg_free_stmt r) stmts2):
    reg_free_stmt r (Stmt.ite cond stmts1 stmts2)
| reg_free_stmt_dowhile
    stmts cond
    (REGFREE1: List.Forall (reg_free_stmt r) stmts)
    (REGFREE2: RegSet.disjoint (RegSet.singleton r) (Instr.regs_of_expr cond)):
    reg_free_stmt r (Stmt.dowhile stmts cond)
.

Definition reg_free_stmts (r: Reg.t) (stmts: list Stmt.t): Prop :=
  List.Forall (reg_free_stmt r) stmts.


Lemma promote_stmts_cons l r stmt stmts:
  promote_stmts l r (stmt :: stmts) =
  (promote_stmt l r stmt) ++ (promote_stmts l r stmts).
Proof.
  unfold promote_stmts. ss.
Qed.

Lemma promote_stmts_app l r stmts1 stmts2:
  promote_stmts l r (stmts1 ++ stmts2) =
  (promote_stmts l r stmts1) ++ (promote_stmts l r stmts2).
Proof.
  induction stmts1; ss.
  repeat rewrite promote_stmts_cons.
  rewrite IHstmts1.
  apply List.app_assoc.
Qed.

Lemma promote_stmt_loc_free l r stmt:
  loc_free_stmts l (promote_stmt l r stmt).
Proof.
  revert stmt. apply Stmt.ind; i.
  - destruct i; ss; try by repeat (econs; ss).
    + condtac; ss; repeat econs; ss.
    + condtac; ss; repeat econs; ss.
    + destruct rmw; ss.
      * condtac; ss; repeat econs; ss.
      * condtac; ss; repeat econs; ss.
  - ss. repeat econs; ss.
    + induction c1; ss.
      inv THEN. apply Forall_app; eauto.
    + induction c2; ss.
      inv ELSE. apply Forall_app; eauto.
  - ss. repeat econs; ss.
    induction c; ss.
    inv LOOP. apply Forall_app; eauto.
Qed.

Lemma promote_stmts_loc_free l r stmts:
  loc_free_stmts l (promote_stmts l r stmts).
Proof.
  unfold promote_stmts.
  induction stmts; ss; i.
  apply Forall_app; ss.
  apply promote_stmt_loc_free.
Qed.

Lemma promote_stmts_cases
      l r stmts_src stmts_tgt
      (PROMOTE: stmts_tgt = promote_stmts l r stmts_src):
  <<NIL: stmts_src = [] /\ stmts_tgt = []>> \/
  <<LOAD: exists lhs ord stmts'_src stmts'_tgt,
    <<STMTS_SRC: stmts_src = (Stmt.instr (Instr.load lhs l ord)) :: stmts'_src>> /\
    <<STMTS_TGT: stmts_tgt = (Stmt.instr (Instr.assign lhs (Instr.expr_val (Value.reg r)))) :: stmts'_tgt>> /\
    <<STMTS: stmts'_tgt = promote_stmts l r stmts'_src>>>> \/
  <<STORE: exists rhs ord stmts'_src stmts'_tgt,
    <<STMTS_SRC: stmts_src = (Stmt.instr (Instr.store l rhs ord)) :: stmts'_src>> /\
    <<STMTS_TGT: stmts_tgt = (Stmt.instr (Instr.assign r rhs)) :: stmts'_tgt>> /\
    <<STMTS: stmts'_tgt = promote_stmts l r stmts'_src>>>> \/
  <<FA: exists lhs addendum ordr ordw stmts'_src stmts'_tgt,
    <<STMTS_SRC: stmts_src = (Stmt.instr (Instr.update lhs l (Instr.fetch_add addendum) ordr ordw)) :: stmts'_src>> /\
    <<STMTS_TGT: stmts_tgt =
                 [Stmt.instr (Instr.assign r (Instr.expr_op2 Op2.add (Value.reg r) addendum));
                    Stmt.instr (Instr.assign lhs (Instr.expr_val (Value.reg r)))] ++ stmts'_tgt>> /\
    <<STMTS: stmts'_tgt = promote_stmts l r stmts'_src>>>> \/
  <<CAS: exists lhs old new ordr ordw stmts'_src stmts'_tgt,
    <<STMTS_SRC: stmts_src = (Stmt.instr (Instr.update lhs l (Instr.cas old new) ordr ordw)) :: stmts'_src>> /\
    <<STMTS_TGT: stmts_tgt =
                 [Stmt.ite
                    (Instr.expr_op2 Op2.eq (Value.reg r) old)
                    [Stmt.instr (Instr.assign r new);
                       Stmt.instr (Instr.assign lhs (Instr.expr_val (Value.const 1)))]
                    [Stmt.instr (Instr.assign lhs (Instr.expr_val (Value.const 0)))]
                 ] ++ stmts'_tgt>> /\
    <<STMTS: stmts'_tgt = promote_stmts l r stmts'_src>>>> \/
  <<ITE: exists cond stmts1 stmts2 stmts'_src stmts'_tgt,
    <<STMTS_SRC: stmts_src = (Stmt.ite cond stmts1 stmts2) :: stmts'_src>> /\
    <<STMTS_TGT: stmts_tgt = (Stmt.ite cond (promote_stmts l r stmts1) (promote_stmts l r stmts2)) :: stmts'_tgt>> /\
    <<STMTS: stmts'_tgt = promote_stmts l r stmts'_src>>>> \/
  <<DOWHILE: exists stmts cond stmts'_src stmts'_tgt,
    <<STMTS_SRC: stmts_src = (Stmt.dowhile stmts cond) :: stmts'_src>> /\
    <<STMTS_TGT: stmts_tgt = (Stmt.dowhile (promote_stmts l r stmts) cond) :: stmts'_tgt>> /\
    <<STMTS: stmts'_tgt = promote_stmts l r stmts'_src>>>> \/
  <<LOCFREE: exists stmt stmts'_src stmts'_tgt,
    <<STMTS_SRC: stmts_src = stmt :: stmts'_src>> /\
    <<STMTS_TGT: stmts_tgt = stmt :: stmts'_tgt>> /\
    <<STMTS: stmts'_tgt = promote_stmts l r stmts'_src>> /\
    <<STMT: loc_free_stmt l stmt>>>>.
Proof.
  destruct stmts_src as [|stmt stmts'_src]; eauto. right.
  destruct stmt; ss.
  - destruct i.
    + rewrite promote_stmts_cons in PROMOTE. ss. subst.
      repeat right. esplits; eauto. econs. ss.
    + rewrite promote_stmts_cons in PROMOTE. ss. subst.
      repeat right. esplits; eauto. econs. ss.
    + rewrite promote_stmts_cons in PROMOTE. ss. des_ifs; ss.
      * left. esplits; eauto.
      * repeat right. esplits; eauto.
    + rewrite promote_stmts_cons in PROMOTE. ss. des_ifs; ss.
      * right. left. esplits; eauto.
      * repeat right. esplits; eauto.
    + rewrite promote_stmts_cons in PROMOTE. ss. destruct rmw; ss.
      * des_ifs; ss.
        { right. right. left. esplits; eauto. }
        { repeat right. esplits; eauto. }
      * des_ifs; ss.
        { right. right. right. left. esplits; eauto. }
        { repeat right. esplits; eauto. }
    + rewrite promote_stmts_cons in PROMOTE. ss. subst.
      repeat right. esplits; eauto. econs. ss.
    + rewrite promote_stmts_cons in PROMOTE. ss. subst.
      repeat right. esplits; eauto. econs. ss.
    + rewrite promote_stmts_cons in PROMOTE. ss. subst.
      repeat right. esplits; eauto. econs. ss.
  - rewrite promote_stmts_cons in PROMOTE. ss. subst.
    do 4 right. left. esplits; eauto.
  - rewrite promote_stmts_cons in PROMOTE. ss. subst.
    do 5 right. left. esplits; eauto.
Qed.


Lemma step_loc_free
      l e st1 st2
      (LOCFREE: loc_free_stmts l (State.stmts st1))
      (STEP: State.step e st1 st2):
  loc_free_stmts l (State.stmts st2).
Proof.
  inv STEP; ss.
  - inv LOCFREE. ss.
  - inv LOCFREE. condtac.
    + inv H1. eapply Forall_app; eauto.
    + inv H1. eapply Forall_app; eauto.
  - inv LOCFREE. inv H1.
    eapply Forall_app; eauto.
Qed.

Lemma loc_free_step_is_accessing_loc
      l e st1 st2
      (LOCFREE: loc_free_stmts l (State.stmts st1))
      (STEP: State.step (ThreadEvent.get_program_event e) st1 st2):
  ~ ThreadEvent.is_accessing_loc l e.
Proof.
  inv STEP; try (by destruct e); ss.
  inv INSTR; destruct e; ss.
  - inv H2. inv LOCFREE. inv H1. ss.
  - inv H2. inv LOCFREE. inv H1. ss.
  - inv H2. inv LOCFREE. inv H1. ss.
  - inv H2. inv LOCFREE. inv H1. ss.
Qed.


Lemma step_reg_free
      r e st1 st2
      (REGFREE: reg_free_stmts r (State.stmts st1))
      (STEP: State.step e st1 st2):
  reg_free_stmts r (State.stmts st2).
Proof.
  inv STEP; ss.
  - inv REGFREE. ss.
  - inv REGFREE. condtac.
    + inv H1. eapply Forall_app; eauto.
    + inv H1. eapply Forall_app; eauto.
  - inv REGFREE. inv H1.
    eapply Forall_app; eauto.
    repeat (econs; eauto).
Qed.
