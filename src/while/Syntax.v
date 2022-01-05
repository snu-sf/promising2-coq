Require Import RelationClasses.
Require Import List.

From sflib Require Import sflib.

From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.

Require Import Event.

Set Implicit Arguments.

Module Reg := Ident.
Module RegSet := IdentSet.
Module RegMap := IdentMap.
Module RegFun := IdentFun.

Module Value.
  Inductive t :=
  | reg (reg:Reg.t)
  | const (const:Const.t)
  .

  Definition regs_of (v:t): RegSet.t :=
    match v with
    | reg r => RegSet.singleton r
    | const _ => RegSet.empty
    end.

  Fixpoint regs_of_list (l:list t): RegSet.t :=
    match l with
    | nil => RegSet.empty
    | (reg r)::l => RegSet.add r (regs_of_list l)
    | (const _)::l => regs_of_list l
    end.

  Definition of_nat (n:nat): t := const n.
End Value.
Coercion Value.reg: Reg.t >-> Value.t.
Coercion Value.const: Const.t >-> Value.t.
Coercion Value.of_nat: nat >-> Value.t.

Module Op1.
  Inductive t :=
  | not
  .

  Definition eval (op:t) (op1:Const.t): Const.t :=
    match op with
    | not =>
      if Const.eq_dec op1 Const.zero
      then Const.one
      else Const.zero
    end.
End Op1.

Module Op2.
  Inductive t :=
  | add
  | sub
  | mul
  | eq
  .

  Definition const_eq (op1 op2: Const.t): Const.t :=
    if Const.eq_dec op1 op2 then 0 else 1.

  Definition eval (op:t): forall (op1 op2:Const.t), Const.t :=
    match op with
    | add => Const.add
    | sub => Const.sub
    | mul => Const.mul
    | eq => const_eq
    end.
End Op2.

Module Instr.
  Inductive expr :=
  | expr_val (val:Value.t)
  | expr_op1 (op:Op1.t) (op:Value.t)
  | expr_op2 (op:Op2.t) (op1 op2:Value.t)
  .

  Definition regs_of_expr (r:expr): RegSet.t :=
    match r with
    | expr_val val => Value.regs_of val
    | expr_op1 _ op => Value.regs_of op
    | expr_op2 _ op1 op2 => RegSet.union (Value.regs_of op1) (Value.regs_of op2)
    end.

  Inductive rmw :=
  | fetch_add (addendum:Value.t)
  | cas (old new:Value.t)
  .

  Inductive t :=
  | skip
  | assign (lhs:Reg.t) (rhs:expr)
  | load (lhs:Reg.t) (rhs:Loc.t) (ord:Ordering.t)
  | store (lhs:Loc.t) (rhs:Value.t) (ord:Ordering.t)
  | update (lhs:Reg.t) (loc:Loc.t) (rmw:rmw) (ordr ordw:Ordering.t)
  | fence (ordr ordw:Ordering.t)
  | syscall (lhs:Reg.t) (rhses:list Value.t)
  | abort
  .

  Definition regs_of_rmw (rmw:rmw): RegSet.t :=
    match rmw with
    | fetch_add addendum => (Value.regs_of addendum)
    | cas old new => RegSet.union (Value.regs_of old) (Value.regs_of new)
    end.

  Definition regs_of (i:t): RegSet.t :=
    match i with
    | skip => RegSet.empty
    | assign reg rhs => RegSet.add reg (regs_of_expr rhs)
    | load reg _ _ => RegSet.singleton reg
    | store _ val _ => Value.regs_of val
    | update reg _ rmw _ _ => RegSet.add reg (regs_of_rmw rmw)
    | fence _ _ => RegSet.empty
    | syscall lhs rhses => RegSet.add lhs (Value.regs_of_list rhses)
    | abort => RegSet.empty
    end.

  Inductive ord: forall (i_src i_tgt:Instr.t), Prop :=
  | ord_skip:
      ord Instr.skip Instr.skip
  | ord_assign
      r e:
      ord (Instr.assign r e) (Instr.assign r e)
  | ord_load
      r l o1 o2 (O: Ordering.le o1 o2):
      ord (Instr.load r l o1) (Instr.load r l o2)
  | ord_store
      l v o1 o2 (O: Ordering.le o1 o2):
      ord (Instr.store l v o1) (Instr.store l v o2)
  | ord_update
      r l rmw or1 or2 ow1 ow2
      (OR: Ordering.le or1 or2)
      (OW: Ordering.le ow1 ow2):
      ord (Instr.update r l rmw or1 ow1) (Instr.update r l rmw or2 ow2)
  | ord_fence
      or1 or2 ow1 ow2
      (OR: Ordering.le or1 or2)
      (OW: Ordering.le ow1 ow2):
      ord (Instr.fence or1 ow1) (Instr.fence or2 ow2)
  | ord_syscall
      o i:
      ord (Instr.syscall o i) (Instr.syscall o i)
  | ord_abort:
      ord Instr.abort Instr.abort
  .

  Global Program Instance instr_ord_Reflexive: Reflexive ord.
  Next Obligation. destruct x; econs; refl. Qed.

  Lemma ord_regs_of
        instr_src instr_tgt
        (ORD: ord instr_src instr_tgt):
    Instr.regs_of instr_src = Instr.regs_of instr_tgt.
  Proof. inv ORD; auto. Qed.
End Instr.
Coercion Instr.expr_val: Value.t >-> Instr.expr.

Module Stmt.
  Inductive t :=
  | instr (i:Instr.t)
  | ite (cond:Instr.expr) (c1 c2:list t)
  | dowhile (c:list t) (cond:Instr.expr)
  .

  Lemma ind
        (P: Stmt.t -> Prop)
        (INSTR: forall i, P (Stmt.instr i))
        (ITE: forall cond c1 c2 (THEN: List.Forall P c1) (ELSE: List.Forall P c2), P (Stmt.ite cond c1 c2))
        (WHILE: forall c cond (LOOP: List.Forall P c), P (Stmt.dowhile c cond)):
    forall stmt, P stmt.
  Proof.
    fix IH 1.
    i. destruct stmt.
    - eapply INSTR.
    - eapply ITE.
      + induction c1; ss.
        econs; eauto.
      + induction c2; ss.
        econs; eauto.
    - eapply WHILE.
      induction c; ss.
      econs; eauto.
  Qed.
End Stmt.
Coercion Stmt.instr: Instr.t >-> Stmt.t.
