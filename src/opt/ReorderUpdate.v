Require Import Basics.
Require Import Bool.
Require Import List.

Require Import sflib.
Require Import paco.
Require Import respectful5.

Require Import Basic.
Require Import Event.
Require Import Language.
Require Import Time.
Require Import Memory.
Require Import Commit.
Require Import Thread.

Require Import Configuration.
Require Import Simulation.
Require Import Compatibility.
Require Import MemInv.
Require Import ReorderBase.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Inductive reorder_update r1 l1 rmw1 or1 ow1: forall (i2:Instr.t), Prop :=
| reorder_update_load
    r2 l2 o2
    (ORDR1: Ordering.le or1 Ordering.acqrel)
    (ORDW1: Ordering.le ow1 Ordering.relaxed)
    (ORD2: Ordering.le o2 Ordering.relaxed)
    (LOC: l1 <> l2)
    (REGS: RegSet.disjoint (Instr.regs_of (Instr.update r1 l1 rmw1 or1 ow1))
                           (Instr.regs_of (Instr.load r2 l2 o2))):
    reorder_update r1 l1 rmw1 or1 ow1 (Instr.load r2 l2 o2)
| reorder_update_store
    l2 v2 o2
    (ORDR1: Ordering.le or1 Ordering.acqrel)
    (ORDW1: Ordering.le ow1 Ordering.relaxed)
    (LOC: l1 <> l2)
    (REGS: RegSet.disjoint (Instr.regs_of (Instr.update r1 l1 rmw1 or1 ow1))
                           (Instr.regs_of (Instr.store l2 v2 o2))):
    reorder_update r1 l1 rmw1 or1 ow1 (Instr.store l2 v2 o2)
| reorder_update_update
    r2 l2 rmw2 or2 ow2
    (ORDR1: Ordering.le or1 Ordering.acqrel)
    (ORDW1: Ordering.le ow1 Ordering.relaxed)
    (ORDR2: Ordering.le or2 Ordering.relaxed)
    (ORDW2: Ordering.le ow2 Ordering.acqrel)
    (LOC: l1 <> l2)
    (REGS: RegSet.disjoint (Instr.regs_of (Instr.update r1 l1 rmw1 or1 ow1))
                           (Instr.regs_of (Instr.update r2 l2 rmw2 or2 ow2))):
    reorder_update r1 l1 rmw1 or1 ow1 (Instr.update r2 l2 rmw2 or2 ow2)
.

Inductive sim_update: forall (st_src:lang.(Language.state)) (th_src:Local.t) (mem_k_src:Memory.t)
                        (st_tgt:lang.(Language.state)) (th_tgt:Local.t) (mem_k_tgt:Memory.t), Prop :=
| sim_update_intro
    r1 l1 from1 to1 vr1 vret1 vw1 releasedr1 releasedw1 rmw1 or1 ow1 i2
    rs th1_src th1_tgt th2_src th3_src
    mem_k_src mem_k_tgt
    (REORDER: reorder_update r1 l1 rmw1 or1 ow1 i2)
    (RMW: RegFile.eval_rmw rs rmw1 vr1 = (vret1, vw1))
    (READ: Local.read_step th1_src mem_k_src l1 from1 vr1 releasedr1 or1 th2_src)
    (FULFILL: Local.fulfill_step th2_src mem_k_src l1 from1 to1 vw1 releasedw1 ow1 th3_src)
    (RELEASED: Snapshot.le releasedr1 releasedw1)
    (LOCAL: sim_local th3_src th1_tgt):
    sim_update
      (State.mk rs [Stmt.instr i2; Stmt.instr (Instr.update r1 l1 rmw1 or1 ow1)]) th1_src mem_k_src
      (State.mk (RegFun.add r1 vret1 rs) [Stmt.instr i2]) th1_tgt mem_k_tgt
.

Lemma sim_update_sim_thread:
  sim_update <6= (sim_thread (sim_terminal eq)).
Proof.
  pcofix CIH. i. pfold. ii. ss. splits; ss.
  - i. inv TERMINAL_TGT. inv PR; ss.
  - i. inv PR. eapply sim_local_future; try apply LOCAL; eauto.
    + exploit Local.read_step_future; try apply WF_SRC; i.
      { eapply Local.future_read_step; eauto. }
      eapply Local.fulfill_step_future; eauto.
      eapply Local.future_fulfill_step; eauto.
    + exploit Local.read_step_future; try apply WF_SRC0; i.
      { eapply Local.future_read_step; eauto.
        eapply Local.future_read_step; eauto.
      }
      eapply Local.fulfill_step_future; try apply x0.
      eapply Local.future_fulfill_step; eauto.
      eapply Local.future_fulfill_step; eauto.
  - admit. (* promise *)
  - inv PR. i. inv STEP_TGT; [|by inv STEP; inv STATE; inv INSTR; inv REORDER].
    exploit Local.future_read_step; try apply READ; eauto. i.
    exploit Local.future_fulfill_step; try apply FULFILL; eauto. i.
    inv STEP; try (inv STATE; inv INSTR; inv REORDER); ss.
    + (* promise *)
      exploit sim_local_promise; eauto.
      { eapply Local.fulfill_step_future; eauto.
        eapply Local.read_step_future; eauto.
      }
      i. des.
      exploit sim_local_fulfill; try apply x3; try reflexivity; eauto.
      { eapply Local.read_step_future; eauto. }
      { eapply Local.read_step_future; eauto. }
      i. des.
      exploit reorder_fulfill_promise; try apply x3; try apply STEP_SRC; eauto.
      { eapply Local.read_step_future; eauto. }
      i. des.
      exploit reorder_read_promise; try apply x0; try apply STEP1; eauto. i. des.
      i. des.
      eexists _, _, _, _, _, _. splits; eauto.
      * econs. econs 1; eauto.
      * right. apply CIH. econs; try apply STEP3; try apply STEP_SRC0; eauto.
    + (* load *)
      exploit sim_local_read; eauto.
      { eapply Local.fulfill_step_future; eauto.
        eapply Local.read_step_future; eauto.
      }
      i. des.
      exploit reorder_fulfill_read; try apply x3; try apply STEP_SRC; eauto.
      { eapply Local.read_step_future; eauto. }
      i. des.
      exploit reorder_read_read; try apply x0; try apply STEP1; eauto. i. des.
      eexists _, _, _, _, _, _. splits.
      * econs 2; [|econs 1]. econs 3; eauto. econs. econs.
      * econs. econs 5; eauto.
        { econs. econs. erewrite RegFile.eq_except_rmw; eauto.
          - admit. (* disjoint add => disjoint *)
          - apply RegFile.eq_except_singleton.
        }
        { s. econs 1; eauto.
          i. rewrite ORDW1 in H. inv H.
        }
      * s. eauto.
      * s. left. eapply paco7_mon; [apply sim_stmts_nil|]; ss.
        apply RegFun.add_add. admit. (* singleton disjoint => neq *)
    + (* store *)
      exploit sim_local_write; eauto.
      { eapply Local.fulfill_step_future; eauto.
        eapply Local.read_step_future; eauto.
      }
      i. des.
      exploit reorder_fulfill_write; try apply x3; try apply STEP_SRC; eauto.
      { eapply Local.read_step_future; eauto. }
      i. des.
      exploit reorder_read_write; try apply x0; try apply STEP1; eauto.
      { i. rewrite ORDR1 in H0. inv H0. }
      i. des.
      eexists _, _, _, _, _, _. splits.
      * econs 2; [|econs 1]. econs 4; eauto. econs.
        erewrite <- RegFile.eq_except_value; eauto.
        { econs. }
        { admit. (* eq_except *) }
      * econs. econs 5; eauto.
        { econs. econs. eauto. }
        { s. econs 1; eauto.
          i. rewrite ORDW1 in H. inv H.
        }
      * s. eauto.
      * s. left. eapply paco7_mon; [apply sim_stmts_nil|]; ss.
    + (* update *)
      exploit sim_local_read; eauto.
      { eapply Local.fulfill_step_future; eauto.
        eapply Local.read_step_future; eauto.
      }
      i. des.
      exploit sim_local_write; eauto.
      { eapply Local.read_step_future; eauto.
        eapply Local.fulfill_step_future; eauto.
        eapply Local.read_step_future; eauto.
      }
      { eapply Local.read_step_future; eauto. }
      i. des.
      exploit reorder_fulfill_read; try apply x3; try apply STEP_SRC; eauto.
      { eapply Local.read_step_future; eauto. }
      i. des.
      exploit reorder_read_read; try apply x0; try apply STEP1; eauto. i. des.
      exploit reorder_fulfill_write; try apply STEP2; try apply STEP_SRC1; eauto.
      { eapply Local.read_step_future; eauto.
        eapply Local.read_step_future; eauto.
      }
      i. des.
      exploit reorder_read_write; try apply STEP3; try apply STEP4; eauto.
      { i. rewrite ORDR1 in H0. inv H0. }
      { eapply Local.read_step_future; eauto. }
      i. des.
      eexists _, _, _, _, _, _. splits.
      * econs 2; [|econs 1]. econs 5; eauto. econs. econs.
        erewrite <- RegFile.eq_except_rmw; eauto.
        { admit. (* disjoint add => disjoint *) }
        { apply RegFile.eq_except_singleton. }
      * econs. econs 5; try apply STEP7; try apply STEP_SRC0; eauto.
        { econs. econs.
          erewrite RegFile.eq_except_rmw; eauto.
          - admit. (* disjoint add => disjoint *)
          - apply RegFile.eq_except_singleton.
        }
        { econs 1; eauto.
          i. rewrite ORDW1 in H. inv H.
        }
      * eauto.
      * left. eapply paco7_mon; [apply sim_stmts_nil|]; ss.
        apply RegFun.add_add. admit. (* singleton disjoint => neq *)
Admitted.