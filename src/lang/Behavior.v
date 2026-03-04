From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.

Require Import lang.Event.
From PromisingLib Require Import Language.
Require Import lang.View.
Require Import lang.Cell.
Require Import lang.Memory.
Require Import lang.TView.
Require Import lang.Local.
Require Import lang.Thread.
Require Import lang.Configuration.

Set Implicit Arguments.

(* NOTE: We currently consider only finite behaviors of program: we
 * ignore non-terminating executions.  This simplification affects two
 * aspects of the development:
 *
 * - Liveness.  In our definition, the liveness matters only for
 *   non-terminating execution.
 *
 * - Simulation.  We do not introduce simulation index for inftau
 *   behaviors (i.e. infinite loop without system call interactions).
 *
 * We will consider infinite behaviors in the future work.
 *)
(* NOTE: We serialize all the events within a behavior, but it may not
 * be the case.  The *NIX kernels are re-entrant: system calls may
 * race.
 *)

Inductive behaviors
          (step: forall (e:MachineEvent.t) (tid:Ident.t) (c1 c2:Configuration.t), Prop):
  forall (conf:Configuration.t) (b:list Event.t), Prop :=
| behaviors_nil
    c
    (TERMINAL: Configuration.is_terminal c):
    behaviors step c nil
| behaviors_syscall
    e tid c1 c2 beh
    (STEP: step (MachineEvent.syscall e) tid c1 c2)
    (NEXT: behaviors step c2 beh):
    behaviors step c1 (e::beh)
| behaviors_failure
    tid c1 c2 beh
    (STEP: step MachineEvent.failure tid c1 c2):
    behaviors step c1 beh
| behaviors_tau
    tid c1 c2 beh
    (STEP: step MachineEvent.silent tid c1 c2)
    (NEXT: behaviors step c2 beh):
    behaviors step c1 beh
.

Lemma rtc_tau_step_behavior
      step c1 c2 b
      (STEPS: rtc (union (step MachineEvent.silent)) c1 c2)
      (BEH: behaviors step c2 b):
  behaviors step c1 b.
Proof.
  revert BEH. induction STEPS; auto. inv H.
  i. specialize (IHSTEPS BEH). econs 4; eauto.
Qed.

Lemma le_step_behavior_improve
      sem0 sem1
      (STEPLE: sem0 <4= sem1):
  behaviors sem0 <2= behaviors sem1.
Proof.
  i. ginduction PR; i.
  - econs 1; eauto.
  - econs 2; eauto.
  - econs 3; eauto.
  - econs 4; eauto.
Qed.
