Require Import RelationClasses.

From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import Loc.
Require Import Time.
Require Import Event.
From PromisingLib Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.

Set Implicit Arguments.


Inductive pf_race_condition e1 e2: Prop :=
| pf_race_condition_rw
    loc val1 val2 ordr ordw
    (EVENT1: ProgramEvent.is_reading e1 = Some (loc, val1, ordr))
    (EVENT2: ProgramEvent.is_writing e2 = Some (loc, val2, ordw))
    (ORDW: Ordering.le ordw Ordering.relaxed)
| pf_race_condition_uu
    loc val1 val2 ordu1 ordu2
    (EVENT1: ProgramEvent.is_updating e1 = Some (loc, val1, ordu1))
    (EVENT2: ProgramEvent.is_updating e2 = Some (loc, val2, ordu2))
    (ORDU: Ordering.le ordu1 Ordering.strong_relaxed)
.
Hint Constructors pf_race_condition.

Definition can_step lang (st : Language.state lang) (e : ProgramEvent.t) : Prop :=
  exists st', Language.step _ e st st'.

Definition is_reading lang (st : Language.state lang) l o :=
  exists e v o', can_step _ st e /\
                 Ordering.le o' o /\
                 ProgramEvent.is_reading e = Some (l, v, o').

Definition is_writing lang (st : Language.state lang) l o :=
  exists e v o', can_step _ st e /\
                 Ordering.le o' o /\
                 ProgramEvent.is_writing e = Some (l, v, o').

Definition is_updating lang (st : Language.state lang) l o :=
  exists e v o', can_step _ st e /\
                 Ordering.le o' o /\
                 ProgramEvent.is_updating e = Some (l, v, o').

Inductive pf_race (c:Configuration.t): Prop :=
| race_intro
    tid1 e1 lang1 st1 lc1
    tid2 e2 lang2 st2 lc2
    (TID1: IdentMap.find tid1 (Configuration.threads c) = Some (existT _ lang1 st1, lc1))
    (TID2: IdentMap.find tid2 (Configuration.threads c) = Some (existT _ lang2 st2, lc2))
    (TIDDIFF: tid1 <> tid2)
    (PROEVT1: can_step _ st1 e1)
    (PROEVT2: can_step _ st2 e2)
    (RACE: pf_race_condition e1 e2)
.
Hint Constructors pf_race.

Inductive step_all A B C D (step: A -> B -> C -> D -> Prop): C -> D -> Prop :=
| step_all_intro
    a b c d
    (STEP: step a b c d)
  :
    step_all step c d.

Definition pf_racefree
           (step : MachineEvent.t -> Ident.t -> Configuration.t -> Configuration.t -> Prop) (c1:Configuration.t): Prop :=
  forall c2
         (STEPS: rtc (step_all step) c1 c2)
         (RACE: pf_race c2), False.

Lemma pf_racefree_step step c1 c2 e tid
      (RACEFREE : pf_racefree step c1)
      (STEP : step e tid c1 c2) :
  pf_racefree step c2.
Proof.
  ii. eapply RACEFREE.
  - econs 2; eauto. econs; eauto.
  - auto.
Qed.
