# Promising 2.0: Global Optimizations in Relaxed Memory Concurrency

This repository contains Coq code supplementing the paper *Promising 2.0: Global Optimizations in Relaxed Memory Concurrency*.

## Build

- Requirement: [Coq 8.9.1](https://coq.inria.fr/download), opam, Make, Rsync.

- Installing dependencies with opam

        opam repo add coq-released https://coq.inria.fr/opam/released
        opam remote add coq-promising -k git https://github.com/snu-sf/promising-opam-coq-archive
        opam install coq-paco.2.0.3
        opam install coq-sflib
        opam install coq-promising-lib

- Initialization

        git clone https://github.com/snu-sf/promising-coq-private.git
        cd promising-coq-private

- `make`: quickly build without checking the proofs.

- `./build.sh`: build with checking all the proofs.  It will incrementally copy the development in the `.build` directory, and then build there.

- Interactive Theorem Proving: use [ProofGeneral](https://proofgeneral.github.io/) or [CoqIDE](https://coq.inria.fr/download).
  Note that `make` creates `_CoqProject`, which is then used by ProofGeneral and CoqIDE. To use it:
    + ProofGeneral: use a recent version.
    + CoqIDE: configure it to use `_CoqProject`: `Edit` > `Preferences` > `Project`: change `ignored` to `appended to arguments`.

## References

### Model

- `promising2/src/lang`: The model
    + `Memory.v`: memory model (`MEMORY: *` rules in Figure 2 and 3)
    + `Local.v`, `Thread.v`: thread and its execution
      (`PROMISE`, `RESERVE`, `CANCEL`, `READ`, `WRITE`, `UPDATE`, `FENCE`, `SYSTEM CALL`, `SILENT`, `FAILURE` rules in Figure 2 and 3,
       note that `PROMISE`, `RESERVE`, and `CANCEL` is covered by one operation, `promise_step`)
    + `Configuration.v`: configuration (machine state) and its execution (`MACHINE STEP` rule in Figure 2 and 3)
    + `Behavior.v`: the behaviors of a configuration

- `promising2/src/pf`: Definition of promise-free machine

- `promising2/src/attachable`: Definition of a machine where attaching a new concrete message in front of another message is allowed, which in particular,
  is (syntactically) equivalent to the promise-free fragment of PS (promising 1.0) when executed in promise-free maner.

- `promising2/src/while`: Toy "while" language that provides the basis for the optimization & compilation results.

- `promising2/src/prop`: General properties on the memory model

### Results

- `promising2/src/opt`: Compiler transformations (Section 6.1)
    + Trace-Preserving Transformations: `sim_trace_sim_stmts` (`SimTrace.v`)
    + Strengthening: `sim_stmts_instr` (`SimTrace.v`)
    + Optimizing `abort`: `sim_stmts_replace_abort`, `sim_stmts_elim_after_abort` (`SimTrace.v`)
    + Reorderings: `reorder_sim_stmts` (`Reorder.v`)
    + Merges: `Merge.v`
    + Unused Plain Read Elimination: `elim_load_sim_stmts` (`ElimLoad.v`)
    + Read Introduction: `intro_load_sim_stmts` (`IntroLoad.v`)
    + Spliting acquire loads/updates and release writes/updates:
        `split_acquire_sim_stmts` (`SplitAcq.v`), `split_release_sim_stmts` (`SplitRel.v`), `split_acqrel_sim_stmts` (`SplitAcqRel.v`)
    + Proof Technique:
        * Simulation (Configuration): `sim` (`Simulation.v`) for the configuration simulation
        * Simulation (Thread): `sim_thread` (`SimThread.v`)
        * Adequacy (Configuration): `sim_adequacy` (`Adequacy.v`).  From the configuration simulation to the behaviors.
        * Adequacy (Thread): `sim_thread_sim` (`AdequacyThread.v`).  From the thread simulation to the configuration simulation.
        * Compatibility: `sim_stmts_*` (`Compatibility.v`).

- `promising2/src/invariant`: An invariant-based program logic (a value-range analysis, Section 6.2)
    + Soundness of Value-Range Analysis (Theorem 6.1): `sound` (`Invariant.v`)

- `promising2/src/gopt`: Global optimization (Section 6.2)
    + Definition of global optimization: `insert_assertion`, `insert_assertion_program` (`AssertInsertion.v`)
    + Soundness of Value-Range Analysis (Theorem 6.2): `insert_assertion_behavior` (`AssertInsertion.v`)

- `promising2/src/promotion`: Register promotion (Section 6.3)
    + Definition of register promotion: `promote_stmts` (`PromotionDef.v`), `promote_program` (`Promotion.v`)
    + Soundness of Register Promotion (Theorem 6.3): `promote_behavior` (`Promotion.v`)

- `promising2/src/attachable`
    + Equivalence between PF and promise-free fragment of PS (Theorem 6.4): `apf_pf_equiv`, `apf_pf_equiv2` (`APFPF.v`)

- `promising2/src/drf`: DRF Theorems (Section 6.4)
    + DRF-Promise (Theorem 6.5): `drf_pf` (`DRF_PF.v`)
