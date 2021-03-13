# Promising 2.0: Global Optimizations in Relaxed Memory Concurrency

Sung-Hwan Lee, Minki Cho, Anton Podkopaev, Soham Chakraborty, Chung-Kil Hur, Ori Lahav, Viktor Vafeiadis.

Proceedings of the 41st annual ACM SIGPLAN conference on Programming Languages Design and Implementation ([PLDI 2020](https://conf.researchr.org/home/pldi-2020))

Please visit the [project website](https://sf.snu.ac.kr/promising2.0/) for more information.


## Build

- Requirement: [Coq 8.9.1](https://coq.inria.fr/download), opam, Make, Rsync.

- Installing dependencies with opam

        opam repo add coq-released https://coq.inria.fr/opam/released
        opam remote add coq-promising -k git https://github.com/snu-sf/promising-opam-coq-archive
        opam install coq-paco.4.0.4 coq-sflib coq-promising-lib

- Building the project

        git clone https://github.com/snu-sf/promising2-coq.git
        cd promising2-coq
        make -j build

- Interactive Theorem Proving: use [ProofGeneral](https://proofgeneral.github.io/) or [CoqIDE](https://coq.inria.fr/download).
  Note that `make` creates `_CoqProject`, which is then used by ProofGeneral and CoqIDE. To use it:
    + ProofGeneral: use a recent version.
    + CoqIDE: configure it to use `_CoqProject`: `Edit` > `Preferences` > `Project`: change `ignored` to `appended to arguments`.

## References

### Model

- `promising2/src/lang`: The model
    + `Memory.v`: memory model (`MEMORY: *` rules in Figure 2 and 4)
    + `Local.v`, `Thread.v`: thread and its execution
      (`PROMISE`, `RESERVE`, `CANCEL`, `READ`, `WRITE`, `UPDATE`, `FENCE`, `SYSTEM CALL`, `SILENT`, `FAILURE` rules in Figure 2 and 4,
       note that `PROMISE`, `RESERVE`, and `CANCEL` is covered by one operation, `promise_step`)
    + `Configuration.v`: configuration (machine state) and its execution (`MACHINE STEP` rule in Figure 2 and 4)
    + `Behavior.v`: the behaviors of a configuration

- `promising2/src/pf`: Definition of promise-free machine

- `promising2/src/attachable`: Definition of a machine where attaching a new concrete message in front of another message is allowed, which in particular,
  is (syntactically) equivalent to the promise-free fragment of PS (promising 1.0) when executed in promise-free manner.

- `promising2/src/while`: Toy "while" language that provides the basis for the optimization & compilation results.

- `promising2/src/prop`: General properties on the memory model

### Results

- `promising2/src/opt`: Compiler transformations (Section 6.1)
    + Trace-preserving transformations: `sim_trace_sim_stmts` (`SimTrace.v`)
    + Strengthening: `sim_stmts_instr` (`SimTrace.v`)
    + Optimizing `abort`: `sim_stmts_replace_abort`, `sim_stmts_elim_after_abort` (`SimTrace.v`)
    + Reorderings: `reorder_sim_stmts` (`Reorder.v`)
    + Merges: `Merge.v`
    + Unused plain read elimination: `elim_load_sim_stmts` (`ElimLoad.v`)
    + Read introduction: `intro_load_sim_stmts` (`IntroLoad.v`)
    + Splitting acquire loads/updates and release writes/updates:
        `split_acquire_sim_stmts` (`SplitAcq.v`), `split_release_sim_stmts` (`SplitRel.v`), `split_acqrel_sim_stmts` (`SplitAcqRel.v`)
    + Proof technique:
        * Simulation (Configuration): `sim` (`Simulation.v`) for the configuration simulation
        * Simulation (Thread): `sim_thread` (`SimThread.v`)
        * Adequacy (Configuration): `sim_adequacy` (`Adequacy.v`).  From the configuration simulation to the behaviors.
        * Adequacy (Thread): `sim_thread_sim` (`AdequacyThread.v`).  From the thread simulation to the configuration simulation.
        * Compatibility: `sim_stmts_*` (`Compatibility.v`).

- `promising2/src/invariant`: An invariant-based program logic (a value-range analysis, Section 6.2)
    + Soundness of value-range analysis (Theorem 6.1): `sound` (`Invariant.v`)

- `promising2/src/gopt`: Global optimization (Section 6.2)
    + Definition of global optimization: `insert_assertion`, `insert_assertion_program` (`AssertInsertion.v`)
    + Soundness of value-range analysis (Theorem 6.2): `insert_assertion_behavior` (`AssertInsertion.v`)

- `promising2/src/promotion`: Register promotion (Section 6.3)
    + Definition of register promotion: `promote_stmts` (`PromotionDef.v`), `promote_program` (`Promotion.v`)
    + Soundness of register promotion (Theorem 6.3): `promote_behavior` (`Promotion.v`)

- `promising2/src/attachable`
    + Equivalence between PF and promise-free fragment of PS (Theorem 6.4): `apf_pf_equiv`, `apf_pf_equiv2` (`APFPF.v`)

- `promising2/src/drf`: DRF theorems (Section 6.4)
    + DRF-Promise (Theorem 6.5): `drf_pf` (`DRF_PF.v`)
