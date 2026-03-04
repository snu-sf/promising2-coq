# Promising 2.0: Global Optimizations in Relaxed Memory Concurrency

Sung-Hwan Lee, Minki Cho, Anton Podkopaev, Soham Chakraborty, Chung-Kil Hur, Ori Lahav, Viktor Vafeiadis.

Proceedings of the 41st annual ACM SIGPLAN conference on Programming Languages Design and Implementation ([PLDI 2020](https://conf.researchr.org/home/pldi-2020))

Please visit the [project website](https://sf.snu.ac.kr/promising2.0/) for more information.


## Build

Requirements: opam (>=2.0.0), OCaml 5.x, Rocq 9.0+, dune (>=3.21)

1. Create a local opam switch and install dependencies
```
opam switch create . ocaml-base-compiler.5.4.0 --no-install
eval $(opam env)
opam repo add rocq-released https://rocq-prover.org/opam/released
opam pin add -y rocq-promising2 . --no-action
opam install -y --deps-only rocq-promising2
```

2. Build the project
```
dune build
```

### IDE Setup

- **VsCoq (VS Code)**: Install the VsCoq extension and open the project folder. Dune generates the `_CoqProject` file automatically.
- **ProofGeneral (Emacs)**: Use a recent version. Run `dune build` first to generate the build artifacts.
- **CoqIDE**: Run `dune build` first, then open `.v` files from the `src/` directory.

## References

### Model

- `src/lang`: The model
    + `Memory.v`: memory model (`MEMORY: *` rules in Figure 2 and 4)
    + `Local.v`, `Thread.v`: thread and its execution
      (`PROMISE`, `RESERVE`, `CANCEL`, `READ`, `WRITE`, `UPDATE`, `FENCE`, `SYSTEM CALL`, `SILENT`, `FAILURE` rules in Figure 2 and 4,
       note that `PROMISE`, `RESERVE`, and `CANCEL` is covered by one operation, `promise_step`)
    + `Configuration.v`: configuration (machine state) and its execution (`MACHINE STEP` rule in Figure 2 and 4)
    + `Behavior.v`: the behaviors of a configuration

- `src/pf`: Definition of promise-free machine

- `src/attachable`: Definition of a machine where attaching a new concrete message in front of another message is allowed, which in particular,
  is (syntactically) equivalent to the promise-free fragment of PS (promising 1.0) when executed in promise-free manner.

- `src/while`: Toy "while" language that provides the basis for the optimization & compilation results.

- `src/prop`: General properties on the memory model

### Results

- `src/opt`: Compiler transformations (Section 6.1)
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

- `src/invariant`: An invariant-based program logic (a value-range analysis, Section 6.2)
    + Soundness of value-range analysis (Theorem 6.1): `sound` (`Invariant.v`)

- `src/gopt`: Global optimization (Section 6.2)
    + Definition of global optimization: `insert_assertion`, `insert_assertion_program` (`AssertInsertion.v`)
    + Soundness of value-range analysis (Theorem 6.2): `insert_assertion_behavior` (`AssertInsertion.v`)

- `src/promotion`: Register promotion (Section 6.3)
    + Definition of register promotion: `promote_stmts` (`PromotionDef.v`), `promote_program` (`Promotion.v`)
    + Soundness of register promotion (Theorem 6.3): `promote_behavior` (`Promotion.v`)

- `src/attachable`
    + Equivalence between PF and promise-free fragment of PS (Theorem 6.4): `apf_pf_equiv`, `apf_pf_equiv2` (`APFPF.v`)

- `src/drf`: DRF theorems (Section 6.4)
    + DRF-Promise (Theorem 6.5): `drf_pf` (`DRF_PF.v`)
