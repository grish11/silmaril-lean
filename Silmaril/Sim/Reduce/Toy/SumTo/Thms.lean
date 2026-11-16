module

public import Silmaril.Sim.Reduce.Toy.SumTo.Defs
public import Silmaril.Proofs.Sim.Reduce.Toy.SumTo

/-!
# The toy's `sum_to`, end to end: results

Proofs in `Silmaril/Proofs/Sim/Reduce/Toy/SumTo.lean`; standard axioms only.

* `piece : PieceStmt` (`wasm_solution`), `x86_of_piece : PieceStmt → X86Stmt`
  (`xlproblem_of_lproblem`);
* `term : TermStmt`: x86-side termination and frame (induction on `rdi` over explicit step
  lemmas `ex_*`; the Wasm piece is partial correctness);
* `run_of_xrun`: table runs are machine runs; `bytesAt_of_loaded`: spans of a loaded image;
* `isa_of : X86Stmt → TermStmt → Toy.isaGoal .sumTo`, and **`isa_sumTo : Toy.isaGoal .sumTo`**:
  the System V contract of the toy's `sum_to` on `Open9.isa` at every placement.
-/

/-- info: 'Silmaril.Sim.Reduce.Toy.SumTo.isa_sumTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Silmaril.Sim.Reduce.Toy.SumTo.isa_sumTo
