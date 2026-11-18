module

public import Silmaril.Sim.Reduce.Toy.Dbl.Defs
public import Silmaril.Proofs.Sim.Reduce.Toy.Dbl

/-!
# The toy's `dbl`, end to end: results

Proofs in `Silmaril/Proofs/Sim/Reduce/Toy/Dbl.lean`; standard axioms only. The pieces of the
problem DAG (`examples/wasm-sim/reduce/toy/out/dag.json`, `wasm-sim reduce --granularity insn`)
and their solutions:

* `piece : PieceStmt` — the Wasm piece `wasm-insn/dbl` (every run of `dbl_body`, the step
  methods given by their contracts), by the every-run call rule `hwp_call_step`;
* `dbl_fns` — translation validity `tv-insn/dbl` and the method pieces `method/s_*`: the
  instantiated module's calls reach step methods whose code is the certified `Silmaril.Sim.X86.G.emit i len`
  (`rfl`, `decide +kernel`);
* composition: `x86_of_piece : PieceStmt → X86Stmt` (P-calls soundness,
  `Silmaril.Sim.Reduce.PCalls.xproblem_of_piece`) and `isa_of_x86 : X86Stmt → Toy.isaGoal .dbl` (decoding,
  `ret`, `FnContract.total_of_ext_returns`, `Spec.Total.toOpen9`);
* **`isa_dbl : Toy.isaGoal .dbl`**: the System V contract of the toy's `dbl` on `Open9.isa`, at
  every placement of the toy's code, solved through Wasm.
-/

/-- info: 'Silmaril.Sim.Reduce.Toy.Dbl.piece' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Silmaril.Sim.Reduce.Toy.Dbl.piece

/-- info: 'Silmaril.Sim.Reduce.Toy.Dbl.isa_dbl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Silmaril.Sim.Reduce.Toy.Dbl.isa_dbl
