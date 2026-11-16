module

public import Silmaril.Sim.Reduce.X86.Defs
public import Silmaril.Sim.Reduce.Core.Thms
public import Silmaril.Proofs.Sim.Reduce.X86

/-!
# Reducing ISA problems to Wasm problems: x86-64 System V contracts (results)

Proofs in `Silmaril/Proofs/Sim/Reduce/X86.lean`; PROVED, standard axioms only.

* `spec_total_iff`: `FnContract.Spec.Total I S` is `IsaReach I.step (specPre I S) (specPost I S)`;
* `specReduction`, `specExact`: `Spec.Total I S` ⇐ `specWasm I S K Init`, for a sound simulator
  `K` of `I` that can be loaded with every entry state of `S` (exact given `Complete`).

The problem templates of `Silmaril.Problems` (`FnCorrectDet`) and the registered problems are in
`Silmaril.Problems.WasmSim`.
-/

/-- info: 'Silmaril.Sim.Reduce.specReduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Silmaril.Sim.Reduce.specReduction
