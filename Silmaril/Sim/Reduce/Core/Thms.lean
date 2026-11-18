module

public import Silmaril.Sim.Reduce.Core.Defs
public import Silmaril.Proofs.Sim.Reduce.Core

/-!
# Reducing ISA problems to Wasm problems: the ISA-agnostic core (results)

Proofs in `Silmaril/Proofs/Sim/Reduce/Core.lean`. Everything listed is PROVED (standard axioms
only, audited below).

* **Decompositions**: `Decomp.solve`, `Decomp.refine` (refine one piece by a decomposition of
  it), `Decomp.Exact.refute`; the goal-indexed view: `Decomp.ofReduction_toReduction`,
  `Decomp.toReduction_ofReduction` (`rfl`). Legacy two-field reductions:
  `Reduction.toDecomp`, `Reduction.Exact.refute`, `Reduction.Exact.toDecomp_exact`.
* **The reduction theorem**: `isaReach_of_wasmTotal` (soundness: Wasm solution ⇒ ISA
  solution, given `Encodes`; the run-level form of `Silmaril.Sim.Simulation.reaches`),
  `wasmTotal_of_isaReach` (completeness, given `Complete`), `reachReduction`, `reachExact`,
  `isaCex_of_wasmCex` (a Wasm counterexample gives an ISA counterexample at a state it
  represents), `not_isaReach_of_isaCex`.
* **From the step-level interface**: `SoundSim.ofSimulation` (a `Silmaril.Sim.Simulation` against
  `Machine.ofStep`, run to completion), `wasmTotal_ofSimulation_iff` (its Wasm problem is the
  angelic `Prog.loop` property), `SoundSim.ofExportCert` (a certified Wasm simulator,
  `Silmaril.Sim.Wasm.ExportSim.Cert`), `SoundSim.ofExportCert_run_of_call`,
  `SoundSim.ofObligations` (derived `WasmSim.Obligations` form).
* **Decomposition**: `ag_compose` and `agDecomp` (per function, acyclic call graph),
  `cut_compose` (per cut point), `SoundSim.ofSteps` (per simulator method),
  `SoundSim.ofRefines` and `wasmTotal_of_refines` (simulator refinement).
-/

/-- info: 'Silmaril.Sim.Reduce.isaReach_of_wasmTotal' does not depend on any axioms -/
#guard_msgs in #print axioms Silmaril.Sim.Reduce.isaReach_of_wasmTotal

/-- info: 'Silmaril.Sim.Reduce.isaCex_of_wasmCex' does not depend on any axioms -/
#guard_msgs in #print axioms Silmaril.Sim.Reduce.isaCex_of_wasmCex

/-- info: 'Silmaril.Sim.Reduce.ag_compose' depends on axioms: [Classical.choice] -/
#guard_msgs in #print axioms Silmaril.Sim.Reduce.ag_compose

/-- info: 'Silmaril.Sim.Reduce.cut_compose' depends on axioms: [Classical.choice] -/
#guard_msgs in #print axioms Silmaril.Sim.Reduce.cut_compose

/-- info: 'Silmaril.Sim.Reduce.wasmTotal_of_refines' does not depend on any axioms -/
#guard_msgs in #print axioms Silmaril.Sim.Reduce.wasmTotal_of_refines

/-- info: 'Silmaril.Sim.Reduce.SoundSim.ofSimulation' does not depend on any axioms -/
#guard_msgs in #print axioms Silmaril.Sim.Reduce.SoundSim.ofSimulation
