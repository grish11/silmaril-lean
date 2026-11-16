module

public import Silmaril.Sim.Reduce.Wasm.Defs
public import Silmaril.Proofs.Sim.Reduce.Wasm

/-!
# Reducing ISA problems to Wasm problems: the call-level Wasm problem, results

Proofs in `Silmaril/Proofs/Sim/Reduce/Wasm.lean`; PROVED, standard axioms only.

* `wasmTotal_of_runSpec`: the call-level problem (`FuncSpec` of the export) gives `WasmTotal` of
  `SoundSim.ofExportCert Ct`.
* `specRunReduction`: `FnContract.Spec.Total I S` ⇐ `runSpec K Init (pullPre …) (pullPost …)`,
  for a certified simulator `K` of `Machine.ofStep I.step view` that can be loaded with every
  entry state of `S`.
-/

/-- info: 'Silmaril.Sim.Reduce.Wasm.wasmTotal_of_runSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Silmaril.Sim.Reduce.Wasm.wasmTotal_of_runSpec

/-- info: 'Silmaril.Sim.Reduce.Wasm.specRunReduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Silmaril.Sim.Reduce.Wasm.specRunReduction
