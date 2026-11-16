module

public import Silmaril.Proofs.Sim.X86.GInst.Transfer

/-!
# The G reduction as institution transfer: results

Proofs in `Silmaril.Proofs.Sim.X86.GInst.Transfer`.

* **`coSim`**: the Wasm model (`wasmM`: runs of the generated code on well-formed stores) is a
  complete simulator (`Silmaril.Sim.CoSimulation`) of the reference x86 model (`x86M`: `Ext.exec`,
  undefined flags concretized), with equal views.
* **`reduce_inst`**: `Silmaril.Sim.X86.G.xproblem_of_wproblem` as `Silmaril.Sim.Institution.transfer_demonic`: every
  demonic sentence (partial correctness of a program of instructions) the Wasm model satisfies,
  the x86 model satisfies.
* `wasm_maxSen` (from the `wpc` solution `Silmaril.Sim.X86.Max.wasm_solution`) and **`x86_maxSen`**:
  `max` in the institution.
-/

/-- info: 'Silmaril.Sim.X86.GInst.x86_maxSen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86.GInst.x86_maxSen
