module

public import Silmaril.Proofs.Sim.X86.GCert.Cert

/-!
# The G simulator as a `Silmaril.Sim` simulator: results

Proofs in `Silmaril.Proofs.Sim.X86.GCert.Cert`; every profile, every host relation.

* `step_valid`: a full step method (`emit i len`) meets `stepSpec` (`FSpecValid`).
* **`cert`**: under the layout assumptions `Hyps`, a `Silmaril.Sim.Wasm.ExportSim.Cert` of
  `exportSim` against the reference x86 machine `xRef cmd` (`Silmaril.X86.Ext.exec` with
  undefined flags concretized); **`sound`**: `Silmaril.Sim.Sound` (the soundness notion of `Silmaril.Sim.Core`),
  so the transfer theorems (`Silmaril.Sim.Institution.transfer`, …) apply.
* **`stepModule_sound`**: the instantiated quotation `stepModule` (full step methods for the
  three instructions of `max`) is sound; its layout assumptions are checked by `rfl` and
  `decide +kernel` (`step_hyps`).
* **`simModule_sound`**: the ABI-style quotation `simModule` (six methods without RIP update and
  `i_next n`), instantiated (`Silmaril.Sim.X86.GModule.s₀`, `f₀`), is a certified
  `ExportSim` of `xRef simCmd`: a method is its instruction at length `0`, `i_next n` a NOP of
  length `n` (`sim_hyps`; `straight_spec`, `method_ex`, `next_ex`).
-/

/-- info: 'Silmaril.Sim.X86.GCert.stepModule_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86.GCert.stepModule_sound

/-- info: 'Silmaril.Sim.X86.GCert.simModule_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86.GCert.simModule_sound
