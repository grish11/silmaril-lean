module

public import Silmaril.Sim.Wasm.FnSpec.Defs
public import Silmaril.Sim.Wasm.Thms
public import Silmaril.Proofs.Sim.Wasm.FnSpec

/-!
# Wasm simulators: per-method soundness from `Verify.FnSpec` (results)

PROVED (proof in `Silmaril/Proofs/Sim/Wasm/FnSpec.lean`, standard axioms):

* `Silmaril.Sim.Wasm.ExportSim.methodOK_of_vc`: the verification condition of a method's body for
  `methodFnSpec`, a store relation that pins the method's code, and matching arities give
  `MethodOK` (through `Silmaril.Wasm.Verify.FnSpec.sound`).
-/
