module

public import Silmaril.Sim.Wasm.Open.Defs
public import Silmaril.Sim.Wasm.Thms
public import Silmaril.Proofs.Sim.Wasm.Open

/-!
# Wasm simulators: open modules and import environments (results)

PROVED (proofs in `Silmaril/Proofs/Sim/Wasm/Open.lean`, names in `Silmaril.Sim.Wasm.ExportSim`,
standard axioms):

* `methodOK_of_moduleSat`: an open module (`Silmaril.Wasm.Logic.Open.ModuleSat`, imports as host
  stubs) under the most general environment `specHost bind Γi` of its import contracts, whose
  export context holds the ghost-free method specification, gives `MethodOK`;
* `methodOK_of_core`: a core verified once against accessor contracts, plus a representation's
  accessors as a host relation sound and live for those contracts (representation equivalence
  reduced to the accessor contracts).
-/
