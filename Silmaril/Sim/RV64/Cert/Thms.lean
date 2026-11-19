module

public import Silmaril.Proofs.Sim.RV64.Cert

/-!
# The memory-state RV64 simulator as a certified simulator: results

Proofs in `Silmaril.Proofs.Sim.RV64.Cert`, every profile and every host relation:

* **`simCert`**: `simK P host` (the instantiated `simM`, one command = one call of `step`,
  view = abstraction of memory `0` on locations `x0 … x31, pc`) has an
  `ExportSim.Cert` (`Silmaril.Sim.Wasm`) for `refM ws` (`Machine.ofStep` of the RV64
  fetch-decode-retire step on any program `ws` of at most 15360 words at `0x1000`); the method
  condition comes from `step_sound`;
* **`sim_sound`**: `Silmaril.Sim.Sound (simK P host).toWasmSim.toMachine (refM ws)`, so the
  transfer theorems of `Silmaril.Sim.Core`/`Institution` apply to this simulator.
-/
