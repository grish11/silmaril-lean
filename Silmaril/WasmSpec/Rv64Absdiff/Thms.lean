module

public import Silmaril.WasmSpec.Rv64Absdiff.Defs
public import Silmaril.Proofs.WasmSpec.Rv64Absdiff.Vc

/-!
# Wasm specification library: `Rv64Absdiff` v1, results

Solutions of `Spec` (see `manifest.toml`):

* `tactic`: `Silmaril.WasmSpec.Rv64Absdiff.spec_vc` (`Silmaril.Proofs.WasmSpec.Rv64Absdiff.Vc`):
  `wpc` on the loop-free body, total soundness, a run by `wp_of_twp`.

Canonical result: `Silmaril.WasmSpec.Rv64Absdiff.spec : Spec`. It solves the piece `ag/absdiff` of
`examples/wasm-sim/rv64/problems/funcs`; the transfer to the RV64 problem is
`Silmaril.Sim.RV64.Transfer.Absdiff.isa`.
-/

@[expose] public section

namespace Silmaril.WasmSpec.Rv64Absdiff

/-- The canonical solution. -/
theorem spec : Spec := spec_vc

end Silmaril.WasmSpec.Rv64Absdiff

/-- info: 'Silmaril.WasmSpec.Rv64Absdiff.spec_vc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.WasmSpec.Rv64Absdiff.spec_vc

/-- info: 'Silmaril.WasmSpec.Rv64Absdiff.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.WasmSpec.Rv64Absdiff.spec
