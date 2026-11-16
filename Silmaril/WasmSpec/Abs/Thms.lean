module

public import Silmaril.WasmSpec.Common.Thms
public import Silmaril.Proofs.WasmSpec.Abs.Tactic

/-!
# Wasm specification library: `Abs` v1, results

Solutions of `Spec` (see `manifest.toml`):

* `tactic`: `Silmaril.WasmSpec.Abs.spec_tactic` (`vc_tactic`: the identity by hand,
  on the sign bit);
* `tactic+smt` (`vc_smt`: one `bv_decide` call, which adds a native-evaluation axiom
  `vc_smt._native.bv_decide.ax_…`) is not in this repository: the trust policy
  (`policy.toml`) admits no native evaluation.

Canonical result: `Silmaril.WasmSpec.Abs.spec : Spec`, from the kernel-checked
`tactic` solution.
-/

@[expose] public section

namespace Silmaril.WasmSpec.Abs

/-- The canonical solution: the kernel-checked `tactic` one. -/
theorem spec : Spec := spec_tactic

end Silmaril.WasmSpec.Abs

/-- info: 'Silmaril.WasmSpec.Abs.spec_tactic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.WasmSpec.Abs.spec_tactic


/-- info: 'Silmaril.WasmSpec.Abs.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.WasmSpec.Abs.spec
