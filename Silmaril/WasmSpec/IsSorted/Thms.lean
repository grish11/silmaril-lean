module

public import Silmaril.Proofs.WasmSpec.IsSorted.Tactic
public import Silmaril.Proofs.WasmSpec.IsSorted.Tests

/-!
# Wasm specification library: `IsSorted` v1, results

Solutions (see `manifest.toml`):

* `tactic`: `spec_tactic : Spec` and `specStore_tactic : SpecStore`
  (`Silmaril.Proofs.WasmSpec.IsSorted.Tactic`): symbolic execution over the `i32` view of
  `Silmaril.Wasm.Logic.Words` with the loop invariant "the prefix of length `i` is sorted" and the
  variant `n + 1 - i`; **every-run total correctness** (`Silmaril.Wasm.Logic.Hoare.TFSpecAt`), at
  every profile and for every host relation.

Tested (`Silmaril.Proofs.WasmSpec.IsSorted.Tests`, `#guard`, not proofs): runs of the instantiated
module with silmaril-lean's verified interpreter agree with `answer` on 300 pseudo-random
arrays, 100 sorted ones and edge cases.

Canonical results: `spec : Spec`, `specStore : SpecStore`; the lemmas of the solution module
(`isSorted_valid`, `body_twp`, `loop_body`, `store₀_funcs`).
-/

@[expose] public section

namespace Silmaril.WasmSpec.IsSorted

/-- The canonical solution of `Spec`. -/
theorem spec : Spec := spec_tactic

/-- The canonical solution of `SpecStore`. -/
theorem specStore : SpecStore := specStore_tactic

end Silmaril.WasmSpec.IsSorted

/-- info: 'Silmaril.WasmSpec.IsSorted.spec_tactic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.WasmSpec.IsSorted.spec_tactic

/-- info: 'Silmaril.WasmSpec.IsSorted.specStore_tactic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.WasmSpec.IsSorted.specStore_tactic

/-- info: 'Silmaril.WasmSpec.IsSorted.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.WasmSpec.IsSorted.spec

/-- info: 'Silmaril.WasmSpec.IsSorted.specStore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.WasmSpec.IsSorted.specStore
