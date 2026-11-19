module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Bridge10

/-!
# 1.0 leg 3 outside round 4's invariants: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10`; see `docs/projects/wasm-spec-bridge.md`.

* **`unstripStep10_of_out`**: the frozen `Task.unstripStep10` from the strictly smaller frozen
  `Task.unstripStep10Out` (configurations violating `Plain10`, `GSetOk` or `MemsAligned10`); the
  rest is `XSwap.unstripStep10_inv`. `unstripStep10Out_of_unstripStep10`: the converse.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10.unstripStep10_of_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unstripStep10_of_out

end Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10
