module

public import Silmaril.Wasm.Examples.LRAT.Bytes.Defs
public import Silmaril.Wasm.Binaryen.Exe.EncodeSound
public import Silmaril.Wasm.Verify.Kernel.Defs
public import Silmaril.Wasm.Binary.Core.Decode

/-!
# The streaming LRAT checker: its exact bytes, theorems

* `encodeModule_eq`: silmaril's encoder writes exactly `bytes` for `lratModule`;
* `bytes_encodes`: `bytes` encodes `lratModule` in the specification's binary grammar
  (`Binary.Core.Encodes`, by `encodeModule?_sound`);
* `decode_bytes`: the decoder reads `bytes` back as `lratModule`;
* `bytes_length`: the size of `bytes`. `scripts/check-wasm-checkers.py` (`make check`) checks
  that `examples/wasm-checkers/lrat.wasm` holds exactly these bytes.

So every theorem of `Silmaril.Wasm.Examples.LRAT.Thms` about `lratModule` is a theorem about the module these
bytes decode to. All by kernel evaluation (`kernel_rfl`); no native evaluation.
That a given engine runs the bytes as Core 3.0 says is not proved here;
`examples/wasm-checkers/README.md` describes the tests on Node.
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.LRAT

open Silmaril.Wasm

theorem encodeModule_eq : Binaryen.Exe.encodeModule? lratModule = .ok bytes := by kernel_rfl

/-- **`bytes` encodes `lratModule`** in the specification's binary grammar. -/
theorem bytes_encodes : Binary.Core.Encodes bytes lratModule :=
  Binaryen.Exe.encodeModule?_sound encodeModule_eq

theorem decode_bytes : Binary.Core.decode? ⟨bytes.toArray⟩ = some lratModule := by kernel_rfl

theorem bytes_length : bytes.length = 1812 := by kernel_rfl

/-- info: 'Silmaril.Wasm.Examples.LRAT.bytes_encodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Silmaril.Wasm.Examples.LRAT.bytes_encodes

/-- info: 'Silmaril.Wasm.Examples.LRAT.decode_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Silmaril.Wasm.Examples.LRAT.decode_bytes

end Silmaril.Wasm.Examples.LRAT
