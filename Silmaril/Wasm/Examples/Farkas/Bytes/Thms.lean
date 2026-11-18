module

public import Silmaril.Wasm.Examples.Farkas.Bytes.Defs
public import Silmaril.Wasm.Binaryen.Exe.EncodeSound
public import Silmaril.Wasm.Verify.Kernel.Defs
public import Silmaril.Wasm.Binary.Core.Decode

/-!
# The Farkas certificate checker: its exact bytes, theorems

* `encodeModule_eq`: silmaril's encoder writes exactly `bytes` for `farkasMod`;
* `bytes_encodes`: `bytes` encodes `farkasMod` in the specification's binary grammar
  (`Binary.Core.Encodes`, by `encodeModule?_sound`);
* `decode_bytes`: the decoder reads `bytes` back as `farkasMod`;
* `bytes_length`: the size of `bytes`. `scripts/check-wasm-checkers.py` (`make check`) checks
  that `examples/wasm-checkers/farkas.wasm` holds exactly these bytes.

So every theorem of `Silmaril.Wasm.Examples.Farkas.Thms` about `farkasMod` is a theorem about the module these
bytes decode to. All by kernel evaluation (`kernel_rfl`); no native evaluation.
That a given engine runs the bytes as Core 3.0 says is not proved here;
`examples/wasm-checkers/README.md` describes the tests on Node.
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.Farkas

open Silmaril.Wasm

theorem encodeModule_eq : Binaryen.Exe.encodeModule? farkasMod = .ok bytes := by kernel_rfl

/-- **`bytes` encodes `farkasMod`** in the specification's binary grammar. -/
theorem bytes_encodes : Binary.Core.Encodes bytes farkasMod :=
  Binaryen.Exe.encodeModule?_sound encodeModule_eq

theorem decode_bytes : Binary.Core.decode? ⟨bytes.toArray⟩ = some farkasMod := by kernel_rfl

theorem bytes_length : bytes.length = 372 := by kernel_rfl

/-- info: 'Silmaril.Wasm.Examples.Farkas.bytes_encodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Silmaril.Wasm.Examples.Farkas.bytes_encodes

/-- info: 'Silmaril.Wasm.Examples.Farkas.decode_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Silmaril.Wasm.Examples.Farkas.decode_bytes

end Silmaril.Wasm.Examples.Farkas
