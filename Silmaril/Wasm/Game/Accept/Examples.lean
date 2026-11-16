module

public import Silmaril.Wasm.Game.Accept.Thms
public import Silmaril.Wasm.Game.Examples.Defs
import Silmaril.Proofs.Wasm.Game.Accept.Example

/-! # Inputs accepted by a core Wasm module: examples and tests

* **Non-vacuity** on a real module: `exStart` (`Silmaril.Wasm.Game.Examples`), whose start
  function calls its import `"env" "f"`, has that call among its reachable callouts, for every
  profile (`exStart_callout`); with the decoder that accepts every call, it accepts `()`
  through `"env" "f"` (`exStart_accepts`).
* **Decoders**, by kernel evaluation: `accept(1, 3)` over the memory `00 68 69 21 00` reads
  `"hi!"`; an out-of-bounds segment, a missing memory and ill-shaped arguments read nothing;
  `accept(x: i32)` reads `x`.

Proofs: `Silmaril.Proofs.Wasm.Game.Accept.Example`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.Accept.Examples

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.Examples

/-- **`exStart` calls `"env" "f"` during instantiation**, for every profile. -/
theorem exStart_callout (P : Profile) :
    (⟨("env", "f"), [], none⟩ : Callout) ∈ Callouts P UEnvOk 0 exStart :=
  Silmaril.Proofs.Wasm.Game.Accept.exStart_callout P

/-- With the decoder accepting every call, `exStart` accepts `()` through `"env" "f"`. -/
theorem exStart_accepts (P : Profile) :
    () ∈ accepted (fun _ => some ()) P UEnvOk 0 ("env", "f") exStart :=
  ⟨_, exStart_callout P, rfl, rfl⟩

/-! ## Decoders -/

/-- A memory holding `00 68 69 21 00` (`"hi!"` at offset 1). -/
def hiMem : ByteArray := ⟨#[0, 0x68, 0x69, 0x21, 0]⟩

/-- `accept(ptr, len)` with `i32` arguments. -/
def call32 (p n : BitVec 32) (mem : Option ByteArray) : Callout :=
  ⟨acceptImport, [.num ⟨.int .i32, p⟩, .num ⟨.int .i32, n⟩], mem⟩

example : (call32 1 3 (some hiMem)).bytes32 = some "hi!".toUTF8.data.toList := by decide +kernel

example : (call32 0 5 (some hiMem)).bytes32 = some [0, 0x68, 0x69, 0x21, 0] := by decide +kernel

example : (call32 5 0 (some hiMem)).bytes32 = some [] := by decide +kernel

/-- Out of bounds: nothing is observed (the canonical ABI traps). -/
example : (call32 3 3 (some hiMem)).bytes32 = none := by decide +kernel

/-- Without a memory nothing is observed. -/
example : (call32 1 3 none).bytes32 = none := by decide +kernel

/-- `i64` arguments are not `accept(ptr: i32, len: i32)`. -/
example : (⟨acceptImport, [.num ⟨.int .i64, 1⟩, .num ⟨.int .i64, 3⟩], some hiMem⟩ : Callout).bytes32
    = none := by decide +kernel

/-- ... but they are its `memory64` form. -/
example : (⟨acceptImport, [.num ⟨.int .i64, 1⟩, .num ⟨.int .i64, 3⟩], some hiMem⟩ : Callout).bytes64
    = some [0x68, 0x69, 0x21] := by decide +kernel

example : (⟨acceptImport, [.num ⟨.int .i32, 7⟩], none⟩ : Callout).i32 = some 7 := by decide +kernel

example : (⟨acceptImport, [.num ⟨.int .i64, 7⟩], none⟩ : Callout).i32 = none := by decide +kernel

example : (⟨acceptImport, [.num ⟨.int .i64, 0xffffffffffffffff⟩], none⟩ : Callout).i64 =
    some 0xffffffffffffffff := by decide +kernel

end Silmaril.Wasm.Game.Accept.Examples
