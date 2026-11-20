module

public import Silmaril.Wasm.Game.HandleAccept.Memory.Thms

/-!
# Memory-carrying writer imports: decoding examples

Kernel-checked decodings of concrete callouts and replies (`decide +kernel`), read through
`view` (events have no decidable equality since atoms carry a membership proof):

* `symbol(1, 3)` over the memory `00 68 69 21 00` answered `5` is the symbol `"hi!"` with
  handle `5`; `string(1, 3)` the string `"hi!"`; `blob(0, 5)` the five bytes;
* `sexp(0, 2)` over `05 00 00 00 07 01 00 00` answered `9` is a list node of the handles `5`
  and `0x107` (little-endian);
* invalid UTF-8, out-of-bounds segments, a trapping reply and an `i64` reply are no events;
* `accept(7)` is the accept of handle `7`.
-/

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Memory.Examples

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api

/-- A decidable view of an event: a code (`0` symbol, `1` string, `2` bytes, `3` list,
`4` accept), the atom's bytes, the children and the handle. -/
def view : MemWEv → Option (Nat × List UInt8 × List (BitVec 32) × BitVec 32)
  | .write (.atom ⟨.symbol, _, s⟩) [] r => some (0, s.toUTF8.data.toList, [], r)
  | .write (.atom ⟨.string, _, s⟩) [] r => some (1, s.toUTF8.data.toList, [], r)
  | .write (.atom ⟨.bytes, _, b⟩) [] r => some (2, b, [], r)
  | .write .list hs r => some (3, [], hs, r)
  | .accept h => some (4, [], [], h)
  | _ => none

/-- The default imports. -/
def ix : MemImports := {}

/-- A memory holding `00 68 69 21 00` (`"hi!"` at offset 1). -/
def hiMem : ByteArray := ⟨#[0, 0x68, 0x69, 0x21, 0]⟩

/-- A memory holding the handles `5` and `0x107`, little-endian. -/
def listMem : ByteArray := ⟨#[5, 0, 0, 0, 7, 1, 0, 0]⟩

/-- A memory holding invalid UTF-8. -/
def badMem : ByteArray := ⟨#[0xff, 0xfe]⟩

/-- A call `name(ptr, len)` of the `sexp` module. -/
def call (name : String) (p n : BitVec 32) (mem : ByteArray) : Callout :=
  ⟨("sexp", name), [.num ⟨.int .i32, p⟩, .num ⟨.int .i32, n⟩], some mem⟩

/-- A reply returning the handle `r`. -/
def reply (r : BitVec 32) : HostReply := ⟨.values [Val.i32 r], none⟩

theorem symbol_hi : ((memWrite ix (call "symbol" 1 3 hiMem) (reply 5)).bind view) =
    some (0, [0x68, 0x69, 0x21], [], 5) := by decide +kernel

theorem string_hi : ((memWrite ix (call "string" 1 3 hiMem) (reply 5)).bind view) =
    some (1, [0x68, 0x69, 0x21], [], 5) := by decide +kernel

theorem blob_all : ((memWrite ix (call "blob" 0 5 hiMem) (reply 6)).bind view) =
    some (2, [0, 0x68, 0x69, 0x21, 0], [], 6) := by decide +kernel

theorem sexp_two : ((memWrite ix (call "sexp" 0 2 listMem) (reply 9)).bind view) =
    some (3, [], [5, 0x107], 9) := by decide +kernel

theorem sexp_empty : ((memWrite ix (call "sexp" 8 0 listMem) (reply 9)).bind view) =
    some (3, [], [], 9) := by decide +kernel

/-- Invalid UTF-8 is no symbol. -/
theorem symbol_bad : (memWrite ix (call "symbol" 0 2 badMem) (reply 5)).isNone = true := by
  decide +kernel

/-- ... but it is a blob. -/
theorem blob_bad : ((memWrite ix (call "blob" 0 2 badMem) (reply 5)).bind view) =
    some (2, [0xff, 0xfe], [], 5) := by decide +kernel

/-- Out of bounds: no event. -/
theorem sexp_oob : (memWrite ix (call "sexp" 4 2 listMem) (reply 9)).isNone = true := by
  decide +kernel

/-- A trapping reply is no write. -/
theorem symbol_trap :
    (memWrite ix (call "symbol" 1 3 hiMem) ⟨.trap, none⟩).isNone = true := by decide +kernel

/-- An `i64` reply is no write. -/
theorem symbol_i64 :
    (memWrite ix (call "symbol" 1 3 hiMem) ⟨.values [Val.i64 5], none⟩).isNone = true := by
  decide +kernel

theorem accept_seven :
    ((memAccept ix ⟨("sexp", "accept"), [Val.i32 7], none⟩).bind view) = some (4, [], [], 7) := by
  decide +kernel

/-- Other imports are not accepts. -/
theorem accept_other :
    (memAccept ix ⟨("env", "accept"), [Val.i32 7], none⟩).isNone = true := by decide +kernel

end Silmaril.Wasm.Game.HandleAccept.Memory.Examples
