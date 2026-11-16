module

public import Silmaril.Wasi.Component.Accept.Thms
import Silmaril.Proofs.Wasi.Component.Accept.Acceptor

/-! # Inputs accepted by a component: specification components and tests

* **Every byte language is the acceptor set of a component**, through an import
  (`bytesLang_importAcceptor`) and through an export (`exportBytesLang_exportAcceptor`): the
  specification components `importAcceptor L run` and `exportAcceptor L` accept exactly `L`
  (sound and complete, `Lang.Exact`).
* **Decoding tests** (`rfl`, by evaluation in the kernel): records, options, results, enums,
  flags, handles, strings and byte lists decode at their WIT types, and ill-shaped values are
  rejected.

Proofs: `Silmaril.Proofs.Wasi.Component.Accept.Acceptor`.
-/

@[expose] public section

namespace Silmaril.Wasi.Accept.Examples

open Silmaril.Formats.Accept Silmaril.Wasi Silmaril.Wasi.Accept
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.WIT

/-- **The import acceptor accepts exactly its language.** -/
theorem bytesLang_importAcceptor (L : ByteLang) (run : FnName) :
    bytesLang (importAcceptor L run) = L :=
  Silmaril.Proofs.Wasi.Component.Accept.bytesLang_importAcceptor L run

/-- **The export acceptor accepts exactly its language.** -/
theorem exportBytesLang_exportAcceptor (L : ByteLang) :
    exportBytesLang (exportAcceptor L) = L :=
  Silmaril.Proofs.Wasi.Component.Accept.exportBytesLang_exportAcceptor L

/-- The import acceptor is sound and complete for its language. -/
theorem importAcceptor_exact (L : ByteLang) (run : FnName) :
    Lang.Exact (bytesLang (importAcceptor L run)) L :=
  bytesLang_importAcceptor L run

/-- An acceptor component for `L` is sound for every weaker specification. -/
theorem importAcceptor_sound {L S : ByteLang} (h : L ≤ S) (run : FnName) :
    Lang.Sound (bytesLang (importAcceptor L run)) S :=
  (bytesLang_importAcceptor L run).symm ▸ h

/-- Both readings agree on the specification components. -/
example (L : ByteLang) (run : FnName) :
    bytesLang (importAcceptor L run) = exportBytesLang (exportAcceptor L) := by
  rw [bytesLang_importAcceptor, exportBytesLang_exportAcceptor]

/-! ## Decoding tests -/

/-- The resources of the tests. -/
abbrev Res := Unit

example : bytes? (bytesVal [104, 105]) = some [104, 105] := rfl

example : decode (ValType.bytes : ClosedType Res) (bytesVal [1, 2, 3]) = some ([1, 2, 3] : List UInt8) := rfl

/-- A `list<u8>` holding a non-`u8` is rejected. -/
example : decode (ValType.bytes : ClosedType Res) (.record [.u8 1, .u16 2]) = none := rfl

example : decode (.prim .u32 : ClosedType Res) (.u32 7) = some (7 : UInt32) := rfl

example : decode (.prim .s64 : ClosedType Res) (.s64 (-1)) = some (-1 : Int64) := rfl

/-- A `u32` is not an `s32`. -/
example : decode (.prim .s32 : ClosedType Res) (.u32 7) = none := rfl

example : decode (.prim .string : ClosedType Res) (strV "ok") = some "ok" := rfl

example : decode (.record [("a", .prim .u32), ("b", .option (.prim .bool))] : ClosedType Res)
    (.record [.u32 5, .variant 1 (some (.bool true))]) = some ((5 : UInt32), some true, ()) := rfl

/-- A record with a missing field is rejected. -/
example : decode (.record [("a", .prim .u32), ("b", .prim .bool)] : ClosedType Res)
    (.record [.u32 5]) = none := rfl

example : decode (.result (some (.prim .u8)) none : ClosedType Res) (okV (some (.u8 3))) =
    some (.inl (3 : UInt8)) := rfl

example : decode (.result (some (.prim .u8)) none : ClosedType Res) (errV none) =
    some (.inr ()) := rfl

/-- `result<u8>` has no error payload. -/
example : decode (.result (some (.prim .u8)) none : ClosedType Res) (errV (some (.u8 3))) =
    none := rfl

example : decode (.enum ["red", "green", "blue"] : ClosedType Res) (.variant 2 none) =
    some (2 : Fin 3) := rfl

/-- An enum case out of range is rejected. -/
example : decode (.enum ["red", "green", "blue"] : ClosedType Res) (.variant 3 none) = none := rfl

example : decode (.flags ["r", "w", "x"] : ClosedType Res)
    (.record [.bool true, .bool false, .bool true]) = some (0b101 : BitVec 3) := rfl

example : decode (.variant [("none", none), ("n", some (.prim .u32))] : ClosedType Res)
    (.variant 1 (some (.u32 9))) = some (.inr (.inl (9 : UInt32))) := rfl

/-- Handles are table indices. -/
example : decode (.own () : ClosedType Res) (.u32 4) = some (4 : UInt32) := rfl

example : decode (.borrow () : ClosedType Res) (.u32 4) = some (4 : UInt32) := rfl

example : decode (.tuple [.prim .char, .list (.prim .bool)] : ClosedType Res)
    (.record [.char 'x', .record [.bool true]]) = some ('x', [true], ()) := rfl

example : decode (.map .string (.prim .u8) : ClosedType Res)
    (.record [.record [strV "k", .u8 1]]) = some [("k", (1 : UInt8))] := rfl

/-- `future` and `stream` (outside the simple types) decode nothing. -/
example : decode (.stream none : ClosedType Res) (.u32 0) = none := rfl

end Silmaril.Wasi.Accept.Examples
