module

public import Silmaril.Wasm.Component.Reference.WIT.Interp.Defs
public import Silmaril.Wasm.Component.Reference.ABI.Calling.Defs
public import Silmaril.Wasm.Component.Reference.ABI.Layout.Defs
public import Silmaril.Formats.Accept.Thms

/-! # Simple WIT types and their interpretation: theorems

* The interpretation computes: `list<u8>` is `List UInt8`, so the acceptor sets of `list<u8>`
  are byte languages (`valLang_bytes`, `ofByteLang_toByteLang`); `u32` is `UInt32`, `s64` is
  `Int64`, and so on (`interp_prim`).
* String acceptor sets are byte languages through UTF-8, faithfully: UTF-8 is injective, so
  soundness and completeness of string acceptors are reflected by their byte languages
  (`sound_utf8_iff`, `complete_utf8_iff`).
* **Canonical ABI signatures** of the `accept` functions (`CanonicalABI.md`'s `flatten_functype`,
  as `ABI.flattenFunc`): the import `accept: func(list<u8>)` lowers to the core function
  `(i32, i32) -> ()` on a 32-bit memory and `(i64, i64) -> ()` on a 64-bit memory; the export
  `accept: func(list<u8>) -> bool` lifts from `(i32, i32) -> i32`; `accept: func(u32)` and
  `accept: func(u64)` lower to `(i32) -> ()` and `(i64) -> ()`. These are the core signatures
  of the module acceptors of `Silmaril.Wasm.Game.Accept`. A `u8` element has size and alignment
  `1` (`layout_u8`), so a `list<u8>` at `(ptr, len)` occupies exactly `[ptr, ptr + len)`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.WIT

open Silmaril.Formats.Accept

universe u v

variable {Ref : Type u} {Resource : Type v} {E : Env Ref Resource}

theorem interp_prim (p : Primitive) : (ValType.prim p : ValType Ref Resource).Interp E = p.Interp :=
  rfl

/-- The values of `list<u8>` are byte strings. -/
theorem interp_bytes : (ValType.bytes : ValType Ref Resource).Interp E = List UInt8 := rfl

/-- The acceptor sets of `list<u8>` are the byte languages. -/
theorem valLang_bytes : ValLang E (ValType.bytes : ValType Ref Resource) = ByteLang := rfl

@[simp] theorem ofByteLang_toByteLang (A : ValLang E .bytes) :
    ValLang.ofByteLang (ValLang.toByteLang A) = A := rfl

@[simp] theorem toByteLang_ofByteLang (L : ByteLang) :
    ValLang.toByteLang (ValLang.ofByteLang (E := E) L) = L := rfl

/-- A byte language is sound for a specification as a `list<u8>` acceptor iff as a byte
language. -/
theorem sound_ofByteLang {L S : ByteLang} :
    Lang.Sound (ValLang.ofByteLang (E := E) L) (ValLang.ofByteLang S) ↔ Lang.Sound L S := Iff.rfl

/-- UTF-8 is injective. -/
theorem utf8_injective : Function.Injective WIT.utf8 := by
  intro a b h
  have h' : a.toByteArray = b.toByteArray := by
    cases ha : a.toByteArray; cases hb : b.toByteArray
    simp only [WIT.utf8, String.toUTF8_eq_toByteArray, ha, hb] at h
    congr
    exact Array.ext' h
  exact String.toByteArray_inj.1 h'

/-- String acceptors are sound iff their UTF-8 byte languages are. -/
theorem sound_utf8_iff {A S : ValLang E (.prim .string)} :
    Lang.Sound A.utf8 S.utf8 ↔ Lang.Sound A S :=
  Lang.sound_encode_iff (α := String) utf8_injective

/-- String acceptors are complete iff their UTF-8 byte languages are. -/
theorem complete_utf8_iff {A S : ValLang E (.prim .string)} :
    Lang.Complete A.utf8 S.utf8 ↔ Lang.Complete A S :=
  Lang.complete_encode_iff (α := String) utf8_injective

/-! ## Canonical ABI signatures of the acceptors -/

section Canon

open Silmaril.Wasm.Component.ABI

variable {R : Type v}

/-- A `u8` element has size and alignment `1`. -/
theorem layout_u8 (p : AddrType) :
    (layout p (.prim .u8 : ClosedType R)).size = 1 ∧
      (layout p (.prim .u8 : ClosedType R)).alignment = .one := by
  rw [layout]; exact ⟨rfl, rfl⟩

/-- `list<u8>` flattens to a pointer and a length. -/
theorem flatten_bytes (p : AddrType) :
    flatten p (ValType.bytes : ClosedType R) = [pointerType p, pointerType p] := by
  simp [flatten]

/-- The core signature of the lowered import `accept: func(list<u8>)`, 32-bit memory. -/
theorem flattenFunc_accept_import :
    flattenFunc {} .lower (⟨[ValType.bytes], []⟩ : ABI.FuncType R) =
      ⟨[.int .i32, .int .i32], []⟩ := by
  simp [flattenFunc, flattenTypes, flatten, fitParams, pointerType, maxFlatParams, maxFlatResults]

/-- The core signature of the lowered import `accept: func(list<u8>)`, 64-bit memory. -/
theorem flattenFunc_accept_import64 :
    flattenFunc { memory := .i64 } .lower (⟨[ValType.bytes], []⟩ : ABI.FuncType R) =
      ⟨[.int .i64, .int .i64], []⟩ := by
  simp [flattenFunc, flattenTypes, flatten, fitParams, pointerType, maxFlatParams, maxFlatResults]

/-- The core signature of the lifted export `accept: func(list<u8>) -> bool`. -/
theorem flattenFunc_accept_export :
    flattenFunc {} .lift (⟨[ValType.bytes], [.prim .bool]⟩ : ABI.FuncType R) =
      ⟨[.int .i32, .int .i32], [.int .i32]⟩ := by
  simp [flattenFunc, flattenTypes, flatten, flattenPrimitive, fitParams, pointerType,
    maxFlatParams, maxFlatResults]

/-- The core signature of the lowered import `accept: func(u32)`. -/
theorem flattenFunc_accept_u32 :
    flattenFunc {} .lower (⟨[.prim .u32], []⟩ : ABI.FuncType R) = ⟨[.int .i32], []⟩ := by
  simp [flattenFunc, flattenTypes, flatten, flattenPrimitive, fitParams, maxFlatParams,
    maxFlatResults]

/-- The core signature of the lowered import `accept: func(u64)`. -/
theorem flattenFunc_accept_u64 :
    flattenFunc {} .lower (⟨[.prim .u64], []⟩ : ABI.FuncType R) = ⟨[.int .i64], []⟩ := by
  simp [flattenFunc, flattenTypes, flatten, flattenPrimitive, fitParams, maxFlatParams,
    maxFlatResults]

end Canon

end Silmaril.Wasm.Component.WIT
