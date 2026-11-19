module

public import Silmaril.Formats.SExp.Family.Defs
public import Silmaril.Wasm.Component.Reference.WIT.Interp.Defs

/-!
# AST payload types as WIT value types

The payload types `Silmaril.Formats.PTy` of tagged ASTs (`WitSig`) are a fragment of the WIT
value types of the Component Model (`WIT.ValType`):

| `PTy` | WIT |
| --- | --- |
| `bool` | `bool` |
| `s32`, `u32`, `s64`, `u64` | `s32`, `u32`, `s64`, `u64` |
| `string` | `string` |
| `bytes` | `list<u8>` |
| `list t` | `list<t>` |

`toWit` is that map (for any name and resource types: the image mentions neither), and
`valEquiv E t : PTy.Val t ≃ (toWit t).Interp E` identifies the payload values with the Lean
interpretation of the WIT type (`WIT.ValType.Interp`) in every
environment `E`. A payload vector `PTy.Vals ps` is the WIT tuple of its types (`valsEquiv`).
`Thms`: every image is a simple type (no `future`/`stream`), and `toWit` is injective.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit

open Silmaril.Formats Silmaril.Wasm.Component Silmaril.Wasm.Component.WIT

universe u v

variable {Ref : Type u} {Resource : Type v}

/-- **The WIT type of a payload type.** -/
def toWit : PTy → WIT.ValType Ref Resource
  | .bool => .prim .bool
  | .s32 => .prim .s32
  | .u32 => .prim .u32
  | .s64 => .prim .s64
  | .u64 => .prim .u64
  | .string => .prim .string
  | .bytes => .list (.prim .u8)
  | .list t => .list (toWit t)

/-- The WIT types of a payload vector. -/
def toWitList (ps : List PTy) : List (WIT.ValType Ref Resource) :=
  ps.map toWit

/-- Lists along an equivalence of elements. -/
def listEquiv {α β : Type} (e : α ≃ β) : List α ≃ List β where
  toFun := List.map e
  invFun := List.map e.symm
  left_inv l := by simp [List.map_map]
  right_inv l := by simp [List.map_map]

/-- **Payload values are the values of their WIT type**, in every environment. -/
def valEquiv (E : WIT.Env Ref Resource) :
    (t : PTy) → t.Val ≃ (toWit t : WIT.ValType Ref Resource).Interp E
  | .bool => Equiv.refl Bool
  | .s32 => Equiv.refl Int32
  | .u32 => Equiv.refl UInt32
  | .s64 => Equiv.refl Int64
  | .u64 => Equiv.refl UInt64
  | .string => Equiv.refl String
  | .bytes => Equiv.refl (List UInt8)
  | .list t => listEquiv (valEquiv E t)

/-- **A payload vector is the WIT tuple of its types.** -/
def valsEquiv (E : WIT.Env Ref Resource) : (ps : List PTy) →
    PTy.Vals ps ≃
      WIT.ValType.InterpList E (toWitList (Ref := Ref) (Resource := Resource) ps)
  | [] => Equiv.refl Unit
  | t :: ps => Equiv.prodCongr (valEquiv E t) (valsEquiv E ps)

end Silmaril.Wasm.Game.HandleAccept.Wit
