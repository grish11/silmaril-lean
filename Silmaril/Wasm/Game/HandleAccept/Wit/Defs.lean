module

public import Silmaril.Formats.SExp.Family.Defs
public import Silmaril.Wasm.Component.Reference.WIT.Interp.Defs

/-!
# AST payload types as WIT value types

The payload types `Silmaril.Formats.PTy` of tagged ASTs (`WitSig`) are a fragment of the WIT
value types of the Component Model (`WIT.ValType`):

| `PTy` | WIT |
| --- | --- |
| `bool`, `char`, `string` | `bool`, `char`, `string` |
| `s8`, `u8`, `s16`, `u16`, `s32`, `u32`, `s64`, `u64` | the same integer types |
| `f32`, `f64` | `f32`, `f64` |
| `list t` (`bytes = list u8`) | `list<t>` (`list<u8>`) |
| `fixedList t n` | `list<t, n>` |
| `record fs`, `tuple ts` | `record { fs }`, `tuple<ts>` |
| `variant cs`, `enum cs`, `flags ls` | `variant { cs }`, `enum { cs }`, `flags { ls }` |
| `option t`, `result ok err` | `option<t>`, `result<ok, err>` (either side optional) |
| `own r`, `borrow r` | `own<r>`, `borrow<r>` (resource types numbered) |

These are exactly the WIT value types (with resource types `Nat`) without names (`ref`), `map`,
`future`, `stream` and `error-context`: `ofWit` is defined on exactly them and is a left inverse
of `toWit` (`ofWit_toWit`).

`toWit` is that map (for any name type; resource types are numbers, `own r ↦ own r`,
`borrow r ↦ borrow r`), and `valEquiv named t : PTy.Val t ≃ (toWit t).Interp (storedEnv named)`
identifies the payload values with the Lean interpretation of the WIT type
(`WIT.ValType.Interp`) in the **stored-tree environment** `storedEnv named`: owned handles are
resource representations (`Nat`), borrows have no value (`Empty`). A payload vector
`PTy.Vals ps` is the WIT tuple of its types (`valsEquiv`).

**Handles and the environment.** The WIT interpretation leaves handles to an environment
(`WIT.Env`); a stored tree fixes it to `storedEnv`. The *representation* of an `own` payload is
read from an explicit resource table at the call that moves the handle into the tree, which
consumes the handle (`Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own`): the meaning of a
tree depends on that table only through the handles it moved.

`Thms`: every image is a simple type (no `future`/`stream`), and `toWit` is injective
(`ofWit_toWit`).

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit

open Silmaril.Formats Silmaril.Wasm.Component Silmaril.Wasm.Component.WIT

universe u

variable {Ref : Type u}

/-- The primitive payload type of a WIT primitive. -/
def ofPrim : WIT.Primitive → PTy
  | .bool => .bool
  | .s8 => .s8 | .u8 => .u8 | .s16 => .s16 | .u16 => .u16
  | .s32 => .s32 | .u32 => .u32 | .s64 => .s64 | .u64 => .u64
  | .f32 => .f32 | .f64 => .f64 | .char => .char | .string => .string

mutual
/-- **The WIT type of a payload type.** -/
def toWit : PTy → WIT.ValType Ref Nat
  | .bool => .prim .bool
  | .s32 => .prim .s32
  | .u32 => .prim .u32
  | .s64 => .prim .s64
  | .u64 => .prim .u64
  | .string => .prim .string
  | .list t => .list (toWit t)
  | .s8 => .prim .s8
  | .u8 => .prim .u8
  | .s16 => .prim .s16
  | .u16 => .prim .u16
  | .f32 => .prim .f32
  | .f64 => .prim .f64
  | .char => .prim .char
  | .fixedList t n => .fixedList (toWit t) n
  | .record fs => .record (toWitFields fs)
  | .tuple ts => .tuple (toWitList ts)
  | .variant cs => .variant (toWitCases cs)
  | .enum cs => .enum cs
  | .option t => .option (toWit t)
  | .result ok err => .result (toWitOpt ok) (toWitOpt err)
  | .flags ls => .flags ls
  | .own r => .own r
  | .borrow r => .borrow r

/-- The WIT types of a payload vector. -/
def toWitList : List PTy → List (WIT.ValType Ref Nat)
  | [] => []
  | t :: ts => toWit t :: toWitList ts

/-- The WIT fields of record fields (names kept). -/
def toWitFields : List (String × PTy) → List (String × WIT.ValType Ref Nat)
  | [] => []
  | (n, t) :: fs => (n, toWit t) :: toWitFields fs

/-- The WIT cases of variant cases (names kept). -/
def toWitCases : List (String × Option PTy) → List (String × Option (WIT.ValType Ref Nat))
  | [] => []
  | (n, o) :: cs => (n, toWitOpt o) :: toWitCases cs

/-- The WIT type of an optional payload. -/
def toWitOpt : Option PTy → Option (WIT.ValType Ref Nat)
  | none => none
  | some t => some (toWit t)
end

mutual
/-- **The payload type of a WIT type**, when it has one: the left inverse of `toWit`
(`ofWit_toWit`). `none` for names, `map`, `future`, `stream` and `error-context`. -/
def ofWit : WIT.ValType Ref Nat → Option PTy
  | .prim p => some (ofPrim p)
  | .list t => (ofWit t).map .list
  | .fixedList t n => (ofWit t).map (.fixedList · n)
  | .record fs => (ofWitFields fs).map .record
  | .tuple ts => (ofWitList ts).map .tuple
  | .variant cs => (ofWitCases cs).map .variant
  | .enum cs => some (.enum cs)
  | .flags ls => some (.flags ls)
  | .option t => (ofWit t).map .option
  | .result ok err => (ofWitOpt ok).bind fun a => (ofWitOpt err).map fun b => .result a b
  | .own r => some (.own r)
  | .borrow r => some (.borrow r)
  | .ref _ | .map _ _ | .future _ | .stream _ | .errorContext => none

/-- `ofWit` on a list of types. -/
def ofWitList : List (WIT.ValType Ref Nat) → Option (List PTy)
  | [] => some []
  | t :: ts => (ofWit t).bind fun a => (ofWitList ts).map (a :: ·)

/-- `ofWit` on record fields. -/
def ofWitFields : List (String × WIT.ValType Ref Nat) → Option (List (String × PTy))
  | [] => some []
  | (n, t) :: fs => (ofWit t).bind fun a => (ofWitFields fs).map ((n, a) :: ·)

/-- `ofWit` on variant cases. -/
def ofWitCases :
    List (String × Option (WIT.ValType Ref Nat)) → Option (List (String × Option PTy))
  | [] => some []
  | (n, o) :: cs => (ofWitOpt o).bind fun a => (ofWitCases cs).map ((n, a) :: ·)

/-- `ofWit` on an optional payload (`some none` for an absent one). -/
def ofWitOpt : Option (WIT.ValType Ref Nat) → Option (Option PTy)
  | none => some none
  | some t => (ofWit t).map some
end

/-- Lists along an equivalence of elements. -/
def listEquiv {α β : Type} (e : α ≃ β) : List α ≃ List β where
  toFun := List.map e
  invFun := List.map e.symm
  left_inv l := by simp [List.map_map]
  right_inv l := by simp [List.map_map]

/-- Fixed-length vectors along an equivalence of elements. -/
def vectorEquiv {α β : Type} (e : α ≃ β) (n : Nat) : Vector α n ≃ Vector β n where
  toFun v := v.map e
  invFun v := v.map e.symm
  left_inv v := by simp [Vector.map_map]
  right_inv v := by simp [Vector.map_map]

/-- **The stored-tree environment** of WIT handles (`WIT.Env` with resource types named by
numbers): an owned handle stored in a tree is its resource's **representation** (`Nat`, as
`Value.Val.own` carries it; never the handle index, which is meaningful only in the table of the
module at the call that moved it), a `borrow` has **no value** (a borrow cannot outlive the call
that lent it, so no stored tree holds one), and `error-context` none either (unsupported, as are
`future` and `stream`). Names are interpreted by `named`. -/
def storedEnv (named : Ref → Type) : WIT.Env Ref Nat := ⟨named, fun _ => Nat, fun _ => Empty, Empty⟩

mutual
/-- **Payload values are the values of their WIT type** in the stored-tree environment
(`storedEnv`): an `own` payload is the resource's representation, a `borrow` payload has none. -/
def valEquiv (named : Ref → Type) :
    (t : PTy) → t.Val ≃ (toWit t : WIT.ValType Ref Nat).Interp (storedEnv named)
  | .bool => Equiv.refl Bool
  | .s32 => Equiv.refl Int32
  | .u32 => Equiv.refl UInt32
  | .s64 => Equiv.refl Int64
  | .u64 => Equiv.refl UInt64
  | .string => Equiv.refl String
  | .list t => listEquiv (valEquiv named t)
  | .s8 => Equiv.refl Int8
  | .u8 => Equiv.refl UInt8
  | .s16 => Equiv.refl Int16
  | .u16 => Equiv.refl UInt16
  | .f32 => Equiv.refl (BitVec 32)
  | .f64 => Equiv.refl (BitVec 64)
  | .char => Equiv.refl Char
  | .fixedList t n => vectorEquiv (valEquiv named t) n
  | .record fs => fieldsEquiv named fs
  | .tuple ts => valsEquiv named ts
  | .variant cs => casesEquiv named cs
  | .enum cs => Equiv.refl (Fin cs.length)
  | .option t => Equiv.optionCongr (valEquiv named t)
  | .result ok err => Equiv.sumCongr (optEquiv named ok) (optEquiv named err)
  | .flags ls => Equiv.refl (BitVec ls.length)
  | .own _ => Equiv.refl Nat
  | .borrow _ => Equiv.refl Empty

/-- **A payload vector is the WIT tuple of its types.** -/
def valsEquiv (named : Ref → Type) : (ps : List PTy) →
    PTy.Vals ps ≃
      WIT.ValType.InterpList (storedEnv named) (toWitList (Ref := Ref) ps)
  | [] => Equiv.refl Unit
  | t :: ps => Equiv.prodCongr (valEquiv named t) (valsEquiv named ps)

/-- Record field values are the values of the WIT record. -/
def fieldsEquiv (named : Ref → Type) : (fs : List (String × PTy)) →
    PTy.FieldVals fs ≃
      WIT.ValType.InterpFields (storedEnv named) (toWitFields (Ref := Ref) fs)
  | [] => Equiv.refl Unit
  | (_, t) :: fs => Equiv.prodCongr (valEquiv named t) (fieldsEquiv named fs)

/-- Variant case values are the values of the WIT variant. -/
def casesEquiv (named : Ref → Type) : (cs : List (String × Option PTy)) →
    PTy.CaseVals cs ≃
      WIT.ValType.InterpCases (storedEnv named) (toWitCases (Ref := Ref) cs)
  | [] => Equiv.refl Empty
  | (_, o) :: cs => Equiv.sumCongr (optEquiv named o) (casesEquiv named cs)

/-- Optional payload values are the values of the optional WIT type. -/
def optEquiv (named : Ref → Type) : (o : Option PTy) →
    PTy.OptVal o ≃
      WIT.ValType.InterpOpt (storedEnv named) (toWitOpt (Ref := Ref) o)
  | none => Equiv.refl Unit
  | some t => valEquiv named t
end

end Silmaril.Wasm.Game.HandleAccept.Wit
