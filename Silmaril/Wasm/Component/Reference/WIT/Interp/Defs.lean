module

public import Silmaril.Wasm.Component.Reference.WIT.Defs
public import Silmaril.Formats.Accept.Defs

/-! # Simple WIT types and their Lean interpretation

The canonical-ABI value types `WIT.ValType Ref Resource` (`Silmaril.Wasm.Component.Reference.WIT`)
are reused, not redefined.

* **Simple types** (`ValType.simple`, `SimpleType`): every type without `future` or `stream`
  anywhere inside it. These are the types whose values are plain data plus handles: no
  asynchronous endpoints. `error-context` is kept: it is a handle like `own`.
* **Interpretation** (`ValType.Interp E t`): the Lean type of the values of `t`.
  * `bool ↦ Bool`, `u8 ↦ UInt8`, `u16 ↦ UInt16`, `u32 ↦ UInt32`, `u64 ↦ UInt64`,
    `s8 ↦ Int8`, `s16 ↦ Int16`, `s32 ↦ Int32`, `s64 ↦ Int64`, `char ↦ Char` (Lean's `Char`
    is exactly a Unicode scalar value, as WIT's `char`), `string ↦ String`.
  * `f32 ↦ BitVec 32`, `f64 ↦ BitVec 64`: IEEE 754 bit patterns, as the component values of
    `Silmaril.Wasm.Component.Value.Val` carry them. The canonical ABI may canonicalise NaN
    payloads on lift (`Value.canonicalizeNaN`), so a float acceptor set relates to the
    reference only up to NaN canonicalisation.
  * `list<T> ↦ List T`, `list<T, N> ↦ Vector T N`, `option<T> ↦ Option T`.
  * `record` and `tuple` ↦ right-nested products ending in `Unit` (field names dropped).
  * `variant` ↦ right-nested sums ending in `Empty` (case `i` is `inr^i (inl _)`; a case
    without payload carries `Unit`); `enum` with `n` cases ↦ `Fin n`; `flags` with `n`
    labels ↦ `BitVec n` (bit `i` is label `i`, the canonical ABI's packing).
  * `result<T, E> ↦ T ⊕ E` (`inl` is `ok`; a missing side is `Unit`).
  * `map<K, V> ↦ List (K × V)`: the canonical ABI's despecialisation (a list of pairs);
    duplicate keys are not excluded at this level.
* **Handles and names** are interpreted by an environment `Env`:
  * `own<R>` and `borrow<R>` ↦ `E.own R` and `E.borrow R`; `error-context ↦ E.errorContext`.
    Ownership (an owned handle moves exactly once, a borrow lives for one call) is a property
    of traces, not of types, so the interpretation only fixes how a handle is named.
    `Env.handles` names handles by their `u32` table index, as the canonical ABI passes them
    and the WASI traces (`Silmaril.Wasi.Theory`) encode them; `Env.reps` by their `Nat`
    representation, as `Value.Val.own`/`borrow` do; `Env.abstract R` by an arbitrary carrier.
  * `ref n ↦ E.named n`. WIT type definitions are acyclic; the only recursion in WIT goes
    through resources, which the interpretation reaches only through handles. The repository's
    WIT types have no recursive (`μ`) form, and `ClosedType` (`Ref = Empty`), the canonical
    ABI's input, has no names at all (`Env.closed`).
  * `future<T>` and `stream<T>` have separate, element-indexed carriers. The synchronous
    environments leave both carriers `Empty`.
* **Value acceptor sets** (`ValLang E t := Lang (t.Interp E)`). The byte languages are the
  acceptor sets of `list<u8>` (`ValType.bytes`), definitionally `Language UInt8`.

A Silmaril addition; types follow the Component Model's `design/mvp/WIT.md` and
`CanonicalABI.md` at the revision pinned by `Silmaril.Wasm.Component.Reference.WIT`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.WIT

open Silmaril.Formats.Accept

universe u v

variable {Ref : Type u} {Resource : Type v}

/-! ## Simple types -/

mutual
/-- No `future` or `stream` occurs in the type. -/
def ValType.simple : ValType Ref Resource → Bool
  | .prim _ | .ref _ | .enum _ | .flags _ | .own _ | .borrow _ | .errorContext => true
  | .list t | .fixedList t _ | .option t | .map _ t => t.simple
  | .record fs => ValType.simpleFields fs
  | .tuple ts => ValType.simpleList ts
  | .variant cs => ValType.simpleCases cs
  | .result ok err => ValType.simpleOpt ok && ValType.simpleOpt err
  | .future _ | .stream _ => false

/-- Every field type is simple. -/
def ValType.simpleFields : List (String × ValType Ref Resource) → Bool
  | [] => true
  | (_, t) :: fs => t.simple && ValType.simpleFields fs

/-- Every type is simple. -/
def ValType.simpleList : List (ValType Ref Resource) → Bool
  | [] => true
  | t :: ts => t.simple && ValType.simpleList ts

/-- Every case payload is simple. -/
def ValType.simpleCases : List (String × Option (ValType Ref Resource)) → Bool
  | [] => true
  | (_, o) :: cs => ValType.simpleOpt o && ValType.simpleCases cs

/-- An absent type, or a simple one. -/
def ValType.simpleOpt : Option (ValType Ref Resource) → Bool
  | none => true
  | some t => t.simple
end

/-- Simple WIT types: no `future` or `stream` inside. -/
abbrev SimpleType (Ref : Type u) (Resource : Type v) :=
  {t : ValType Ref Resource // t.simple = true}

/-! ## Environments -/

/-- How names and handles are interpreted. -/
structure Env (Ref : Type u) (Resource : Type v) where
  /-- The values of the named type `n` (a `use`d or defined, non-recursive type). -/
  named : Ref → Type
  /-- The values of `own<r>`. -/
  own : Resource → Type
  /-- The values of `borrow<r>`. -/
  borrow : Resource → Type
  /-- The values of `error-context`. -/
  errorContext : Type
  /-- The readable end of a `future`, parameterized by the declared element type. -/
  futureEnd : Option (ValType Ref Resource) → Type := fun _ => Empty
  /-- The readable end of a `stream`, parameterized by the declared element type. -/
  streamEnd : Option (ValType Ref Resource) → Type := fun _ => Empty

namespace Env

/-- Handles named by their canonical-ABI table index (`u32`), as core code and the WASI traces
see them. -/
def handles (named : Ref → Type) : Env Ref Resource :=
  { named, own := fun _ => UInt32, borrow := fun _ => UInt32, errorContext := UInt32 }

/-- Handles named by their representation (`Nat`), as `Value.Val.own`/`borrow` carry them. -/
def reps (named : Ref → Type) : Env Ref Resource :=
  { named, own := fun _ => Nat, borrow := fun _ => Nat, errorContext := Nat }

/-- Owned and borrowed handles of resource `r` as values of an arbitrary carrier `R r`. -/
def abstract (named : Ref → Type) (R : Resource → Type) (errorContext : Type) :
    Env Ref Resource :=
  { named, own := R, borrow := R, errorContext }

/-- Extend an environment without changing its primitive, named or resource values. -/
def withEndpoints (E : Env Ref Resource)
    (futureEnd streamEnd : Option (ValType Ref Resource) → Type) : Env Ref Resource :=
  { E with futureEnd, streamEnd }

/-- The closed environment (no names), with handles as table indices. -/
abbrev closed (Resource : Type v) : Env Empty Resource := handles Empty.elim

end Env

/-! ## Interpretation -/

/-- The Lean type of a primitive. -/
@[reducible] def Primitive.Interp : Primitive → Type
  | .bool => Bool
  | .u8 => UInt8 | .u16 => UInt16 | .u32 => UInt32 | .u64 => UInt64
  | .s8 => Int8 | .s16 => Int16 | .s32 => Int32 | .s64 => Int64
  | .f32 => BitVec 32 | .f64 => BitVec 64
  | .char => Char
  | .string => String

mutual
/-- **The Lean type of the values of a WIT type.** -/
@[reducible] def ValType.Interp (E : Env Ref Resource) : ValType Ref Resource → Type
  | .prim p => p.Interp
  | .ref n => E.named n
  | .list t => List (t.Interp E)
  | .fixedList t n => Vector (t.Interp E) n
  | .record fs => ValType.InterpFields E fs
  | .tuple ts => ValType.InterpList E ts
  | .variant cs => ValType.InterpCases E cs
  | .enum cs => Fin cs.length
  | .flags ls => BitVec ls.length
  | .option t => Option (t.Interp E)
  | .result ok err => ValType.InterpOpt E ok ⊕ ValType.InterpOpt E err
  | .map k v => List (k.toPrimitive.Interp × v.Interp E)
  | .own r => E.own r
  | .borrow r => E.borrow r
  | .errorContext => E.errorContext
  | .future element => E.futureEnd element
  | .stream element => E.streamEnd element

/-- Record fields: a right-nested product. -/
@[reducible] def ValType.InterpFields (E : Env Ref Resource) :
    List (String × ValType Ref Resource) → Type
  | [] => Unit
  | (_, t) :: fs => t.Interp E × ValType.InterpFields E fs

/-- Tuple components: a right-nested product. -/
@[reducible] def ValType.InterpList (E : Env Ref Resource) : List (ValType Ref Resource) → Type
  | [] => Unit
  | t :: ts => t.Interp E × ValType.InterpList E ts

/-- Variant cases: a right-nested sum. -/
@[reducible] def ValType.InterpCases (E : Env Ref Resource) :
    List (String × Option (ValType Ref Resource)) → Type
  | [] => Empty
  | (_, o) :: cs => ValType.InterpOpt E o ⊕ ValType.InterpCases E cs

/-- An optional payload: `Unit` when absent. -/
@[reducible] def ValType.InterpOpt (E : Env Ref Resource) : Option (ValType Ref Resource) → Type
  | none => Unit
  | some t => t.Interp E
end

/-! ## Value acceptor sets -/

/-- An acceptor set of values of the WIT type `t`. -/
abbrev ValLang (E : Env Ref Resource) (t : ValType Ref Resource) : Type := Lang (t.Interp E)

/-- `list<u8>`. -/
abbrev ValType.bytes : ValType Ref Resource := .list (.prim .u8)

/-- A byte language as an acceptor set of `list<u8>` values (the identity). -/
def ValLang.ofByteLang {E : Env Ref Resource} (L : ByteLang) : ValLang E .bytes := L

/-- An acceptor set of `list<u8>` values as a byte language (the identity). -/
def ValLang.toByteLang {E : Env Ref Resource} (A : ValLang E .bytes) : ByteLang := A

/-- The UTF-8 bytes of a `string` value. -/
def utf8 (s : String) : List UInt8 := s.toUTF8.data.toList

/-- The byte language of an acceptor set of strings: their UTF-8 encodings (the canonical
ABI's `string-encoding=utf8`). -/
def ValLang.utf8 {E : Env Ref Resource} (A : ValLang E (.prim .string)) : ByteLang :=
  ByteLang.ofEncoding WIT.utf8 A

end Silmaril.Wasm.Component.WIT
