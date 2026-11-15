module

public import Silmaril.Wasm.Component.Reference.WIT.Interp.Defs
public import Mathlib.Logic.Equiv.List
public import Mathlib.Logic.Equiv.Option
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Logic.Equiv.Sum

/-! # Representing Lean types by WIT types

A **WIT representation** of a Lean type `α` at a WIT type `t` is an equivalence
`Repr E α t := α ≃ t.Interp E`: every value of `α` has exactly one WIT value of type `t`, and
back. With a representation, a specification `S : Set α` becomes a specification of WIT values
(`Repr.lang r S`), so a component validator taking `t` (`Silmaril.Wasi.Accept.valLang`) can be
sound or complete for `S` itself (`Silmaril.Wasm.Component.WIT.Repr.sound_lang_iff`, …).

Combinators: primitives and `list<u8>` (identities), `list<T>`, `option<T>`, two-element
`tuple<T, U>`, `result<T, U>` (`α ⊕ β`), two-case `variant`s, and composition with any Lean
equivalence (`Repr.ofEquiv`).

**Streams.** WIT types are not recursive, so a recursive syntax tree (a JSON value, a CBOR data
item) has no WIT type of its own. A token or event *stream* does: `list<event>`, where `event`
is a non-recursive WIT `variant`. `Repr.stream r` represents `List α` by `list<t>` from a
representation `r` of one event. JSONL-shaped inputs (one byte string per item) are
`list<list<u8>>` (`Repr.items`). Which streams are *valid* (balanced brackets, lexically valid
numbers, CBOR's tags, indefinite-length boundaries and numeric profile) is a property of the
specification `S` supplied by the format, not of the representation.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.WIT

open Silmaril.Formats.Accept

universe u v

variable {Ref : Type u} {Resource : Type v} {E : Env Ref Resource}

/-- **A WIT representation of `α` at the WIT type `t`.** -/
abbrev Repr (E : Env Ref Resource) (α : Type) (t : ValType Ref Resource) : Type :=
  α ≃ t.Interp E

namespace Repr

variable {α β : Type} {t u : ValType Ref Resource}

/-- A primitive represents its own interpretation. -/
def prim (p : Primitive) : Repr E p.Interp (.prim p) := Equiv.refl _

/-- `list<u8>` represents byte strings. -/
def bytes : Repr E (List UInt8) .bytes := Equiv.refl _

/-- Precompose with a Lean equivalence. -/
def ofEquiv (e : β ≃ α) (r : Repr E α t) : Repr E β t := e.trans r

/-- `list<t>` represents lists. -/
def list (r : Repr E α t) : Repr E (List α) (.list t) := Equiv.listEquivOfEquiv r

/-- `option<t>` represents options. -/
def option (r : Repr E α t) : Repr E (Option α) (.option t) := r.optionCongr

/-- `tuple<t, u>` represents pairs. -/
def pair (r : Repr E α t) (s : Repr E β u) : Repr E (α × β) (.tuple [t, u]) :=
  r.prodCongr (s.trans (Equiv.prodPUnit _).symm)

/-- `result<t, u>` represents sums (`ok` is `inl`). -/
def result (r : Repr E α t) (s : Repr E β u) : Repr E (α ⊕ β) (.result (some t) (some u)) :=
  r.sumCongr s

/-- A two-case `variant { a(t), b(u) }` represents sums. -/
def variant2 (a b : String) (r : Repr E α t) (s : Repr E β u) :
    Repr E (α ⊕ β) (.variant [(a, some t), (b, some u)]) :=
  r.sumCongr (s.trans (Equiv.sumEmpty _ Empty).symm)

/-- **Event streams**: `list<event>` represents lists of events. -/
abbrev stream (r : Repr E α t) : Repr E (List α) (.list t) := list r

/-- **JSONL-shaped inputs**: one byte string per item, as `list<list<u8>>`. -/
def items : Repr E (List (List UInt8)) (.list .bytes) := list bytes

/-- The WIT specification of a Lean specification. -/
def lang (r : Repr E α t) (S : Set α) : ValLang E t := Lang.encode r S

end Repr

end Silmaril.Wasm.Component.WIT
