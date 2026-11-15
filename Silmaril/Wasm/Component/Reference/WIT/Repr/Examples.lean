module

public import Silmaril.Wasm.Component.Reference.WIT.Repr.Thms

/-! # Representing Lean types by WIT types: examples

* A structural event type, purely as a representation layer: `variant { num(u64), flag(bool) }`
  represents `UInt64 ⊕ Bool`, and `list<…>` represents event streams. Which streams are valid
  is left to the specification.
* JSONL-shaped inputs, `list<list<u8>>`, with a per-item length bound transported to WIT values.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.WIT.Examples

open Silmaril.Formats.Accept

/-- The WIT event type `variant { num(u64), flag(bool) }`. -/
abbrev evT : ClosedType Unit := .variant [("num", some (.prim .u64)), ("flag", some (.prim .bool))]

/-- Its representation of `UInt64 ⊕ Bool`. -/
def ev : Repr (Env.closed Unit) (UInt64 ⊕ Bool) evT :=
  Repr.variant2 "num" "flag" (Repr.prim .u64) (Repr.prim .bool)

/-- Event streams. -/
def evs : Repr (Env.closed Unit) (List (UInt64 ⊕ Bool)) (.list evT) := Repr.stream ev

example : ev (.inl 5) = .inl (5 : UInt64) := rfl
example : ev (.inr true) = .inr (.inl true) := rfl
example : evs [.inl 1, .inr false] = [.inl (1 : UInt64), .inr (.inl false)] := rfl
example : ev.symm (.inr (.inl true)) = .inr true := rfl

/-- Streams that start with a number. -/
def startsNum : Set (List (UInt64 ⊕ Bool)) := {s | ∃ n t, s = .inl n :: t}

/-- Membership in the represented specification is membership of the Lean stream. -/
example : evs [.inl 3] ∈ evs.lang startsNum := evs.mem_lang.2 ⟨3, [], rfl⟩

/-! ## JSONL-shaped inputs -/

/-- Item lists whose items have at most `n` bytes each (a per-item bound). -/
def perItem (n : Nat) : Set (List (List UInt8)) := {xs | ∀ x ∈ xs, x.length ≤ n}

/-- A WIT validator of `list<list<u8>>` complete within the per-item bound, for a Lean
specification `S`, is the same as its Lean pullback being complete within it. -/
example (A : ValLang (Env.closed Unit) (.list .bytes)) (S : Set (List (List UInt8))) (n : Nat) :
    Lang.CompleteWithin ((Repr.items).lang (perItem n)) A ((Repr.items).lang S) ↔
      Lang.CompleteWithin (perItem n) ((Repr.items).pull A) S :=
  Repr.completeWithin_lang_iff _

end Silmaril.Wasm.Component.WIT.Examples
