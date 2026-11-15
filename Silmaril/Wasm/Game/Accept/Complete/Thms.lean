module

public import Silmaril.Wasm.Game.Accept.Acceptor.Thms
public import Silmaril.Formats.Accept.Bounded.Thms

/-! # Completeness of one-call module acceptors is bounded

Scope: a `ModuleAcceptor` observes a whole input in **one** call of `accept(ptr, len)`, with
`len` an `i32` (or `i64` for `memory64`). For that interface:

* its language is finite (`ModuleAcceptor.lang_finite`), so it is **complete for no infinite
  specification** (`ModuleAcceptor.not_complete_of_infinite`); every infinite format language
  (all valid JSON texts, all JSONL streams, all CBOR items) is out of reach;
* it can at best be complete **within** the length bound of the interface: inputs shorter
  than `addrBound A.addr` (`ModuleAcceptor.completeWithin_iff`), and any bounded completeness
  it has is over a finite part of the specification (`finite_of_completeWithin`).

This is a statement about the one-call interface, not about validators in general: a module
that receives its input in several calls (chunks, items, events) is not covered, and nothing
here says that unbounded streaming completeness is impossible.
-/

@[expose] public section

namespace Silmaril.Wasm.Game.Accept.ModuleAcceptor

open Silmaril.Formats.Accept

variable (A : ModuleAcceptor) {S : Set (List UInt8)}

/-- **A one-call module acceptor is complete for no infinite specification.** -/
theorem not_complete_of_infinite (hS : S.Infinite) : ¬ Lang.Complete A.lang S :=
  Lang.not_complete_of_finite A.lang_finite hS

/-- Its strict language neither. -/
theorem not_complete_strict_of_infinite (hS : S.Infinite) : ¬ Lang.Complete A.strictLang S :=
  Lang.not_complete_of_finite A.strictLang_finite hS

/-- Completeness within the interface's length bound is completeness on the short inputs:
outside the bound the acceptor accepts nothing. -/
theorem completeWithin_iff :
    Lang.CompleteWithin (Silmaril.Accept.within List.length (addrBound A.addr - 1)) A.lang S ↔
      Lang.Complete A.lang (S ∩ Silmaril.Accept.within List.length (addrBound A.addr - 1)) :=
  Iff.rfl

/-- Accepted strings are within the interface's bound. -/
theorem mem_within_of_mem_lang {w : List UInt8} (h : w ∈ A.lang) :
    w ∈ Silmaril.Accept.within List.length (addrBound A.addr - 1) := by
  have := A.length_lt h
  show w.length ≤ addrBound A.addr - 1
  omega

/-- Soundness only needs checking inside the bound. -/
theorem sound_iff_soundWithin :
    Lang.Sound A.lang S ↔
      Lang.SoundWithin (Silmaril.Accept.within List.length (addrBound A.addr - 1)) A.lang S :=
  ⟨fun h => h.soundWithin _, fun h _ hw => h ⟨hw, A.mem_within_of_mem_lang hw⟩⟩

theorem finite_of_completeWithin {D : Set (List UInt8)} (h : Lang.CompleteWithin D A.lang S) :
    (S ∩ D).Finite :=
  Lang.finite_of_completeWithin A.lang_finite h

end Silmaril.Wasm.Game.Accept.ModuleAcceptor
