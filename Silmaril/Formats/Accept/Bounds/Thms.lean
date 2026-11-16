module

public import Silmaril.Formats.Accept.Thms
public import Mathlib.Data.Set.Finite.List

/-! # Byte languages with length bounds

* `UInt8` is finite, so a byte language all of whose strings are shorter than a bound is
  finite (`finite_of_length_lt`, `finite_of_length_le`).
* The size filter `Silmaril.Accept.upTo List.length n L` (strings of length `≤ n`) of any byte
  language is finite (`finite_upTo`), and a language whose strings are all `≤ n` long is its own
  filter (`upTo_eq_self`). Bounds are stated with `<` or `≤` exactly as they arise: an `i32`
  length gives `< 2 ^ 32`, the canonical ABI's `MAX_LIST_BYTE_LENGTH` check gives `≤`.
-/

@[expose] public section

namespace Silmaril.Formats.Accept

/-- Bytes are finitely many. -/
instance : Finite UInt8 := Finite.of_injective UInt8.toFin fun _ _ h => UInt8.toFin_inj.1 h

namespace ByteLang

theorem finite_of_length_lt {L : ByteLang} {n : Nat} (h : ∀ w ∈ L, w.length < n) :
    (L : Set (List UInt8)).Finite :=
  (List.finite_length_lt (α := UInt8) (n := n)).subset h

theorem finite_of_length_le {L : ByteLang} {n : Nat} (h : ∀ w ∈ L, w.length ≤ n) :
    (L : Set (List UInt8)).Finite :=
  (List.finite_length_le (α := UInt8) (n := n)).subset h

/-- The size slices of a byte language are finite. -/
theorem finite_upTo (L : ByteLang) (n : Nat) :
    (Silmaril.Accept.upTo List.length n (L : Set (List UInt8))).Finite :=
  (List.finite_length_le (α := UInt8) (n := n)).subset fun _ h => h.2

/-- A language whose strings are at most `n` long is its own size slice at `n`. -/
theorem upTo_eq_self {L : Set (List UInt8)} {n : Nat} (h : ∀ w ∈ L, w.length ≤ n) :
    Silmaril.Accept.upTo List.length n L = L := by
  ext w; exact ⟨fun hw => hw.1, fun hw => ⟨hw, h w hw⟩⟩

/-- A language of strings shorter than `n + 1` is its own size slice at `n`. -/
theorem upTo_eq_self_of_lt {L : Set (List UInt8)} {n : Nat} (h : ∀ w ∈ L, w.length < n + 1) :
    Silmaril.Accept.upTo List.length n L = L :=
  upTo_eq_self fun w hw => Nat.lt_succ_iff.1 (h w hw)

end ByteLang

end Silmaril.Formats.Accept
