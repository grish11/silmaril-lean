module

public import Silmaril.Formats.JsonBytes.Depth.Defs
public import Silmaril.Formats.JsonBytes.Decide.Thms
public import Silmaril.Semantics.Accept.Thms
public import Silmaril.Semantics.StreamBounds.Thms
import Silmaril.Proofs.Formats.JsonBytes.Depth

/-!
# JSON texts of bounded nesting depth: lemmas

* `ValueAt.toValue`, `Value.exists_valueAt`, `ValueAt.mono`: depth-indexed derivations are
  derivations, every derivation has a depth, and bounds can be raised;
* `languageAt_mono`, `languageAt_le_language`, `iUnion_languageAt`: the bounded languages
  increase with the bound, and together they are the whole language. So completeness on every
  `languageAt p d` is completeness;
* `valueAt_zero`: depth `0` is exactly the scalars;
* `Decide.textAtB_iff`, `decides_textAtB`: decidable, in the `Silmaril.Accept` vocabulary;
* `byteBracket_not_jsonDepth`: the generic byte bracket depth is not JSON depth. A string
  containing `[[[` is a depth-0 text, but its bytes leave `DepthBound byteBracket 0`;
* examples.
-/

@[expose] public section

namespace Silmaril.Formats.JsonBytes

theorem ValueAt.toValue {p : Profile} {d : Nat} {w : List UInt8} (h : ValueAt p d w) :
    Value p w :=
  Silmaril.Proofs.Formats.JsonBytes.Depth.ValueAt.toValue h

theorem ValueAt.mono {p : Profile} {d e : Nat} {w : List UInt8} (h : ValueAt p d w)
    (hde : d ≤ e) : ValueAt p e w :=
  Silmaril.Proofs.Formats.JsonBytes.Depth.ValueAt.mono h hde

theorem Value.exists_valueAt {p : Profile} {w : List UInt8} (h : Value p w) :
    ∃ d, ValueAt p d w :=
  Silmaril.Proofs.Formats.JsonBytes.Depth.Value.exists_valueAt h

theorem valueAt_zero {p : Profile} {w : List UInt8} :
    ValueAt p 0 w ↔ w ∈ (scalar p).matches' :=
  Silmaril.Proofs.Formats.JsonBytes.Depth.valueAt_zero

theorem languageAt_mono {p : Profile} {d e : Nat} (h : d ≤ e) :
    languageAt p d ≤ languageAt p e :=
  Silmaril.Proofs.Formats.JsonBytes.Depth.languageAt_mono h

theorem languageAt_le_language (p : Profile) (d : Nat) : languageAt p d ≤ language p :=
  Silmaril.Proofs.Formats.JsonBytes.Depth.languageAt_le_language p d

theorem iUnion_languageAt (p : Profile) :
    (⋃ d, (languageAt p d : Set (List UInt8))) = language p :=
  Silmaril.Proofs.Formats.JsonBytes.Depth.iUnion_languageAt p

theorem Decide.textAtB_iff {p : Profile} {d : Nat} {w : List UInt8} :
    Decide.textAtB p d w = true ↔ w ∈ languageAt p d :=
  Silmaril.Proofs.Formats.JsonBytes.Depth.textAtB_iff

instance languageAt.decidableMem (p : Profile) (d : Nat) (w : List UInt8) :
    Decidable (w ∈ languageAt p d) :=
  decidable_of_iff _ Decide.textAtB_iff

theorem decides_textAtB (p : Profile) (d : Nat) :
    Silmaril.Accept.Decides (Decide.textAtB p d) (languageAt p d) :=
  fun _ => Decide.textAtB_iff

/-- The bytes of `"[[["`. -/
def bracketsInString : List UInt8 := [0x22, 0x5B, 0x5B, 0x5B, 0x22]

/-- Byte-level bracket counting is not JSON depth: `"[[["` is a JSON text of depth `0`, but
its bytes have byte-bracket depth `3`. -/
theorem byteBracket_not_jsonDepth :
    bracketsInString ∈ languageAt .rfc8259 0 ∧
      bracketsInString ∉ Silmaril.Streams.DepthBound byteBracket 0 := by
  refine ⟨by decide +kernel, fun h => ?_⟩
  have := Silmaril.Streams.RunBound.le h
  revert this
  decide +kernel

/-! ## Examples -/

section Examples

-- `1` and `"x"` have depth 0; `[]` and `{}` depth 1.
example : [0x31] ∈ languageAt .rfc8259 0 := by decide +kernel
example : [0x5B, 0x5D] ∉ languageAt .rfc8259 0 := by decide +kernel
example : [0x5B, 0x5D] ∈ languageAt .rfc8259 1 := by decide +kernel
example : [0x7B, 0x7D] ∈ languageAt .rfc8259 1 := by decide +kernel
-- `[[1]]` has depth 2.
example : [0x5B, 0x5B, 0x31, 0x5D, 0x5D] ∉ languageAt .rfc8259 1 := by decide +kernel
example : [0x5B, 0x5B, 0x31, 0x5D, 0x5D] ∈ languageAt .rfc8259 2 := by decide +kernel
-- `[1,[2]]`: the depth is the largest element's, plus one.
example : [0x5B, 0x31, 0x2C, 0x5B, 0x32, 0x5D, 0x5D] ∉ languageAt .rfc8259 1 := by
  decide +kernel
example : [0x5B, 0x31, 0x2C, 0x5B, 0x32, 0x5D, 0x5D] ∈ languageAt .rfc8259 2 := by
  decide +kernel
-- `{"a":{"b":[]}}` has depth 3; names add nothing.
example : [0x7B, 0x22, 0x61, 0x22, 0x3A, 0x7B, 0x22, 0x62, 0x22, 0x3A, 0x5B, 0x5D, 0x7D,
    0x7D] ∉ languageAt .rfc8259 2 := by decide +kernel
example : [0x7B, 0x22, 0x61, 0x22, 0x3A, 0x7B, 0x22, 0x62, 0x22, 0x3A, 0x5B, 0x5D, 0x7D,
    0x7D] ∈ languageAt .rfc8259 3 := by decide +kernel
-- `["[["]`: brackets inside strings do not count.
example : [0x5B, 0x22, 0x5B, 0x5B, 0x22, 0x5D] ∈ languageAt .rfc8259 1 := by decide +kernel
-- An invalid text is in no bounded language: `[1,]`.
example : [0x5B, 0x31, 0x2C, 0x5D] ∉ languageAt .rfc8259 5 := by decide +kernel

end Examples

end Silmaril.Formats.JsonBytes

end
