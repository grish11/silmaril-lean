module

public import Silmaril.Formats.Utf16.Defs
import Silmaril.Proofs.Formats.Utf16.Basic

/-!
# The languages of well-formed UTF-16 bytes: lemmas

* `units_eq_some_iff`: reading bytes as code units inverts `serialize`;
* `wellFormedUnitsB_iff`, `isWellFormed_iff`: the executable checks decide well-formedness and
  `language e`, hence the `Decidable` instances (and one for `schemeLanguage`);
* `wellFormedUnits_iff_exists_chars`, `mem_language_iff_exists_chars`: the well-formed sequences
  are exactly the encodings of strings of Unicode scalar values (Lean `Char`s), and
  `encodeChar_injective`: distinct scalar values have distinct encodings;
* examples: both byte orders, a surrogate pair, the byte-order-mark policy, and the ill-formed
  cases (lone, reversed and truncated surrogates, odd length).
-/

@[expose] public section

namespace Silmaril.Formats.Utf16

theorem units_eq_some_iff {e : Endian} {w : List UInt8} {us : List UInt16} :
    units e w = some us ↔ w = serialize e us :=
  Silmaril.Proofs.Formats.Utf16.units_eq_some_iff

/-- The executable check decides well-formedness of code units. -/
theorem wellFormedUnitsB_iff {us : List UInt16} :
    wellFormedUnitsB us = true ↔ WellFormedUnits us :=
  Silmaril.Proofs.Formats.Utf16.wellFormedUnitsB_iff

/-- The executable check decides the language. -/
theorem isWellFormed_iff {e : Endian} {w : List UInt8} :
    isWellFormed e w = true ↔ w ∈ language e :=
  Silmaril.Proofs.Formats.Utf16.isWellFormed_iff

instance WellFormedUnits.decidable (us : List UInt16) : Decidable (WellFormedUnits us) :=
  decidable_of_iff _ wellFormedUnitsB_iff

instance language.decidableMem (e : Endian) (w : List UInt8) : Decidable (w ∈ language e) :=
  decidable_of_iff _ isWellFormed_iff

theorem mem_schemeLanguage_iff {w : List UInt8} :
    w ∈ schemeLanguage ↔
      if w.take 2 = [0xFF, 0xFE] then w.drop 2 ∈ language .little else w ∈ language .big := by
  change (∃ t ∈ language .little, w = [0xFF, 0xFE] ++ t) ∨
    (w ∈ language .big ∧ w.take 2 ≠ [0xFF, 0xFE]) ↔ _
  split
  · rename_i h
    refine ⟨?_, fun ht => Or.inl ⟨_, ht, by rw [← h, List.take_append_drop]⟩⟩
    rintro (⟨t, ht, rfl⟩ | ⟨-, hn⟩)
    · simpa using ht
    · exact absurd h hn
  · rename_i h
    refine ⟨?_, fun hb => Or.inr ⟨hb, h⟩⟩
    rintro (⟨t, -, rfl⟩ | ⟨hb, -⟩)
    · exact absurd (by simp) h
    · exact hb

instance schemeLanguage.decidableMem (w : List UInt8) : Decidable (w ∈ schemeLanguage) :=
  decidable_of_iff' _ mem_schemeLanguage_iff

/-- Encoded scalar values are well-formed. -/
theorem encodeUnits_wellFormed (cs : List Char) : WellFormedUnits (encodeUnits cs) :=
  Silmaril.Proofs.Formats.Utf16.encodeUnits_wellFormed cs

/-- The well-formed code-unit sequences are exactly the encodings of scalar-value strings. -/
theorem wellFormedUnits_iff_exists_chars {us : List UInt16} :
    WellFormedUnits us ↔ ∃ cs, us = encodeUnits cs :=
  Silmaril.Proofs.Formats.Utf16.wellFormedUnits_iff_exists_chars

/-- The language is exactly the serialized encodings of scalar-value strings. -/
theorem mem_language_iff_exists_chars {e : Endian} {w : List UInt8} :
    w ∈ language e ↔ ∃ cs, w = serialize e (encodeUnits cs) :=
  Silmaril.Proofs.Formats.Utf16.mem_language_iff_exists_chars

theorem encodeChar_injective : Function.Injective encodeChar :=
  Silmaril.Proofs.Formats.Utf16.encodeChar_injective

/-! ## Examples -/

section Examples

-- `A` (`U+0041`) in each byte order.
example : [0x00, 0x41] ∈ language .big := by decide +kernel
example : [0x41, 0x00] ∈ language .little := by decide +kernel
-- `U+1F600` (😀) is the surrogate pair `D83D DE00`.
example : encodeChar '😀' = [0xD83D, 0xDE00] := by decide +kernel
example : [0xD8, 0x3D, 0xDE, 0x00] ∈ language .big := by decide +kernel
example : [0x3D, 0xD8, 0x00, 0xDE] ∈ language .little := by decide +kernel
example : serialize .big (encodeUnits ['A', '😀']) = [0x00, 0x41, 0xD8, 0x3D, 0xDE, 0x00] := by
  decide +kernel
-- `U+FFFF` and `U+E000` are not surrogates.
example : [0xFF, 0xFF, 0xE0, 0x00] ∈ language .big := by decide +kernel

-- A lone high surrogate, a lone low surrogate, a reversed pair, a truncated pair.
example : [0xD8, 0x3D] ∉ language .big := by decide +kernel
example : [0xDE, 0x00] ∉ language .big := by decide +kernel
example : [0xDE, 0x00, 0xD8, 0x3D] ∉ language .big := by decide +kernel
example : [0xD8, 0x3D, 0x00, 0x41] ∉ language .big := by decide +kernel
-- Odd length.
example : [0x00, 0x41, 0x00] ∉ language .big := by decide +kernel
-- The same bytes are well-formed in one byte order only: `00D8` big-endian, the lone
-- surrogate `D800` little-endian.
example : [0x00, 0xD8] ∈ language .big := by decide +kernel
example : [0x00, 0xD8] ∉ language .little := by decide +kernel

-- Explicit-endian schemes keep `FE FF` as the character `U+FEFF`.
example : [0xFE, 0xFF, 0x00, 0x41] ∈ language .big := by decide +kernel
example : [0xFF, 0xFE, 0x41, 0x00] ∈ language .little := by decide +kernel
-- The UTF-16 scheme: big-endian without a mark, or the mark `FF FE` and little-endian text.
example : [0x00, 0x41] ∈ schemeLanguage := by decide +kernel
example : [0xFF, 0xFE, 0x41, 0x00] ∈ schemeLanguage := by decide +kernel
example : [0xFF, 0xFE, 0x3D, 0xD8, 0x00, 0xDE] ∈ schemeLanguage := by decide +kernel
-- Without a mark, `3D D8 00 DE` is read big-endian (`U+3DD8 U+00DE`), not as the little-endian
-- pair `D83D DE00`.
example : [0x3D, 0xD8, 0x00, 0xDE] ∈ schemeLanguage := by decide +kernel
example : [0xD8, 0x3D] ∉ schemeLanguage := by decide +kernel
-- After the mark `FF FE` the text is little-endian, so this well-formed UTF-16BE is rejected.
example : [0xFF, 0xFE, 0x00, 0xD8] ∈ language .big := by decide +kernel
example : [0xFF, 0xFE, 0x00, 0xD8] ∉ schemeLanguage := by decide +kernel

end Examples

end Silmaril.Formats.Utf16

end
