module

public import Silmaril.Formats.Utf8.Defs
import Silmaril.Proofs.Formats.Utf8.Basic
import Silmaril.Proofs.Formats.Utf8.Core

/-!
# The language of well-formed UTF-8 bytes: lemmas

* `mem_byteRange`, `mem_word`, `mem_anyOf`: the byte classes and words mean what they say;
* `isWellFormed_iff`: the executable check decides the language, hence the `Decidable`
  instances `IsWellFormed.decidable` and `Bytes.IsUtf8.decidable`;
* `isWellFormed_iff_flatten`: a well-formed sequence is a concatenation of encoded scalars;
* `isWellFormed_nil`, `isWellFormed_append`, `isWellFormed_of_ascii`: closure properties;
* the bridge to Lean core's UTF-8 (`String.utf8EncodeChar`, `List.utf8Encode`,
  `ByteArray.IsValidUTF8`, `ByteArray.validateUTF8`, `String.fromUTF8?`): `scalar` is exactly
  the image of `String.utf8EncodeChar` (`utf8EncodeChar_mem_scalar`,
  `exists_char_of_mem_scalar`) and the language is exactly the image of
  `List.flatMap String.utf8EncodeChar` (`isWellFormed_iff_exists_chars`), hence
  `isValidUTF8_iff`, `validateUTF8_iff`, `fromUTF8?_isSome_iff`, `toUTF8_isWellFormed` and
  `Bytes.isUtf8_iff_isValidUTF8`;
* worked examples, accepted and rejected, for every row of Table 3-7.
-/

@[expose] public section

namespace Silmaril.Formats.Utf8

open RegularExpression

theorem mem_anyOf {l w : List UInt8} : w ∈ (anyOf l).matches' ↔ ∃ b ∈ l, w = [b] :=
  Silmaril.Proofs.Formats.Utf8.mem_anyOf

theorem mem_rangeList {lo hi b : UInt8} : b ∈ rangeList lo hi ↔ lo ≤ b ∧ b ≤ hi :=
  Silmaril.Proofs.Formats.Utf8.mem_rangeList

theorem mem_byteRange {lo hi : UInt8} {w : List UInt8} :
    w ∈ (byteRange lo hi).matches' ↔ ∃ b, w = [b] ∧ lo ≤ b ∧ b ≤ hi :=
  Silmaril.Proofs.Formats.Utf8.mem_byteRange

theorem mem_word {l w : List UInt8} : w ∈ (word l).matches' ↔ w = l :=
  Silmaril.Proofs.Formats.Utf8.mem_word

theorem mem_ascii {w : List UInt8} : w ∈ ascii.matches' ↔ ∃ b, w = [b] ∧ b < 0x80 :=
  Silmaril.Proofs.Formats.Utf8.mem_ascii

/-- The executable check decides the language. -/
theorem isWellFormed_iff {w : List UInt8} : isWellFormed w = true ↔ IsWellFormed w :=
  Silmaril.Proofs.Formats.Utf8.isWellFormed_iff

instance IsWellFormed.decidable (w : List UInt8) : Decidable (IsWellFormed w) :=
  decidable_of_iff _ isWellFormed_iff

instance _root_.Silmaril.Formats.Bytes.IsUtf8.decidable (b : Bytes) : Decidable b.IsUtf8 :=
  IsWellFormed.decidable b.toList

theorem isWellFormed_iff_flatten {w : List UInt8} :
    IsWellFormed w ↔ ∃ L : List (List UInt8), w = L.flatten ∧ ∀ y ∈ L, y ∈ scalar.matches' :=
  Silmaril.Proofs.Formats.Utf8.isWellFormed_iff_flatten

theorem isWellFormed_nil : IsWellFormed [] := Silmaril.Proofs.Formats.Utf8.isWellFormed_nil

theorem isWellFormed_append {a b : List UInt8} (ha : IsWellFormed a) (hb : IsWellFormed b) :
    IsWellFormed (a ++ b) :=
  Silmaril.Proofs.Formats.Utf8.isWellFormed_append ha hb

theorem scalar_isWellFormed {w : List UInt8} (h : w ∈ scalar.matches') : IsWellFormed w :=
  Silmaril.Proofs.Formats.Utf8.scalar_isWellFormed h

/-- Every ASCII byte list is well-formed UTF-8. -/
theorem isWellFormed_of_ascii {w : List UInt8} (h : ∀ b ∈ w, b < 0x80) : IsWellFormed w :=
  Silmaril.Proofs.Formats.Utf8.isWellFormed_of_ascii h


/-! ## The bridge to Lean core's UTF-8 -/

/-- Lean core encodes every character as one row of Table 3-7. -/
theorem utf8EncodeChar_mem_scalar (c : Char) : String.utf8EncodeChar c ∈ scalar.matches' :=
  Silmaril.Proofs.Formats.Utf8.Core.utf8EncodeChar_mem_scalar c

/-- Every row of Table 3-7 is Lean core's encoding of some character. -/
theorem exists_char_of_mem_scalar {w : List UInt8} (h : w ∈ scalar.matches') :
    ∃ c : Char, String.utf8EncodeChar c = w :=
  Silmaril.Proofs.Formats.Utf8.Core.exists_char_of_mem_scalar h

/-- The language is exactly the set of encodings of character lists. -/
theorem isWellFormed_iff_exists_chars {w : List UInt8} :
    IsWellFormed w ↔ ∃ cs : List Char, w = cs.flatMap String.utf8EncodeChar :=
  Silmaril.Proofs.Formats.Utf8.Core.isWellFormed_iff_exists_chars

/-- Lean core's `ByteArray.IsValidUTF8` is this language on the list view. -/
theorem isValidUTF8_iff {b : ByteArray} : b.IsValidUTF8 ↔ IsWellFormed b.data.toList :=
  Silmaril.Proofs.Formats.Utf8.Core.isValidUTF8_iff

/-- Lean core's executable validator `ByteArray.validateUTF8` decides this language. -/
theorem validateUTF8_iff {b : ByteArray} : b.validateUTF8 = true ↔ IsWellFormed b.data.toList :=
  ByteArray.validateUTF8_eq_true_iff.trans isValidUTF8_iff

/-- `String.fromUTF8?` succeeds exactly on this language. -/
theorem fromUTF8?_isSome_iff {b : ByteArray} :
    (String.fromUTF8? b).isSome ↔ IsWellFormed b.data.toList :=
  Silmaril.Proofs.Formats.Utf8.Core.fromUTF8?_isSome_iff

/-- The bytes of every Lean `String` are well-formed UTF-8. -/
theorem toUTF8_isWellFormed (s : String) : IsWellFormed s.toUTF8.data.toList :=
  isValidUTF8_iff.mp s.isValidUTF8

theorem _root_.Silmaril.Formats.Bytes.isUtf8_iff_isValidUTF8 (b : Bytes) :
    b.IsUtf8 ↔ b.data.IsValidUTF8 :=
  isValidUTF8_iff.symm

/-! ## Examples: one accepted and one rejected sequence per row of Table 3-7 -/

section Examples

-- `U+0041` and `U+007F`.
example : IsWellFormed [0x41, 0x7F] := by decide +kernel
-- `U+00E9` (é), `U+07FF`.
example : IsWellFormed [0xC3, 0xA9, 0xDF, 0xBF] := by decide +kernel
-- `U+0800`, `U+20AC` (€), `U+D7FF` (last scalar before the surrogates), `U+E000`, `U+FFFF`.
example : IsWellFormed [0xE0, 0xA0, 0x80] := by decide +kernel
example : IsWellFormed [0xE2, 0x82, 0xAC] := by decide +kernel
example : IsWellFormed [0xED, 0x9F, 0xBF] := by decide +kernel
example : IsWellFormed [0xEE, 0x80, 0x80] := by decide +kernel
example : IsWellFormed [0xEF, 0xBF, 0xBF] := by decide +kernel
-- The byte-order mark `U+FEFF` is well-formed UTF-8.
example : IsWellFormed [0xEF, 0xBB, 0xBF] := by decide +kernel
-- `U+10000`, `U+1F600` (😀), `U+10FFFF` (the last scalar value).
example : IsWellFormed [0xF0, 0x90, 0x80, 0x80] := by decide +kernel
example : IsWellFormed [0xF0, 0x9F, 0x98, 0x80] := by decide +kernel
example : IsWellFormed [0xF4, 0x8F, 0xBF, 0xBF] := by decide +kernel

-- Overlong encodings of `U+0000`, `U+007F`, `U+07FF` and `U+FFFF`.
example : ¬ IsWellFormed [0xC0, 0x80] := by decide +kernel
example : ¬ IsWellFormed [0xC1, 0xBF] := by decide +kernel
example : ¬ IsWellFormed [0xE0, 0x9F, 0xBF] := by decide +kernel
example : ¬ IsWellFormed [0xF0, 0x8F, 0xBF, 0xBF] := by decide +kernel
-- Encoded surrogates `U+D800` and `U+DFFF` (CESU-8 style).
example : ¬ IsWellFormed [0xED, 0xA0, 0x80] := by decide +kernel
example : ¬ IsWellFormed [0xED, 0xBF, 0xBF] := by decide +kernel
-- Beyond `U+10FFFF`; lead bytes `F5..FF` never occur.
example : ¬ IsWellFormed [0xF4, 0x90, 0x80, 0x80] := by decide +kernel
example : ¬ IsWellFormed [0xF5, 0x80, 0x80, 0x80] := by decide +kernel
example : ¬ IsWellFormed [0xFF] := by decide +kernel
-- A stray continuation byte, truncated sequences, and a bad continuation byte.
example : ¬ IsWellFormed [0x80] := by decide +kernel
example : ¬ IsWellFormed [0x41, 0xC3] := by decide +kernel
example : ¬ IsWellFormed [0xE2, 0x82] := by decide +kernel
example : ¬ IsWellFormed [0xF0, 0x9F, 0x98] := by decide +kernel
example : ¬ IsWellFormed [0xC3, 0x41] := by decide +kernel

-- The same check on a `Bytes` value.
example : (Bytes.ofList [0x68, 0xC3, 0xA9]).IsUtf8 := by decide +kernel

-- Lean core's validator agrees, here derived from the decision procedure of this language.
example : [0xC0, 0x80].toByteArray.validateUTF8 = false := by
  rw [Bool.eq_false_iff, ne_eq, validateUTF8_iff]; decide +kernel
example : [0xF0, 0x9F, 0x98, 0x80].toByteArray.validateUTF8 = true := by
  rw [validateUTF8_iff]; decide +kernel
example : (String.fromUTF8? [0xED, 0xA0, 0x80].toByteArray).isSome = false := by
  rw [Bool.eq_false_iff, ne_eq, fromUTF8?_isSome_iff]; decide +kernel

end Examples

end Silmaril.Formats.Utf8

end
