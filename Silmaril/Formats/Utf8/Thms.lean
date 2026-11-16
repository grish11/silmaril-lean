module

public import Silmaril.Formats.Utf8.Defs
import Silmaril.Proofs.Formats.Utf8.Basic
import Silmaril.Proofs.Formats.Utf8.Core
import Silmaril.Proofs.Formats.Utf8.Encode
import Silmaril.Proofs.Formats.Utf8.Transport

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
* the encoding of character lists, `encode`: it distributes over `++` (`encode_append`), is
  injective (`encode_injective`), so a split of an encoding into well-formed parts is a split of
  the characters (`encode_eq_append`); `String.fromUTF8?` inverts it (`fromUTF8?_eq_some`,
  `fromUTF8?_encode`); ASCII bytes are the encoding of `ofAscii` (`encode_ofAscii`, `eq_ofAscii`);
* byte regular expressions on encodings (`encode_mem_mul`, `encode_mem_add`, `encode_mem_star`,
  `encode_mem_one`, `encode_mem_char`, `encode_mem_byteRange`, `encode_mem_multibyte`): a match
  of `encode cs` is a condition on the characters `cs`, given that the expressions are `Good`
  (all their words are well-formed UTF-8; `good_mul` … `good_multibyte`). Grammars written over
  bytes can so be compared with readers that work on characters;
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

/-! ## The encoding of character lists -/

@[simp] theorem encode_nil : encode [] = [] := rfl

@[simp] theorem encode_cons (c : Char) (cs : List Char) :
    encode (c :: cs) = String.utf8EncodeChar c ++ encode cs :=
  Silmaril.Proofs.Formats.Utf8.Encode.encode_cons c cs

@[simp] theorem encode_append (a b : List Char) : encode (a ++ b) = encode a ++ encode b :=
  Silmaril.Proofs.Formats.Utf8.Encode.encode_append a b

/-- The encoding is injective: Lean core decodes it back (`String.ofList`). -/
theorem encode_injective {cs cs' : List Char} (h : encode cs = encode cs') : cs = cs' :=
  Silmaril.Proofs.Formats.Utf8.Encode.encode_injective h

theorem isWellFormed_encode (cs : List Char) : IsWellFormed (encode cs) :=
  Silmaril.Proofs.Formats.Utf8.Encode.isWellFormed_encode cs

/-- **Splitting an encoding** into two well-formed parts splits the characters. -/
theorem encode_eq_append {cs : List Char} {a b : List UInt8} (h : encode cs = a ++ b)
    (ha : IsWellFormed a) (hb : IsWellFormed b) :
    ∃ c₁ c₂, cs = c₁ ++ c₂ ∧ encode c₁ = a ∧ encode c₂ = b :=
  Silmaril.Proofs.Formats.Utf8.Encode.encode_eq_append h ha hb

/-- `String.fromUTF8?` decodes to the characters whose encoding is the input. -/
theorem fromUTF8?_eq_some {b : ByteArray} {s : String} (h : String.fromUTF8? b = some s) :
    b.data.toList = encode s.toList :=
  Silmaril.Proofs.Formats.Utf8.Encode.fromUTF8?_eq_some h

/-- `String.fromUTF8?` decodes every encoding, to its characters. -/
theorem fromUTF8?_encode (cs : List Char) :
    ∃ s, String.fromUTF8? (encode cs).toByteArray = some s ∧ s.toList = cs :=
  Silmaril.Proofs.Formats.Utf8.Encode.fromUTF8?_encode cs

/-- An ASCII byte list is the encoding of its characters. -/
theorem encode_ofAscii {bs : List UInt8} (h : ∀ b ∈ bs, b < 0x80) : encode (ofAscii bs) = bs :=
  Silmaril.Proofs.Formats.Utf8.Encode.encode_ofAscii h

/-- The only characters whose encoding is a given ASCII byte list. -/
theorem eq_ofAscii {cs : List Char} {bs : List UInt8} (h : encode cs = bs)
    (ha : ∀ b ∈ bs, b < 0x80) : cs = ofAscii bs :=
  Silmaril.Proofs.Formats.Utf8.Encode.eq_ofAscii h ha

/-! ## Byte regular expressions on encodings -/

section Transport
open Silmaril.Proofs.Formats.Utf8.Transport

theorem good_mul {r s : RegularExpression UInt8} (hr : Good r) (hs : Good s) : Good (r * s) :=
  Silmaril.Proofs.Formats.Utf8.Transport.good_mul hr hs
theorem good_add {r s : RegularExpression UInt8} (hr : Good r) (hs : Good s) : Good (r + s) :=
  Silmaril.Proofs.Formats.Utf8.Transport.good_add hr hs
theorem good_one : Good 1 := Silmaril.Proofs.Formats.Utf8.Transport.good_one
theorem good_star {r : RegularExpression UInt8} (hr : Good r) : Good (star r) :=
  Silmaril.Proofs.Formats.Utf8.Transport.good_star hr
theorem good_anyOf {l : List UInt8} (h : ∀ b ∈ l, b < 0x80) : Good (anyOf l) :=
  Silmaril.Proofs.Formats.Utf8.Transport.good_anyOf h
theorem good_char {b : UInt8} (h : b < 0x80) : Good (char b) :=
  Silmaril.Proofs.Formats.Utf8.Transport.good_char h
theorem good_byteRange {lo hi : UInt8} (h : hi < 0x80) : Good (byteRange lo hi) :=
  Silmaril.Proofs.Formats.Utf8.Transport.good_byteRange h
theorem good_word {l : List UInt8} (h : ∀ b ∈ l, b < 0x80) : Good (word l) :=
  Silmaril.Proofs.Formats.Utf8.Transport.good_word h
theorem good_scalar : Good scalar := Silmaril.Proofs.Formats.Utf8.Transport.good_scalar
theorem good_multibyte : Good multibyte := Silmaril.Proofs.Formats.Utf8.Transport.good_multibyte

/-- An encoding matches a product of `Good` expressions exactly when its characters split. -/
theorem encode_mem_mul {r s : RegularExpression UInt8} (hr : Good r) (hs : Good s) {cs : List Char} :
    encode cs ∈ (r * s).matches' ↔
      ∃ c₁ c₂, cs = c₁ ++ c₂ ∧ encode c₁ ∈ r.matches' ∧ encode c₂ ∈ s.matches' :=
  Silmaril.Proofs.Formats.Utf8.Transport.encode_mem_mul hr hs

theorem encode_mem_add {r s : RegularExpression UInt8} {cs : List Char} :
    encode cs ∈ (r + s).matches' ↔ encode cs ∈ r.matches' ∨ encode cs ∈ s.matches' :=
  Silmaril.Proofs.Formats.Utf8.Transport.encode_mem_add

theorem encode_mem_one {cs : List Char} :
    encode cs ∈ (1 : RegularExpression UInt8).matches' ↔ cs = [] :=
  Silmaril.Proofs.Formats.Utf8.Transport.encode_mem_one

theorem encode_mem_star {r : RegularExpression UInt8} (hr : Good r) {cs : List Char} :
    encode cs ∈ (star r).matches' ↔
      ∃ L : List (List Char), cs = L.flatten ∧ ∀ x ∈ L, encode x ∈ r.matches' :=
  Silmaril.Proofs.Formats.Utf8.Transport.encode_mem_star hr

theorem encode_singleton_ascii {c : Char} (h : c.toNat < 0x80) :
    encode [c] = [UInt8.ofNat c.toNat] :=
  Silmaril.Proofs.Formats.Utf8.Transport.encode_singleton_ascii h

theorem encode_mem_byteRange {lo hi : UInt8} (h : hi < 0x80) {cs : List Char} :
    encode cs ∈ (byteRange lo hi).matches' ↔
      ∃ c, cs = [c] ∧ lo.toNat ≤ c.toNat ∧ c.toNat ≤ hi.toNat :=
  Silmaril.Proofs.Formats.Utf8.Transport.encode_mem_byteRange h

theorem encode_mem_char {b : UInt8} (h : b < 0x80) {cs : List Char} :
    encode cs ∈ (char b).matches' ↔ cs = [Char.ofNat b.toNat] :=
  Silmaril.Proofs.Formats.Utf8.Transport.encode_mem_char h

theorem encode_mem_anyOf {l : List UInt8} (h : ∀ b ∈ l, b < 0x80) {cs : List Char} :
    encode cs ∈ (anyOf l).matches' ↔ ∃ b ∈ l, cs = [Char.ofNat b.toNat] :=
  Silmaril.Proofs.Formats.Utf8.Transport.encode_mem_anyOf h

/-- The multi-byte rows of Table 3-7 encode exactly the non-ASCII characters. -/
theorem encode_mem_multibyte {cs : List Char} :
    encode cs ∈ multibyte.matches' ↔ ∃ c, cs = [c] ∧ 0x80 ≤ c.toNat :=
  Silmaril.Proofs.Formats.Utf8.Transport.encode_mem_multibyte

theorem toNat_ofNat_ascii {n : Nat} (h : n < 0x80) : (Char.ofNat n).toNat = n :=
  Silmaril.Proofs.Formats.Utf8.Encode.toNat_ofNat_ascii h

end Transport

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

-- The transport lemmas: `é` (two bytes) is one multi-byte row; `ab` splits as `a`, `b`.
example : encode ['é'] ∈ multibyte.matches' := encode_mem_multibyte.mpr ⟨'é', rfl, by decide⟩
example : encode ['a', 'b'] ∈ (char (0x61 : UInt8) * char (0x62 : UInt8)).matches' :=
  (encode_mem_mul (good_char (b := 0x61) (by decide)) (good_char (b := 0x62) (by decide))).mpr
    ⟨['a'], ['b'], rfl, (encode_mem_char (b := 0x61) (by decide)).mpr rfl,
      (encode_mem_char (b := 0x62) (by decide)).mpr rfl⟩
-- `fromUTF8?` inverts the encoding.
example : ∃ s, String.fromUTF8? (encode ['é', 'a']).toByteArray = some s ∧ s.toList = ['é', 'a'] :=
  fromUTF8?_encode _

end Examples

end Silmaril.Formats.Utf8

end
