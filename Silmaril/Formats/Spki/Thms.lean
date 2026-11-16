module

public import Silmaril.Formats.Spki.Defs
import Silmaril.Proofs.Formats.Spki.Basic

/-!
# SPKI S-expressions in canonical form: lemmas

* `isDecimal_iff`, `digitsValue_decimal`: `decimal` is exactly the numerals of the `decimal`
  rule, and denotes its argument;
* `mem_canonical_iff`: the image of `encode` is the language of the ABNF of RFC 9804 §7.2;
* `decode_eq_some_iff`, `parse_encode`: the parser inverts the encoding and accepts nothing
  else, hence `encode_injective` (the canonical form is unique for each S-expression, as
  §6.2 states) and the `Decidable` instance for `canonical`;
* examples: the canonical examples of RFC 9804 §6.2, and rejected inputs (leading zeros, wrong
  lengths, unclosed lists, trailing bytes, nested or dangling display hints, whitespace).
-/

@[expose] public section

namespace Silmaril.Formats.Spki

theorem digitsValue_decimal (n : Nat) : digitsValue (decimal n) = n :=
  Silmaril.Proofs.Formats.Spki.digitsValue_decimal n

/-- The `decimal` rule allows exactly the numerals `decimal n`. -/
theorem isDecimal_iff {ds : List UInt8} : IsDecimal ds ↔ ∃ n, ds = decimal n :=
  Silmaril.Proofs.Formats.Spki.isDecimal_iff

/-- `canonical` is the language of the ABNF of RFC 9804 §7.2. -/
theorem mem_canonical_iff {w : List UInt8} : w ∈ canonical ↔ ABNF w :=
  Silmaril.Proofs.Formats.Spki.mem_canonical_iff

/-- The parser reads an encoding back, leaving the rest of the input. -/
theorem parse_encode (x : Sexp) (n : Nat) (rest : List UInt8) (h : (encode x).length < n) :
    parse n (encode x ++ rest) = some (x, rest) :=
  Silmaril.Proofs.Formats.Spki.parse_encode x n rest h

/-- Decoding succeeds exactly on encodings. -/
theorem decode_eq_some_iff {w : List UInt8} {x : Sexp} : decode w = some x ↔ w = encode x :=
  Silmaril.Proofs.Formats.Spki.decode_eq_some_iff

/-- Each S-expression has exactly one canonical representation (RFC 9804 §6.2). -/
theorem encode_injective : Function.Injective encode :=
  Silmaril.Proofs.Formats.Spki.encode_injective

theorem mem_canonical_iff_decode {w : List UInt8} : w ∈ canonical ↔ (decode w).isSome := by
  constructor
  · rintro ⟨x, rfl⟩; simp [decode_eq_some_iff.mpr rfl]
  · intro h
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
    exact ⟨x, (decode_eq_some_iff.mp hx).symm⟩

instance canonical.decidableMem (w : List UInt8) : Decidable (w ∈ canonical) :=
  decidable_of_iff' _ mem_canonical_iff_decode

/-! ## Examples -/

section Examples

-- RFC 9804 §6.2.
example : "(6:issuer3:bob)".toUTF8.toList ∈ canonical := by decide +kernel
example : "(4:icon[12:image/bitmap]9:xxxxxxxxx)".toUTF8.toList ∈ canonical := by decide +kernel
example : "(7:subject(3:ref5:alice6:mother))".toUTF8.toList ∈ canonical := by decide +kernel
example : "10:foo)]}>bar".toUTF8.toList ∈ canonical := by decide +kernel
example : "0:".toUTF8.toList ∈ canonical := by decide +kernel
example : "()".toUTF8.toList ∈ canonical := by decide +kernel
-- Octets are arbitrary bytes, not text.
example : [0x32, 0x3A, 0x00, 0xFF] ∈ canonical := by decide +kernel
example : encode (.list [.atom none [0x61], .atom (some [0x62]) []]) = "(1:a[1:b]0:)".toUTF8.toList :=
  by decide +kernel
example : decode "(1:a[1:b]0:)".toUTF8.toList =
    some (.list [.atom none [0x61], .atom (some [0x62]) []]) := by decide +kernel

-- A leading zero in a length, a length too long or too short, no length.
example : "01:a".toUTF8.toList ∉ canonical := by decide +kernel
example : "3:ab".toUTF8.toList ∉ canonical := by decide +kernel
example : "1:ab".toUTF8.toList ∉ canonical := by decide +kernel
example : ":".toUTF8.toList ∉ canonical := by decide +kernel
-- An unclosed list, a stray close, two expressions, the empty input.
example : "(1:a".toUTF8.toList ∉ canonical := by decide +kernel
example : ")".toUTF8.toList ∉ canonical := by decide +kernel
example : "1:a1:b".toUTF8.toList ∉ canonical := by decide +kernel
example : ([] : List UInt8) ∉ canonical := by decide +kernel
-- A display hint must precede an octet string and does not nest.
example : "[1:a]".toUTF8.toList ∉ canonical := by decide +kernel
example : "[[1:a]1:b]1:c".toUTF8.toList ∉ canonical := by decide +kernel
example : "[1:a]()".toUTF8.toList ∉ canonical := by decide +kernel
-- Whitespace and the advanced forms are not canonical.
example : "(1:a 1:b)".toUTF8.toList ∉ canonical := by decide +kernel
example : "(abc)".toUTF8.toList ∉ canonical := by decide +kernel
example : "#616263#".toUTF8.toList ∉ canonical := by decide +kernel

end Examples

end Silmaril.Formats.Spki

end
