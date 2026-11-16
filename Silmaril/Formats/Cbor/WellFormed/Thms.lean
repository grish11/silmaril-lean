module

public import Silmaril.Formats.Cbor.WellFormed.Defs
import Silmaril.Proofs.Formats.Cbor.WellFormed

/-!
# Well-formed CBOR: lemmas and the RFC 8949 test vectors

* `isWellFormed_iff`: the Appendix C style checker `isWellFormed` decides `wellFormed`. It is
  sound (whatever it accepts is one well-formed item) and complete. This gives the `Decidable`
  instance `wellFormed.decidableMem`;
* `skip_sound`, `item_skip`: the item-level statements behind it;
* every example of RFC 8949 Appendix F.1 (not well-formed) is rejected, and the well-formed
  examples of Appendix A are accepted (a selection, including indefinite-length items, tags,
  simple values and floats). A few more vectors separate well-formedness from validity and
  determinism.
-/

@[expose] public section

namespace Silmaril.Formats.Cbor

theorem isWellFormed_iff {w : List UInt8} : isWellFormed w = true ↔ w ∈ wellFormed :=
  Silmaril.Proofs.Formats.Cbor.WellFormed.isWellFormed_iff

instance wellFormed.decidableMem (w : List UInt8) : Decidable (w ∈ wellFormed) :=
  decidable_of_iff _ isWellFormed_iff

theorem skip_sound {n : Nat} {w r : List UInt8} (h : skip n w = some r) :
    ∃ x, Item x ∧ w = x ++ r :=
  Silmaril.Proofs.Formats.Cbor.WellFormed.skip_sound n w r h

theorem item_skip {x : List UInt8} (h : Item x) {n : Nat} (r : List UInt8)
    (hn : 2 * x.length ≤ n) : skip n (x ++ r) = some r :=
  Silmaril.Proofs.Formats.Cbor.WellFormed.item_skip h n r hn

/-- Every well-formed item starts with a byte other than `break`. -/
theorem item_head {x : List UInt8} (h : Item x) : ∃ b t, x = b :: t ∧ b ≠ breakByte :=
  Silmaril.Proofs.Formats.Cbor.WellFormed.item_head h

/-! ## RFC 8949 Appendix A: well-formed examples, and validity/determinism contrasts -/

section Examples

-- 0
example : [0x00] ∈ wellFormed := by decide +kernel
-- 23
example : [0x17] ∈ wellFormed := by decide +kernel
-- 24
example : [0x18, 0x18] ∈ wellFormed := by decide +kernel
-- 1000
example : [0x19, 0x03, 0xE8] ∈ wellFormed := by decide +kernel
-- 1000000000000
example : [0x1B, 0x00, 0x00, 0x00, 0xE8, 0xD4, 0xA5, 0x10, 0x00] ∈ wellFormed := by decide +kernel
-- 18446744073709551615
example : [0x1B, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF] ∈ wellFormed := by decide +kernel
-- -1
example : [0x20] ∈ wellFormed := by decide +kernel
-- -100
example : [0x38, 0x63] ∈ wellFormed := by decide +kernel
-- bignum 2^64 (tag 2)
example : [0xC2, 0x49, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] ∈ wellFormed := by decide +kernel
-- 0.0 (half)
example : [0xF9, 0x00, 0x00] ∈ wellFormed := by decide +kernel
-- Infinity (half)
example : [0xF9, 0x7C, 0x00] ∈ wellFormed := by decide +kernel
-- NaN (half)
example : [0xF9, 0x7E, 0x00] ∈ wellFormed := by decide +kernel
-- -0.0 (half)
example : [0xF9, 0x80, 0x00] ∈ wellFormed := by decide +kernel
-- 100000.0 (single)
example : [0xFA, 0x47, 0xC3, 0x50, 0x00] ∈ wellFormed := by decide +kernel
-- 1.1 (double)
example : [0xFB, 0x3F, 0xF1, 0x99, 0x99, 0x99, 0x99, 0x99, 0x9A] ∈ wellFormed := by decide +kernel
-- false
example : [0xF4] ∈ wellFormed := by decide +kernel
-- true
example : [0xF5] ∈ wellFormed := by decide +kernel
-- null
example : [0xF6] ∈ wellFormed := by decide +kernel
-- undefined
example : [0xF7] ∈ wellFormed := by decide +kernel
-- simple(16)
example : [0xF0] ∈ wellFormed := by decide +kernel
-- simple(255)
example : [0xF8, 0xFF] ∈ wellFormed := by decide +kernel
-- 0("2013-03-21T20:04:00Z")
example : [0xC0, 0x74, 0x32, 0x30, 0x31, 0x33, 0x2D, 0x30, 0x33, 0x2D, 0x32, 0x31, 0x54, 0x32, 0x30, 0x3A, 0x30, 0x34, 0x3A, 0x30, 0x30, 0x5A] ∈ wellFormed := by decide +kernel
-- h''
example : [0x40] ∈ wellFormed := by decide +kernel
-- h'01020304'
example : [0x44, 0x01, 0x02, 0x03, 0x04] ∈ wellFormed := by decide +kernel
-- ""
example : [0x60] ∈ wellFormed := by decide +kernel
-- "IETF"
example : [0x64, 0x49, 0x45, 0x54, 0x46] ∈ wellFormed := by decide +kernel
-- []
example : [0x80] ∈ wellFormed := by decide +kernel
-- [1, 2, 3]
example : [0x83, 0x01, 0x02, 0x03] ∈ wellFormed := by decide +kernel
-- [1, [2, 3], [4, 5]]
example : [0x83, 0x01, 0x82, 0x02, 0x03, 0x82, 0x04, 0x05] ∈ wellFormed := by decide +kernel
-- {}
example : [0xA0] ∈ wellFormed := by decide +kernel
-- {1: 2, 3: 4}
example : [0xA2, 0x01, 0x02, 0x03, 0x04] ∈ wellFormed := by decide +kernel
-- {"a": 1, "b": [2, 3]}
example : [0xA2, 0x61, 0x61, 0x01, 0x61, 0x62, 0x82, 0x02, 0x03] ∈ wellFormed := by decide +kernel
-- (_ h'0102', h'030405')
example : [0x5F, 0x42, 0x01, 0x02, 0x43, 0x03, 0x04, 0x05, 0xFF] ∈ wellFormed := by decide +kernel
-- (_ "strea", "ming")
example : [0x7F, 0x65, 0x73, 0x74, 0x72, 0x65, 0x61, 0x64, 0x6D, 0x69, 0x6E, 0x67, 0xFF] ∈ wellFormed := by decide +kernel
-- [_ ]
example : [0x9F, 0xFF] ∈ wellFormed := by decide +kernel
-- [_ 1, [2, 3], [_ 4, 5]]
example : [0x9F, 0x01, 0x82, 0x02, 0x03, 0x9F, 0x04, 0x05, 0xFF, 0xFF] ∈ wellFormed := by decide +kernel
-- [1, [_ 2, 3], [4, 5]]
example : [0x83, 0x01, 0x9F, 0x02, 0x03, 0xFF, 0x82, 0x04, 0x05] ∈ wellFormed := by decide +kernel
-- {_ "a": 1, "b": [_ 2, 3]}
example : [0xBF, 0x61, 0x61, 0x01, 0x61, 0x62, 0x9F, 0x02, 0x03, 0xFF, 0xFF] ∈ wellFormed := by decide +kernel
-- (_ ) empty indefinite byte string
example : [0x5F, 0xFF] ∈ wellFormed := by decide +kernel
-- 0 with a non-preferred 1-byte argument (not deterministic, still well-formed)
example : [0x18, 0x00] ∈ wellFormed := by decide +kernel
-- a text string with ill-formed UTF-8 (well-formed, not valid)
example : [0x62, 0xC3, 0x28] ∈ wellFormed := by decide +kernel
-- a map with a duplicate key (well-formed, not valid)
example : [0xA2, 0x01, 0x02, 0x01, 0x03] ∈ wellFormed := by decide +kernel
-- an unassigned tag (well-formed; tag validity is not checked)
example : [0xD9, 0xFF, 0xFF, 0x00] ∈ wellFormed := by decide +kernel
-- two items: not a single item
example : ([0x00, 0x00] : List UInt8) ∉ wellFormed := by decide +kernel
-- trailing break
example : ([0x00, 0xFF] : List UInt8) ∉ wellFormed := by decide +kernel
-- the empty input
example : ([] : List UInt8) ∉ wellFormed := by decide +kernel

/-! ## RFC 8949 Appendix F.1: every listed not-well-formed example -/

-- End of input in a head.
example : [0x18] ∉ wellFormed := by decide +kernel
example : [0x19] ∉ wellFormed := by decide +kernel
example : [0x1A] ∉ wellFormed := by decide +kernel
example : [0x1B] ∉ wellFormed := by decide +kernel
example : [0x19, 0x01] ∉ wellFormed := by decide +kernel
example : [0x1A, 0x01, 0x02] ∉ wellFormed := by decide +kernel
example : [0x1B, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07] ∉ wellFormed := by decide +kernel
example : [0x38] ∉ wellFormed := by decide +kernel
example : [0x58] ∉ wellFormed := by decide +kernel
example : [0x78] ∉ wellFormed := by decide +kernel
example : [0x98] ∉ wellFormed := by decide +kernel
example : [0x9A, 0x01, 0xFF, 0x00] ∉ wellFormed := by decide +kernel
example : [0xB8] ∉ wellFormed := by decide +kernel
example : [0xD8] ∉ wellFormed := by decide +kernel
example : [0xF8] ∉ wellFormed := by decide +kernel
example : [0xF9, 0x00] ∉ wellFormed := by decide +kernel
example : [0xFA, 0x00, 0x00] ∉ wellFormed := by decide +kernel
example : [0xFB, 0x00, 0x00, 0x00] ∉ wellFormed := by decide +kernel
-- Definite-length strings with short data.
example : [0x41] ∉ wellFormed := by decide +kernel
example : [0x61] ∉ wellFormed := by decide +kernel
example : [0x5A, 0xFF, 0xFF, 0xFF, 0xFF, 0x00] ∉ wellFormed := by decide +kernel
example : [0x5B, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x01, 0x02, 0x03] ∉ wellFormed := by decide +kernel
example : [0x7A, 0xFF, 0xFF, 0xFF, 0xFF, 0x00] ∉ wellFormed := by decide +kernel
example : [0x7B, 0x7F, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x01, 0x02, 0x03] ∉ wellFormed := by decide +kernel
-- Definite-length maps and arrays not closed with enough items.
example : [0x81] ∉ wellFormed := by decide +kernel
example : [0x81, 0x81, 0x81, 0x81, 0x81, 0x81, 0x81, 0x81, 0x81] ∉ wellFormed := by decide +kernel
example : [0x82, 0x00] ∉ wellFormed := by decide +kernel
example : [0xA1] ∉ wellFormed := by decide +kernel
example : [0xA2, 0x01, 0x02] ∉ wellFormed := by decide +kernel
example : [0xA1, 0x00] ∉ wellFormed := by decide +kernel
example : [0xA2, 0x00, 0x00, 0x00] ∉ wellFormed := by decide +kernel
-- Tag number not followed by tag content.
example : [0xC0] ∉ wellFormed := by decide +kernel
-- Indefinite-length strings not closed by a break stop code.
example : [0x5F, 0x41, 0x00] ∉ wellFormed := by decide +kernel
example : [0x7F, 0x61, 0x00] ∉ wellFormed := by decide +kernel
-- Indefinite-length maps and arrays not closed by a break stop code.
example : [0x9F] ∉ wellFormed := by decide +kernel
example : [0x9F, 0x01, 0x02] ∉ wellFormed := by decide +kernel
example : [0xBF] ∉ wellFormed := by decide +kernel
example : [0xBF, 0x01, 0x02, 0x01, 0x02] ∉ wellFormed := by decide +kernel
example : [0x81, 0x9F] ∉ wellFormed := by decide +kernel
example : [0x9F, 0x80, 0x00] ∉ wellFormed := by decide +kernel
example : [0x9F, 0x9F, 0x9F, 0x9F, 0x9F, 0xFF, 0xFF, 0xFF, 0xFF] ∉ wellFormed := by decide +kernel
example : [0x9F, 0x81, 0x9F, 0x81, 0x9F, 0x9F, 0xFF, 0xFF, 0xFF] ∉ wellFormed := by decide +kernel
-- Subkind 1: reserved additional information values.
example : [0x1C] ∉ wellFormed := by decide +kernel
example : [0x1D] ∉ wellFormed := by decide +kernel
example : [0x1E] ∉ wellFormed := by decide +kernel
example : [0x3C] ∉ wellFormed := by decide +kernel
example : [0x3D] ∉ wellFormed := by decide +kernel
example : [0x3E] ∉ wellFormed := by decide +kernel
example : [0x5C] ∉ wellFormed := by decide +kernel
example : [0x5D] ∉ wellFormed := by decide +kernel
example : [0x5E] ∉ wellFormed := by decide +kernel
example : [0x7C] ∉ wellFormed := by decide +kernel
example : [0x7D] ∉ wellFormed := by decide +kernel
example : [0x7E] ∉ wellFormed := by decide +kernel
example : [0x9C] ∉ wellFormed := by decide +kernel
example : [0x9D] ∉ wellFormed := by decide +kernel
example : [0x9E] ∉ wellFormed := by decide +kernel
example : [0xBC] ∉ wellFormed := by decide +kernel
example : [0xBD] ∉ wellFormed := by decide +kernel
example : [0xBE] ∉ wellFormed := by decide +kernel
example : [0xDC] ∉ wellFormed := by decide +kernel
example : [0xDD] ∉ wellFormed := by decide +kernel
example : [0xDE] ∉ wellFormed := by decide +kernel
example : [0xFC] ∉ wellFormed := by decide +kernel
example : [0xFD] ∉ wellFormed := by decide +kernel
example : [0xFE] ∉ wellFormed := by decide +kernel
-- Subkind 2: reserved two-byte encodings of simple values.
example : [0xF8, 0x00] ∉ wellFormed := by decide +kernel
example : [0xF8, 0x01] ∉ wellFormed := by decide +kernel
example : [0xF8, 0x18] ∉ wellFormed := by decide +kernel
example : [0xF8, 0x1F] ∉ wellFormed := by decide +kernel
-- Subkind 3: indefinite-length string chunks not of the correct type.
example : [0x5F, 0x00, 0xFF] ∉ wellFormed := by decide +kernel
example : [0x5F, 0x21, 0xFF] ∉ wellFormed := by decide +kernel
example : [0x5F, 0x61, 0x00, 0xFF] ∉ wellFormed := by decide +kernel
example : [0x5F, 0x80, 0xFF] ∉ wellFormed := by decide +kernel
example : [0x5F, 0xA0, 0xFF] ∉ wellFormed := by decide +kernel
example : [0x5F, 0xC0, 0x00, 0xFF] ∉ wellFormed := by decide +kernel
example : [0x5F, 0xE0, 0xFF] ∉ wellFormed := by decide +kernel
example : [0x7F, 0x41, 0x00, 0xFF] ∉ wellFormed := by decide +kernel
-- Subkind 3: indefinite-length string chunks not definite length.
example : [0x5F, 0x5F, 0x41, 0x00, 0xFF, 0xFF] ∉ wellFormed := by decide +kernel
example : [0x7F, 0x7F, 0x61, 0x00, 0xFF, 0xFF] ∉ wellFormed := by decide +kernel
-- Subkind 4: break on its own outside an indefinite-length item.
example : [0xFF] ∉ wellFormed := by decide +kernel
-- Subkind 4: break in a definite-length array or map or a tag.
example : [0x81, 0xFF] ∉ wellFormed := by decide +kernel
example : [0x82, 0x00, 0xFF] ∉ wellFormed := by decide +kernel
example : [0xA1, 0xFF] ∉ wellFormed := by decide +kernel
example : [0xA1, 0xFF, 0x00] ∉ wellFormed := by decide +kernel
example : [0xA1, 0x00, 0xFF] ∉ wellFormed := by decide +kernel
example : [0xA2, 0x00, 0x00, 0xFF] ∉ wellFormed := by decide +kernel
example : [0x9F, 0x81, 0xFF] ∉ wellFormed := by decide +kernel
example : [0x9F, 0x82, 0x9F, 0x81, 0x9F, 0x9F, 0xFF, 0xFF, 0xFF, 0xFF] ∉ wellFormed := by decide +kernel
-- Subkind 4: break in a value position of an indefinite-length map.
example : [0xBF, 0x00, 0xFF] ∉ wellFormed := by decide +kernel
example : [0xBF, 0x00, 0x00, 0x00, 0xFF] ∉ wellFormed := by decide +kernel
-- Subkind 5: major type 0, 1, 6 with additional information 31.
example : [0x1F] ∉ wellFormed := by decide +kernel
example : [0x3F] ∉ wellFormed := by decide +kernel
example : [0xDF] ∉ wellFormed := by decide +kernel

end Examples

end Silmaril.Formats.Cbor

end
