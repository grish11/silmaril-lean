module

public import Silmaril.Formats.Cbor.Drisl.Defs
public import Silmaril.Formats.Cbor.Value.Thms
import Silmaril.Proofs.Formats.Cbor.Drisl

/-!
# DRISL and the ATProto core: lemmas and test vectors

* `check_iff`: `check P` decides `language P`, hence the `Decidable` instance;
* `language_le_wellFormed`: every DRISL (or ATProto core) byte string is one well-formed CBOR
  item;
* `value_unique`: a DRISL byte string has exactly one value (determinism);
* `language_mono`, `atprotoCore_le_drislNoFloats`, `drislNoFloats_le_drisl`: the profiles nest;
* test vectors, accepted and rejected, for each rule of the module documentation.
-/

@[expose] public section

namespace Silmaril.Formats.Cbor.Drisl

theorem check_iff {P : Profile} {w : List UInt8} : check P w = true ↔ w ∈ language P :=
  Silmaril.Proofs.Formats.Cbor.Drisl.check_iff

instance language.decidableMem (P : Profile) (w : List UInt8) : Decidable (w ∈ language P) :=
  decidable_of_iff _ check_iff

theorem language_le_wellFormed (P : Profile) : language P ≤ wellFormed :=
  Silmaril.Proofs.Formats.Cbor.Drisl.language_le_wellFormed P

/-- Determinism: an allowed value is determined by its bytes. -/
theorem value_unique {P : Profile} {v v' : Value} (h : ok P v = true) (h' : ok P v' = true)
    (he : v.encode = v'.encode) : v = v' :=
  Silmaril.Proofs.Formats.Cbor.Drisl.value_unique h h' he

theorem language_mono {P Q : Profile} (hf : P.floats = true → Q.floats = true)
    (hi : Q.int64 = true → P.int64 = true) (hc : P.cid = Q.cid ∨ Q.cid = .prefix) :
    language P ≤ language Q :=
  Silmaril.Proofs.Formats.Cbor.Drisl.language_mono hf hi hc

theorem atprotoCore_le_drislNoFloats :
    language .atprotoCoreExactCid ≤ language .drislNoFloatsExactCid :=
  language_mono (fun h => h) (fun h => by cases h) (Or.inl rfl)

theorem drislNoFloats_le_drisl : language .drislNoFloatsExactCid ≤ language .drislExactCid :=
  language_mono (fun h => by cases h) (fun h => by cases h) (Or.inl rfl)

/-- The exact CID boundary is the stronger assumption. -/
theorem drislExactCid_le_drislCidPrefix : language .drislExactCid ≤ language .drislCidPrefix :=
  language_mono (fun h => h) (fun h => h) (Or.inr rfl)

/-! ## Test vectors -/

section Examples

-- `{"a": 1, "b": [true, null]}`: accepted by all three profiles.
example : [0xA2, 0x61, 0x61, 0x01, 0x61, 0x62, 0x82, 0xF5, 0xF6] ∈ language .drislExactCid := by
  decide +kernel
example : [0xA2, 0x61, 0x61, 0x01, 0x61, 0x62, 0x82, 0xF5, 0xF6] ∈ language .atprotoCoreExactCid := by
  decide +kernel
-- Unsorted keys `{"b": 1, "a": 2}`, a duplicate key `{"a": 1, "a": 2}`, an integer key `{1: 2}`.
example : [0xA2, 0x61, 0x62, 0x01, 0x61, 0x61, 0x02] ∉ language .drislExactCid := by decide +kernel
example : [0xA2, 0x61, 0x61, 0x01, 0x61, 0x61, 0x02] ∉ language .drislExactCid := by decide +kernel
example : [0xA1, 0x01, 0x02] ∉ language .drislExactCid := by decide +kernel
-- Key order is bytewise on encodings: `{"b": 0, "aa": 0}` is sorted (`61 62` < `62 61 61`).
example : [0xA2, 0x61, 0x62, 0x00, 0x62, 0x61, 0x61, 0x00] ∈ language .drislExactCid := by decide +kernel
-- Non-shortest heads, indefinite lengths, trailing bytes.
example : [0x18, 0x00] ∉ language .drislExactCid := by decide +kernel
example : [0x9F, 0xFF] ∉ language .drislExactCid := by decide +kernel
example : [0x00, 0x00] ∉ language .drislExactCid := by decide +kernel
-- Text must be UTF-8: `"\xC3("`.
example : [0x62, 0xC3, 0x28] ∉ language .drislExactCid := by decide +kernel
-- Simple values: `undefined` and `simple(16)` are rejected.
example : [0xF7] ∉ language .drislExactCid := by decide +kernel
example : [0xF0] ∉ language .drislExactCid := by decide +kernel
-- Floats: 1.0 as a double is DRISL, not ATProto; as a half it is not DRISL.
example : [0xFB, 0x3F, 0xF0, 0, 0, 0, 0, 0, 0] ∈ language .drislExactCid := by decide +kernel
example : [0xFB, 0x3F, 0xF0, 0, 0, 0, 0, 0, 0] ∉ language .atprotoCoreExactCid := by decide +kernel
example : [0xF9, 0x3C, 0x00] ∉ language .drislExactCid := by decide +kernel
-- `+0.0` is allowed, `-0.0`, NaN and infinity are not.
example : [0xFB, 0, 0, 0, 0, 0, 0, 0, 0] ∈ language .drislExactCid := by decide +kernel
example : [0xFB, 0x80, 0, 0, 0, 0, 0, 0, 0] ∉ language .drislExactCid := by decide +kernel
example : [0xFB, 0x7F, 0xF8, 0, 0, 0, 0, 0, 0] ∉ language .drislExactCid := by decide +kernel
example : [0xFB, 0x7F, 0xF0, 0, 0, 0, 0, 0, 0] ∉ language .drislExactCid := by decide +kernel
-- Integers: 2^63 is DRISL but outside atproto's signed 64-bit range; 2^63 - 1 is in both,
-- and so is -2^63 (`nint (2^63 - 1)`).
example : [0x1B, 0x80, 0, 0, 0, 0, 0, 0, 0] ∈ language .drislExactCid := by decide +kernel
example : [0x1B, 0x80, 0, 0, 0, 0, 0, 0, 0] ∉ language .atprotoCoreExactCid := by decide +kernel
example : [0x1B, 0x7F, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF] ∈ language .atprotoCoreExactCid := by
  decide +kernel
example : [0x3B, 0x7F, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF] ∈ language .atprotoCoreExactCid := by
  decide +kernel
-- Tags: tag 1 (epoch time) and a bignum (tag 2) are rejected.
example : [0xC1, 0x00] ∉ language .drislExactCid := by decide +kernel
example : [0xC2, 0x41, 0x01] ∉ language .drislExactCid := by decide +kernel
-- Tag 42 with `00` and a DASL CID (codec DRISL `71` or raw `55`, SHA-256, 32 bytes).
example : [0xD8, 0x2A, 0x58, 0x25, 0x00, 0x01, 0x71, 0x12, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] ∈ language .drislExactCid := by decide +kernel
example : [0xD8, 0x2A, 0x58, 0x25, 0x00, 0x01, 0x55, 0x12, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] ∈ language .atprotoCoreExactCid := by decide +kernel
-- … but not with a BLAKE3 hash type (`1E`), without the `00` prefix, or with a trailing byte.
example : [0xD8, 0x2A, 0x58, 0x25, 0x00, 0x01, 0x55, 0x1E, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] ∉ language .drislExactCid := by decide +kernel
example : [0xD8, 0x2A, 0x58, 0x24, 0x01, 0x71, 0x12, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] ∉ language .drislExactCid := by decide +kernel
example : [0xD8, 0x2A, 0x58, 0x26, 0x00, 0x01, 0x71, 0x12, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] ∉ language .drislExactCid := by decide +kernel
-- The trailing byte is exactly what the `.prefix` CID-boundary assumption admits.
example : [0xD8, 0x2A, 0x58, 0x26, 0x00, 0x01, 0x71, 0x12, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] ∈ language .drislCidPrefix := by decide +kernel

end Examples

end Silmaril.Formats.Cbor.Drisl

end
