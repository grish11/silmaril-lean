module

public import Silmaril.Formats.Cbor.Value.Defs
public import Silmaril.Formats.Cbor.WellFormed.Thms
import Silmaril.Proofs.Formats.Cbor.Value
import Silmaril.Proofs.Formats.Cbor.Value.Decode

/-!
# CBOR values and the definite-length codec: lemmas

* `beNat_beBytes`, `head_encodeHead`: shortest heads are heads (RFC 8949 §3) of their argument;
* `decode_encode`: `decode` inverts `encode` on `Encodable` values, and `encode_injective`
  follows;
* `encode_mem_wellFormed`: every encoding is one well-formed CBOR item;
* examples from RFC 8949 Appendix A.
-/

@[expose] public section

namespace Silmaril.Formats.Cbor

theorem beNat_beBytes (k n : Nat) : beNat (beBytes k n) = n % 256 ^ k :=
  Silmaril.Proofs.Formats.Cbor.Value.beNat_beBytes k n

theorem head_encodeHead {mt n : Nat} (hn : n < 2 ^ 64) : Head mt n (encodeHead mt n) :=
  Silmaril.Proofs.Formats.Cbor.Value.head_encodeHead hn

/-- Decoding inverts the deterministic definite-length encoding. -/
theorem decode_encode (v : Value) (hv : v.Encodable) : decode v.encode = some v :=
  Silmaril.Proofs.Formats.Cbor.Value.decode_encode v hv

theorem encodable_of_decode {bytes : List UInt8} {value : Value}
    (read : decode bytes = some value) : value.Encodable :=
  Silmaril.Proofs.Formats.Cbor.Value.encodable_of_decode read

theorem encode_injective {v w : Value} (hv : v.Encodable) (hw : w.Encodable)
    (h : v.encode = w.encode) : v = w :=
  Option.some.inj ((decode_encode v hv).symm.trans (h ▸ decode_encode w hw))

/-- Every encoding is exactly one well-formed CBOR data item. -/
theorem encode_mem_wellFormed (v : Value) (hv : v.Encodable) : v.encode ∈ wellFormed :=
  Silmaril.Proofs.Formats.Cbor.Value.encode_item v hv

/-! ## Examples (RFC 8949 Appendix A) -/

section Examples

example : (Value.uint 1000).encode = [0x19, 0x03, 0xE8] := by decide
example : (Value.uint 1000000000000).encode = [0x1B, 0, 0, 0, 0xE8, 0xD4, 0xA5, 0x10, 0] := by
  decide
example : (Value.nint 99).encode = [0x38, 0x63] := by decide
example : (Value.array [.uint 1, .array [.uint 2, .uint 3], .array [.uint 4, .uint 5]]).encode =
    [0x83, 0x01, 0x82, 0x02, 0x03, 0x82, 0x04, 0x05] := by decide
example : (Value.map [(.text [0x61], .uint 1), (.text [0x62], .array [.uint 2, .uint 3])]).encode =
    [0xA2, 0x61, 0x61, 0x01, 0x61, 0x62, 0x82, 0x02, 0x03] := by decide
-- 1.1 as a double.
example : (Value.float 8 0x3FF199999999999A).encode =
    [0xFB, 0x3F, 0xF1, 0x99, 0x99, 0x99, 0x99, 0x99, 0x9A] := by decide
-- Indefinite lengths do not decode: `9F FF` is well-formed but not definite.
example : decode [0x9F, 0xFF] = none := by decide
-- A non-preferred head decodes to the same value as the preferred one.
example : decode [0x18, 0x00] = some (.uint 0) := rfl

end Examples

end Silmaril.Formats.Cbor

end
