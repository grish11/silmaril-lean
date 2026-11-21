module
public import Silmaril.Formats.Json.Dasl.Defs

public section
namespace Silmaril.Proofs.Formats.Json.Dasl
open Silmaril.Formats Silmaril.Formats.Dasl Silmaril.Formats.Dasl.Encode Silmaril.Formats.JsonDasl

theorem i64_value {input : Int} {output : Int64} (encoded : i64Number? input = some output) :
    output.toInt = input := by
  unfold i64Number? at encoded
  split at encoded
  · rename_i bounds
    cases encoded
    exact Int64.toInt_ofInt_of_le bounds.1 bounds.2
  · cases encoded

theorem nat_roundtrip (value : Nat) : decodeNat? (encodeNat value) = some value := by
  unfold decodeNat? encodeNat
  rw [(listOf bits).recovers]
  simp only [Option.map_some, List.map_map, Option.some.injEq]
  have digits : (Nat.digits 256 value).map (UInt64.toNat ∘ UInt64.ofNat) = Nat.digits 256 value := by
    conv_rhs => rw [← List.map_id (Nat.digits 256 value)]
    apply List.map_congr_left
    intro digit member
    have bound : digit < 256 := Nat.digits_lt_base (by decide) member
    have fits : digit < UInt64.size := Nat.lt_trans bound (by decide)
    simp [Nat.mod_eq_of_lt fits]
  rw [digits, Nat.ofDigits_digits]

theorem int_roundtrip (value : Int) : decodeInt? (encodeInt value) = some value := by
  cases value <;> simp [encodeInt, decodeInt?, boolean, nat_roundtrip]

theorem decimal_roundtrip (number : JsonWire.Decimal) : decodeDecimal? (encodeDecimal number) = some number := by
  cases number
  simp [encodeDecimal, decodeDecimal?, boolean, nat_roundtrip, int_roundtrip]

theorem scalar_roundtrip {N : Type} (numbers : TotalCodec N Value) (value : JsonWire.Scalar N) :
    decodeScalar? numbers (encodeScalar numbers value) = some value := by
  rcases value with _ | (_ | _ | _) <;> simp [encodeScalar, decodeScalar?, unitsCodec.recovers, numbers.recovers]

theorem bytes_scalar_roundtrip {N : Type} (numbers : TotalCodec N Value) (value : JsonWire.Scalar N ⊕ ByteArray) :
    decodeBytesScalar? numbers (encodeBytesScalar numbers value) = some value := by
  rcases value with (_ | (_ | _ | _)) | _ <;>
    simp [encodeBytesScalar, decodeBytesScalar?, encodeScalar, decodeScalar?, unitsCodec.recovers, numbers.recovers]

theorem ordered_scalar_roundtrip {N : Type} (numbers : TotalCodec N Value) (value : JsonWithBytes.Scalar N) :
    decodeOrderedScalar? numbers (encodeOrderedScalar numbers value) = some value := by
  cases value <;> simp [encodeOrderedScalar, decodeOrderedScalar?, numbers.recovers]

theorem raw_roundtrip {Key Scalar : Type} (keys : TotalCodec Key Value) (scalar : TotalCodec Scalar Value)
    {sort : JsonIx} (ast : RawSyn Key Scalar sort) :
    decodeRaw? keys scalar sort (encodeRaw keys scalar ast) = some ast := by
  induction ast <;> simp [decodeRaw?, encodeRaw, *, scalar.recovers, keys.recovers]

theorem include_embed {N : Type} (ordinary : TotalCodec (JsonWire.Scalar N) Value)
    (extended : TotalCodec (JsonWire.Scalar N ⊕ ByteArray) Value)
    (same : ∀ value, extended.encode (.inl value) = ordinary.encode value)
    {sort : JsonIx} (ast : JsonWire.Syn N sort) :
    encodeRaw unitsCodec extended (ast.mapScalar Sum.inl) = encodeRaw unitsCodec ordinary ast := by
  induction ast <;> simp [encodeRaw, RawSyn.mapScalar, *]

end Silmaril.Proofs.Formats.Json.Dasl
