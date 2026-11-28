module

public import Silmaril.Formats.ThriftCompact.Defs
import Silmaril.Proofs.Formats.ThriftCompact.Varint
import Silmaril.Proofs.Formats.ThriftCompact.Payload

/-! Wire correctness for Compact varints and binary payloads, and signed round trips. -/

public section

namespace Silmaril.Formats.ThriftCompact

theorem unzigzag_zigzag (value : Int) : unzigzag (zigzag value) = value :=
  Proofs.Formats.ThriftCompact.unzigzag_zigzag value

theorem zigzag_unzigzag (value : Nat) : zigzag (unzigzag value) = value :=
  Proofs.Formats.ThriftCompact.zigzag_unzigzag value

/-- The unsigned width bound on a ZigZag code is exactly the signed width bound. -/
theorem zigzag_lt_iff (width : Width) (value : Int) :
    zigzag value < 2 ^ width.bits ↔ -width.halfRange ≤ value ∧ value < width.halfRange :=
  Proofs.Formats.ThriftCompact.zigzag_lt_iff width value

/-- Successful unsigned reads consume exactly a wire prefix within the byte and value bounds. -/
theorem readVarint_ok_iff {width : Width} {mode : VarintMode}
    {source : Bytes} {offset value next : Nat} :
    readVarint width mode source offset = .ok (value, next) ↔
      value < 2 ^ width.bits ∧
      ∃ octets suffix : List UInt8,
        source.toList.drop offset = octets ++ suffix ∧
        VarintWire mode octets value ∧ octets.length ≤ width.byteCount ∧
        next = offset + octets.length :=
  Proofs.Formats.ThriftCompact.readVarint_ok_iff

/-- Successful signed reads consume the wire prefix for the value's ZigZag code
and return a value in the signed domain of the requested width. -/
theorem readSigned_ok_iff {width : Width} {mode : VarintMode}
    {source : Bytes} {offset next : Nat} {value : Int} :
    readSigned width mode source offset = .ok (value, next) ↔
      (-width.halfRange ≤ value ∧ value < width.halfRange) ∧
      ∃ octets suffix : List UInt8,
        source.toList.drop offset = octets ++ suffix ∧
        VarintWire mode octets (zigzag value) ∧ octets.length ≤ width.byteCount ∧
        next = offset + octets.length :=
  Proofs.Formats.ThriftCompact.readSigned_ok_iff

theorem encodeSigned?_isSome_iff (width : Width) (value : Int) :
    (encodeSigned? width value).isSome = true ↔
      -width.halfRange ≤ value ∧ value < width.halfRange :=
  Proofs.Formats.ThriftCompact.encodeSigned?_isSome_iff width value

/-- Decoding the signed encoding at any byte offset recovers the value and leaves
the following bytes unread, in either varint mode. -/
theorem readSigned_encodeSigned? {width : Width} {value : Int} {encoded : Bytes}
    (hencode : encodeSigned? width value = some encoded) (mode : VarintMode)
    (leading trailing : Bytes) :
    readSigned width mode (leading.append (encoded.append trailing)) leading.length =
      .ok (value, leading.length + encoded.length) :=
  Proofs.Formats.ThriftCompact.readSigned_encodeSigned? hencode mode leading trailing

/-- A successful fixed-width read returns exactly the checked source slice. -/
theorem readFixed_ok_iff {count offset next : Nat} {source payload : Bytes} :
    readFixed count source offset = .ok (payload, next) ↔
      next = offset + count ∧
      source.slice? offset (some next) = some payload :=
  Proofs.Formats.ThriftCompact.readFixed_ok_iff

/-- A binary value consists of the bounded length prefix and exactly that many payload octets. -/
theorem readBinary_ok_iff {mode : VarintMode} {limit offset next : Nat}
    {source payload : Bytes} :
    readBinary mode limit source offset = .ok (payload, next) ↔
      ∃ count payloadOffset,
        readVarint .i32 mode source offset = .ok (count, payloadOffset) ∧
        count < 2 ^ 31 ∧ count ≤ limit ∧ next = payloadOffset + count ∧
        source.slice? payloadOffset (some next) = some payload :=
  Proofs.Formats.ThriftCompact.readBinary_ok_iff

end Silmaril.Formats.ThriftCompact
