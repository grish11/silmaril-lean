module

import Silmaril.Formats.Dasl.Wire.Canonical.Thms
meta import Silmaril.Formats.Dasl.Wire.Canonical.Thms

open Silmaril.Formats.Dasl

private def nested : Shallow Wire.Cid :=
  .dict {"aa", "b"} fun outer =>
    if outer.val = "aa" then .null else
      .dict {"ww", "x"} fun inner => if inner.val = "ww" then .i64 (-2 : Int64).toUInt64 else .bool true

private def encoded : ByteArray := ⟨#[0xa2, 0x61, 0x62, 0xa2, 0x61, 0x78, 0xf5, 0x62, 0x77, 0x77, 0x21, 0x62, 0x61, 0x61, 0xf6]⟩

public def main : IO Unit := do
  let codec := Wire.canonicalCodec
  unless codec.encode? nested == some encoded do
    throw (IO.userError "recursive map order must be by encoded CBOR key, not by String")
  let some value := codec.decode? encoded | throw (IO.userError "canonical abstract readback failed")
  unless codec.encode? value == some encoded do
    throw (IO.userError "canonical fixture did not reprint identically")
  let tag := fun (codecByte : UInt8) => ([0xd8, 0x2a, 0x58, 37, 0, 1, codecByte, 0x12, 32] ++ List.replicate 32 0).toByteArray
  let some (.ref (.obj object)) := codec.decode? (tag 0x71) | throw (IO.userError "expected DAG-CBOR object CID")
  let some (.ref (.blob raw)) := codec.decode? (tag 0x55) | throw (IO.userError "expected raw blob CID")
  unless codec.encode? (.ref (.obj object)) == some (tag 0x71) &&
      codec.encode? (.ref (.blob raw)) == some (tag 0x55) &&
      (codec.encode? (.ref (.obj raw))).isNone && (codec.encode? (.ref (.blob object))).isNone do
    throw (IO.userError "wrong typed CID tag must not serialize")
  let independentlyEncoded := ([0x84, 0x3b, 0x7f] ++ List.replicate 7 0xff ++ encoded.data.toList ++
    (tag 0x71).data.toList ++ (tag 0x55).data.toList).toByteArray
  let some decoded := codec.decode? independentlyEncoded | throw (IO.userError "accepted typed canonical input")
  unless codec.encode? decoded == some independentlyEncoded && Wire.render? decoded == some independentlyEncoded do
    throw (IO.userError "exact reprint of independently accepted nested typed data")
  let wrongOrder : ByteArray := ⟨#[0xa2, 0x62, 0x61, 0x61, 0xf6, 0x61, 0x62, 0xf6]⟩
  let duplicate : ByteArray := ⟨#[0xa2, 0x61, 0x62, 0xf6, 0x61, 0x62, 0xf6]⟩
  unless (codec.decode? wrongOrder).isNone && (codec.decode? duplicate).isNone && (codec.decode? (tag 0x70)).isNone do
    throw (IO.userError "wrong encoded-key order, duplicate keys and unsupported link codecs must be rejected")
