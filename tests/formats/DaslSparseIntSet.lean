module

import Silmaril.Formats.Dasl.SparseIntSet.Thms
import Silmaril.Formats.Dasl.Wire.Profile.Thms
meta import Silmaril.Formats.Dasl.SparseIntSet.Defs
meta import Silmaril.Formats.Dasl.Wire.Profile.Defs

open Silmaril.Formats.Dasl Silmaril.Formats.Cbor

private def check (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

private def signedEdges : List Int64 := [-9223372036854775808, -1, 0, 9223372036854775807]

private def setWire : ByteArray := ⟨#[0x84,
  0x3b, 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x20, 0x00,
  0x1b, 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]⟩

private def checkSet {Name : Type} (profile : Wire.Profile Name) : IO Unit := do
  let set := SparseIntSet.normalize (signedEdges.reverse ++ [-1, 0])
  check (SparseIntSet.keys set == signedEdges) "signed order and deduplication"
  check (SparseIntSet.cardinality set == 4) "cardinality at signed edges"
  check (SparseIntSet.contains set (-9223372036854775808) && !SparseIntSet.contains set 1) "membership"
  let codec := profile.codec SparseIntSet.codec
  check (codec.encode? set == some setWire) "golden signed i64 array"
  check (decide (codec.decode? setWire = some set)) "wire recovery"
  check (codec.encode? (SparseIntSet.normalize []) == some ⟨#[0x80]⟩) "empty set"
  check ((codec.decode? ⟨#[0x82, 0x20, 0x20]⟩).isNone) "duplicate keys rejected"
  check ((codec.decode? ⟨#[0x82, 0x00, 0x20]⟩).isNone) "out of signed order rejected"
  check ((codec.decode? ⟨#[0x81, 0xf4]⟩).isNone) "non-integer keys rejected"
  check ((codec.decode? ⟨#[0x81, 0x18, 0x00]⟩).isNone) "overlong CBOR integer rejected"

private def checkBdasl : IO Unit := do
  let cidBytes (kind : UInt8) := [1, kind, 0x1e, 0x20] ++ List.replicate 32 0xa5
  let tag (cid : List UInt8) := ([0xd8, 0x2a, 0x58, 0x25, 0] ++ cid).toByteArray
  let some obj := (Drisl.Cid.codec .bdasl).parse? (cidBytes 0x71) | throw (IO.userError "BLAKE3 object CID")
  let some raw := (Drisl.Cid.codec .bdasl).parse? (cidBytes 0x55) | throw (IO.userError "BLAKE3 raw CID")
  let profile := Wire.Profile.bdasl
  let objectWire := tag (cidBytes 0x71)
  let blobWire := tag (cidBytes 0x55)
  check (profile.render? (.ref (.obj obj)) == some objectWire) "BLAKE3 object link bytes"
  check (profile.render? (.ref (.blob raw)) == some blobWire) "BLAKE3 blob link bytes"
  match profile.parse? objectWire, profile.parse? blobWire with
  | some (.ref (.obj obj')), some (.ref (.blob raw')) =>
    check (obj'.val == obj.val && raw'.val == raw.val) "BLAKE3 links recover by kind"
  | _, _ => throw (IO.userError "wrong decoded BDASL link kind")
  check ((profile.render? (.ref (.obj raw))).isNone && (profile.render? (.ref (.blob obj))).isNone)
    "mismatched link kinds rejected"
  check ((profile.parse? (tag (cidBytes 0x70))).isNone) "unsupported CID codec rejected"
  check ((Wire.Profile.dasl.parse? objectWire).isNone) "DASL rejects BLAKE3 links"
  let read := fun _ => some setWire
  check (decide (profile.read? SparseIntSet.codec read obj = SparseIntSet.fromKeys? signedEdges))
    "recover from an object CID"
  check ((profile.read? SparseIntSet.codec read raw).isNone) "a raw CID cannot name a set root"

public def main : IO Unit := do
  checkSet Wire.Profile.dasl
  checkSet Wire.Profile.bdasl
  checkBdasl
