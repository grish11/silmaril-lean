module

import Silmaril.Formats.Dasl.Encode.Partition.Thms
import Silmaril.Formats.Dasl.SparseIntSet.Defs
import Silmaril.Formats.Dasl.Wire.Profile.Thms
import Silmaril.Formats.PER.UnionFind.Thms
meta import Silmaril.Formats.Dasl.Encode.Partition.Thms
meta import Silmaril.Formats.Dasl.SparseIntSet.Defs
meta import Silmaril.Formats.Dasl.Wire.Profile.Defs
meta import Silmaril.Formats.PER.UnionFind.Thms

open Silmaril.Formats Silmaril.Formats.Dasl Silmaril.Semantics
open Silmaril.Formats.Dasl.Encode.Partition

attribute [local instance] SparseIntSet.signedOrder

local instance : DecidableEq (OrderedMap Int64 Int64) := fun left right =>
  decidable_of_iff (left.entries = right.entries) ⟨OrderedMap.ext, congrArg OrderedMap.entries⟩

private def check (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

private def labels (offset : Int64) : OrderedMap Int64 Int64 :=
  OrderedMap.ofLookupOn {10, 20, 30, 40} fun key =>
    some (offset + if key ≤ 20 then 0 else key)

private def checkWire {Name : Type} (profile : Wire.Profile Name)
    (layout : Encode.TotalCodec (OrderedMap Int64 Int64) (Shallow Name)) : IO Unit := do
  let codec := profile.codec layout
  let first := labels 100
  let other := labels 200
  check (first.lookup? 10 != other.lookup? 10 && (first.lookup? 100).isNone) "external labels differ and are not keys"
  let some canonical := encodeCanonical? codec first | throw (IO.userError "canonical encoding failed")
  check (encodeCanonical? codec other == some canonical) "canonical bytes ignore labels"
  let some firstBytes := codec.encode? first | throw (IO.userError "raw encoding failed")
  let some otherBytes := codec.encode? other | throw (IO.userError "second raw encoding failed")
  check (firstBytes != otherBytes) "raw layouts retain labels"
  let some decoded := codec.decode? firstBytes | throw (IO.userError "raw decoding failed")
  let state := PER.Partition.toUnionFind decoded
  check (state.find 20 == some 10 && (state.find 100).isNone) "choose known least root, drop external label"
  let some merged := state.union 20 30 | throw (IO.userError "merge failed")
  let some bytes := encodeCanonical? codec merged.labels | throw (IO.userError "merge encoding failed")
  let some roundtrip := codec.decode? bytes | throw (IO.userError "merge recovery failed")
  let recovered := PER.Partition.toUnionFind roundtrip
  check (recovered.sameClass 10 30 == some true && recovered.sameClass 10 40 == some false) "exact union recovered"
  check ((recovered.sameClass 10 100).isNone && (recovered.union 10 100).isNone) "unknown stays outside partition"

private def checkProfile {Name : Type} (profile : Wire.Profile Name) : IO Unit := do
  checkWire profile (representativeMap Encode.signed)
  checkWire profile (classMembers Encode.signed)
  let raw : Encode.TotalCodec (ClassMembers Int64) (Shallow Name) :=
    Encode.pairMap Encode.signed (Encode.finiteSet Encode.signed)
  let layout : Encode.TotalCodec (OrderedMap Int64 Int64) (Shallow Name) := classMembers Encode.signed
  let overlap : ClassMembers Int64 := OrderedMap.ofLookupOn {100, 200} fun _ => some {10}
  let empty : ClassMembers Int64 := OrderedMap.ofLookupOn {100} fun _ => some ∅
  check (layout.decode? (raw.encode overlap)).isNone "overlapping classes rejected"
  check (layout.decode? (raw.encode empty)).isNone "empty class rejected"

public def main : IO Unit := do
  checkProfile Wire.Profile.dasl
  checkProfile Wire.Profile.bdasl
