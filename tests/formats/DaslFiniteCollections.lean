module

import Mathlib.Data.String.Basic
import Silmaril.Formats.Dasl.Encode.Collection.Optimized.Defs
import Silmaril.Formats.Dasl.Wire.Profile.Thms
meta import Silmaril.Formats.Dasl.Encode.Collection.Optimized.Defs
meta import Silmaril.Formats.Dasl.Wire.Profile.Defs

open Silmaril.Formats.Dasl Encode

attribute [local instance] SparseIntSet.signedOrder

private def check (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

private def checkProfile {Name : Type} (profile : Wire.Profile Name) : IO Unit := do
  let array : TotalCodec (Finset Int64) (Shallow Name) := finiteSet signed
  let keys : Finset Int64 := {-2, -1, 0, 1, 8}
  let arrayWire := profile.codec array
  let rangeWire := profile.codec (signedRangeSet (Name := Name))
  let some arrayBytes := arrayWire.encode? keys | throw (IO.userError "array rejected")
  let some rangeBytes := rangeWire.encode? keys | throw (IO.userError "ranges rejected")
  check (decide (arrayWire.decode? arrayBytes = some keys)) "array wire recovery"
  check (decide (rangeWire.decode? rangeBytes = some keys)) "range wire recovery"
  let codec : TotalCodec (Silmaril.Semantics.OrderedMap String Int64) (Shallow Name) :=
    finiteMap pairEntry text signed
  let entry := pairEntry.encode (text.encode "duplicate", signed.encode 1)
  check (codec.decode? (Encode.list.encode [entry, entry])).isNone "reject duplicate decoded map keys"

public def main : IO Unit := do
  checkProfile Wire.Profile.dasl
  checkProfile Wire.Profile.bdasl
