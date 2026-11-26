module

import Silmaril.Formats.Arrow.TimestampStream.Writer.Defs
meta import Silmaril.Formats.Arrow.TimestampStream.Writer.Defs

open Silmaril Silmaril.Formats
open Silmaril.Numeric.Timestamp (TickUnit)

private def unit? : String → Option TickUnit
  | "s" => some .second
  | "ms" => some .millisecond
  | "us" => some .microsecond
  | "ns" => some .nanosecond
  | _ => none

private def batches (binding : Arrow.TimestampBatch.Binding) (empty : Bool) :
    List (Arrow.TimestampBatch.Column binding) :=
  if empty then []
  else
    let nullableSlots : Arrow.TimestampBatch.Column binding :=
      if binding.nullable then [none] else [some ⟨-7⟩]
    [[some ⟨-9223372036854775808⟩] ++ nullableSlots ++
      [some ⟨-1⟩, some ⟨0⟩, some ⟨9223372036854775807⟩], [],
      nullableSlots ++ [some ⟨87654321⟩]]

public def main (args : List String) : IO Unit := do
  let [name, unitName, zone, nullability, scenario, schemaPath, streamPath] := args
    | throw (IO.userError "usage: Emit.lean NAME UNIT ZONE NULLABILITY SCENARIO SCHEMA STREAM")
  let some unit := unit? unitName | throw (IO.userError "unsupported fixture unit")
  let binding : Arrow.TimestampBatch.Binding :=
    ⟨name, nullability == "optional", ⟨unit, if zone == "UTC" then some zone else none⟩⟩
  let .ok schema := Arrow.TimestampStream.Writer.emitSchema {} binding
    | throw (IO.userError "native TIMESTAMP Schema emission failed")
  let .ok stream := Arrow.TimestampStream.Writer.emit {} binding (batches binding (scenario == "empty"))
    | throw (IO.userError "native TIMESTAMP stream emission failed")
  IO.FS.writeBinFile schemaPath schema.toByteArray
  IO.FS.writeBinFile streamPath stream.toByteArray
