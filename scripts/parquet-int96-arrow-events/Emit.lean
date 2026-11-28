module

import Silmaril.Formats.Parquet.Int96.Mixed.File.Events.Defs
import Silmaril.Formats.Arrow.TimestampStream.FromCsv.Defs
meta import Silmaril.Formats.Parquet.Int96.Mixed.File.Events.Defs
meta import Silmaril.Formats.Arrow.TimestampStream.FromCsv.Defs

open Silmaril Silmaril.Formats
open Silmaril.Numeric.Timestamp (TickUnit)

private def unit? : String → Option TickUnit
  | "us" => some .microsecond
  | "ns" => some .nanosecond
  | _ => none

/-- Test-only composition of the observed event batches with the existing
record writer and a supplied independent schema frame. -/
public def main (args : List String) : IO Unit := do
  let [sourcePath, schemaPath, outputPath, unitName, policyName, layoutName] := args
    | throw (IO.userError "usage: Emit.lean SOURCE SCHEMA OUTPUT UNIT POLICY LAYOUT")
  let some unit := unit? unitName
    | throw (IO.userError "unexpected timestamp unit")
  let policy : Parquet.Int96.Policy := if policyName == "utc" then .prolepticUtc else .prolepticLocal
  let layout : Parquet.FlatColumn.Layout := if layoutName == "optional" then .optional else .required
  let source : Bytes := ⟨← IO.FS.readBinFile sourcePath⟩
  let .ok ⟨schema, trace⟩ :=
      Parquet.Int96.Mixed.File.Events.readAll {} "legacy_ts" layout policy unit source
    | throw (IO.userError "INT96 event open failed")
  let .eos := trace.termination
    | throw (IO.userError "INT96 event read failed")
  let raw ← IO.FS.readBinFile schemaPath
  let frame := KBytes.ofChunks 1 raw.size (raw.data.toList.map UInt8.toNat)
  let .ok (binding, next) := Arrow.TimestampStream.readSchema {} frame
    | throw (IO.userError "TIMESTAMP fixture schema rejected")
  let true := decide (next = frame.len ∧ schema.width = 1)
    | throw (IO.userError "unexpected schema extent or width")
  let field : Fin schema.width ←
    if h : 0 < schema.width then pure ⟨0, h⟩ else throw (IO.userError "missing timestamp field")
  let (name, kind) := schema.kind field
  unless binding.name == name && binding.nullable == kind.nullable &&
      decide (binding.metadata.unit = kind.metadata.unit ∧ binding.metadata.timezone = kind.metadata.timezone) do
    throw (IO.userError "TIMESTAMP schema differs from event metadata")
  let mut wire := frame
  for batch in trace.batches do
    let slots : Arrow.TimestampBatch.Column binding := (batch.values field).map (Option.map fun tick => ⟨tick.ticks⟩)
    let .ok record := Arrow.TimestampStream.FromCsv.emitRecord {} binding slots
      | throw (IO.userError "TIMESTAMP record encoding failed")
    wire := wire ++ record
  IO.FS.writeBinFile outputPath (wire ++ Arrow.StreamWriter.eos).toByteArray
