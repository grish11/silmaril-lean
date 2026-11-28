module

import Silmaril.Formats.Arrow.TimestampStream.FromCsv.Defs
meta import Silmaril.Formats.Arrow.TimestampStream.FromCsv.Defs

open Silmaril Silmaril.Formats Silmaril.Relational
open Silmaril.Formats.Arrow.TimestampStream.FromCsv
open Silmaril.Formats.Arrow.TimestampStream.ToCsv (Cell CsvLimits schemaOf)
open Silmaril.Formats.Relational.NamedTable (Packed schemaMatches)
open Silmaril.Numeric.Timestamp (TickUnit)

private def tickUnit : String → Option TickUnit
  | "s" => some .second
  | "ms" => some .millisecond
  | "us" => some .microsecond
  | "ns" => some .nanosecond
  | _ => none

private def retained : Arrow.TimestampBatch.Binding := ⟨"retained", true, ⟨.second, none⟩⟩
private def db : Packed Nat Csv.Field Cell := fun name =>
  if name = 0 then some ⟨schemaOf retained, [fun _ => some ⟨-7⟩]⟩ else none

private def observation (table : Scan.Observation Csv.Field Cell) : List (List (Option Int)) :=
  table.rows.map fun row => List.ofFn fun i => (row i).map (·.ticks)

private def ipcLimits (mode : String) : Arrow.Limits :=
  match mode with
  | "ipc-rows" => { rows := 1 }
  | "ipc-body" => { bodyBytes := 1 }
  | "ipc-batches" => { batches := 0 }
  | _ => {}

private def csvLimits (mode : String) : CsvLimits :=
  match mode with
  | "csv-bytes" => ⟨64, 1⟩
  | "csv-rows" => ⟨1, 4096⟩
  | _ => ⟨64, 4096⟩

private def expected (mode : String) (frame : KBytes) : Option Error :=
  match mode with
  | "schema-mismatch" => some .schemaMismatch
  | "extra-frame" => some (.schemaExtent (frame.len - 8) frame.len)
  | "truncated-frame" => some (.schema (.schemaEnvelope (.malformed .truncated)))
  | "v4" => some (.schema (.schemaMetadata (.unsupported (.metadataVersion 3))))
  | "shape" => some (.schema (.schemaBinding (.malformed .batchLayout)))
  | "bad-csv" => some (.csv .malformedWire)
  | "bad-header" => some (.csv .headerMismatch)
  | "bad-tick" => some (.csv (.parseCell 0))
  | "required-null" => some .requiredNull
  | "occupied" => some .nameConflict
  | "csv-bytes" => some .csvByteLimit
  | "csv-rows" => some .csvRowLimit
  | "ipc-rows" => some (.writer (.limit .rows))
  | "ipc-body" => some (.writer (.limit .bodyBytes))
  | "ipc-batches" => some (.writer (.limit .batches))
  | _ => none

public def main (args : List String) : IO Unit := do
  let [mode, source, schemaPath, output, field, unit, zonePresent, zone, nullable] := args
    | throw (IO.userError "usage: Emit.lean MODE CSV SCHEMA OUT FIELD UNIT ZONE-PRESENT ZONE NULLABLE")
  let some kind := tickUnit unit
    | throw (IO.userError "invalid timestamp unit")
  let declared : Arrow.TimestampBatch.Binding :=
    ⟨field, nullable == "true", ⟨kind, if zonePresent == "true" then some zone else none⟩⟩
  let rawFrame ← IO.FS.readBinFile schemaPath
  let frame := KBytes.ofChunks 1 rawFrame.size (rawFrame.data.toList.map UInt8.toNat)
  let wire := (← IO.FS.readBinFile source).data.toList
  let destination := if mode == "occupied" then 0 else 1
  let result := convert db destination (ipcLimits mode) (csvLimits mode) (schemaOf declared) frame wire
  if mode != "ok" then
    let .error reason := result
      | throw (IO.userError "expected a failure without a named result")
    unless some reason == expected mode frame do
      throw (IO.userError s!"unexpected error for {mode}")
  else
    let .ok emitted := result
      | throw (IO.userError "TIMESTAMP emission failed")
    let some inserted := Scan.observePacked emitted.db destination
      | throw (IO.userError "missing named table")
    let some unchanged := Scan.observePacked emitted.db 0
      | throw (IO.userError "missing original table")
    let .ok read := Arrow.TimestampStream.read {} emitted.wire
      | throw (IO.userError "TIMESTAMP readback failed")
    unless schemaMatches (schemaOf declared) inserted.schema &&
        schemaMatches inserted.schema (schemaOf read.binding) &&
        observation inserted == (tickCounts read.batches.flatten).map (fun tick => [tick]) &&
        schemaMatches (schemaOf retained) unchanged.schema && observation unchanged == [[some (-7)]] do
      throw (IO.userError "named result or TIMESTAMP readback mismatch")
    IO.FS.writeBinFile output emitted.wire.toByteArray
