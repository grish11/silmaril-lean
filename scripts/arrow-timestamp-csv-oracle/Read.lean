module

import Lean.Data.Json
import Silmaril.Formats.Arrow.TimestampStream.ToCsv.Defs
meta import Silmaril.Formats.Arrow.TimestampStream.ToCsv.Defs

open Silmaril Silmaril.Formats Silmaril.Relational Silmaril.Numeric.Timestamp
open Silmaril.Formats.Arrow.TimestampStream.ToCsv
open Silmaril.Formats.Relational.NamedTable (Packed)

private def retained : Arrow.TimestampBatch.Binding := ⟨"retained", true, ⟨.second, none⟩⟩
private def db : Packed Nat Csv.Field Cell := fun name =>
  if name = 0 then some ⟨schemaOf retained, [fun _ => some ⟨-7⟩]⟩ else none

private def limits : CsvLimits := ⟨64, 4096⟩

private def observe (table : Scan.Observation Csv.Field Cell) : List (List (Option Int)) :=
  table.rows.map fun row => List.ofFn fun i => (row i).map (·.ticks)

private def unitName : TickUnit → String
  | .second => "s"
  | .millisecond => "ms"
  | .microsecond => "us"
  | .nanosecond => "ns"

private def writeExport (input : KBytes) (csvPath metadataPath : String) : IO Unit := do
  let .ok result := convert db 1 {} limits input
    | throw (IO.userError "TIMESTAMP conversion failed")
  let some inserted := Scan.observePacked result.db 1
    | throw (IO.userError "expected a named update")
  let some kept := Scan.observePacked result.db 0
    | throw (IO.userError "expected the original table")
  unless observe kept == [[some (-7)]] && List.ofFn kept.schema.kind == List.ofFn (schemaOf retained).kind do
    throw (IO.userError "the original table changed")
  let .ok rows := Csv.Typed.Utf8.decode result.schema codecs result.wire
    | throw (IO.userError "typed CSV readback failed")
  unless observe ⟨result.schema, rows⟩ == observe inserted &&
      List.ofFn inserted.schema.kind == List.ofFn result.schema.kind do
    throw (IO.userError "typed CSV readback and named update differ")
  let .ok boundary := convert db 1 {} ⟨rows.length, result.wire.length⟩ input
    | throw (IO.userError "exact row and byte limits should admit the result")
  unless boundary.wire == result.wire do
    throw (IO.userError "limits changed the admitted export")
  let [(label, kind)] := List.ofFn result.schema.kind
    | throw (IO.userError "expected one declared timestamp column")
  let some fieldName := String.fromUTF8? ⟨label.toArray⟩
    | throw (IO.userError "expected a UTF-8 field name")
  let utc := match kind.metadata.kind with
    | .utcInstant => true
    | .localReading => false
  let metadata := Lean.Json.mkObj [
    ("name", Lean.toJson fieldName), ("unit", Lean.toJson (unitName kind.unit)),
    ("timezone", Lean.toJson kind.timezone), ("nullable", Lean.toJson kind.nullable),
    ("utc", Lean.toJson utc)]
  IO.FS.writeBinFile csvPath ⟨result.wire.toArray⟩
  IO.FS.writeFile metadataPath (metadata.compress ++ "\n")

private def expectError (name : Nat) (ipc : Arrow.Limits) (csv : CsvLimits)
    (input : KBytes) (expected : Error) : IO Unit := do
  let .error actual := convert db name ipc csv input
    | throw (IO.userError "expected failure without a named result")
  unless actual == expected do
    throw (IO.userError "unexpected TIMESTAMP conversion error")

public def main (args : List String) : IO Unit := do
  let source :: options := args
    | throw (IO.userError "usage: Read.lean INPUT.arrows OUTPUT.csv SCHEMA.json, or INPUT.arrows CASE")
  let bytes ← IO.FS.readBinFile source
  let input := KBytes.ofChunks 1 bytes.size (bytes.data.toList.map UInt8.toNat)
  match options with
  | [csvPath, metadataPath] => writeExport input csvPath metadataPath
  | ["missing-eos"] => expectError 1 {} limits input (.input (.batch 3 (.envelope (.malformed .truncated))))
  | ["late-body"] => expectError 1 {} limits input (.input (.batch 2 (.body (.malformed .truncated))))
  | ["occupied"] => expectError 0 {} limits input .nameConflict
  | ["ipc-cap"] => expectError 1 { batches := 1 } limits input (.input (.batch 1 .batchLimit))
  | ["row-cap"] => expectError 1 {} { limits with maxRows := 5 } input .rowLimit
  | ["byte-cap"] => expectError 1 {} { limits with maxBytes := 1 } input .byteLimit
  | ["header"] => expectError 1 {} limits input (.csv (.output (.encodeError .unrepresentableWire)))
  | _ => throw (IO.userError "unknown TIMESTAMP oracle case")
