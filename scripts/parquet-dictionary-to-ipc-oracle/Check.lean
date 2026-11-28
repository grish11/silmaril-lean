module

import Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary.ToIpc.Defs
import Silmaril.Formats.Parquet.FlatInt32Writer.Defs
meta import Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary.ToIpc.Defs
meta import Silmaril.Formats.Parquet.FlatInt32Writer.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary.ToIpc

private def fields : List Arrow.Field :=
  [⟨"required_i32", false, .int32⟩, ⟨"optional_i32", true, .int32⟩]

private def readInput (path : String) : IO Bytes := do
  return ⟨← IO.FS.readBinFile path⟩

private def readKBytes (path : String) : IO KBytes := do
  let raw ← IO.FS.readBinFile path
  return KBytes.ofChunks 1 raw.size (raw.data.toList.map UInt8.toNat)

private def observe (wire : KBytes) (counts : List Nat) : IO Arrow.ObservedStream := do
  let .ok stream := Arrow.readStream {} wire
    | throw (IO.userError "IPC framing failed")
  let .ok read := Arrow.readRows {} wire
    | throw (IO.userError "IPC rows failed")
  unless stream.fields == fields && stream.batches.map (·.metadata.rowCount) == counts &&
      read.fields == fields && read.batches.map List.length == counts do
    throw (IO.userError "wrong descriptor or per-batch count")
  return read

private def expectError (label : String) (expected : Error) (output : Except Error KBytes) : IO Unit :=
  match output with
  | .ok _ => throw (IO.userError s!"unexpected IPC output: {label}")
  | .error error =>
    unless error == expected do
      throw (IO.userError s!"wrong typed error for {label}: {repr error}")

private def writeEmpty : Except FlatInt32Writer.Error Bytes :=
  (FlatInt32Writer.emit ⟨16, 4096, {}, ⟨{}, 32, ⟨64, 64, ⟨16, 32⟩, 0⟩⟩⟩
    ⟨0, [⟨"required_i32", .required []⟩, ⟨"optional_i32", .optional []⟩]⟩).map (·.bytes)

public def main (args : List String) : IO Unit := do
  let [mixed, late, reference, crc, snappy, noGroups, pyarrowEmpty, output] := args
    | throw (IO.userError "expected seven fixture paths and an output directory")
  let output : System.FilePath := ⟨output⟩
  let mixed ← readInput mixed
  let late ← readInput late
  let .ok wire := convert {} {} fields mixed
    | throw (IO.userError "mixed PLAIN/dictionary conversion failed")
  let observed ← observe wire [8, 8]
  let expected ← observe (← readKBytes reference) [8, 8]
  unless observed == expected do throw (IO.userError "PyArrow reference slots differ")
  IO.FS.writeBinFile (output / "mixed-output.arrows") wire.toByteArray

  let .ok schemaOnly := convert {} {} fields (← readInput noGroups)
    | throw (IO.userError "schema-only Parquet conversion failed")
  let _ ← observe schemaOnly []
  IO.FS.writeBinFile (output / "schema-only-output.arrows") schemaOnly.toByteArray

  let .ok empty := writeEmpty | throw (IO.userError "admitted zero-row group generation failed")
  let .ok emptyWire := convert {} {} fields empty
    | throw (IO.userError "conversion of admitted zero-row group failed")
  let _ ← observe emptyWire [0]
  IO.FS.writeBinFile (output / "empty-lean.parquet") empty.data
  IO.FS.writeBinFile (output / "empty-output.arrows") emptyWire.toByteArray

  let cause : SourceError :=
    .decode 1 (.column 1 "optional_i32" (.dictionary (.dictionaryPage (.hybrid .invalidWidth))))
  let .ok bound := openSource {} fields late | throw (IO.userError "late-error fixture should open")
  let .ok ⟨_, earlier⟩ := bound.snapshot.readAll bound.decode
    | throw (IO.userError "late-error fixture should yield events")
  unless earlier.batches.map (·.rowCount) == [8] && decide (earlier.termination = .readError cause) do
    throw (IO.userError "wrong prefix or terminal error from abstract events")
  expectError "late dictionary width" (.source cause) (convert {} {} fields late)
  expectError "reordered descriptor precedes corrupt group" (.schemaMismatch fields)
    (convert {} {} fields.reverse late)
  expectError "field name mismatch" (.schemaMismatch fields)
    (convert {} {} [⟨"other_i32", false, .int32⟩, ⟨"optional_i32", true, .int32⟩] mixed)
  expectError "required flag mismatch" (.schemaMismatch fields)
    (convert {} {} [⟨"required_i32", true, .int32⟩, ⟨"optional_i32", true, .int32⟩] mixed)
  expectError "CRC PLAIN column" (.source (.decode 0 (.column 0 "required_i32" (.plain .crcUnsupported))))
    (convert {} {} fields (← readInput crc))
  expectError "Snappy dictionary column" (.source (.decode 0 (.column 0 "required_i32" (.codec 1))))
    (convert {} {} fields (← readInput snappy))
  expectError "writer batch cap" (.writer (.limit .batches))
    (convert {} { ipc.batches := 1 } fields mixed)
  expectError "PyArrow zero-row chunks with offset zero" (.source (.invalidMetadata .pageInterval))
    (convert {} {} fields (← readInput pyarrowEmpty))
  IO.println "Lean: preserved mixed, schema-only and admitted empty-group batches; eight typed rejections passed"
