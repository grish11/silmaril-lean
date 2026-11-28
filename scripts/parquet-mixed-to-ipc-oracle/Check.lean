module

import Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc.Defs
meta import Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Int32ByteArrayGroup
open Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc

private def ordinal : Field := ⟨"ordinal", .required⟩
private def nullableOrdinal : Field := ⟨"ordinal", .optional⟩
private def payload : Field := ⟨"payload", .optional⟩
private def key : Field := ⟨"key", .required⟩

private def load (directory : System.FilePath) (file : String) : IO Bytes := do
  return ⟨← IO.FS.readBinFile (directory / file)⟩

private def emit (directory : System.FilePath) (input : Bytes) (output : String) (int32 binary : Field)
    (counts : List Nat) : IO Unit := do
  let .ok prepared := Prepare.prepare {} input int32 binary
    | throw (IO.userError s!"could not prepare {output}")
  let .ok wire := convert {} {} input int32 binary
    | throw (IO.userError s!"native conversion failed for {output}")
  let .ok decoded := Arrow.MixedFlat.Stream.read {} wire
    | throw (IO.userError s!"checked mixed reader rejected {output}")
  let schema := writerSchema prepared.schema
  let expected := (prepared.batches.map writerBatch).map (Arrow.MixedFlat.StreamWriter.BatchInput.observe schema)
  unless decoded.fields == prepared.schema.fields &&
      decoded.batches.map (·.observed.rowCount) == counts &&
      decoded.batches.map Arrow.MixedFlat.StreamWriter.observeBatch == expected do
    throw (IO.userError s!"wrong fields, group boundaries or paired slots for {output}")
  IO.FS.writeBinFile (directory / output) wire.toByteArray

public def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected the fixture directory")
  let directory := System.FilePath.mk path
  let v1 ← load directory "plain-byte-array-v1.parquet"
  let v2 ← load directory "plain-byte-array-v2.parquet"
  let badV2 ← load directory "plain-byte-array-v2-bad-length.parquet"
  let emptyMiddle ← load directory "empty-middle-v2.parquet"
  let nullable ← load directory "nullable-int32-v2.parquet"
  let schemaOnly ← load directory "mixed-schema-only.parquet"
  emit directory v1 "v1.arrows" ordinal payload [12, 12, 12]
  emit directory v2 "v2.arrows" ordinal payload [12, 12, 12]
  emit directory badV2 "intact-sibling.arrows" ordinal key [12, 12, 12]
  emit directory emptyMiddle "empty-middle.arrows" ordinal payload [3, 0, 2]
  emit directory nullable "nullable-int32.arrows" nullableOrdinal key [3, 2]
  emit directory schemaOnly "schema-only.arrows" nullableOrdinal key []

  let writerRefusal : Arrow.MixedFlat.Limits := { observation := { totalRows := 0 } }
  let .error (.source (.openFailure (.fileByteLimit 4 actual))) :=
    convert { group := { maxFileBytes := 4 } } writerRefusal emptyMiddle ordinal payload
    | throw (IO.userError "the original source byte limit did not precede the writer limit")
  unless actual == emptyMiddle.length do throw (IO.userError "wrong input size in byte cap error")

  let .error (.source (.groupFailure 1
      (.byteArray (.page 1 1 "payload" 1 646 (.decode (.scalar (.plain .truncated))))))) :=
    convert {} {} badV2 ordinal payload
    | throw (IO.userError "wrong late V2 source failure")
  unless emptyMiddle.data[122]! == 0 do throw (IO.userError "wrong original encoding byte")
  let late : Bytes := ⟨emptyMiddle.data.set! 122 6⟩
  let reason := File.Error.groupFailure 2 (.byteArray (.page 2 1 "payload" 0 108 (.encoding 3)))
  let .error (.source failed) := convert {} writerRefusal late ordinal payload
    | throw (IO.userError "late source failure lost precedence over the writer")
  unless failed == reason do throw (IO.userError "wrong original last-group cause")
  let .ok ⟨_, trace⟩ := Reader.readAll (File.openSource {} late ordinal payload)
    | throw (IO.userError "late source failed without an opened trace")
  unless trace.batches.map (·.rowCount) == [3, 0] && trace.termination == .readError reason do
    throw (IO.userError "the separate trace lost its completed prefix")

  let .error (.writer (.budget 2 (.limit .totalRows))) :=
    convert {} { observation := { totalRows := 4 } } emptyMiddle ordinal payload
    | throw (IO.userError "wrong indexed running row budget failure")
  let .error (.writer (.batch 1 (.view 1 .valueLimit))) :=
    convert {} { view := { valueBytes := 12 } } nullable nullableOrdinal key
    | throw (IO.userError "wrong indexed BinaryView value cap")
  let .error (.writer (.ipc (.limit .batches))) :=
    convert {} { observation := { ipc := { batches := 2 } } } emptyMiddle ordinal payload
    | throw (IO.userError "wrong writer batch-count cap")
  let .error (.writer (.schema (.limit .fields))) :=
    convert {} { observation := { ipc := { fields := 1 } } } schemaOnly nullableOrdinal key
    | throw (IO.userError "wrong writer schema cap")
  IO.println "Lean: six actual V5 streams and seven typed source/writer refusals"
