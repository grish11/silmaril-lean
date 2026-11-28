module

import Lean.Data.Json
import Silmaril.Formats.Relational.NamedTable.MixedIpc.FromParquet.Defs
import Silmaril.Formats.Relational.NamedTable.MixedIpc.Export.Defs
meta import Lean.Data.Json
meta import Silmaril.Formats.Relational.NamedTable.MixedIpc.FromParquet.Defs
meta import Silmaril.Formats.Relational.NamedTable.MixedIpc.Export.Defs

open Lean (Json toJson)
open Silmaril Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Int32ByteArrayGroup
open Silmaril.Formats.Relational.NamedTable.MixedIpc
open Silmaril.Formats.Relational.NamedTable.MixedIpc.FromParquet

private def ordinal : Field := ⟨"ordinal", .required⟩
private def nullableOrdinal : Field := ⟨"ordinal", .optional⟩
private def payload : Field := ⟨"payload", .optional⟩
private def key : Field := ⟨"key", .required⟩

private def original : Database String := fun name =>
  let schema := descriptor ordinal payload
  if name = "other" then some ⟨schema.schema, [schema.row (some 7, some [255, 0])]⟩ else none

private def load (dir : System.FilePath) (file : String) : IO Bytes := do
  return ⟨← IO.FS.readBinFile (dir / file)⟩

private def examine (input : Bytes) (integer binary : Field) : IO Json := do
  let expected := descriptor integer binary
  let .ok wire := ToIpc.convert {} {} input integer binary
    | throw (IO.userError "the mixed converter failed")
  let .ok grouped := read {} wire
    | throw (IO.userError "the checked mixed IPC observation failed")
  let counts := grouped.batches.map List.length
  let .ok updated := importNamed original "target" {} {} input integer binary
    | throw (IO.userError "the composed named insert failed")
  let .ok [rows] := Export.prepare updated "target" expected [counts.sum]
    | throw (IO.userError "the exact ordered descriptor or inserted row count changed")
  let .ok [[(some 7, some [255, 0])]] := Export.prepare updated "other" (descriptor ordinal payload) [1]
    | throw (IO.userError "an existing entry changed")
  unless rows == grouped.batches.flatten do throw (IO.userError "inserted row order differs from IPC")
  return Json.mkObj [
    ("intName", toJson expected.integer.1), ("intNullable", toJson expected.integer.2),
    ("viewName", toJson expected.binary.1), ("viewNullable", toJson expected.binary.2),
    ("counts", toJson counts),
    ("rows", toJson (rows.map fun row => [toJson (row.1.map Int32.toInt),
      toJson (row.2.map (List.map UInt8.toNat))]))]

public def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected the fixture directory")
  let dir := System.FilePath.mk path
  let v1 ← load dir "plain-byte-array-v1.parquet"
  let v2 ← load dir "plain-byte-array-v2.parquet"
  let badV2 ← load dir "plain-byte-array-v2-bad-length.parquet"
  let emptyMiddle ← load dir "empty-middle-v2.parquet"
  let nullable ← load dir "nullable-int32-v2.parquet"
  let schemaOnly ← load dir "mixed-schema-only.parquet"

  let .error (.conversion (.source (.openFailure (.fileByteLimit 4 actual)))) :=
    importNamed original "other" { group := { maxFileBytes := 4 } } { inputBytes := 0 }
      emptyMiddle ordinal payload
    | throw (IO.userError "wrong source admission failure or error precedence")
  unless actual == emptyMiddle.length do throw (IO.userError "wrong original file size")

  let .error (.conversion (.source (.groupFailure 1
      (.byteArray (.page 1 1 "payload" 1 646 (.decode (.scalar (.plain .truncated)))))))) :=
    importNamed original "target" {} {} badV2 ordinal payload
    | throw (IO.userError "late Parquet failure lost its exact cause")

  unless emptyMiddle.data[122]! == 0 do throw (IO.userError "wrong source encoding byte")
  let late : Bytes := ⟨emptyMiddle.data.set! 122 6⟩
  let .error (.conversion (.source (.groupFailure 2 (.byteArray (.page 2 1 "payload" 0 108 (.encoding 3)))))) :=
    importNamed original "target" {} { mixed := { observation := { totalRows := 0 } } } late ordinal payload
    | throw (IO.userError "failure after an empty group lost its original index or precedence")

  let .error (.conversion (.writer (.budget 2 (.limit .totalRows)))) :=
    importNamed original "target" {} { mixed := { observation := { totalRows := 4 } } } emptyMiddle ordinal payload
    | throw (IO.userError "wrong indexed native writer refusal")

  let .ok wire := ToIpc.convert {} {} emptyMiddle ordinal payload
    | throw (IO.userError "clean wire fixture failed")
  let .error (.ipcImport (.openError (.inputBytes actual limit))) :=
    importNamed original "target" {} { inputBytes := wire.len - 1 } emptyMiddle ordinal payload
    | throw (IO.userError "wrong checked IPC carrier cap refusal")
  unless actual == wire.len && limit == wire.len - 1 do throw (IO.userError "wrong IPC wire size")
  let .ok _ := importNamed original "target" {} { inputBytes := wire.len } emptyMiddle ordinal payload
    | throw (IO.userError "exact IPC byte-cap boundary did not admit the table")

  let .error (.ipcImport .nameConflict) :=
    importNamed original "other" {} { inputBytes := 0 } emptyMiddle ordinal payload
    | throw (IO.userError "vacancy did not take precedence inside the IPC import gate")

  let result ← [(v1, ordinal, payload), (v2, ordinal, payload), (badV2, ordinal, key),
    (emptyMiddle, ordinal, payload), (nullable, nullableOrdinal, key), (schemaOnly, nullableOrdinal, key)].mapM
    fun (bytes, integer, binary) => examine bytes integer binary
  IO.println (toJson result).compress
