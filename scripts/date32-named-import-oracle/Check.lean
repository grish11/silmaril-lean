module

import Silmaril.Formats.Relational.NamedTable.Date32.Defs
meta import Silmaril.Formats.Relational.NamedTable.Date32.Defs

open Silmaril Silmaril.Formats Silmaril.Relational
open Silmaril.Formats.Relational.NamedTable (schemaMatches)
open Silmaril.Formats.Relational.NamedTable.Date32

private def seed : Database String := fun key =>
  if key = "keep" then some ⟨schema "prior" false, rows "prior" false [some (-7)]⟩ else none

private def days : List (Option Int) :=
  [some (-2147483648), some (-719528), some (-1), none, some 0, some 11016, some 2147483647]

private def observeMatches (db : Database String) (key field : String) (nullable : Bool)
    (expected : List (Option Int)) : Bool :=
  match Scan.observePacked db key with
  | none => false
  | some table =>
    if h : 0 < table.schema.width then
      schemaMatches (schema field nullable) table.schema &&
        table.rows.map (fun row => (row ⟨0, h⟩).map Int32.toInt) == expected
    else false

private def expectError {Error Value : Type} [DecidableEq Error]
    (label : String) (expected : Error) (result : Except Error Value) : IO Unit :=
  match result with
  | .error actual => unless actual == expected do throw (IO.userError s!"wrong error: {label}")
  | .ok _ => throw (IO.userError s!"unexpected named result: {label}")

private def arrowBytes (input : ByteArray) : KBytes :=
  KBytes.ofChunks 1 input.size (input.data.toList.map UInt8.toNat)

public def main (args : List String) : IO Unit := do
  let [parquetPath, ipcPath, corruptPath, truncatedPath, date64Path] := args
    | throw (IO.userError "expected five fixture paths")
  let parquet := Bytes.ofList (← IO.FS.readBinFile parquetPath).data.toList
  let corrupt := Bytes.ofList (← IO.FS.readBinFile corruptPath).data.toList
  let ipc := arrowBytes (← IO.FS.readBinFile ipcPath)
  let truncated := arrowBytes (← IO.FS.readBinFile truncatedPath)
  let date64 := arrowBytes (← IO.FS.readBinFile date64Path)
  let fromParquet := fun name field nullable input => importParquet seed name field nullable {} input
  let fromIpc := fun name field nullable input => importIpc seed name field nullable {} input

  let .ok parquetDb := fromParquet "new" "date" true parquet
    | throw (IO.userError "Parquet DATE import failed")
  let .ok ipcDb := fromIpc "new" "date" true ipc
    | throw (IO.userError "Arrow Date32 import failed")
  for db in [parquetDb, ipcDb] do
    unless observeMatches db "new" "date" true days && observeMatches db "keep" "prior" false [some (-7)] &&
        (db "absent").isNone do
      throw (IO.userError "named table descriptor, ordered slots or retained entry differ")
  let .ok parsed := Arrow.DateStream.read {} ipc
    | throw (IO.userError "expected checked IPC batches")
  unless parsed.batches.map List.length == [4, 0, 3] do
    throw (IO.userError "unexpected IPC batch boundaries")

  let parquetFailure := .readError (.groupFailure 1 (.scan .unsupportedPageEncoding))
  let ipcFailure := .readError (.source (.batch 2 (.body (.malformed .truncated))))
  expectError "late Parquet group" parquetFailure (fromParquet "new" "date" true corrupt)
  expectError "late IPC record" ipcFailure (fromIpc "new" "date" true truncated)
  expectError "Parquet field name" .schemaMismatch (fromParquet "new" "other" true parquet)
  expectError "IPC field name" .schemaMismatch (fromIpc "new" "other" true ipc)
  expectError "Parquet nullability" .schemaMismatch (fromParquet "new" "date" false parquet)
  expectError "IPC nullability" .schemaMismatch (fromIpc "new" "date" false ipc)
  expectError "occupied name before Parquet error" .nameConflict (fromParquet "keep" "date" true corrupt)
  expectError "occupied name before IPC error" .nameConflict (fromIpc "keep" "date" true truncated)
  expectError "Date64 unit" (.openError .date64) (fromIpc "new" "date" true date64)
  IO.println "Lean: 2 exact named inserts with 7 ordered slots each, and 9 typed rejections"
