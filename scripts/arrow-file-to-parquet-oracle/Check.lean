module

import Silmaril.Formats.Csv.ParquetIpc.FromFile.Defs
meta import Silmaril.Formats.Csv.ParquetIpc.FromFile.Defs

open Silmaril Silmaril.Relational Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Csv.ParquetIpc.FromFile
open Silmaril.Formats.Relational.NamedTable (Packed schemaMatches)
open Snapshot.FlatInt32 (Cell)
open Snapshot.FlatInt32.ToCsv (csvSchema)

private def schema : Scan.Schema String Unit :=
  ⟨2, fun i => (if i.val = 0 then "n" else "m", ())⟩

private def reversed : Scan.Schema String Unit :=
  ⟨2, fun i => (if i.val = 0 then "m" else "n", ())⟩

private def db : Packed Nat Csv.Field Cell := fun name =>
  if name = 0 then some ⟨csvSchema schema, [fun _ => some 55]⟩ else none

private def limits : FlatInt32Writer.Limits :=
  ⟨8, 16384, {}, ⟨{}, 64, ⟨4096, 4096, ⟨64, 512⟩, 0⟩⟩⟩

private def expectedRows : List (List (Option Int)) :=
  [[some (-2147483648), none], [some 0, some 17], [none, some (-1)],
   [some 2147483647, none], [some (-9), some 4]]

private def rowsOf (table : Scan.Observation Csv.Field Cell) : List (List (Option Int)) :=
  table.rows.map fun row => List.ofFn fun i => (row i).map Int32.toInt

private def readInput (path : String) : IO KBytes := do
  let bytes ← IO.FS.readBinFile path
  return KBytes.ofChunks 1 bytes.size (bytes.data.toList.map UInt8.toNat)

private def checkSuccess (wire : KBytes) (expected : List (List (Option Int)))
    (target : String) : IO Unit := do
  let .ok converted := convert db 1 schema {} limits wire
    | throw (IO.userError "Arrow file conversion rejected")
  let some inserted := Scan.observePacked converted.db 1
    | throw (IO.userError "missing converted named table")
  let some retained := Scan.observePacked converted.db 0
    | throw (IO.userError "lost existing table")
  unless schemaMatches (csvSchema schema) inserted.schema && rowsOf inserted == expected &&
      schemaMatches (csvSchema schema) retained.schema && rowsOf retained == [[some 55, some 55]] &&
      (converted.db 2).isNone do
    throw (IO.userError "wrong named schema, slots or update")
  IO.FS.writeBinFile target converted.bytes.data

private def expectError (label : String) (reason : Csv.ParquetIpc.FromIpc.Error)
    (result : Except Csv.ParquetIpc.FromIpc.Error (FlatInt32Writer.FromCsv.Result Nat)) : IO Unit :=
  match result with
  | .error actual => unless actual == reason do throw (IO.userError s!"wrong error: {label}")
  | .ok _ => throw (IO.userError s!"unexpected output: {label}")

public def main (args : List String) : IO Unit := do
  let [valid, empty, damaged, target, emptyTarget] := args
    | throw (IO.userError "expected three Arrow files and two Parquet outputs")
  let valid ← readInput valid
  let empty ← readInput empty
  let damaged ← readInput damaged
  checkSuccess valid expectedRows target
  checkSuccess empty [] emptyTarget
  let .ok index := Arrow.FileReader.readIndex {} damaged
    | throw (IO.userError "damaged file index should remain admissible")
  let .ok (some first) := index.readRowsAt {} 0
    | throw (IO.userError "first record should remain readable")
  unless first.length == 2 do throw (IO.userError "wrong prefix rows")
  let .ok (some []) := index.readRowsAt {} 1
    | throw (IO.userError "empty second batch should remain readable")
  let .error (.malformed .bodyLength) := index.readRowsAt {} 2
    | throw (IO.userError "expected a length error at the third indexed batch")
  expectError "late record" (.input (.ipc (.malformed .bodyLength))) (convert db 1 schema {} limits damaged)
  expectError "ordered schema" .schemaMismatch (convert db 1 reversed {} limits valid)
  expectError "occupied name" .nameConflict (convert db 0 schema {} limits damaged)
  IO.println "Lean: exact named updates for 5 and 0 rows; late input, schema, and occupied-name errors passed"
