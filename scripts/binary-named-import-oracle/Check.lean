module

import Silmaril.Formats.Relational.NamedTable.Binary.Defs
meta import Silmaril.Formats.Relational.NamedTable.Binary.Defs

open Silmaril Silmaril.Formats Silmaril.Relational
open Silmaril.Formats.Relational.BinaryObservation
open Silmaril.Formats.Relational.NamedTable
open Silmaril.Formats.Parquet.Plain.ByteArray

private def field : Field := ⟨"blob", true⟩
private def otherField : Field := ⟨"other", true⟩
private def required : Field := ⟨"blob", false⟩

private def initial : Binary.Database String :=
  let old := observation ⟨"prior", true⟩ [some [42], none, some []]
  Function.update (fun _ => none) "existing" (some ⟨old.schema, old.rows⟩)

private def tableRows (value : Observation) : List (List Slot) :=
  value.rows.map fun row => List.ofFn fun i => row i

private def atName (db : Binary.Database String) (name : String) :
    Option (List (String × Bool) × List (List Slot)) :=
  (Scan.observePacked db name).map fun entry => (List.ofFn entry.schema.kind, tableRows entry)

private def keys (db : Binary.Database String) :=
  ["existing", "dest", "unrelated"].map (atName db)

private def checkAbort {Error : Type} (db : Binary.Database String)
    (result : Except Error (Binary.Database String)) : IO Unit := do
  unless keys (result.toOption.getD db) == keys db do
    throw (IO.userError "failure changed the existing database")

private def bytes (path : String) : IO Bytes := do
  return ⟨← IO.FS.readBinFile path⟩

private def ipc (path : String) : IO KBytes := do
  let input ← IO.FS.readBinFile path
  return KBytes.ofChunks 1 input.size (input.data.toList.map UInt8.toNat)

private def expectedRows : List Slot :=
  [none, some [], some [255, 0], some "123456789012".toUTF8.data.toList,
    some "1234567890123".toUTF8.data.toList, none, some [0],
    some [108, 111, 110, 103, 0, 111, 112, 97, 113, 117, 101, 254, 118, 97, 108, 117, 101]]

public def main (args : List String) : IO Unit := do
  let [source, bad, wire, reordered, utf8] := args
    | throw (IO.userError "expected Parquet sources and three IPC fixtures")
  let source ← bytes source
  let bad ← bytes bad
  let wire ← ipc wire
  let reordered ← ipc reordered
  let utf8 ← ipc utf8
  let parquet := Binary.importParquet initial "dest" field field {} source
  let arrow := Binary.importIpc initial "dest" field {} {} wire
  let .ok parquetDb := parquet | throw (IO.userError "valid projected Parquet failed")
  let .ok ipcDb := arrow | throw (IO.userError "valid BinaryView IPC failed")
  unless keys parquetDb == keys ipcDb &&
      atName parquetDb "dest" == some ([("blob", true)], expectedRows.map (· :: [])) &&
      atName parquetDb "existing" == some ([("prior", true)], [[some [42]], [none], [some []]]) &&
      atName parquetDb "unrelated" == none do
    throw (IO.userError "wrong cross-format rows or more than one key changed")
  let .ok orderDb := Binary.importIpc initial "dest" field {} {} reordered
    | throw (IO.userError "reordered IPC should still import")
  let expectedReordered := expectedRows.drop 2 ++ expectedRows.take 2
  unless atName orderDb "dest" == some ([("blob", true)], expectedReordered.map (· :: [])) &&
      atName orderDb "dest" != atName parquetDb "dest" do
    throw (IO.userError "reordering batches failed to change row order")

  for input in [source, bad] do
    let repeated := Binary.importParquet parquetDb "dest" field field {} input
    let .error .nameConflict := repeated | throw (IO.userError "Parquet bypassed the occupied name gate")
    checkAbort parquetDb repeated
  for input in [wire, KBytes.empty] do
    let repeated := Binary.importIpc ipcDb "dest" field {} {} input
    let .error .nameConflict := repeated | throw (IO.userError "IPC bypassed the occupied name gate")
    checkAbort ipcDb repeated

  let opened := Binary.importParquet initial "dest" field otherField {} source
  let .error (.openError (.schema (.unknownLeaf "other"))) := opened
    | throw (IO.userError "wrong Parquet open error")
  checkAbort initial opened
  let mismatch := Binary.importParquet initial "dest" required field {} source
  let .error .schemaMismatch := mismatch | throw (IO.userError "wrong Parquet descriptor error")
  checkAbort initial mismatch
  let late := Binary.importParquet initial "dest" field field {} bad
  let .error (.readError (.column (.page 1 1 "blob" 0 136 (.decode (.scalar (.plain .integerOverflow)))))) := late
    | throw (IO.userError "wrong Parquet indexed read error")
  checkAbort initial late
  let .ok completed := Binary.collectParquet {} bad field | throw (IO.userError "lost completed Parquet prefix")
  unless tableRows completed.table == (expectedRows.take 4).map (· :: []) do
    throw (IO.userError "wrong ordered prefix")
  let closed := importCollected initial "dest" field.schema
    (.ok ⟨completed.table, .closed⟩ : Except String (Arrow.Events.Observation String Cell String))
  let .error .closed := closed | throw (IO.userError "early close passed the gate")
  checkAbort initial closed
  let closeFailed := importCollected initial "dest" field.schema (.ok ⟨completed.table, .closeError "close"⟩)
  let .error (.closeError "close") := closeFailed | throw (IO.userError "close cause changed")
  checkAbort initial closeFailed

  let missingSchema := Binary.importIpc initial "dest" field {} {} KBytes.empty
  let .error (.openError (.reader (.schemaEnvelope (.malformed .truncated)))) := missingSchema
    | throw (IO.userError "wrong IPC open error")
  checkAbort initial missingSchema
  let missingEos := Binary.importIpc initial "dest" field {} {} (wire.slice 0 (wire.len - 8))
  let .error (.readError (.reader (.batch 3 (.envelope (.malformed .truncated))))) := missingEos
    | throw (IO.userError "wrong original IPC batch error")
  checkAbort initial missingEos
  for expected in [otherField, required] do
    let rejected := Binary.importIpc initial "dest" expected {} {} wire
    let .error .schemaMismatch := rejected | throw (IO.userError "wrong IPC descriptor error")
    checkAbort initial rejected
  let wrongKind := Binary.importIpc initial "dest" field {} {} utf8
  let .error (.openError .utf8View) := wrongKind | throw (IO.userError "Utf8View entered the binary profile")
  checkAbort initial wrongKind
  IO.println "Lean: matching imports, reordered IPC, four occupied-name and ten other failure controls"
