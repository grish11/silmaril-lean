module

import Silmaril.Formats.Relational.NamedTable.MixedIpc.FromParquet.Defs
import Silmaril.Formats.Relational.NamedTable.MixedIpc.Export.Defs
meta import Silmaril.Formats.Relational.NamedTable.MixedIpc.FromParquet.Defs
meta import Silmaril.Formats.Relational.NamedTable.MixedIpc.Export.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet.Int32ByteArrayGroup
open Silmaril.Formats.Relational.NamedTable.MixedIpc
open Silmaril.Formats.Relational.NamedTable.MixedIpc.FromParquet

private def empty : Database String := fun _ => none

private def compare (directory : System.FilePath) (file ipcFile : String) (integer binary : Field)
    (groups batches : List Nat) (agree : Bool) : IO Unit := do
  let input : Bytes := ⟨← IO.FS.readBinFile (directory / (file ++ ".parquet"))⟩
  let bytes ← IO.FS.readBinFile (directory / (ipcFile ++ ".arrows"))
  let direct := KBytes.ofChunks 1 bytes.size (bytes.data.toList.map UInt8.toNat)
  let expected := descriptor integer binary
  let .ok bridge := ToIpc.convert {} {} input integer binary
    | throw (IO.userError s!"{file}: checked conversion failed")
  let .ok original := read { inputBytes := bridge.len } bridge
    | throw (IO.userError s!"{file}: checked intermediate IPC read failed")
  let .ok supplied := read { inputBytes := direct.len } direct
    | throw (IO.userError s!"{ipcFile}: checked direct IPC read failed")
  unless original.descriptor == expected && supplied.descriptor == expected &&
      original.batches.map List.length == groups && supplied.batches.map List.length == batches do
    throw (IO.userError s!"{ipcFile}: incorrect checked descriptors or boundaries")

  let .ok viaParquet :=
    importNamed empty "table" {} { inputBytes := bridge.len } input integer binary
    | throw (IO.userError s!"{file}: Parquet insertion failed")
  let .ok viaIpc := importIpc empty "table" expected { inputBytes := direct.len } direct
    | throw (IO.userError s!"{ipcFile}: IPC insertion failed")
  let .ok [first] := Export.prepare viaParquet "table" expected [groups.sum]
    | throw (IO.userError s!"{file}: cannot observe the inserted Parquet table")
  let .ok [second] := Export.prepare viaIpc "table" expected [batches.sum]
    | throw (IO.userError s!"{ipcFile}: cannot observe the inserted IPC table")
  unless first == original.batches.flatten && second == supplied.batches.flatten &&
      (first == second) == agree do
    throw (IO.userError s!"{ipcFile}: wrong ordered-table comparison")

  if ipcFile == "coalesced" then
    unless bridge.len > direct.len do
      throw (IO.userError "coalescing did not produce the intended cap asymmetry")
    let .error (.ipcImport (.openError (.inputBytes actual cap))) :=
      importNamed empty "table" {} { inputBytes := direct.len } input integer binary
      | throw (IO.userError "the direct IPC cap unexpectedly admitted the larger intermediate")
    unless actual == bridge.len && cap == direct.len do
      throw (IO.userError "the intermediate IPC cap error lost its actual lengths")

public def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected the fixture directory")
  let dir := System.FilePath.mk path
  let ordinal : Field := ⟨"ordinal", .required⟩
  let optional : Field := ⟨"ordinal", .optional⟩
  let payload : Field := ⟨"payload", .optional⟩
  let key : Field := ⟨"key", .required⟩
  compare dir "empty-middle-v2" "coalesced" ordinal payload [3, 0, 2] [5] true
  compare dir "nullable-int32-v2" "resplit" optional key [3, 2] [0, 1, 4] true
  compare dir "mixed-schema-only" "explicit-empty" optional key [] [0] true
  compare dir "empty-middle-v2" "reordered" ordinal payload [3, 0, 2] [5] false
  compare dir "empty-middle-v2" "null-to-empty" ordinal payload [3, 0, 2] [5] false
  IO.println "Three equal inserts, two distinct inserts, and one IPC carrier-cap asymmetry."
