module

import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Defs
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc.Defs
meta import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Defs
meta import Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Int32ByteArrayGroup
open Silmaril.Formats.Relational.NamedTable
open Silmaril.Formats.Parquet.MixedV1Writer.FromIpc (field)

private def sink : MixedV1Writer.Multi.Limits :=
  ⟨⟨4096, {}, ⟨{}, 32, ⟨128, 128, ⟨16, 32⟩, 0⟩⟩,
    ⟨⟨{}, 32, ⟨128, 128, ⟨16, 32⟩, 0⟩⟩, ⟨128, 32⟩⟩, {}⟩, 8, 16⟩

private def inputIpc (directory : System.FilePath) (name : String) : IO KBytes := do
  let wire ← IO.FS.readBinFile (directory / (name ++ ".arrows"))
  return KBytes.ofChunks 1 wire.size (wire.data.toList.map UInt8.toNat)

private def inputParquet (directory : System.FilePath) (name : String) : IO Bytes := do
  return ⟨← IO.FS.readBinFile (directory / (name ++ ".parquet"))⟩

public def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected the fixture directory")
  let directory := System.FilePath.mk path

  for (name, counts) in [("mixed", [3, 0, 2]), ("required", [2, 1]), ("empty-batch", [0])] do
    let original ← inputIpc directory name
    let file ← inputParquet directory name
    let .ok source := MixedIpc.read {} original | throw (IO.userError s!"{name}: input was refused")
    let integer := MixedV1Writer.FromIpc.field source.descriptor.integer
    let binary := MixedV1Writer.FromIpc.field source.descriptor.binary
    let .ok wire := ToIpc.convert {} {} file integer binary
      | throw (IO.userError s!"{name}: reverse conversion failed")
    let .ok orderedFile := MixedV1Writer.FromIpc.convertOrdered {} sink original
      | throw (IO.userError s!"{name}: ordered forward conversion failed")
    let .ok orderedWire := ToIpc.convertOrdered {} {} file integer binary
      | throw (IO.userError s!"{name}: ordered reverse conversion failed")
    unless orderedFile.bytes == file && orderedWire.toByteArray == wire.toByteArray do
      throw (IO.userError s!"{name}: ordered INT32-first conversion differs from default bytes")
    let .ok returned := MixedIpc.read { inputBytes := wire.len } wire
      | throw (IO.userError s!"{name}: native readback failed")
    unless returned.descriptor == source.descriptor && returned.batches == source.batches &&
        returned.batches.map List.length == counts do
      throw (IO.userError s!"{name}: records or descriptor changed")
    IO.FS.writeBinFile (directory / (name ++ "-returned.arrows")) wire.toByteArray

    if name == "mixed" then
      let .error (.source (.fileRowLimit 4 5)) := ToIpc.convert { maxFileRows := 4 } {} file integer binary
        | throw (IO.userError "reverse aggregate Parquet cap did not retain its typed cause")
      let .error (.writer (.ipc (.limit .batches))) :=
        ToIpc.convert {} { observation := { ipc := { batches := 2 } } } file integer binary
        | throw (IO.userError "reverse writer ignored the empty batch in its count")
      let .error (.inputBytes actual limit) := MixedIpc.read { inputBytes := wire.len - 1 } wire
        | throw (IO.userError "returned IPC cap did not reject the frame")
      unless actual == wire.len && limit == wire.len - 1 do
        throw (IO.userError "returned IPC cap reported the wrong lengths")
  for (name, counts) in [("view-first", [3, 0, 2]), ("view-first-empty", [0])] do
    let original ← inputIpc directory name
    let .ok source := MixedIpc.read {} original
      | throw (IO.userError s!"{name}: input was refused")
    let .ok parquet := MixedV1Writer.FromIpc.convertOrdered {} sink original
      | throw (IO.userError s!"{name}: ordered forward conversion failed")
    let integer := field source.descriptor.integer
    let binary := field source.descriptor.binary
    let .ok wire := ToIpc.convertOrdered {} {} parquet.bytes integer binary
      | throw (IO.userError s!"{name}: ordered reverse conversion failed")
    let .ok returned := MixedIpc.read { inputBytes := wire.len } wire
      | throw (IO.userError s!"{name}: native readback failed")
    unless source.descriptor.viewFirst && returned.descriptor == source.descriptor &&
        returned.batches == source.batches && returned.batches.map List.length == counts do
      throw (IO.userError s!"{name}: order, records or descriptor changed")
    IO.FS.writeBinFile (directory / (name ++ ".parquet")) parquet.bytes.data
    IO.FS.writeBinFile (directory / (name ++ "-returned.arrows")) wire.toByteArray

    if name == "view-first" then
      let .error (.plan .fieldOrder) := MixedV1Writer.FromIpc.convert {} sink original
        | throw (IO.userError "original forward conversion changed its order policy")
      let truncated := original.toByteArray.extract 0 (original.len - 8)
      let missingEos := KBytes.ofChunks 1 truncated.size (truncated.data.toList.map UInt8.toNat)
      let .error (.source (.reader (.batch 3 (.envelope (.malformed .truncated))))) :=
          MixedV1Writer.FromIpc.convertOrdered {} { sink with maxGroups := 0 } missingEos
        | throw (IO.userError "ordered forward conversion lost the exact source error")
      let .error (.sink .groupLimit) :=
          MixedV1Writer.FromIpc.convertOrdered {} { sink with maxGroups := 2 } original
        | throw (IO.userError "ordered forward conversion ignored the empty batch in its count")
      let .error (.source (.fileRowLimit 4 5)) :=
          ToIpc.convertOrdered { maxFileRows := 4 } {} parquet.bytes integer binary
        | throw (IO.userError "ordered reverse conversion lost its source cap")
      let .error (.source (.groupFailure 2
          (.byteArray (.page 2 0 "raw" 0 offset (.decode (.scalar (.plain .valueByteLimit))))))) :=
          ToIpc.convertOrdered { group := { maxValueBytes := 16 } } {} parquet.bytes integer binary
        | throw (IO.userError "ordered reverse conversion lost the late selected BYTE_ARRAY failure")
      unless some offset == (parquet.groups[2]?.map (·.index.octets.span.start)) do
        throw (IO.userError "ordered reverse conversion reported the wrong page offset")
      let .error (.writer (.ipc (.limit .batches))) :=
          ToIpc.convertOrdered {} { observation := { ipc := { batches := 2 } } } parquet.bytes integer binary
        | throw (IO.userError "ordered reverse conversion lost its writer cap")

  let schemaOnly ← inputIpc directory "view-first-schema-only"
  let .error (.plan .noBatches) := MixedV1Writer.FromIpc.convertOrdered {} sink schemaOnly
    | throw (IO.userError "ordered conversion accepted a schema-only stream")
  IO.println "Five native round trips, six default-byte comparisons and ten typed controls."
