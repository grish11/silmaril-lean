module

import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Defs
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc.Defs
meta import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Defs
meta import Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Int32ByteArrayGroup
open Silmaril.Formats.Relational.NamedTable

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
  IO.println "Three native round trips and three reverse-side or returned-carrier cap controls."
