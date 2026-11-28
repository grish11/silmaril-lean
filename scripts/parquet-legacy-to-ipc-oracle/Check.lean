module

import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc.Defs
meta import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Int32ByteArrayGroup
open Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc

private def load (directory : System.FilePath) (name : String) : IO Bytes := do
  return ⟨← IO.FS.readBinFile (directory / (name ++ ".parquet"))⟩

private def emit (directory : System.FilePath) (name : String) (ipc : Arrow.MixedFlat.Limits) :
    IO (Except Legacy.ToIpc.Error Unit) := do
  let input ← load directory name
  match convert {} ipc input "ordinal" "payload" with
  | .error cause => return .error cause
  | .ok wire =>
    let .ok decoded := Arrow.MixedFlat.Stream.read ipc wire |
      throw (IO.userError s!"native mixed IPC reader rejected {name}")
    unless decoded.fields == (writerSchema "ordinal" "payload").fields &&
        decoded.batches.map (·.observed.rowCount) == [384, 0, 384] do
      throw (IO.userError "wrong native schema or batch boundaries")
    IO.FS.writeBinFile (directory / (name ++ ".arrows")) wire.toByteArray
    return .ok ()

public def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected the fixture directory")
  let directory := System.FilePath.mk path
  for name in ["original", "opaque"] do
    let .ok () ← emit directory name {} |
      throw (IO.userError s!"paired conversion rejected {name}")

  let writerRefusal : Arrow.MixedFlat.Limits := { observation := { totalRows := 0 } }
  let .error (.source (.byteArray (.page 2 1 "payload" 19 21009
      (.decode (.plain (.plain .integerOverflow)))))) ← emit directory "damaged" writerRefusal |
    throw (IO.userError "wrong original late source error or source/writer precedence")
  let damaged ← load directory "damaged"
  let .error (.source (.openFailure (.fileRowLimit 767 768))) :=
    convert { file := { maxFileRows := 767 } } writerRefusal damaged "ordinal" "payload" |
    throw (IO.userError "wrong checked footer row cap")
  let clean ← load directory "original"
  let .error (.writer (.budget 0 (.limit .totalRows))) :=
    convert {} writerRefusal clean "ordinal" "payload" |
    throw (IO.userError "writer budget should fail after a successful source")
  IO.println "Lean checked two native streams, source-cap precedence, the original late typed error, and the writer cap"
