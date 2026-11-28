module

import Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc.Defs
meta import Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Plain.ByteArray
open Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc
open Silmaril.Formats.Arrow.BinaryView

private def load (directory : System.FilePath) (file : String) : IO Bytes := do
  return ⟨← IO.FS.readBinFile (directory / file)⟩

private def octets (batches : List (List (Option KBytes))) : List (List (Option (List UInt8))) :=
  batches.map (List.map (Option.map KBytes.toList))

private def emit (directory : System.FilePath) (parquet destination name : String)
    (layout : FlatColumn.Layout) (sizes : List Nat) : IO Unit := do
  let input ← load directory parquet
  let .ok source := readSource {} input name layout
    | throw (IO.userError s!"source rejected {parquet}")
  let .ok wire := convert {} {} {} input name layout
    | throw (IO.userError s!"native writer rejected {parquet}")
  let .ok ⟨⟨label, nullable, .binary⟩, batches⟩ := Stream.read {} {} wire
    | throw (IO.userError s!"checked stream reader rejected {destination}")
  unless label == name && nullable == (layout == .optional) &&
      batches.map List.length == sizes && octets batches == octets source.batches do
    throw (IO.userError s!"invalid native descriptor, batch shape or ordered octets for {destination}")
  IO.FS.writeBinFile (directory / destination) wire.toByteArray

public def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected the fixture directory")
  let directory := System.FilePath.mk path
  emit directory "selected.parquet" "optional-v2.arrows" "blob" .optional [4, 4]
  emit directory "plain-byte-array-v1.parquet" "required-v1.arrows" "key" .required [12, 12, 12]
  emit directory "schema-only.parquet" "schema-only.arrows" "blob" .optional []
  emit directory "framed-zero-row-group.parquet" "empty-batch.arrows" "blob" .optional [0]

  let input ← load directory "selected.parquet"
  let .ok checked := File.openFile {} input "blob" .optional
    | throw (IO.userError "selected source failed admission")
  unless checked.binding.columnOrdinal == 1 do
    throw (IO.userError "selected wrong original column")
  let .error (.source (.openError (.schema (.unknownLeaf "other")))) :=
    convert {} {} {} input "other" .optional
    | throw (IO.userError "wrong source unknown-field error")
  let .error (.source (.openError (.schema (.leafMismatch 1 _)))) := convert {} {} {} input "blob" .required
    | throw (IO.userError "wrong source layout error")
  let .error (.source (.openError (.fileByteLimit 4 504))) :=
    convert { maxFileBytes := 4 } {} {} input "blob" .optional
    | throw (IO.userError "wrong Parquet byte limit")
  let .error (.writer (.record 1 (.column .valueLimit))) :=
    convert {} {} { valueBytes := 12 } input "blob" .optional
    | throw (IO.userError "wrong native value limit error or record index")
  let .error (.writer (.ipc (.limit .batches))) :=
    convert {} { batches := 1 } {} input "blob" .optional
    | throw (IO.userError "wrong native IPC batch limit")
  let late ← load directory "late-length-error.parquet"
  let reason := FlatColumn.Error.page 1 1 "blob" 0 136 (.decode (.scalar (.plain .integerOverflow)))
  let .error (.source (.readError cause)) := convert {} {} {} late "blob" .optional
    | throw (IO.userError "late source failure returned native wire")
  unless cause == reason do throw (IO.userError "wrong original late source cause")
  let .error (.source (.readError limitedCause)) := convert {} { batches := 0 } {} late "blob" .optional
    | throw (IO.userError "writer limits obscured the source error")
  unless limitedCause == reason do throw (IO.userError "source cause changed under stricter writer limits")
  let .ok ⟨_, trace⟩ := File.readAll {} late "blob" .optional
    | throw (IO.userError "late source failure lost the opened trace")
  unless trace.batches.map (·.rowCount) == [4] && trace.termination == .readError (.column reason) do
    throw (IO.userError "late source events lost the completed prefix")
  let .error (.source (.openError (.snapshot (.invalidMetadata .pageInterval)))) :=
    convert {} {} {} (← load directory "zero-row-group.parquet") "blob" .optional
    | throw (IO.userError "wrong exact rejection for zero page offsets")
  IO.println "Lean: four native streams, eight exact failure controls and the original Parquet prefix"
