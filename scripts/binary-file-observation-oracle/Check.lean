module

import Silmaril.Formats.Relational.BinaryObservation.ParquetFile.Thms
meta import Silmaril.Formats.Parquet.Plain.ByteArray.File.Defs
meta import Silmaril.Formats.Relational.BinaryObservation.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Relational.BinaryObservation
open Silmaril.Formats.Parquet.Plain.ByteArray

private def field : Field := ⟨"blob", true⟩

private def readParquet (path : String) : IO Bytes := do
  return ⟨← IO.FS.readBinFile path⟩

private def readIpc (path : String) : IO KBytes := do
  let bytes ← IO.FS.readBinFile path
  return KBytes.ofChunks 1 bytes.size (bytes.data.toList.map UInt8.toNat)

private def octetRows (observation : Observation) : List (List Slot) :=
  observation.rows.map fun row =>
    List.ofFn fun index : Fin observation.schema.width => (row index : Slot)

public def main (args : List String) : IO Unit := do
  let [valid, damaged, reference] := args
    | throw (IO.userError "expected valid Parquet, damaged Parquet and BinaryView IPC")
  let parquet ← readParquet valid
  let corrupt ← readParquet damaged
  let ipc ← readIpc reference
  let .ok checked := File.openFile {} parquet "blob" .optional
    | throw (IO.userError "optional BYTE_ARRAY leaf rejected")
  unless checked.binding.columnOrdinal == 1 && checked.binding.leafOrdinal == 2 do
    throw (IO.userError "wrong projected leaf")
  let .ok group0 := checked.readGroup {} 0 | throw (IO.userError "group 0 rejected")
  let .ok group1 := checked.readGroup {} 1 | throw (IO.userError "group 1 rejected")
  unless [group0.length, group1.length] == [4, 4] do
    throw (IO.userError "wrong ordered Parquet boundaries")
  let .ok observed := observeIpc field {} {} ipc | throw (IO.userError "BinaryView IPC rejected")
  let .ok ⟨⟨"blob", true, .binary⟩, batches⟩ := Arrow.BinaryView.Stream.read {} {} ipc
    | throw (IO.userError "could not check IPC batch boundaries")
  unless batches.map List.length == [2, 0, 6] do
    throw (IO.userError "wrong ordered IPC boundaries")
  let expected := observation field ((group0 ++ group1).map (Option.map Bytes.toList))
  unless List.ofFn observed.schema.kind == [("blob", true)] &&
      octetRows observed == octetRows expected do
    throw (IO.userError "selected Parquet descriptor or raw nullable bytes differ")

  let .ok ⟨schema, trace⟩ := File.readAll {} parquet "blob" .optional
    | throw (IO.userError "full event source rejected")
  let .eos := trace.termination | throw (IO.userError "full source did not reach EOS")
  let fromEvents := trace.rows.map fun row =>
    List.ofFn fun i : Fin schema.width => (row i : Option Bytes).map Bytes.toList
  unless trace.batches.map (·.rowCount) == [4, 4] && fromEvents == octetRows observed do
    throw (IO.userError "file trace and successful IPC observation differ")

  let .ok late := File.openFile {} corrupt "blob" .optional
    | throw (IO.userError "late-body control should open")
  let .ok earlier := late.readGroup {} 0 | throw (IO.userError "good prefix was lost")
  unless (earlier.map (Option.map Bytes.toList)) == (group0.map (Option.map Bytes.toList)) do
    throw (IO.userError "file prefix rows differ")
  let .error (.page 1 1 "blob" 0 136 (.decode (.scalar (.plain .integerOverflow)))) :=
    late.readGroup {} 1
    | throw (IO.userError "wrong original group, column, page, offset or cause")
  let .ok ⟨schema, trace⟩ := File.readAll {} corrupt "blob" .optional
    | throw (IO.userError "event source lost the good prefix")
  let .readError (.column (.page 1 1 "blob" 0 136 (.decode (.scalar (.plain .integerOverflow))))) :=
    trace.termination
    | throw (IO.userError "event source changed the original terminal error")
  let eventPrefix := trace.rows.map fun row =>
    List.ofFn fun i : Fin schema.width => (row i : Option Bytes).map Bytes.toList
  unless trace.batches.map (·.rowCount) == [4] &&
      eventPrefix == (group0.map fun slot => [slot.map Bytes.toList]) do
    throw (IO.userError "late event source changed the good prefix")
  let .error (.schema (.unknownLeaf "other")) := File.readAll {} parquet "other" .optional
    | throw (IO.userError "wrong open error for unknown projected field")
  let .error (.schema (.leafMismatch 1 _)) := File.readAll {} parquet "blob" .required
    | throw (IO.userError "wrong open error for Parquet nullability mismatch")
  let .error (.fieldMismatch ⟨"blob", true⟩) := observeIpc ⟨"blob", false⟩ {} {} ipc
    | throw (IO.userError "wrong error for IPC nullability mismatch")
  let .error (.fieldMismatch ⟨"blob", true⟩) := observeIpc ⟨"other", true⟩ {} {} ipc
    | throw (IO.userError "wrong error for IPC name mismatch")
  let .error (.reader (.batch 3 (.envelope (.malformed .truncated)))) :=
    observeIpc field {} {} (ipc.slice 0 (ipc.len - 8))
    | throw (IO.userError "wrong indexed error for missing IPC EOS")
  IO.println "Lean: one shared observation, six exact error controls, and the retained Parquet prefix"
