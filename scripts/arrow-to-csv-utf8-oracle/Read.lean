module

import Silmaril.Formats.Arrow.ToCsv.Utf8.Defs
meta import Silmaril.Formats.Arrow.ToCsv.Utf8.Defs
import Silmaril.Formats.Arrow.FromCsv.Stream.Defs
meta import Silmaril.Formats.Arrow.FromCsv.Stream.Defs

open Silmaril Silmaril.Relational Silmaril.Formats Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.ToCsv (Cell schemaOf)
open Silmaril.Formats.Relational.NamedTable (Packed schemaMatches)

private def fields : List Field := [⟨"n", true, .int32⟩, ⟨"téxt", true, .utf8⟩]

private def db : Packed String Csv.Field Cell := fun name =>
  if name = "keep" then some ⟨schemaOf fields, []⟩ else none

public def main (args : List String) : IO Unit := do
  let [source, target, roundTrip] := args
    | throw (IO.userError "usage: Read.lean INPUT.arrows OUTPUT.csv ROUND-TRIP.arrows")
  let bytes ← IO.FS.readBinFile source
  let ipc := KBytes.ofChunks 1 bytes.size (bytes.data.toList.map UInt8.toNat)
  let .ok (loaded, schema, csv) := ToCsv.Utf8.convert db "fixture" (schemaOf fields) {} ipc
    | throw (IO.userError "IPC to named UTF-8 CSV conversion failed")
  let some table := Scan.observePacked loaded "fixture"
    | throw (IO.userError "missing named table")
  unless schemaMatches (schemaOf fields) schema && table.rowCount == 6 do
    throw (IO.userError "unexpected schema or row count")
  unless (Scan.observePacked loaded "keep").map Scan.Observation.rowCount == some 0 do
    throw (IO.userError "the unrelated table changed")
  let .error (.input (.openError (.ipc (.malformed .truncated)))) :=
      ToCsv.Utf8.convert db "fixture" (schemaOf fields) {} (ipc.slice 0 (ipc.len - 1))
    | throw (IO.userError "late truncation did not return the original read error")
  let .ok emitted := FromCsv.Stream.emitCsvUtf8 {} fields csv
    | throw (IO.userError "UTF-8 CSV to IPC emission failed")
  IO.FS.writeBinFile target csv.toByteArray
  IO.FS.writeBinFile roundTrip ⟨emitted.toList.toArray⟩
  IO.println s!"IPC bytes={bytes.size}, named rows={table.rowCount}, UTF-8 CSV bytes={csv.length}"
