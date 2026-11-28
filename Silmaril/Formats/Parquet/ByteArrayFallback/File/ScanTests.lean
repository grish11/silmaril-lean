module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.ByteArrayFallback.File.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.ByteArrayFallback.File.Defs

namespace Silmaril.Formats.Parquet.ByteArrayFallback.File

open Silmaril.Formats.Arrow Silmaril.Relational

private def clean : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-byte-array-legacy-events/legacy-v1-empty-middle.parquet"⟩
private def damaged : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-byte-array-legacy-events/legacy-v1-late-error.parquet"⟩

private abbrev SelectedSchema := Scan.Schema String FlatColumn.Layout
private abbrev Project := (selected : SelectedSchema) → Scan.Projection selected
private abbrev Keep := (selected : SelectedSchema) → Scan.Predicate selected Value

private def zeroColumns : Project := fun _ => ⟨0, Fin.elim0⟩

private def longValues : Keep := fun selected row =>
  if column : 0 < selected.width then
    (row ⟨0, column⟩).map fun value => value.length > 8
  else none

private def keepAll : Keep := fun _ _ => some true
private def allUnknown : Keep := fun _ _ => none

private def verify (input : Bytes) (project : Project) (keep : Keep)
    (fields : List (String × FlatColumn.Layout)) (expected : List (List (List (Option Bytes))))
    (outcome : Events.Termination Error) : IO Unit := do
  let .ok ⟨selected, trace⟩ := (readAllLegacy {} input "payload").scan project keep |
    throw (IO.userError "checked legacy scan failed to open")
  unless List.ofFn selected.kind == fields do throw (IO.userError "wrong projection schema")
  let observed := trace.batches.map fun batch =>
    batch.toRows.map fun row => List.ofFn fun column => row column
  unless observed == expected && trace.batches.map (·.rowCount) == expected.map List.length do
    throw (IO.userError "wrong projected slots or original group boundaries")
  unless trace.termination == outcome do throw (IO.userError "wrong EOS or original indexed cause")

#eval do
  let failure : Events.Termination Error :=
    .readError (.readFailure (.page 2 1 "payload" 19 21009 (.decode (.plain (.plain .integerOverflow)))))
  let .ok checked := ByteArrayFallback.openFile {} clean "payload" |
    throw (IO.userError "fixture rejected at open")
  let .ok original := ByteArrayFallback.readLegacyGroup checked {} 0 |
    throw (IO.userError "expected the original first group")
  let kept := original.filter fun (slot : Option Bytes) => slot.any (fun (value : Bytes) => value.length > 8)
  unless original.length == 384 && kept.length == 118 do
    throw (IO.userError "unexpected fixture row counts")

  let zeros := List.replicate 384 []
  verify clean zeroColumns keepAll [] [zeros, [], zeros] .eos
  verify damaged zeroColumns keepAll [] [zeros, []] failure

  let selected := kept.map fun value => [value]
  verify clean Scan.Projection.id longValues [("payload", .optional)] [selected, [], selected] .eos
  verify damaged Scan.Projection.id longValues [("payload", .optional)] [selected, []] failure

  let keptZeros := List.replicate 118 []
  verify clean zeroColumns longValues [] [keptZeros, [], keptZeros] .eos
  verify damaged zeroColumns longValues [] [keptZeros, []] failure
  verify damaged zeroColumns allUnknown [] [[], []] failure
  IO.println "Legacy scan: [384, 0, 384] and [118, 0, 118] at EOS. Damage retains the original indexed error after [384, 0], [118, 0], or [0, 0]."

end Silmaril.Formats.Parquet.ByteArrayFallback.File
