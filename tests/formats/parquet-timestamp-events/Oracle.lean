module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.Defs
meta import Silmaril.Formats.ColumnarTimestamp.Defs
meta import Silmaril.Numeric.Timestamp.Defs

open Silmaril.Formats Silmaril.Formats.Parquet.Timestamp.Leaf.Events
open Silmaril.Numeric.Timestamp

private def check (passed : Bool) (label : String) : IO Unit :=
  unless passed do throw (IO.userError label)

private def checkTrace (label name : String) (unit : TickUnit) (timezone : Option String)
    (nullable : Bool) (expected : List (List (Option Int))) (outcome : Arrow.Events.Termination Error)
    (result : Arrow.Events.EventStream String Cell Error) : IO Unit := do
  match result with
  | .error cause => throw (IO.userError s!"{label}: unexpected {repr cause}")
  | .ok ⟨schema, trace⟩ =>
    if one : schema.width = 1 then
      let field : Fin schema.width := ⟨0, by omega⟩
      let (actualName, kind) := schema.kind field
      check (actualName == name && kind.nullable == nullable &&
        kind.metadata.unit == unit && kind.metadata.timezone == timezone) s!"{label}: schema"
      let adjusted := match kind.metadata.kind with
        | .utcInstant => true
        | .localReading => false
      check (adjusted == timezone.isSome) s!"{label}: epoch kind"
      check (trace.batches.map (fun batch => batch.rowCount) == expected.map List.length)
        s!"{label}: group order and sizes"
      check (trace.batches.map (fun batch => (batch.values field).map (Option.map Ticks.ticks)) ==
        expected) s!"{label}: nullable signed counts"
      check (trace.collect.table.rows.map (fun row => (row field).map Ticks.ticks) == expected.flatten)
        s!"{label}: collected rows"
      check (decide (trace.termination = outcome)) s!"{label}: termination"
    else throw (IO.userError s!"{label}: schema width {schema.width}")

private def checkFixture (path name : String) (unit : TickUnit) (timezone : Option String)
    (nullable : Bool) (expected : List (List (Option Int))) : IO Unit := do
  let wire : Bytes := ⟨← IO.FS.readBinFile path⟩
  checkTrace name name unit timezone nullable expected .eos (readAll {} {} 1 wire)

private def checkDamaged (path name : String) (expected : List (List (Option Int))) : IO Unit := do
  let wire : Bytes := ⟨← IO.FS.readBinFile path⟩
  checkTrace "late failure" name .microsecond none true expected
    (.readError (.groupFailure 2 (.page 0 (.scalar (.unsupportedEncoding 8)))))
    (readAll {} {} 1 wire)
  checkTrace "closed prefix" name .microsecond none true expected .closed
    ((batchReader {} {} 1).read 2 wire)
  match readAll {} {} 0 wire with
  | .error (.openFailure (.annotation .notInt64Leaf)) => pure ()
  | _ => throw (IO.userError "expected typed open failure for root selection")
