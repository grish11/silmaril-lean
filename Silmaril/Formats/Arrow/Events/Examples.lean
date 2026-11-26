module

import Silmaril.Formats.Arrow.Events.Thms

/-! Kernel-checked examples for rechunking and the reader's outcome policy. -/

namespace Silmaril.Formats.Arrow.Events

open Silmaril.Relational

private abbrev Value (_ : Unit) := Nat

private def schema : Scan.Schema Nat Unit := ⟨2, fun i => (i.val, ())⟩

private def row (key payload : Option Nat) : Scan.Row schema Value :=
  fun i => if i.val = 0 then key else payload

private def duplicate : Scan.Row schema Value := row (some 4) none
private def unknown : Scan.Row schema Value := row none (some 9)
private def rejected : Scan.Row schema Value := row (some 2) (some 0)

private def manyBatches : Trace schema Value Nat :=
  ⟨[AlignedColumns.ofRows [duplicate, unknown], AlignedColumns.ofRows [],
    AlignedColumns.ofRows [rejected, duplicate]], .readError 7⟩

private def oneBatch : Trace schema Value Nat :=
  ⟨[AlignedColumns.ofRows [duplicate, unknown, rejected, duplicate]], .readError 7⟩

private def predicate : Scan.Predicate schema Value := fun r =>
  (r (0 : Fin 2)).map (fun key => key == 4)

private def projection : Scan.Projection schema :=
  Scan.Projection.ofArray (#[1, 0, 1] : Array (Fin 2))

private def emptyProjection : Scan.Projection schema := Scan.Projection.ofArray #[]

example : EventStream.Equivalent (.ok ⟨schema, manyBatches⟩) (.ok ⟨schema, oneBatch⟩) :=
  EventStream.equivalent_open_iff.mpr ⟨rfl, rfl⟩

example : EventStream.Equivalent (.ok ⟨projection.schema, manyBatches.scan projection predicate⟩)
    (.ok ⟨projection.schema, oneBatch.scan projection predicate⟩) :=
  EventStream.scan_rechunk projection predicate rfl rfl

example : (manyBatches.scan projection predicate).rows.map
    (fun r => (r (0 : Fin 3), r (1 : Fin 3), r (2 : Fin 3))) =
      [(none, some 4, none), (none, some 4, none)] := rfl

example : (manyBatches.scan emptyProjection predicate).collect.table.rowCount = 2 := rfl

example : (manyBatches.scan emptyProjection predicate).batches.map AlignedColumns.rowCount =
    [1, 0, 1] := rfl

private abbrev Cursor (s : Scan.Schema Nat Unit) := List (Batch s Value) × Bool

private def reader : BatchReader (Option Bool) Nat Value Nat Cursor where
  openInput
    | none => .error 7
    | some fail => .ok ⟨schema, ([AlignedColumns.ofRows [duplicate]], fail)⟩
  next
    | (batch :: batches, fail) => .ok (some (batch, (batches, fail)))
    | ([], fail) => if fail then .error 7 else .ok none
  close cursor := if cursor.1.isEmpty then .error 7 else .ok ()

example : (reader.read 2 none).collect = .error 7 := rfl

example : (reader.read 2 (some false)).collect = .ok ⟨⟨schema, [duplicate]⟩, .eos⟩ := rfl

example : (reader.read 2 (some true)).collect = .ok ⟨⟨schema, [duplicate]⟩, .readError 7⟩ := rfl

example : (reader.read 1 (some true)).collect = .ok ⟨⟨schema, [duplicate]⟩, .closeError 7⟩ := rfl

example : (reader.read 0 (some true)).collect = .ok ⟨⟨schema, []⟩, .closed⟩ := rfl

example : ¬ EventStream.Equivalent (reader.read 2 none) (reader.read 2 (some true)) := by
  intro equal
  nomatch equal

example : ¬ EventStream.Equivalent (reader.read 1 (some true)) (reader.read 2 (some true)) := by
  intro equal
  have termination : Termination.closeError 7 = .readError 7 :=
    congrArg Observation.termination (Except.ok.inj equal)
  nomatch termination

example : ¬ EventStream.Equivalent (.ok ⟨schema, oneBatch⟩)
    (.ok ⟨schema, { oneBatch with termination := .readError 8 }⟩) := by
  intro equal
  have termination : Termination.readError 7 = .readError 8 :=
    (EventStream.equivalent_open_iff.mp equal).2
  nomatch termination

end Silmaril.Formats.Arrow.Events
