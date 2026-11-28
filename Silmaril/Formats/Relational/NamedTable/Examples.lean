module

import Silmaril.Formats.Relational.NamedTable.Thms

/-! Kernel-checked named loads and typed exports, including failure after output. -/

namespace Silmaril.Formats.Relational.NamedTable

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet

private abbrev Value : Bool → Type
  | false => Nat
  | true => String

private def schema : Scan.Schema Nat Bool := ⟨2, Fin.cases (7, false) (fun _ => (8, true))⟩

private def wrongSchema : Scan.Schema Nat Bool := ⟨2, Fin.cases (8, false) (fun _ => (7, true))⟩

private def row (key : Option Nat) (text : Option String) : Scan.Row schema Value :=
  Fin.cases (motive := fun i => Option (Value (schema.kind i).2)) key (fun _ => text)

private def first : Scan.Row schema Value := row (some 4) none
private def second : Scan.Row schema Value := row none (some "")

private def db : Packed String Nat Value := fun name =>
  if name = "keep" then some ⟨schema, [second]⟩ else none

private def stream (termination : Events.Termination Nat) : Events.EventStream Nat Value Nat :=
  .ok ⟨schema, ⟨[AlignedColumns.ofRows [first], AlignedColumns.ofRows [second, first]], termination⟩⟩

example : (importArrow db "load" schema (stream .eos)).map
    (fun loaded => (Scan.observePacked loaded "load", Scan.observePacked loaded "keep")) =
      .ok (some ⟨schema, [first, second, first]⟩, some ⟨schema, [second]⟩) := rfl

example : (importArrowDependent db.unpack "load" schema (stream .eos)).map
    (fun loaded => Scan.observeDependent loaded "load") =
      .ok (some ⟨schema, [first, second, first]⟩) := rfl

example : importArrow db "keep" schema (stream .eos) = .error .nameConflict := rfl

example : importArrow db "load" wrongSchema (stream .eos) = .error .schemaMismatch := rfl

example : importArrow db "load" schema (stream (.readError 17)) = .error (.readError 17) := rfl

example : importArrow db "load" schema (stream .closed) = .error .closed := rfl

example : importArrow db "load" schema (stream (.closeError 17)) = .error (.closeError 17) := rfl

example : importArrow db "load" schema (.error 17) = .error (.openError 17) := rfl

private def parquet (fail : Bool) : Reader.OpenResult Nat Nat Value Nat :=
  .ok ⟨schema, ⟨[0, 1], fun group =>
    if group = 0 then .ok [first]
    else if fail then .error 17 else .ok [second, first], fun _ => .ok ()⟩⟩

example : (importParquet db "load" schema (parquet false)).map
    (fun loaded => Scan.observePacked loaded "load") = .ok (some ⟨schema, [first, second, first]⟩) := rfl

example : (Reader.readAll (parquet true)).collect = .ok ⟨⟨schema, [first]⟩, .readError 17⟩ := rfl

example : importParquet db "load" schema (parquet true) = .error (.readError 17) := rfl

example : exportArrow db "load" [] = .error .missingName := rfl

example : exportArrow db "keep" [2] = .error (.rowCountMismatch 2 1) := rfl

example : (importArrow db "load" schema (exportArrow db "keep" [0, 1])).map
    (fun loaded => Scan.observePacked loaded "load") = .ok (some ⟨schema, [second]⟩) := rfl

private def emptySchema : Scan.Schema Nat Bool := ⟨0, Fin.elim0⟩

private def emptyRow : Scan.Row emptySchema Value := fun i => Fin.elim0 i

private def zeroDb : Packed String Nat Value := fun name =>
  if name = "zero" then some ⟨emptySchema, [emptyRow, emptyRow, emptyRow]⟩ else none

example : (exportArrow zeroDb "zero" [1, 0, 2]).map
    (fun entry => entry.snd.batches.map AlignedColumns.rowCount) = .ok [1, 0, 2] := rfl

example : (Events.EventStream.collect ((exportParquet zeroDb "zero" [1, 0, 2]).bind
      (fun ⟨s, source⟩ => Reader.readAll (.ok ⟨s, source⟩)))).map
    (fun observation => (observation.table.schema.width, observation.table.rowCount)) = .ok (0, 3) := rfl

end Silmaril.Formats.Relational.NamedTable
