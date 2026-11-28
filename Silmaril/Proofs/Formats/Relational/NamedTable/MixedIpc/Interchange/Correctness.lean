module

public import Silmaril.Formats.Relational.NamedTable.MixedIpc.FromParquet.Thms
import Silmaril.Formats.Relational.NamedTable.MixedIpc.Export.Thms
import Silmaril.Formats.Relational.NamedTable.MixedIpc.Thms

public section

namespace Silmaril.Proofs.Formats.Relational.NamedTable.MixedIpc.Interchange

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Relational
open Silmaril.Formats.Parquet.Int32ByteArrayGroup
open Silmaril.Formats.Relational.NamedTable
open Silmaril.Formats.Relational.NamedTable.MixedIpc
open Silmaril.Formats.Relational.NamedTable.MixedIpc.FromParquet

private theorem pair_row (d : Descriptor) (row : Pair) : Export.rowPair d (d.row row) = row := by
  cases d with
  | mk order integer binary => cases order <;> cases row <;> rfl

theorem table_eq_iff {left right : Prepared} (same : left.descriptor = right.descriptor) :
    left.table = right.table ↔ left.batches.flatten = right.batches.flatten := by
  rcases left with ⟨d, xs⟩
  rcases right with ⟨d', ys⟩
  change d = d' at same
  subst d'
  constructor
  · intro equal
    have rows := eq_of_heq (Scan.Observation.mk.inj equal).2
    have pairs := congrArg (List.map (Export.rowPair d)) rows
    simpa [List.map_map, Function.comp_def, pair_row] using pairs
  · intro equal
    simp [Prepared.table, equal]

private def updated {Name : Type*} [DecidableEq Name]
    (db : Database Name) (key : Name) (table : Scan.Observation Label Cell) : Database Name :=
  Function.update db key (some ⟨table.schema, table.rows⟩)

private theorem updated_eq_iff {Name : Type*} [DecidableEq Name]
    (db : Database Name) (key : Name) (left right : Scan.Observation Label Cell) :
    updated db key left = updated db key right ↔ left = right := by
  constructor
  · intro equal
    have found := congrArg (fun next => Scan.observePacked next key) equal
    cases left
    cases right
    simpa [updated, Scan.observePacked, Database.Packed.erase, Database.Partial.map] using found
  · rintro rfl
    rfl

theorem imports_agree_iff {Name : Type*} [DecidableEq Name]
    (db : Database Name) (key : Name) (vacant : db key = none)
    {parquet : File.Limits} {intermediate direct : MixedIpc.Limits} {input : Bytes}
    {int32 byteArray : Field} {wire other : KBytes} {ipc : Prepared}
    (converted : ToIpc.convert parquet intermediate.mixed input int32 byteArray = .ok wire)
    (fits : wire.len ≤ intermediate.inputBytes)
    (read : MixedIpc.read direct other = .ok ipc)
    (same : ipc.descriptor = descriptor int32 byteArray) :
    (∃ next, importNamed db key parquet intermediate input int32 byteArray = .ok next ∧
      importIpc db key (descriptor int32 byteArray) direct other = .ok next) ↔
      ∃ (checked : File.Checked parquet int32 byteArray) (groups : List (List Row)),
        File.openFile parquet input int32 byteArray = .ok checked ∧
        (List.range checked.projection.snapshot.groupCount).mapM
          (checked.projection.readGroup parquet.group) = .ok groups ∧
        (groups.map groupPairs).flatten = ipc.batches.flatten := by
  obtain ⟨checked, groups, opened, reads, _⟩ := convert_observation converted fits
  let fromParquet := observation int32 byteArray groups
  have left : importNamed db key parquet intermediate input int32 byteArray =
      .ok (updated db key fromParquet.table) :=
    (importNamed_ok_iff _ _ _ _ _ _ _ _).mpr
      ⟨vacant, wire, checked, groups, converted, fits, opened, reads, rfl⟩
  have right : importIpc db key (descriptor int32 byteArray) direct other =
      .ok (updated db key ipc.table) :=
    (importIpc_ok_iff _ _ _ _ _ _).mpr ⟨vacant, ipc, read, same, rfl⟩
  have equalTables := table_eq_iff (left := fromParquet) (right := ipc) same.symm
  rw [left, right]
  constructor
  · rintro ⟨next, leftOk, rightOk⟩
    have tables := (updated_eq_iff db key _ _).mp ((Except.ok.inj leftOk).trans (Except.ok.inj rightOk).symm)
    exact ⟨checked, groups, opened, reads, equalTables.mp tables⟩
  · rintro ⟨actual, rows, actualOpen, actualReads, pairs⟩
    rw [opened] at actualOpen
    cases actualOpen
    rw [reads] at actualReads
    cases actualReads
    have updates := (updated_eq_iff db key _ _).mpr (equalTables.mpr pairs)
    exact ⟨_, rfl, congrArg Except.ok updates.symm⟩

end Silmaril.Proofs.Formats.Relational.NamedTable.MixedIpc.Interchange
