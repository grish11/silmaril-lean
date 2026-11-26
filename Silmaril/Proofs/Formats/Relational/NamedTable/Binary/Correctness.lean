module

public import Silmaril.Formats.Relational.NamedTable.Binary.Defs
import Silmaril.Formats.Relational.BinaryObservation.ParquetFile.Thms
import Silmaril.Formats.Relational.NamedTable.Thms
import Silmaril.Semantics.Relational.Table.Thms

public section

namespace Silmaril.Proofs.Formats.Relational.NamedTable.Binary

open Silmaril.Formats
open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Plain.ByteArray
open Silmaril.Formats.Relational
open Silmaril.Formats.Relational.BinaryObservation
open Silmaril.Formats.Relational.NamedTable.Binary
open Silmaril.Relational

private theorem normalize_groups (groups : List (List (Option Bytes))) :
    ((groups.map (List.map fun slot (_ : Fin 1) => slot)).map
      (List.map fun row index => (row index).map Bytes.toList)).flatten =
    (groups.map (List.map fun slot (_ : Fin 1) => slot.map Bytes.toList)).flatten := by
  simp [List.map_map, Function.comp_def]

private theorem collectParquet_of_trace {limits : File.Limits} {input : Bytes} {selected : Field}
    {groups : List (List (Option Bytes))} {terminal : Arrow.Events.Termination File.Error}
    (trace : File.readAll limits input selected.name (layoutOf selected) = .ok
      ⟨File.schema selected.name (layoutOf selected),
        ⟨groups.map (AlignedColumns.ofRows ∘ File.rows selected.name (layoutOf selected)), terminal⟩⟩) :
    collectParquet limits input selected = .ok
      ⟨observation selected (groups.flatten.map (Option.map Bytes.toList)), terminal⟩ := by
  have rows_eq :
      (groups.map (AlignedColumns.ofRows ∘ File.rows selected.name (layoutOf selected))).flatMap
        AlignedColumns.toRows = (groups.map (File.rows selected.name (layoutOf selected))).flatten := by
    simp [List.flatMap, List.map_map, Function.comp_def]
  rw [collectParquet, trace]
  simp only [Arrow.Events.EventStream.collect, Arrow.Events.Trace.collect, Arrow.Events.Trace.rows,
    Except.map, rows_eq]
  cases selected with
  | mk name nullable =>
    cases nullable <;> simp [parquetObservation, observation, Field.schema, File.schema, layoutOf,
      List.map_flatten, List.map_map, Function.comp_def]
    all_goals exact normalize_groups groups

theorem collectParquet_groups {limits : File.Limits} {input : Bytes} {selected : Field}
    {checked : File.Checked selected.name (layoutOf selected)} {groups : List (List (Option Bytes))}
    (opened : File.openFile limits input selected.name (layoutOf selected) = .ok checked)
    (decoded : (List.range checked.snapshot.groupCount).mapM (checked.readGroup limits) = .ok groups) :
    collectParquet limits input selected = .ok
      ⟨observation selected (groups.flatten.map (Option.map Bytes.toList)), .eos⟩ :=
  collectParquet_of_trace (ParquetFile.readAll_success opened decoded)

theorem collectParquet_first_error {limits : File.Limits} {input : Bytes} {selected : Field}
    {checked : File.Checked selected.name (layoutOf selected)} {before after : List Nat} {index : Nat}
    {groups : List (List (Option Bytes))} {cause : FlatColumn.Error File.PageError}
    (opened : File.openFile limits input selected.name (layoutOf selected) = .ok checked)
    (indices : List.range checked.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (checked.readGroup limits) = .ok groups)
    (failure : checked.readGroup limits index = .error cause) :
    collectParquet limits input selected = .ok
      ⟨observation selected (groups.flatten.map (Option.map Bytes.toList)), .readError (.column cause)⟩ :=
  collectParquet_of_trace (ParquetFile.readAll_first_error opened indices earlier failure)

open Silmaril.Formats.Arrow.BinaryView

variable {Name : Type*} [DecidableEq Name] {db next : Database Name} {name : Name} {expected : Field}
variable {ipcLimits : Arrow.Limits} {viewLimits : Column.Limits} {ipc : KBytes}

theorem importIpc_ok_iff :
    importIpc db name expected ipcLimits viewLimits ipc = .ok next ↔
      db name = none ∧ ∃ rows : Scan.Table expected.schema Cell,
        collectIpc ipcLimits viewLimits ipc = .ok ⟨⟨expected.schema, rows⟩, .eos⟩ ∧
        next = Function.update db name (some ⟨expected.schema, rows⟩) := by
  rw [← NamedTable.importCollected_ok_iff db next name expected.schema]
  unfold importIpc
  cases NamedTable.importCollected db name expected.schema (collectIpc ipcLimits viewLimits ipc)
  <;> simp [Except.mapError]

end Silmaril.Proofs.Formats.Relational.NamedTable.Binary
