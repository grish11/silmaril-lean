module

public import Silmaril.Formats.Relational.NamedTable.Date32.Export.Defs
import Silmaril.Proofs.Formats.Relational.NamedTable.Date32.Export.Correctness

public section

namespace Silmaril.Formats.Relational.NamedTable.Date32.Export

open Silmaril.Relational Silmaril.Formats.Parquet

variable {Name : Type*} {db : Database Name} {name : Name} {column : Column}
variable {maxRows : Nat} {slots : List Slot} {limits : Limits} {wire : Bytes}
variable {table : Scan.Observation String Date.Events.Cell}

/-- Selection is exactly the original named table, matching positional field
and kind, and its ordered nullable words within the row cap. -/
theorem select_eq_ok_iff :
    select db name column maxRows = .ok slots ↔
      ∃ table, Scan.observePacked db name = some table ∧
        ∃ within : column.index < table.schema.width,
        table.schema.kind ⟨column.index, within⟩ = (column.field, .date32 column.nullable) ∧
        table.rowCount ≤ maxRows ∧ slots = table.rows.map (· ⟨column.index, within⟩) :=
  Proofs.Formats.Relational.NamedTable.Date32.Export.select_eq_ok_iff

theorem select_missing (missing : Scan.observePacked db name = none) :
    select db name column maxRows = .error .missingName := by
  simp [select, missing]

theorem select_badIndex (found : Scan.observePacked db name = some table)
    (outside : table.schema.width ≤ column.index) :
    select db name column maxRows = .error (.columnIndex column.index table.schema.width) := by
  simp [select, found, not_lt.mpr outside]

theorem select_badField (found : Scan.observePacked db name = some table)
    (within : column.index < table.schema.width)
    (label : (table.schema.kind ⟨column.index, within⟩).1 ≠ column.field) :
    select db name column maxRows =
      .error (.fieldMismatch (table.schema.kind ⟨column.index, within⟩).1) := by
  simp [select, found, within, label]

theorem select_badKind (found : Scan.observePacked db name = some table)
    (within : column.index < table.schema.width)
    (label : (table.schema.kind ⟨column.index, within⟩).1 = column.field)
    (kind : (table.schema.kind ⟨column.index, within⟩).2 ≠ .date32 column.nullable) :
    select db name column maxRows =
      .error (.kindMismatch (table.schema.kind ⟨column.index, within⟩).2) := by
  simp [select, found, within, label, kind]

theorem select_rowLimit (found : Scan.observePacked db name = some table)
    (within : column.index < table.schema.width)
    (descriptor : table.schema.kind ⟨column.index, within⟩ = (column.field, .date32 column.nullable))
    (over : maxRows < table.rowCount) :
    select db name column maxRows = .error (.rowLimit table.rowCount maxRows) := by
  simp [select, found, within, descriptor, over]

/-- The native writer and checked reader keep their independent limits after
bounded selection. -/
theorem convert_eq_ok_iff :
    convert db name column limits = .ok wire ↔
      ∃ slots, select db name column limits.maxRows = .ok slots ∧
        Date.FromIpc.emitGroup limits.writer limits.readback column.field column.nullable
          (slots.map (Option.map DateInterop.Date32.toCivil)) = .ok wire :=
  Proofs.Formats.Relational.NamedTable.Date32.Export.convert_eq_ok_iff

theorem convert_selectError {cause : Error}
    (failed : select db name column limits.maxRows = .error cause) :
    convert db name column limits = .error cause := by
  simp [convert, failed, Bind.bind, Except.bind]

theorem convert_writeError {cause : Date.FromIpc.Error}
    (prepared : select db name column limits.maxRows = .ok slots)
    (failed : Date.FromIpc.emitGroup limits.writer limits.readback column.field column.nullable
      (slots.map (Option.map DateInterop.Date32.toCivil)) = .error cause) :
    convert db name column limits = .error (.write cause) := by
  simp [convert, prepared, failed, Except.mapError, Bind.bind, Except.bind]

/-- Success returns one checked INT32 DATE group with both annotations, the
exact field descriptor, and all selected nullable signed slots in table order. -/
theorem convert_readback (written : convert db name column limits = .ok wire) :
    wire.length ≤ limits.writer.maxFileBytes ∧
    ∃ slots checked group, select db name column limits.maxRows = .ok slots ∧
      Date.openChecked limits.readback wire = .ok checked ∧ Date.readGroup limits.readback wire 0 = .ok group ∧
      checked.snapshot.groupCount = 1 ∧
      group.binding.leaf = Date.FromIpc.leaf ⟨column.field, column.nullable, .day⟩ ∧
      group.binding.annotation = .logicalAndConverted ∧
      group.rowCount = slots.length ∧ group.date32Slots = slots :=
  Proofs.Formats.Relational.NamedTable.Date32.Export.convert_readback written

end Silmaril.Formats.Relational.NamedTable.Date32.Export
