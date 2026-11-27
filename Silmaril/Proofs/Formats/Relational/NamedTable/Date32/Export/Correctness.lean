module

public import Silmaril.Formats.Relational.NamedTable.Date32.Export.Defs
import Silmaril.Formats.Parquet.Date.FromIpc.Thms
import Silmaril.Formats.DateInterop.Thms

public section

namespace Silmaril.Proofs.Formats.Relational.NamedTable.Date32.Export

open Silmaril.Formats Parquet
open Silmaril.Formats.Relational.NamedTable.Date32
open Silmaril.Formats.Relational.NamedTable.Date32.Export
open Silmaril.Relational

theorem select_eq_ok_iff {Name : Type*} {db : Database Name} {name : Name}
    {column : Column} {maxRows : Nat} {slots : List Slot} :
    select db name column maxRows = .ok slots ↔
      ∃ table, Scan.observePacked db name = some table ∧
        ∃ within : column.index < table.schema.width,
        table.schema.kind ⟨column.index, within⟩ = (column.field, .date32 column.nullable) ∧
        table.rowCount ≤ maxRows ∧ slots = table.rows.map (· ⟨column.index, within⟩) := by
  unfold select
  cases observed : Scan.observePacked db name with
  | none => simp
  | some table =>
    by_cases within : column.index < table.schema.width
    · have descriptor :
          table.schema.kind ⟨column.index, within⟩ = (column.field, .date32 column.nullable) ↔
            (table.schema.kind ⟨column.index, within⟩).1 = column.field ∧
            (table.schema.kind ⟨column.index, within⟩).2 = .date32 column.nullable :=
        Prod.ext_iff
      simp only [within, dite_true, Option.some.injEq, exists_eq_left', descriptor, ne_eq]
      by_cases label : (table.schema.kind ⟨column.index, within⟩).1 = column.field
      · by_cases kind : (table.schema.kind ⟨column.index, within⟩).2 = .date32 column.nullable
        · by_cases over : maxRows < table.rowCount
          · simp [label, kind, over, Nat.not_le_of_gt over]
          · simp [label, kind, over, Nat.le_of_not_gt over, eq_comm]
        · simp [label, kind]
      · simp [label]
    · simp [within]

theorem convert_eq_ok_iff {Name : Type*} {db : Database Name} {name : Name}
    {column : Column} {limits : Limits} {wire : Bytes} :
    convert db name column limits = .ok wire ↔
      ∃ slots, select db name column limits.maxRows = .ok slots ∧
        Date.FromIpc.emitGroup limits.writer limits.readback column.field column.nullable
          (slots.map (Option.map DateInterop.Date32.toCivil)) = .ok wire := by
  unfold convert
  cases select db name column limits.maxRows with
  | error cause => simp [Bind.bind, Except.bind]
  | ok slots =>
    cases written : Date.FromIpc.emitGroup limits.writer limits.readback column.field column.nullable
        (slots.map (Option.map DateInterop.Date32.toCivil)) <;>
      simp [written, Except.mapError, Bind.bind, Except.bind]

theorem convert_readback {Name : Type*} {db : Database Name} {name : Name}
    {column : Column} {limits : Limits} {wire : Bytes}
    (written : convert db name column limits = .ok wire) :
    wire.length ≤ limits.writer.maxFileBytes ∧
    ∃ slots checked group, select db name column limits.maxRows = .ok slots ∧
      Date.openChecked limits.readback wire = .ok checked ∧ Date.readGroup limits.readback wire 0 = .ok group ∧
      checked.snapshot.groupCount = 1 ∧
      group.binding.leaf = Date.FromIpc.leaf ⟨column.field, column.nullable, .day⟩ ∧
      group.binding.annotation = .logicalAndConverted ∧
      group.rowCount = slots.length ∧ group.date32Slots = slots := by
  obtain ⟨slots, projected, emitted⟩ := convert_eq_ok_iff.mp written
  obtain ⟨bounded, checked, group, opened, read, agrees⟩ := Date.FromIpc.emitGroup_readback emitted
  have words := Date.FromIpc.Matches.exactWords agrees
  have back : ∀ value : Slot,
      (value.map DateInterop.Date32.toCivil).bind DateInterop.Date32.ofCivil? = value := by
    intro value
    cases value <;> simp
  refine ⟨bounded, slots, checked, group, projected, opened, read, agrees.1, agrees.2.1, agrees.2.2.1,
    by simpa using agrees.2.2.2.1, ?_⟩
  simpa [List.map_map, Function.comp_def, back] using words

end Silmaril.Proofs.Formats.Relational.NamedTable.Date32.Export
