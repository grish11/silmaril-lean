module

public import Silmaril.Formats.Parquet.Date.Defs
import all Silmaril.Formats.Parquet.Date.Defs
import Silmaril.Formats.DateInterop.Thms
import Silmaril.Formats.Parquet.FlatScan.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Date

open Silmaril.Formats
open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Date
open ThriftCompact.Traversal (Field Reader)

theorem classify_ok_iff (logical : Bool) (converted : Option Int) (annotation : Annotation) :
    Internal.classify logical converted = .ok annotation ↔
      match annotation with
      | .logical => logical = true ∧ converted = none
      | .logicalAndConverted => logical = true ∧ converted = some 6
      | .converted => logical = false ∧ converted = some 6 := by
  cases logical <;> cases converted <;> cases annotation <;> simp [Internal.classify]
  all_goals split <;> simp_all

theorem checkLogicalDate_ok_iff (reader : Reader) (field : Field) :
    Internal.checkLogicalDate reader field = .ok () ↔
      ∃ member, Internal.payload field .struct (Internal.structFields reader) = .ok [member] ∧
        member.id = 6 ∧ Internal.payload member .struct (Internal.structFields reader) = .ok [] := by
  cases payloadRead : Internal.payload field .struct (Internal.structFields reader) with
  | error =>
    simp [Internal.checkLogicalDate, payloadRead, Bind.bind, Except.bind]
  | ok members =>
    cases members with
    | nil => simp [Internal.checkLogicalDate, payloadRead, Bind.bind, Except.bind]
    | cons member rest =>
      cases rest with
      | cons => simp [Internal.checkLogicalDate, payloadRead, Bind.bind, Except.bind]
      | nil =>
        by_cases isDate : member.id = 6
        · cases dateRead : Internal.payload member .struct (Internal.structFields reader) with
          | error => simp [Internal.checkLogicalDate, payloadRead, isDate, dateRead, Bind.bind, Except.bind]
          | ok body =>
            cases body <;>
              simp [Internal.checkLogicalDate, payloadRead, isDate, dateRead, Bind.bind, Except.bind, pure,
                Except.pure]
        · simp [Internal.checkLogicalDate, payloadRead, isDate, Bind.bind, Except.bind]

theorem readAnnotation_ok_iff (reader : Reader) (fields : List Field) (annotation : Annotation) :
    Internal.readAnnotation reader fields = .ok annotation ↔
      ∃ modern checked legacy converted,
        Internal.optionalField fields 10 = .ok modern ∧
        modern.mapM (Internal.checkLogicalDate reader) = .ok checked ∧
        Internal.optionalField fields 6 = .ok legacy ∧
        legacy.mapM (Internal.convertedCode reader) = .ok converted ∧
        Internal.classify modern.isSome converted = .ok annotation := by
  cases modernRead : Internal.optionalField fields 10 with
  | error => simp [Internal.readAnnotation, modernRead, Bind.bind, Except.bind]
  | ok modern =>
    cases checkedRead : modern.mapM (Internal.checkLogicalDate reader) with
    | error => simp [Internal.readAnnotation, modernRead, checkedRead, Bind.bind, Except.bind]
    | ok checked =>
      cases legacyRead : Internal.optionalField fields 6 with
      | error => simp [Internal.readAnnotation, modernRead, checkedRead, legacyRead, Bind.bind, Except.bind]
      | ok legacy =>
        cases convertedRead : legacy.mapM (Internal.convertedCode reader) with
        | error =>
          simp [Internal.readAnnotation, modernRead, checkedRead, legacyRead, convertedRead,
            Bind.bind, Except.bind]
        | ok converted =>
          simp [Internal.readAnnotation, modernRead, checkedRead, legacyRead, convertedRead,
            Bind.bind, Except.bind]

theorem bind_ok_iff (limits : Footer.Limits) (snapshot : Snapshot.Checked) (binding : Binding) :
    Date.bind limits snapshot = .ok binding ↔
      ∃ root fields, snapshot.metadata.schema = [root, binding.leaf] ∧ IsDateLeaf binding.leaf ∧
        Internal.leafFields (Internal.annotationReader limits snapshot) = .ok fields ∧
        Internal.readAnnotation (Internal.annotationReader limits snapshot) fields =
          .ok binding.annotation := by
  cases schemaRead : snapshot.metadata.schema with
  | nil => simp [Date.bind, schemaRead]
  | cons root rest =>
    cases rest with
    | nil => simp [Date.bind, schemaRead]
    | cons leaf tail =>
      cases tail with
      | cons => simp [Date.bind, schemaRead]
      | nil =>
        rcases binding with ⟨observed, annotation⟩
        by_cases isDate : IsDateLeaf leaf
        · cases fieldsRead : Internal.leafFields (Internal.annotationReader limits snapshot) with
          | error => simp [Date.bind, schemaRead, isDate, fieldsRead, Bind.bind, Except.bind]
          | ok fields =>
            cases annotationRead :
                Internal.readAnnotation (Internal.annotationReader limits snapshot) fields with
            | error => simp [Date.bind, schemaRead, isDate, fieldsRead, annotationRead, Bind.bind, Except.bind]
            | ok tag =>
              simp [Date.bind, schemaRead, isDate, fieldsRead, annotationRead, Bind.bind, Except.bind,
                pure, Except.pure]
              grind
        · simp [Date.bind, schemaRead, isDate, Bind.bind, Except.bind]
          grind

theorem checkColumn_ok_iff (binding : Binding) (group : Footer.RowGroup) :
    checkColumn binding group = .ok () ↔
      ∃ chunk, group.columns = [chunk] ∧ chunk.metadata.pathInSchema = [binding.leaf.name] := by
  cases columns : group.columns with
  | nil => simp [checkColumn, columns]
  | cons chunk tail =>
    cases tail with
    | cons => simp [checkColumn, columns]
    | nil =>
      by_cases path : chunk.metadata.pathInSchema = [binding.leaf.name] <;>
        simp [checkColumn, columns, path, pure, Except.pure]

theorem openChecked_ok_iff (limits : Limits) (source : Bytes) (checked : Checked) :
    openChecked limits source = .ok checked ↔
      Snapshot.check (Failure := Unit) limits.snapshot source = .ok checked.snapshot ∧
      Date.bind limits.snapshot.footer checked.snapshot = .ok checked.binding := by
  obtain ⟨snapshot, binding⟩ := checked
  cases opened : Snapshot.check (Failure := Unit) limits.snapshot source with
  | error => simp [openChecked, opened, Bind.bind, Except.bind, Except.mapError]
  | ok checked =>
    by_cases same : checked = snapshot
    · subst snapshot
      cases bound : Date.bind limits.snapshot.footer checked <;>
        simp [openChecked, opened, bound, Bind.bind, Except.bind, Except.mapError, pure, Except.pure]
    · cases bound : Date.bind limits.snapshot.footer checked <;>
        simp [openChecked, opened, bound, same, Bind.bind, Except.bind, Except.mapError, pure,
          Except.pure]

theorem readGroup_ok_iff (limits : Limits) (source : Bytes) (index : Nat)
    (result : RowGroup) :
    readGroup limits source index = .ok result ↔
      ∃ snapshot group field,
        Snapshot.check (Failure := Unit) limits.snapshot source = .ok snapshot ∧
        Date.bind limits.snapshot.footer snapshot = .ok result.binding ∧
        snapshot.groupAt index = some group ∧ checkColumn result.binding group = .ok () ∧
        FlatScan.scanRowGroup limits.scan (FlatScan.decodeInt32Page limits.page)
          snapshot.bytes snapshot.footer.start snapshot.metadata.schema group =
          .ok ⟨result.rowCount, [(field, result.column)]⟩ := by
  cases opened : Snapshot.check (Failure := Unit) limits.snapshot source with
  | error => simp [readGroup, openChecked, opened, Bind.bind, Except.bind, Except.mapError]
  | ok snapshot =>
    obtain ⟨binding, rows, column⟩ := result
    cases bound : Date.bind limits.snapshot.footer snapshot with
    | error => simp [readGroup, openChecked, opened, bound, Bind.bind, Except.bind, Except.mapError]
    | ok observed =>
      by_cases same : observed = binding
      · subst binding
        cases found : snapshot.groupAt index with
        | none => simp [readGroup, openChecked, Checked.readGroup, opened, bound, found, Bind.bind, Except.bind, Except.mapError, pure, Except.pure]
        | some group =>
          cases associated : checkColumn observed group with
          | error => simp [readGroup, openChecked, Checked.readGroup, opened, bound, found, associated, Bind.bind, Except.bind, Except.mapError, pure, Except.pure]
          | ok ready =>
            cases ready
            cases scanned : FlatScan.scanRowGroup limits.scan (FlatScan.decodeInt32Page limits.page)
                snapshot.bytes snapshot.footer.start snapshot.metadata.schema group with
            | error =>
              simp [readGroup, openChecked, Checked.readGroup, opened, bound, found, associated, scanned, Bind.bind, Except.bind, Except.mapError, pure, Except.pure]
            | ok batch =>
              obtain ⟨rowCount, columns⟩ := batch
              cases columns with
              | nil =>
                simp [readGroup, openChecked, Checked.readGroup, opened, bound, found, associated, scanned, Bind.bind, Except.bind,
                  Except.mapError, pure, Except.pure]
                intro sameRows
                subst rows
                simp
              | cons first tail =>
                cases tail with
                | cons =>
                  simp [readGroup, openChecked, Checked.readGroup, opened, bound, found, associated, scanned, Bind.bind, Except.bind,
                    Except.mapError, pure, Except.pure]
                  intro sameRows
                  subst rows
                  simp
                | nil =>
                  obtain ⟨field, values⟩ := first
                  simp [readGroup, openChecked, Checked.readGroup, opened, bound, found, associated, scanned, Bind.bind, Except.bind,
                    Except.mapError, pure, Except.pure]
                  intro sameRows
                  subst rows
                  simp
      · cases found : snapshot.groupAt index with
        | none => simp [readGroup, openChecked, Checked.readGroup, opened, bound, found, same, Bind.bind, Except.bind, Except.mapError, pure, Except.pure]
        | some group =>
          cases associated : checkColumn observed group with
          | error =>
            simp [readGroup, openChecked, Checked.readGroup, opened, bound, found, associated, same, Bind.bind, Except.bind, Except.mapError, pure, Except.pure]
          | ok ready =>
            cases ready
            cases scanned : FlatScan.scanRowGroup limits.scan (FlatScan.decodeInt32Page limits.page)
                snapshot.bytes snapshot.footer.start snapshot.metadata.schema group with
            | error =>
              simp [readGroup, openChecked, Checked.readGroup, opened, bound, found, associated, scanned, same, Bind.bind, Except.bind,
                Except.mapError, pure, Except.pure]
            | ok batch =>
              obtain ⟨rows, columns⟩ := batch
              cases columns with
              | nil =>
                simp [readGroup, openChecked, Checked.readGroup, opened, bound, found, associated, scanned, same, Bind.bind, Except.bind,
                  Except.mapError, pure, Except.pure]
              | cons field tail =>
                cases tail <;>
                  simp [readGroup, openChecked, Checked.readGroup, opened, bound, found, associated, scanned, same, Bind.bind,
                    Except.bind, Except.mapError, pure, Except.pure]

theorem readGroup_date32Count {limits : Limits} {source : Bytes} {index : Nat}
    {result : RowGroup} (read : readGroup limits source index = .ok result) :
    ∃ snapshot group, Snapshot.check (Failure := Unit) limits.snapshot source = .ok snapshot ∧
      snapshot.groupAt index = some group ∧ result.date32Slots.length = group.numRows.toNat := by
  obtain ⟨snapshot, group, _, checked, _, selected, _, scanned⟩ :=
    (readGroup_ok_iff _ _ _ _).mp read
  have rows := (FlatScan.scanRowGroup_dimensions scanned).1
  rw [FlatScan.rows_length] at rows
  exact ⟨snapshot, group, checked, selected, by simpa [Parquet.Date.RowGroup.date32Slots,
    result.column.sized] using rows⟩

theorem RowGroup.date32_civil (group : RowGroup) :
    group.civilSlots.map (fun cell => cell.bind DateInterop.Date32.ofCivil?) = group.date32Slots := by
  unfold Parquet.Date.RowGroup.civilSlots
  rw [List.map_map]
  conv_rhs => rw [← List.map_id group.date32Slots]
  apply List.map_congr_left
  intro slot _
  cases slot <;> simp

theorem readGroup_scan_error {limits : Limits} {source : Bytes} {index : Nat}
    {snapshot : Snapshot.Checked} {binding : Binding} {group : Footer.RowGroup}
    {cause : FlatScan.Error FlatScan.AdapterError}
    (opened : Snapshot.check (Failure := Unit) limits.snapshot source = .ok snapshot)
    (bound : bind limits.snapshot.footer snapshot = .ok binding)
    (selected : snapshot.groupAt index = some group)
    (associated : checkColumn binding group = .ok ())
    (scan : FlatScan.scanRowGroup limits.scan (FlatScan.decodeInt32Page limits.page)
      snapshot.bytes snapshot.footer.start snapshot.metadata.schema group = .error cause) :
    readGroup limits source index = .error (.scan cause) := by
  simp [readGroup, openChecked, Checked.readGroup, opened, bound, selected, associated, scan, Bind.bind, Except.bind, Except.mapError, pure, Except.pure]

end Silmaril.Proofs.Formats.Parquet.Date
