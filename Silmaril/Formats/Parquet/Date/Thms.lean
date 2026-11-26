module

public import Silmaril.Formats.Parquet.Date.Defs
import Silmaril.Proofs.Formats.Parquet.Date.Binding

/-! Exact annotation admission and ordered nullable Parquet DATE observations. -/

public section

namespace Silmaril.Formats.Parquet.Date

open ThriftCompact.Traversal (Field Reader)

/-- The converted DATE fallback applies precisely when the modern field is absent. -/
theorem classify_ok_iff (logical : Bool) (converted : Option Int) (annotation : Annotation) :
    Internal.classify logical converted = .ok annotation ↔
      match annotation with
      | .logical => logical = true ∧ converted = none
      | .logicalAndConverted => logical = true ∧ converted = some 6
      | .converted => logical = false ∧ converted = some 6 :=
  Proofs.Formats.Parquet.Date.classify_ok_iff logical converted annotation

/-- The IDL union has one DATE member with an empty DateType payload. -/
theorem checkLogicalDate_ok_iff (reader : Reader) (field : Field) :
    Internal.checkLogicalDate reader field = .ok () ↔
      ∃ member, Internal.payload field .struct (Internal.structFields reader) = .ok [member] ∧
        member.id = 6 ∧ Internal.payload member .struct (Internal.structFields reader) = .ok [] :=
  Proofs.Formats.Parquet.Date.checkLogicalDate_ok_iff reader field

/-- Both annotation fields are checked from the given raw leaf before classification. -/
theorem readAnnotation_ok_iff (reader : Reader) (fields : List Field) (annotation : Annotation) :
    Internal.readAnnotation reader fields = .ok annotation ↔
      ∃ modern checked legacy converted,
        Internal.optionalField fields 10 = .ok modern ∧
        modern.mapM (Internal.checkLogicalDate reader) = .ok checked ∧
        Internal.optionalField fields 6 = .ok legacy ∧
        legacy.mapM (Internal.convertedCode reader) = .ok converted ∧
        Internal.classify modern.isSome converted = .ok annotation :=
  Proofs.Formats.Parquet.Date.readAnnotation_ok_iff reader fields annotation

/-- The typed and raw leaf use the same checked footer and schema ordinal. -/
theorem bind_ok_iff (limits : Footer.Limits) (snapshot : Snapshot.Checked) (binding : Binding) :
    Date.bind limits snapshot = .ok binding ↔
      ∃ root fields, snapshot.metadata.schema = [root, binding.leaf] ∧ IsDateLeaf binding.leaf ∧
        Internal.leafFields (Internal.annotationReader limits snapshot) = .ok fields ∧
        Internal.readAnnotation (Internal.annotationReader limits snapshot) fields =
          .ok binding.annotation :=
  Proofs.Formats.Parquet.Date.bind_ok_iff limits snapshot binding

/-- The selected chunk is the group's sole column and has the annotated leaf's path. -/
theorem checkColumn_ok_iff (binding : Binding) (group : Footer.RowGroup) :
    checkColumn binding group = .ok () ↔
      ∃ chunk, group.columns = [chunk] ∧ chunk.metadata.pathInSchema = [binding.leaf.name] :=
  Proofs.Formats.Parquet.Date.checkColumn_ok_iff binding group

/-- The Date32 result preserves the exact scanner vector for the selected snapshot group. -/
theorem readGroup_ok_iff (limits : Limits) (source : Bytes) (index : Nat)
    (result : RowGroup) :
    readGroup limits source index = .ok result ↔
      ∃ snapshot group field,
        Snapshot.check (Failure := Unit) limits.snapshot source = .ok snapshot ∧
        Date.bind limits.snapshot.footer snapshot = .ok result.binding ∧
        snapshot.groupAt index = some group ∧ checkColumn result.binding group = .ok () ∧
        FlatScan.scanRowGroup limits.scan (FlatScan.decodeInt32Page limits.page)
          snapshot.bytes snapshot.footer.start snapshot.metadata.schema group =
          .ok ⟨result.rowCount, [(field, result.column)]⟩ :=
  Proofs.Formats.Parquet.Date.readGroup_ok_iff limits source index result

/-- The Date32 vector has the selected group's advertised row count. -/
theorem readGroup_date32Count {limits : Limits} {source : Bytes} {index : Nat}
    {result : RowGroup} (read : readGroup limits source index = .ok result) :
    ∃ snapshot group, Snapshot.check (Failure := Unit) limits.snapshot source = .ok snapshot ∧
      snapshot.groupAt index = some group ∧ result.date32Slots.length = group.numRows.toNat :=
  Proofs.Formats.Parquet.Date.readGroup_date32Count read

/-- Mapping the Gregorian view back to Date32 preserves every ordered nullable slot. -/
theorem RowGroup.date32_civil (group : RowGroup) :
    group.civilSlots.map (fun cell => cell.bind DateInterop.Date32.ofCivil?) = group.date32Slots :=
  Proofs.Formats.Parquet.Date.RowGroup.date32_civil group

/-- Scanner failures keep the original typed cause after DATE admission. -/
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
  simp [readGroup, opened, bound, selected, associated, scan, Bind.bind, Except.bind, Except.mapError]

/-- The outer option marks a valid index and the inner option marks a present date. -/
theorem RowGroup.civilSlot (result : RowGroup) (index : Nat) :
    result.civilSlots[index]? =
      result.date32Slots[index]?.map (Option.map DateInterop.ParquetDate.toCivil) := by
  simp [RowGroup.civilSlots]

end Silmaril.Formats.Parquet.Date
