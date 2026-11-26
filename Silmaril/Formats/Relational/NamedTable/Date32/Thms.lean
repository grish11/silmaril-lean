module

public import Silmaril.Formats.Relational.NamedTable.Date32.Defs
import Silmaril.Proofs.Formats.Relational.NamedTable.Date32.Correctness

/-! Exact named Date32 admission, ordered row preservation, and indexed failures. -/

public section

namespace Silmaril.Formats.Relational.NamedTable.Date32

open Silmaril.Relational
open Silmaril.Numeric.Gregorian (CivilDate)
open Arrow

/-- The validity bit and little-endian word determine the exact nullable signed
epoch day. Every signed Int32 word is admitted. -/
theorem recover_wire_slot {view : DateValues.View} {index : Nat} {date : Option CivilDate}
    (wire : DateValues.SlotWire .day view index date) :
    ∃ valid word,
      Body.validAt view.validity (view.start + index) = some valid ∧
      view.values.readLE (4 * (view.start + index)) 4 = some word ∧
      recover date = .ok (if valid then some (Int32.ofNat word) else none) :=
  Proofs.Formats.Relational.NamedTable.Date32.recover_wire_slot wire

/-- Successful Date32 IPC reads always recover the original ordered nullable
slots from the checked batches, including both signed endpoints. -/
theorem read_date32_slots {limits : Arrow.Limits} {input : KBytes} {stream : DateStream.Stream}
    (read : DateStream.read limits input = .ok stream) (day : stream.field.unit = .day) :
    ∃ slots : List Slot,
      stream.batches.flatten = slots.map (Option.map DateInterop.Date32.toCivil) ∧
      stream.batches.flatten.mapM recover = .ok slots :=
  Proofs.Formats.Relational.NamedTable.Date32.read_date32_slots read day

/-- A matching shared schema has exactly the same field name and nullability. -/
theorem schema_eq_iff {left right : String} {nullableLeft nullableRight : Bool} :
    schema left nullableLeft = schema right nullableRight ↔
      left = right ∧ nullableLeft = nullableRight :=
  Proofs.Formats.Relational.NamedTable.Date32.schema_eq_iff

/-- Reading the sole field in order gives exactly the inserted slots. -/
theorem rows_slots (field : String) (nullable : Bool) (slots : List Slot) :
    (rows field nullable slots).map (fun row => row (0 : Fin 1)) = slots := by
  rw [rows, List.map_map]
  exact List.map_id slots

variable {Name : Type*} [DecidableEq Name]
variable {db next : Database Name} {name : Name} {field : String} {nullable : Bool}
variable {parquetLimits : Parquet.Date.Limits} {parquet : Bytes}
variable {ipcLimits : Arrow.Limits} {ipc : KBytes}

/-- Success is exactly a vacant destination, admission of the declared field,
and full ordered decoding of every footer-indexed group. Only the named
entry is updated, with the original nullable signed slots. -/
theorem importParquet_ok_iff :
    importParquet db name field nullable parquetLimits parquet = .ok next ↔
      db name = none ∧ ∃ checked groups,
        Parquet.Date.openChecked parquetLimits parquet = .ok checked ∧
        (List.range checked.snapshot.groupCount).mapM (checked.readGroup parquetLimits) = .ok groups ∧
        checked.binding.leaf.name = field ∧ (checked.binding.leaf.repetition == some .optional) = nullable ∧
        next = Function.update db name (some ⟨schema field nullable,
          rows field nullable (groups.flatMap Parquet.Date.RowGroup.date32Slots)⟩) :=
  Proofs.Formats.Relational.NamedTable.Date32.importParquet_ok_iff

/-- Success is exactly a vacant destination and a completed Date32 read at
the declared field. All batches through explicit EOS contribute their
ordered nullable slots to the sole updated entry. -/
theorem importIpc_ok_iff :
    importIpc db name field nullable ipcLimits ipc = .ok next ↔
      db name = none ∧ ∃ stream slots,
        DateStream.read ipcLimits ipc = .ok stream ∧
        stream.field = ⟨field, nullable, .day⟩ ∧
        stream.batches.flatten = slots.map (Option.map DateInterop.Date32.toCivil) ∧
        next = Function.update db name (some ⟨schema field nullable, rows field nullable slots⟩) :=
  Proofs.Formats.Relational.NamedTable.Date32.importIpc_ok_iff

/-- Exhausted sources with the same descriptor and observed rows yield the
same database, irrespective of group and batch boundaries. -/
theorem imports_equal_of_rows
    {checked : Parquet.Date.Checked} {groups : List Parquet.Date.RowGroup}
    {stream : DateStream.Stream}
    (vacant : db name = none)
    (opened : Parquet.Date.openChecked parquetLimits parquet = .ok checked)
    (decoded : (List.range checked.snapshot.groupCount).mapM (checked.readGroup parquetLimits) = .ok groups)
    (label : checked.binding.leaf.name = field)
    (repetition : (checked.binding.leaf.repetition == some .optional) = nullable)
    (read : DateStream.read ipcLimits ipc = .ok stream)
    (exactField : stream.field = ⟨field, nullable, .day⟩)
    (sameRows : stream.batches.flatten =
      (groups.flatMap Parquet.Date.RowGroup.date32Slots).map (Option.map DateInterop.Date32.toCivil)) :
    ∃ next, importParquet db name field nullable parquetLimits parquet = .ok next ∧
      importIpc db name field nullable ipcLimits ipc = .ok next :=
  Proofs.Formats.Relational.NamedTable.Date32.imports_equal_of_rows
    vacant opened decoded label repetition read exactField sameRows

/-- The first failing group returns its exact indexed cause without a named
update, even after earlier groups have decoded. -/
theorem importParquet_group_error {checked : Parquet.Date.Checked}
    {before after : List Nat} {index : Nat} {groups : List Parquet.Date.RowGroup} {cause : Parquet.Date.Error}
    (vacant : db name = none)
    (opened : Parquet.Date.openChecked parquetLimits parquet = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (checked.readGroup parquetLimits) = .ok groups)
    (failed : checked.readGroup parquetLimits index = .error cause) :
    importParquet db name field nullable parquetLimits parquet = .error (.readError (.groupFailure index cause)) :=
  Proofs.Formats.Relational.NamedTable.Date32.importParquet_group_error
    vacant opened split earlier failed

/-- A late IPC failure returns the original batch index and cause without a
named update. -/
theorem importIpc_batch_error {index : Nat} {cause : DateStream.BatchError}
    (vacant : db name = none)
    (failed : DateStream.read ipcLimits ipc = .error (.batch index cause)) :
    importIpc db name field nullable ipcLimits ipc =
      .error (.readError (.source (.batch index cause))) := by
  simp [importIpc, vacant, failed]

end Silmaril.Formats.Relational.NamedTable.Date32
