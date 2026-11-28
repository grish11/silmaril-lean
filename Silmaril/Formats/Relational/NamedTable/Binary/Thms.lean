module

public import Silmaril.Formats.Relational.NamedTable.Binary.Defs
import Silmaril.Formats.Relational.BinaryObservation.ParquetFile.Thms
import Silmaril.Formats.Relational.NamedTable.Thms
import Silmaril.Proofs.Formats.Relational.NamedTable.Binary.Correctness

/-! Exact ordered binary observations, the named insertion gate, and failures. -/

public section

namespace Silmaril.Formats.Relational.NamedTable.Binary

open Silmaril.Relational
open Parquet.Plain.ByteArray
open Arrow.BinaryView
open Relational.BinaryObservation

/-- Successful indexed groups contribute their exact opaque slots at EOS. -/
theorem collectParquet_groups {limits : File.Limits} {input : Bytes} {selected : Field}
    {checked : File.Checked selected.name (layoutOf selected)} {groups : List (List (Option Bytes))}
    (opened : File.openFile limits input selected.name (layoutOf selected) = .ok checked)
    (decoded : (List.range checked.snapshot.groupCount).mapM (checked.readGroup limits) = .ok groups) :
    collectParquet limits input selected = .ok
      ⟨observation selected (groups.flatten.map (Option.map Bytes.toList)), .eos⟩ :=
  Proofs.Formats.Relational.NamedTable.Binary.collectParquet_groups opened decoded

/-- A late failure retains exactly the completed prefix and indexed cause. -/
theorem collectParquet_first_error {limits : File.Limits} {input : Bytes} {selected : Field}
    {checked : File.Checked selected.name (layoutOf selected)} {before after : List Nat} {index : Nat}
    {groups : List (List (Option Bytes))} {cause : Parquet.FlatColumn.Error File.PageError}
    (opened : File.openFile limits input selected.name (layoutOf selected) = .ok checked)
    (indices : List.range checked.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (checked.readGroup limits) = .ok groups)
    (failure : checked.readGroup limits index = .error cause) :
    collectParquet limits input selected = .ok
      ⟨observation selected (groups.flatten.map (Option.map Bytes.toList)), .readError (.column cause)⟩ :=
  Proofs.Formats.Relational.NamedTable.Binary.collectParquet_first_error opened indices earlier failure

/-- A checked BinaryView stream contributes all batches through exact EOS. -/
theorem collectIpc_binary {ipcLimits : Arrow.Limits} {viewLimits : Column.Limits} {ipc : KBytes}
    {field : Field} {batches : List (List (Option KBytes))}
    (read : Stream.read ipcLimits viewLimits ipc = .ok ⟨⟨field.name, field.nullable, .binary⟩, batches⟩) :
    collectIpc ipcLimits viewLimits ipc = .ok ⟨observation field (ipcSlots batches), .eos⟩ := by
  rw [collectIpc, read]

/-- An unsuccessful result carries no replacement database. Retaining the
prior state on an error leaves every entry equal to its original value. -/
theorem unchanged_on_error {Name Error : Type*} {db : Database Name}
    {result : Except Error (Database Name)} {cause : Error}
    (failure : result = .error cause) : result.toOption.getD db = db := by
  rw [failure]
  rfl

variable {Name : Type*} [DecidableEq Name] {db next : Database Name} {name : Name}
variable {expected selected : Field} {parquetLimits : File.Limits} {parquet : Bytes}
variable {ipcLimits : Arrow.Limits} {viewLimits : Column.Limits} {ipc : KBytes}

/-- A successful import changes just the vacant destination under the exact
expected descriptor and stores all the observed rows in order. -/
theorem importParquet_ok_iff :
    importParquet db name expected selected parquetLimits parquet = .ok next ↔
      db name = none ∧ ∃ rows : Scan.Table expected.schema Cell,
        collectParquet parquetLimits parquet selected = .ok ⟨⟨expected.schema, rows⟩, .eos⟩ ∧
        next = Function.update db name (some ⟨expected.schema, rows⟩) :=
  NamedTable.importCollected_ok_iff db next name expected.schema _

theorem importIpc_ok_iff :
    importIpc db name expected ipcLimits viewLimits ipc = .ok next ↔
      db name = none ∧ ∃ rows : Scan.Table expected.schema Cell,
        collectIpc ipcLimits viewLimits ipc = .ok ⟨⟨expected.schema, rows⟩, .eos⟩ ∧
        next = Function.update db name (some ⟨expected.schema, rows⟩) :=
  Proofs.Formats.Relational.NamedTable.Binary.importIpc_ok_iff

/-- Equal complete observations yield the identical named update regardless
of the original page, group, or batch boundaries. -/
theorem imports_equal_of_eos {rows : Scan.Table expected.schema Cell}
    (vacant : db name = none)
    (left : collectParquet parquetLimits parquet selected = .ok ⟨⟨expected.schema, rows⟩, .eos⟩)
    (right : collectIpc ipcLimits viewLimits ipc = .ok ⟨⟨expected.schema, rows⟩, .eos⟩) :
    ∃ next, importParquet db name expected selected parquetLimits parquet = .ok next ∧
      importIpc db name expected ipcLimits viewLimits ipc = .ok next :=
  ⟨_, importParquet_ok_iff.mpr ⟨vacant, rows, left, rfl⟩, importIpc_ok_iff.mpr ⟨vacant, rows, right, rfl⟩⟩

theorem importCollected_conflict {Error : Type*}
    {collected : Except Error (Arrow.Events.Observation String Cell Error)}
    (occupied : (db name).isSome = true) :
    NamedTable.importCollected db name expected.schema collected = .error .nameConflict := by
  simp [NamedTable.importCollected, occupied]

theorem importCollected_closed {Error : Type*} {completed : Observation} (vacant : db name = none) :
    NamedTable.importCollected db name expected.schema (.ok ⟨completed, .closed⟩ :
      Except Error (Arrow.Events.Observation String Cell Error)) = .error .closed := by
  simp [NamedTable.importCollected, vacant]

theorem importCollected_close_error {Error : Type*} {completed : Observation} {cause : Error}
    (vacant : db name = none) :
    NamedTable.importCollected db name expected.schema (.ok ⟨completed, .closeError cause⟩) =
      .error (.closeError cause) := by
  simp [NamedTable.importCollected, vacant]

theorem importCollected_descriptor_error {Error : Type*} {actual : Observation}
    (vacant : db name = none) (different : expected.schema ≠ actual.schema) :
    NamedTable.importCollected db name expected.schema (.ok ⟨actual, .eos⟩ :
      Except Error (Arrow.Events.Observation String Cell Error)) = .error .schemaMismatch := by
  have rejected : NamedTable.schemaMatches expected.schema actual.schema = false := by
    simpa [Bool.eq_false_iff] using different
  simp [NamedTable.importCollected, vacant, rejected]

theorem importParquet_descriptor_error {actual : Observation} (vacant : db name = none)
    (read : collectParquet parquetLimits parquet selected = .ok ⟨actual, .eos⟩)
    (different : expected.schema ≠ actual.schema) :
    importParquet db name expected selected parquetLimits parquet = .error .schemaMismatch := by
  rw [importParquet, read]
  exact importCollected_descriptor_error vacant different

theorem importIpc_descriptor_error {actual : Observation} (vacant : db name = none)
    (read : collectIpc ipcLimits viewLimits ipc = .ok ⟨actual, .eos⟩)
    (different : expected.schema ≠ actual.schema) :
    importIpc db name expected ipcLimits viewLimits ipc = .error .schemaMismatch := by
  rw [importIpc, read, importCollected_descriptor_error vacant different]
  rfl

theorem importParquet_open_error {cause : File.Error} (vacant : db name = none)
    (failure : File.openFile parquetLimits parquet selected.name (layoutOf selected) = .error cause) :
    importParquet db name expected selected parquetLimits parquet = .error (.openError cause) := by
  rw [importParquet, collectParquet, ParquetFile.readAll_open_error failure]
  simp [Arrow.Events.EventStream.collect, Except.map, NamedTable.importCollected, vacant]

/-- Even a previously successful prefix cannot produce a named update after
the selected file encounters its first indexed read failure. -/
theorem importParquet_first_error {checked : File.Checked selected.name (layoutOf selected)}
    {before after : List Nat} {index : Nat}
    {groups : List (List (Option Bytes))} {cause : Parquet.FlatColumn.Error File.PageError}
    (vacant : db name = none)
    (opened : File.openFile parquetLimits parquet selected.name (layoutOf selected) = .ok checked)
    (indices : List.range checked.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (checked.readGroup parquetLimits) = .ok groups)
    (failure : checked.readGroup parquetLimits index = .error cause) :
    importParquet db name expected selected parquetLimits parquet = .error (.readError (.column cause)) := by
  rw [importParquet, collectParquet_first_error opened indices earlier failure]
  simp [NamedTable.importCollected, vacant]

theorem importIpc_open_error {cause : Stream.Error} (vacant : db name = none)
    (failure : Stream.read ipcLimits viewLimits ipc = .error cause)
    (beforeBatches : ∀ index detail, cause ≠ .batch index detail) :
    importIpc db name expected ipcLimits viewLimits ipc = .error (.openError (.reader cause)) := by
  cases cause <;> simp_all [importIpc, collectIpc, NamedTable.importCollected, Except.mapError]

/-- A read failure returns its exact IPC batch index and underlying error. -/
theorem importIpc_batch_error {index : Nat} {cause : Stream.BatchError} (vacant : db name = none)
    (failure : Stream.read ipcLimits viewLimits ipc = .error (.batch index cause)) :
    importIpc db name expected ipcLimits viewLimits ipc = .error (.readError (.reader (.batch index cause))) := by
  simp [importIpc, collectIpc, NamedTable.importCollected, Except.mapError, vacant, failure]

end Silmaril.Formats.Relational.NamedTable.Binary
