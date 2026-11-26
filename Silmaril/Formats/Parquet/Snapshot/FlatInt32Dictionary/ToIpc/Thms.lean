module

public import Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary.ToIpc.Defs
import Silmaril.Proofs.Formats.Parquet.Snapshot.FlatInt32Dictionary.ToIpc.Correctness

/-! Exact descriptors, indexed group order, IPC readback and source failure. -/

public section

namespace Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary.ToIpc

open Silmaril.Relational
open FlatInt32 (Cell)

/-- Each writer batch has the checked physical fields in order. -/
theorem batchInput_fields (fields : List FlatScan.Field) (rows : Reader.RowGroup (schema fields) Cell) :
    (batchInput fields rows).fields = fields.map ipcField :=
  Proofs.Formats.Parquet.Snapshot.FlatInt32Dictionary.ToIpc.batchInput_fields fields rows

/-- The writer input preserves each signed INT32 or null slot in row order. -/
theorem batchInput_observe (fields : List FlatScan.Field) (rows : Reader.RowGroup (schema fields) Cell) :
    (batchInput fields rows).observe = ipcRows fields rows :=
  Proofs.Formats.Parquet.Snapshot.FlatInt32Dictionary.ToIpc.batchInput_observe fields rows

/-- Successful open uses the original checked snapshot, the exact expected
field list and the existing dictionary-aware decoder. -/
theorem openSource_checked {limits : FlatInt32Dictionary.Limits} {expected : List Arrow.Field}
    {input : Bytes} {bound : Bound} (opened : openSource limits expected input = .ok bound) :
    input.length ≤ limits.maxFileBytes ∧
      Snapshot.check (Failure := FlatInt32Dictionary.Error) limits.plain.snapshot input =
        .ok bound.snapshot ∧
      FlatScan.flatSchema (ε := Unit) limits.plain.groups bound.snapshot.metadata.schema = .ok bound.fields ∧
      bound.fields.map ipcField = expected ∧
      FlatInt32Dictionary.bind limits (schema bound.fields) bound.snapshot.metadata = .ok bound.decode :=
  Proofs.Formats.Parquet.Snapshot.FlatInt32Dictionary.ToIpc.openSource_checked opened

/-- Successful materialization gives one row list per footer index. The row
list at each position is the exact result of reading that group. -/
theorem readGroups_indexed {bound : Bound} {groups : List (Reader.RowGroup (schema bound.fields) Cell)}
    (read : bound.readGroups = .ok groups) :
    groups.length = bound.snapshot.groupCount ∧
      ∀ i : Fin groups.length, bound.snapshot.readGroup bound.decode i.val = .ok (groups.get i) :=
  Proofs.Formats.Parquet.Snapshot.FlatInt32Dictionary.ToIpc.readGroups_indexed read

/-- Success requires checked admission, successful reads of every group and
checked emission under the requested IPC limits. -/
theorem convert_ok_iff {limits : FlatInt32Dictionary.Limits} {ipc : Arrow.ObservationLimits}
    {expected : List Arrow.Field} {input : Bytes} {wire : KBytes} :
    convert limits ipc expected input = .ok wire ↔ ∃ bound groups,
      openSource limits expected input = .ok bound ∧ bound.readGroups = .ok groups ∧
      Arrow.StreamWriter.emit ipc expected (groups.map (batchInput bound.fields)) = .ok wire :=
  Proofs.Formats.Parquet.Snapshot.FlatInt32Dictionary.ToIpc.convert_ok_iff

/-- Readback gives the exact checked descriptor and one batch per footer
group. Metadata counts and nullable rows are preserved, including empty
groups and flattened order. -/
theorem convert_readback {limits : FlatInt32Dictionary.Limits} {ipc : Arrow.ObservationLimits}
    {expected : List Arrow.Field} {input : Bytes} {wire : KBytes}
    (converted : convert limits ipc expected input = .ok wire) :
    ∃ (bound : Bound) (groups : List (Reader.RowGroup (schema bound.fields) Cell))
      (stream : Arrow.Stream),
      openSource limits expected input = .ok bound ∧
      bound.fields.map ipcField = expected ∧
      bound.readGroups = .ok groups ∧
      groups.length = bound.snapshot.groupCount ∧
      (∀ i : Fin groups.length, bound.snapshot.readGroup bound.decode i.val = .ok (groups.get i)) ∧
      Arrow.readStream ipc.ipc wire = .ok stream ∧ stream.fields = expected ∧
      stream.batches.map (·.metadata.rowCount) = groups.map List.length ∧
      Arrow.readRows ipc wire = .ok ⟨expected, groups.map (ipcRows bound.fields)⟩ ∧
      (groups.map (ipcRows bound.fields)).flatten = ipcRows bound.fields groups.flatten :=
  Proofs.Formats.Parquet.Snapshot.FlatInt32Dictionary.ToIpc.convert_readback converted

/-- A checked source-open failure is returned with its original cause. -/
theorem convert_open_error {limits : FlatInt32Dictionary.Limits} {ipc : Arrow.ObservationLimits}
    {expected : List Arrow.Field} {input : Bytes} {cause : SourceError}
    (failed : openSource limits expected input = .error (.source cause)) :
    convert limits ipc expected input = .error (.source cause) := by
  simp [convert, failed, Bind.bind, Except.bind]

/-- The first indexed failure retains earlier rows in the abstract events.
Conversion returns that exact cause without a completed IPC stream. -/
theorem convert_first_error {limits : FlatInt32Dictionary.Limits} {ipc : Arrow.ObservationLimits}
    {expected : List Arrow.Field} {input : Bytes} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List (Reader.RowGroup (schema bound.fields) Cell)}
    {cause : SourceError}
    (opened : openSource limits expected input = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (bound.snapshot.readGroup bound.decode) = .ok groups)
    (failed : bound.snapshot.readGroup bound.decode index = .error cause) :
    convert limits ipc expected input = .error (.source cause) ∧
      (bound.snapshot.readAll bound.decode).collect =
        .ok ⟨⟨schema bound.fields, groups.flatten⟩, .readError cause⟩ :=
  Proofs.Formats.Parquet.Snapshot.FlatInt32Dictionary.ToIpc.convert_first_error
    opened split earlier failed

end Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary.ToIpc
