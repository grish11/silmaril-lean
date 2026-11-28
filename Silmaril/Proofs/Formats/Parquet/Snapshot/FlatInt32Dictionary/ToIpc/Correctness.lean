module

public import Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary.ToIpc.Defs
import Silmaril.Formats.Parquet.Snapshot.Thms
import Silmaril.Formats.Arrow.StreamWriter.Thms
import Mathlib.Data.List.Forall2

public section

namespace Silmaril.Proofs.Formats.Parquet.Snapshot.FlatInt32Dictionary.ToIpc

open Silmaril.Formats Silmaril.Relational
open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Snapshot.FlatInt32 (Cell)
open Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary.ToIpc

private theorem rowsOfColumns_ofFn {width : Nat} (rows : List (Fin width → Option Arrow.Value)) :
    Arrow.Body.rowsOfColumns rows.length (List.ofFn fun i => rows.map (fun row => row i)) =
      rows.map List.ofFn := by
  induction width with
  | zero =>
    change List.replicate rows.length [] = rows.map (fun _ => [])
    exact List.map_const'.symm
  | succ width ih =>
    rw [List.ofFn_succ]
    change List.zipWith List.cons (rows.map fun row => row 0)
      (Arrow.Body.rowsOfColumns rows.length (List.ofFn fun i : Fin width => rows.map (fun row => row i.succ))) = _
    have tail := ih (rows.map fun row (i : Fin width) => row i.succ)
    simp only [List.length_map, List.map_map, Function.comp_def] at tail
    rw [tail, List.zipWith_map, List.zipWith_self]
    simp [List.ofFn_succ]

theorem batchInput_fields (fields : List FlatScan.Field) (rows : Reader.RowGroup (schema fields) Cell) :
    (batchInput fields rows).fields = fields.map ipcField := by
  rw [Arrow.Writer.BatchInput.fields, batchInput, List.map_ofFn]
  change List.ofFn (ipcField ∘ fun i : Fin fields.length => fields[i.val]) = fields.map ipcField
  rw [← List.map_ofFn, List.ofFn_getElem]

theorem batchInput_observe (fields : List FlatScan.Field) (rows : Reader.RowGroup (schema fields) Cell) :
    (batchInput fields rows).observe = ipcRows fields rows := by
  have exactRows := rowsOfColumns_ofFn (rows.map fun row (i : Fin fields.length) => (row i).map Arrow.Value.int32)
  simpa [batchInput, ipcRows, Arrow.Writer.BatchInput.observe, Arrow.Writer.ColumnValues.observe,
    AlignedColumns.ofRows, List.map_ofFn, List.map_map, Function.comp_def] using exactRows

theorem openSource_checked {limits : Parquet.Snapshot.FlatInt32Dictionary.Limits} {expected : List Arrow.Field}
    {input : Bytes} {bound : Bound} (opened : openSource limits expected input = .ok bound) :
    input.length ≤ limits.maxFileBytes ∧
      Snapshot.check (Failure := Snapshot.FlatInt32Dictionary.Error) limits.plain.snapshot input =
        .ok bound.snapshot ∧
      FlatScan.flatSchema (ε := Unit) limits.plain.groups bound.snapshot.metadata.schema = .ok bound.fields ∧
      bound.fields.map ipcField = expected ∧
      Snapshot.FlatInt32Dictionary.bind limits (schema bound.fields) bound.snapshot.metadata = .ok bound.decode := by
  by_cases oversized : limits.maxFileBytes < input.length
  · simp [openSource, oversized, Bind.bind, Except.bind, throw, throwThe] at opened
  · cases checked : Snapshot.check (Failure := Snapshot.FlatInt32Dictionary.Error) limits.plain.snapshot input with
    | error cause => simp [openSource, oversized, checked, Bind.bind, Except.bind, Except.mapError] at opened
    | ok snapshot =>
      cases physical : FlatScan.flatSchema (ε := Unit) limits.plain.groups snapshot.metadata.schema with
      | error cause =>
        simp [openSource, oversized, checked, physical, Bind.bind, Except.bind, Except.mapError] at opened
      | ok fields =>
        by_cases same : fields.map ipcField = expected
        · cases decoder : Snapshot.FlatInt32Dictionary.bind limits (schema fields) snapshot.metadata with
          | error cause =>
            simp [openSource, oversized, checked, physical, same, decoder,
              Bind.bind, Except.bind, Except.mapError] at opened
          | ok decode =>
            simp [openSource, oversized, checked, physical, same, decoder, Bind.bind, Except.bind, Except.mapError,
              pure, Except.pure] at opened
            subst bound
            exact ⟨Nat.le_of_not_gt oversized, rfl, physical, same, decoder⟩
        · simp [openSource, oversized, checked, physical, same, Bind.bind, Except.bind, Except.mapError,
            throw, throwThe] at opened

private theorem mapM_forall₂ {α β ε : Type*} {f : α → Except ε β}
    {source : List α} {output : List β} (read : source.mapM f = .ok output) :
    List.Forall₂ (fun value result => f value = .ok result) source output := by
  induction source generalizing output with
  | nil =>
    have empty : [] = output := Except.ok.inj read
    subst output
    exact .nil
  | cons value rest ih =>
    cases first : f value with
    | error cause => simp [List.mapM_cons, first, Bind.bind, Except.bind] at read
    | ok result =>
      cases tail : rest.mapM f with
      | error cause => simp [List.mapM_cons, first, tail, Bind.bind, Except.bind] at read
      | ok later =>
        have same : result :: later = output := by
          simpa [List.mapM_cons, first, tail, Bind.bind, Except.bind, pure, Except.pure] using read
        subst output
        exact .cons first (ih tail)

theorem readGroups_indexed {bound : Bound} {groups : List (Reader.RowGroup (schema bound.fields) Cell)}
    (read : bound.readGroups = .ok groups) :
    groups.length = bound.snapshot.groupCount ∧
      ∀ i : Fin groups.length, bound.snapshot.readGroup bound.decode i.val = .ok (groups.get i) := by
  have ordered := mapM_forall₂ (show (List.range bound.snapshot.groupCount).mapM
    (bound.snapshot.readGroup bound.decode) = .ok groups from read)
  refine ⟨by simpa using ordered.length_eq.symm, ?_⟩
  intro i
  have valid : i.val < (List.range bound.snapshot.groupCount).length := ordered.length_eq.symm ▸ i.isLt
  simpa [List.get_eq_getElem] using ordered.get valid i.isLt

theorem convert_ok_iff {limits : Snapshot.FlatInt32Dictionary.Limits} {ipc : Arrow.ObservationLimits}
    {expected : List Arrow.Field} {input : Bytes} {wire : KBytes} :
    convert limits ipc expected input = .ok wire ↔ ∃ bound groups,
      openSource limits expected input = .ok bound ∧ bound.readGroups = .ok groups ∧
      Arrow.StreamWriter.emit ipc expected (groups.map (batchInput bound.fields)) = .ok wire := by
  cases opened : openSource limits expected input with
  | error cause => simp [convert, opened, Bind.bind, Except.bind]
  | ok bound =>
    cases read : bound.readGroups with
    | error cause => simp [convert, opened, read, Bind.bind, Except.bind, Except.mapError]
    | ok groups =>
      cases emitted : Arrow.StreamWriter.emit ipc expected (groups.map (batchInput bound.fields)) <;>
        simp [convert, opened, read, emitted, Bind.bind, Except.bind, Except.mapError]

theorem convert_readback {limits : Snapshot.FlatInt32Dictionary.Limits} {ipc : Arrow.ObservationLimits}
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
      (groups.map (ipcRows bound.fields)).flatten = ipcRows bound.fields groups.flatten := by
  obtain ⟨bound, groups, opened, read, emitted⟩ := convert_ok_iff.mp converted
  obtain ⟨stream, framing, fields, counts, observed, _⟩ := Arrow.StreamWriter.emit_roundtrip emitted
  obtain ⟨size, indexed⟩ := readGroups_indexed read
  refine ⟨bound, groups, stream, opened, (openSource_checked opened).2.2.2.1, read, size,
    indexed, framing, fields, ?_, ?_, ?_⟩
  · simpa [List.map_map, Function.comp_def, batchInput, AlignedColumns.ofRows] using counts
  · simpa [List.map_map, Function.comp_def, batchInput_observe] using observed
  · exact (List.map_flatten (L := groups)
      (f := fun row : Scan.Row (schema bound.fields) Cell =>
        List.ofFn fun i : Fin bound.fields.length => (row i).map Arrow.Value.int32)).symm

theorem convert_first_error {limits : Snapshot.FlatInt32Dictionary.Limits} {ipc : Arrow.ObservationLimits}
    {expected : List Arrow.Field} {input : Bytes} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List (Reader.RowGroup (schema bound.fields) Cell)}
    {cause : SourceError}
    (opened : openSource limits expected input = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (bound.snapshot.readGroup bound.decode) = .ok groups)
    (failed : bound.snapshot.readGroup bound.decode index = .error cause) :
    convert limits ipc expected input = .error (.source cause) ∧
      (bound.snapshot.readAll bound.decode).collect =
        .ok ⟨⟨schema bound.fields, groups.flatten⟩, .readError cause⟩ := by
  have stopped : bound.readGroups = .error cause := by
    simp [Bound.readGroups, split, List.mapM_append, earlier, List.mapM_cons, failed, Bind.bind, Except.bind]
  exact ⟨by simp [convert, opened, stopped, Bind.bind, Except.bind, Except.mapError],
    bound.snapshot.collect_readAll_first_error bound.decode before after index groups cause split earlier failed⟩

end Silmaril.Proofs.Formats.Parquet.Snapshot.FlatInt32Dictionary.ToIpc
