module

public import Silmaril.Formats.Parquet.Snapshot.FlatInt32.Defs
import all Silmaril.Formats.Parquet.Snapshot.FlatInt32.Defs
import Silmaril.Formats.Parquet.Snapshot.Thms
import Silmaril.Formats.Parquet.FlatScan.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Snapshot.FlatInt32

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet Silmaril.Formats
open Silmaril.Formats.Parquet.Snapshot.FlatInt32

private theorem typedRows (schema : Scan.Schema String Unit) (source : List (List (Option Int32)))
    (rectangular : ∀ row ∈ source, List.length row = schema.width) :
    ∃ rows, source.mapM (typedRow (InputFailure := Unit) schema) = .ok rows ∧
      rows.map List.ofFn = source := by
  induction source with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons head tail ih =>
    have width := rectangular head List.mem_cons_self
    let row : Scan.Row schema Cell := fun index => head[index.val]'(width.symm ▸ index.isLt)
    obtain ⟨rows, decoded, observed⟩ := ih (fun row mem => rectangular row (List.mem_cons_of_mem _ mem))
    have headDecoded : typedRow (InputFailure := Unit) schema head = .ok row := by
      simp [typedRow, width, row]
    have headObserved : List.ofFn row = head := by
      apply List.ext_getElem
      · simp [width]
      · intro index left right
        simp [row]
    refine ⟨row :: rows, ?_, ?_⟩
    · rw [List.mapM_cons, headDecoded, decoded]
      rfl
    · simp only [List.map_cons, headObserved, observed]

/-- Exact physical names and a rectangular one-group scan yield a single
typed Arrow batch and EOS. The schema-indexed rows recover the scanned cells. -/
theorem readAll_single {limits : Limits} {schema : Scan.Schema String Unit} {bytes : Bytes}
    {footer : Footer.Span} {metadata : Footer.Metadata} {group : Footer.RowGroup}
    {fields : List FlatScan.Field} {batch : FlatScan.Batch}
    (read : Footer.readFooter limits.snapshot.footer bytes = .ok (footer, metadata))
    (valid : Footer.validate footer.start limits.snapshot.maxSchemaDepth metadata = .ok ())
    (single : metadata.rowGroups = [group])
    (prepared : FlatScan.flatSchema (ε := FlatScan.AdapterError) limits.groups metadata.schema = .ok fields)
    (names : List.ofFn (fun index => (schema.kind index).1) = fields.map (·.name))
    (run : FlatScan.scanRowGroup limits.groups (FlatScan.decodeInt32Page limits.pages)
      bytes footer.start metadata.schema group = .ok batch)
    (width : batch.columns.length = schema.width) :
    ∃ rows : Scan.Table schema Cell, rows.map List.ofFn = batch.rows ∧
      Silmaril.Formats.Parquet.Snapshot.FlatInt32.readAll limits schema bytes =
        .ok ⟨schema, ⟨[AlignedColumns.ofRows rows], .eos⟩⟩ := by
  obtain ⟨rows, typed, seen⟩ := typedRows schema batch.rows
    (fun row mem => (FlatScan.rows_width batch row mem).trans width)
  let decode : Snapshot.DecodeGroup schema Cell (Error Unit) := fun snapshot _ group => do
    let result ← (FlatScan.scanRowGroup limits.groups (FlatScan.decodeInt32Page limits.pages)
      snapshot.bytes snapshot.footer.start metadata.schema group).mapError .profile
    result.rows.mapM (typedRow schema)
  have bound : bind limits schema metadata = .ok decode := by
    simp [Silmaril.Formats.Parquet.Snapshot.FlatInt32.bind, prepared, names, decode,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have decoded (snapshot : Snapshot.Checked) (source : snapshot.bytes = bytes)
      (span : snapshot.footer = footer) : decode snapshot 0 group = .ok rows := by
    simp [decode, source, span, run, typed, Except.mapError, Bind.bind, Except.bind]
  have count : rows.length = group.numRows.toNat := by
    simpa using (congrArg List.length seen).trans (FlatScan.scanRowGroup_dimensions run).1
  refine ⟨rows, seen, ?_⟩
  unfold Silmaril.Formats.Parquet.Snapshot.FlatInt32.readAll
  exact Snapshot.readAll_single read valid single bound decoded count

end Silmaril.Proofs.Formats.Parquet.Snapshot.FlatInt32
