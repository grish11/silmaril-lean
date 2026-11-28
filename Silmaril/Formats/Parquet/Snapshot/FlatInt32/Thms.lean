module

public import Silmaril.Formats.Parquet.Snapshot.FlatInt32.Defs
import Silmaril.Proofs.Formats.Parquet.Snapshot.FlatInt32.Correctness

public section

namespace Silmaril.Formats.Parquet.Snapshot.FlatInt32

open Silmaril.Relational

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
      readAll limits schema bytes =
        .ok ⟨schema, ⟨[AlignedColumns.ofRows rows], .eos⟩⟩ :=
  Proofs.Formats.Parquet.Snapshot.FlatInt32.readAll_single read valid single prepared names run width

end Silmaril.Formats.Parquet.Snapshot.FlatInt32
