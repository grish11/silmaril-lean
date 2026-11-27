module

public import Silmaril.Formats.Parquet.FlatScan.Defs
import Silmaril.Proofs.Formats.Parquet.FlatScan.Counts
public import Batteries.Data.List.Basic
import Silmaril.Proofs.Formats.Parquet.FlatScan.Wire

/-! Count guarantees for checked flat Parquet scans. -/

public section

namespace Silmaril.Formats.Parquet.FlatScan

/-- A successful strict scan consumes the exact chunk frames and appends the
callback's nullable words in wire order. The strict path rejects page CRCs. -/
theorem scanColumn_wire {ε : Type} {limits : Limits} {decoder : DecodePage ε}
    {source : Bytes} {footerStart rows : Nat} {field : Field}
    {column : Footer.ColumnChunk} {result : ColumnValues rows}
    (scanned : scanColumn limits decoder source footerStart field rows column = .ok result) :
    ∃ span frames pages, Page.columnSpan footerStart column.metadata = some span ∧
      Page.readChunk limits.page source span = .ok frames ∧
      List.Forall₂ (fun frame values => frame.value.crc = none ∧ decoder field frame.value
        (Footer.fileBytes source frame.payload.start frame.payload.stop) = .ok values) frames pages ∧
      result.cells.toList = pages.flatten :=
  Proofs.Formats.Parquet.FlatScan.scanColumn_wire scanned

/-- Every decoded column carries exactly the row count requested when scanning it. -/
theorem column_count {rowCount : Nat} (column : ColumnValues rowCount) :
    column.cells.size = rowCount := column.sized

/-- Row assembly keeps the explicit row count, including when there are no columns. -/
theorem rows_length (batch : Batch) : batch.rows.length = batch.rowCount :=
  Proofs.Formats.Parquet.FlatScan.rows_length batch

/-- Success preserves both row-group dimensions regardless of the callback. -/
theorem scanRowGroup_dimensions {ε : Type} {limits : Limits} {decoder : DecodePage ε}
    {source : Bytes} {footerStart : Nat} {schema : List Footer.SchemaElement} {group : Footer.RowGroup}
    {batch : Batch} (parsed : scanRowGroup limits decoder source footerStart schema group = .ok batch) :
    batch.rows.length = group.numRows.toNat ∧ batch.columns.length = group.columns.length :=
  Proofs.Formats.Parquet.FlatScan.scanRowGroup_dimensions parsed

/-- Every assembled row has one cell per scanned column. -/
theorem rows_width (batch : Batch) (row : List (Option Int32)) (present : row ∈ batch.rows) :
    row.length = batch.columns.length :=
  Proofs.Formats.Parquet.FlatScan.rows_width batch row present

/-- Reuse a recovered footer when its version, row counts and group index
pass the file-level checks. -/
theorem scanFileRowGroup_of_footer {ε : Type} {limits : Limits} {decoder : DecodePage ε}
    {source : Bytes} {footer : Footer.Span} {metadata : Footer.Metadata} {index : Nat}
    {group : Footer.RowGroup}
    (read : Footer.readFooter limits.footer source = .ok (footer, metadata))
    (version : metadata.version = 1 ∨ metadata.version = 2)
    (counts : (metadata.rowGroups.all fun group => 0 ≤ group.numRows) = true)
    (total : (metadata.rowGroups.map (·.numRows)).sum = metadata.numRows)
    (found : metadata.rowGroups[index]? = some group) :
    scanFileRowGroup limits decoder source index =
      scanRowGroup limits decoder source footer.start metadata.schema group :=
  Proofs.Formats.Parquet.FlatScan.scanFileRowGroup_of_footer read version counts total found

end Silmaril.Formats.Parquet.FlatScan
