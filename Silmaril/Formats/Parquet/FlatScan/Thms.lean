module

public import Silmaril.Formats.Parquet.FlatScan.Defs
import Silmaril.Proofs.Formats.Parquet.FlatScan.Counts

/-! Count guarantees for checked flat Parquet scans. -/

public section

namespace Silmaril.Formats.Parquet.FlatScan

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

end Silmaril.Formats.Parquet.FlatScan
