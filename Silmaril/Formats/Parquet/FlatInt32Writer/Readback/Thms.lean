module

public import Silmaril.Formats.Parquet.FlatInt32Writer.Readback.Defs
public import Batteries.Data.List.Basic
import Silmaril.Proofs.Formats.Parquet.FlatInt32Writer.Readback.Decode
import Silmaril.Proofs.Formats.Parquet.FlatInt32Writer.Readback.Scan

/-! Read back emitted pages and complete files with the checked flat INT32 scanner. -/

public section

namespace Silmaril.Formats.Parquet.FlatInt32Writer

theorem emit_decodeScanPages {limits : Limits} {input : Input} {output : Encoded}
    (written : emit limits input = .ok output) :
    List.Forall₂ (fun column chunk => chunk.column = column ∧
      Page.readChunk limits.pageReader output.bytes chunk.index.span = .ok [chunk.frame] ∧
      FlatScan.decodeInt32Page limits.page.scalar column.scanField chunk.frame.value
        (Footer.fileBytes output.bytes chunk.frame.payload.start chunk.frame.payload.stop) =
        .ok column.values.slots) input.columns output.chunks :=
  Proofs.Formats.Parquet.FlatInt32Writer.Readback.emit_decodeScanPages written

/-- A successful write yields the exact ordered fields, nullable cells and
rows when read from file bytes by the checked scanner. The explicit count is
preserved, including an empty row group. -/
theorem emit_scanFileRowGroup {limits : Limits} {input : Input} {output : Encoded}
    (written : emit limits input = .ok output) :
    ∃ batch, FlatScan.scanFileRowGroup (limits.scanLimits input) (FlatScan.decodeInt32Page limits.page.scalar)
      output.bytes 0 = .ok batch ∧ batch.rowCount = input.rowCount ∧
      batch.columns.map (fun (field, cells) => (field, cells.cells.toList)) =
        input.columns.map Column.scanObservation ∧ batch.rows = input.rows :=
  Proofs.Formats.Parquet.FlatInt32Writer.Readback.emit_scanFileRowGroup written

end Silmaril.Formats.Parquet.FlatInt32Writer

