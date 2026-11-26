module

public import Silmaril.Formats.Parquet.FlatInt32Writer.Readback.Defs
public import Batteries.Data.List.Basic
import Silmaril.Proofs.Formats.Parquet.FlatInt32Writer.Readback.Decode

/-! Compose exact emitted page slices with the scan's INT32 decoder. -/

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

end Silmaril.Formats.Parquet.FlatInt32Writer
