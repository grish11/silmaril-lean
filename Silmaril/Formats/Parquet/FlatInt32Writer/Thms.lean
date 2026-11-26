module

public import Silmaril.Formats.Parquet.FlatInt32Writer.Defs
import Silmaril.Proofs.Formats.Parquet.FlatInt32Writer.Correctness
public import Batteries.Data.List.Basic
import Mathlib.Data.List.Forall2

/-! Exact footer, contiguous chunk index, and per-column page round trip. -/

public section

namespace Silmaril.Formats.Parquet.FlatInt32Writer

/-- A successful writer recovers its exact footer and its ordered chunks cover
the data area from the leading magic to the start of Compact metadata. -/
theorem emit_layout {limits : Limits} {input : Input} {output : Encoded}
    (written : emit limits input = .ok output) :
    input.Valid limits ∧ output.Checked limits input.rowCount ∧
      output.metadata = Compact.metadata input.rowCount (output.chunks.map Chunk.index) ∧
      Contiguous 4 output.chunks output.footer.start ∧
      Footer.Framed limits.footer.maxFooterBytes output.bytes output.footer :=
  Proofs.Formats.Parquet.FlatInt32Writer.emit_layout written

/-- Each declared column appears in order, with a checked singleton page and
the original nullable values decoded from its exact on-disk body. -/
theorem emit_columns {limits : Limits} {input : Input} {output : Encoded}
    (written : emit limits input = .ok output) :
    List.Forall₂ (fun column chunk => chunk.column = column ∧
      chunk.Checked limits output.bytes output.footer.start input.rowCount ∧
      chunk.frame.value = column.values.header ∧ column.values.Fits limits.page ∧
      ScalarPage.decode .int32 column.values.parameters limits.page.scalar
        (Footer.fileBytes output.bytes chunk.frame.payload.start chunk.frame.payload.stop) =
        .ok column.values.slots) input.columns output.chunks :=
  Proofs.Formats.Parquet.FlatInt32Writer.emit_columns written

end Silmaril.Formats.Parquet.FlatInt32Writer
