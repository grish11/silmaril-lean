module

public import Silmaril.Formats.Parquet.FlatInt32Writer.Readback.Defs
public import Batteries.Data.List.Basic
import Silmaril.Formats.Parquet.FlatInt32Writer.Thms
import Mathlib.Data.List.Forall2

public section

namespace Silmaril.Proofs.Formats.Parquet.FlatInt32Writer.Readback

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.FlatInt32Writer

theorem emit_decodeScanPages {limits : Limits} {input : Input} {output : Encoded}
    (written : emit limits input = .ok output) :
    List.Forall₂ (fun column chunk => chunk.column = column ∧
      Page.readChunk limits.pageReader output.bytes chunk.index.span = .ok [chunk.frame] ∧
      FlatScan.decodeInt32Page limits.page.scalar column.scanField chunk.frame.value
        (Footer.fileBytes output.bytes chunk.frame.payload.start chunk.frame.payload.stop) =
        .ok column.values.slots) input.columns output.chunks := by
  refine (emit_columns written).imp ?_
  intro column chunk related
  obtain ⟨same, checked, header, _, decoded⟩ := related
  refine ⟨same, checked.2.1, ?_⟩
  rw [header]
  let body := Footer.fileBytes output.bytes chunk.frame.payload.start chunk.frame.payload.stop
  have callback : FlatScan.decodeInt32Page limits.page.scalar column.scanField column.values.header body =
      (ScalarPage.decode .int32 column.values.parameters limits.page.scalar body).mapError FlatScan.AdapterError.scalar := by
    rcases column with ⟨name, values⟩
    cases values <;> simp [FlatScan.decodeInt32Page_v1, Column.scanField, PlainV1Writer.Input.header,
      PlainV1Writer.Input.parameters, PlainV1Writer.Input.schema, Payload.Codec.id]
  rw [callback, decoded]
  rfl

end Silmaril.Proofs.Formats.Parquet.FlatInt32Writer.Readback
