module

public import Silmaril.Formats.Parquet.Date.FromIpc.SchemaOnly.Defs
public import Silmaril.Formats.Parquet.Date.RoundTrip.Defs
import Silmaril.Proofs.Formats.Parquet.Date.FromIpc.SchemaOnly.Correctness

public section

namespace Silmaril.Formats.Parquet.Date.FromIpc.SchemaOnly

open Silmaril.Formats.Parquet.Date.FromIpc.SchemaOnly.Internal

/-- The entire data region is empty. The only payload is the bounded
Compact footer with one DATE leaf and an empty row-group list. -/
theorem encode_extent {limits : Limits} {field : Arrow.DateStream.Field} {wire : Bytes}
    (written : encode limits field = .ok wire) :
    ∃ footer, FlatInt32Writer.Compact.encodeGroups .date (footerLimit limits) [columnIndex field] [] =
        .ok footer ∧ wire = frame footer ∧ footer.length ≤ footerLimit limits ∧
      wire.length = footer.length + 12 ∧ wire.length ≤ fileLimit limits :=
  Proofs.Formats.Parquet.Date.FromIpc.SchemaOnly.encode_extent written

/-- Successful conversion preserves the one Date32 descriptor and observes
zero groups through EOF. The checked footer starts immediately after PAR1. -/
theorem convert_readback {inputLimits : Arrow.Limits} {writerLimits : Limits}
    {readbackLimits : Date.Limits} {input : KBytes} {wire : Bytes}
    (written : convert inputLimits writerLimits readbackLimits input = .ok wire) :
    ∃ field checked,
      Arrow.DateStream.read inputLimits input = .ok ⟨field, []⟩ ∧ field.unit = .day ∧
      encode writerLimits field = .ok wire ∧ Date.openChecked readbackLimits wire = .ok checked ∧
      Matches checked field ∧ Date.RoundTrip.ParquetObserves readbackLimits wire ⟨field.name, field.nullable, []⟩ ∧
      Date.Events.readAll readbackLimits wire = .ok ⟨Date.Events.schema checked, ⟨[], .eos⟩⟩ :=
  Proofs.Formats.Parquet.Date.FromIpc.SchemaOnly.convert_readback written

/-- A real record batch is refused by this bridge even when it carries zero rows. -/
theorem convert_nonempty {inputLimits : Arrow.Limits} {writerLimits : Limits}
    {readbackLimits : Date.Limits} {input : KBytes} {source : Arrow.DateStream.Stream}
    (read : Arrow.DateStream.read inputLimits input = .ok source)
    (day : source.field.unit = .day) (record : source.batches ≠ []) :
    convert inputLimits writerLimits readbackLimits input = .error (.batchCount source.batches.length) :=
  Proofs.Formats.Parquet.Date.FromIpc.SchemaOnly.convert_nonempty read day record

/-- Source failures take precedence over shape and writer checks. -/
theorem convert_readError {inputLimits : Arrow.Limits} {writerLimits : Limits}
    {readbackLimits : Date.Limits} {input : KBytes} {cause : Arrow.DateStream.Error}
    (failed : Arrow.DateStream.read inputLimits input = .error cause) :
    convert inputLimits writerLimits readbackLimits input = .error (.reader cause) := by
  simp [convert, failed, Except.mapError, Bind.bind, Except.bind]

end Silmaril.Formats.Parquet.Date.FromIpc.SchemaOnly
