module

public import Silmaril.Formats.Parquet.Date.FromIpc.Defs
import Silmaril.Proofs.Formats.Parquet.Date.FromIpc.Correctness

public section

namespace Silmaril.Formats.Parquet.Date.FromIpc

/-- Successful conversion has exactly the source's one batch and the matching
checked DATE group at index zero, even when that batch is empty. -/
theorem convert_readback {inputLimits : Arrow.Limits} {writerLimits : FlatInt32Writer.Limits}
    {readbackLimits : Date.Limits} {input : KBytes} {wire : Bytes}
    (written : convert inputLimits writerLimits readbackLimits input = .ok wire) :
    ∃ source dates checked group,
      Arrow.DateStream.read inputLimits input = .ok source ∧
      source.field.unit = .day ∧ source.batches = [dates] ∧
      Date.openChecked readbackLimits wire = .ok checked ∧
      Date.readGroup readbackLimits wire 0 = .ok group ∧ Matches checked group source.field dates :=
  Proofs.Formats.Parquet.Date.FromIpc.convert_readback written

/-- Readback recovers the exact signed day in every present slot and keeps nulls. -/
theorem Matches.exactWords {checked : Date.Checked} {group : Date.RowGroup}
    {field : Arrow.DateStream.Field} {dates : Arrow.DateValues.Column}
    (agrees : Matches checked group field dates) :
    group.date32Slots = dates.map (fun slot => slot.bind DateInterop.Date32.ofCivil?) :=
  Proofs.Formats.Parquet.Date.FromIpc.Matches.exactWords agrees

/-- Source failure takes precedence over the shape and writer budgets. -/
theorem convert_readError {inputLimits : Arrow.Limits} {writerLimits : FlatInt32Writer.Limits}
    {readbackLimits : Date.Limits} {input : KBytes} {cause : Arrow.DateStream.Error}
    (failed : Arrow.DateStream.read inputLimits input = .error cause) :
    convert inputLimits writerLimits readbackLimits input = .error (.reader cause) := by
  simp [convert, failed, Except.mapError, Bind.bind, Except.bind]

/-- A checked Date64 stream always receives the unit error before its batch count is used. -/
theorem convert_wrongUnit {inputLimits : Arrow.Limits} {writerLimits : FlatInt32Writer.Limits}
    {readbackLimits : Date.Limits} {input : KBytes} {source : Arrow.DateStream.Stream}
    (read : Arrow.DateStream.read inputLimits input = .ok source)
    (unit : source.field.unit ≠ .day) :
    convert inputLimits writerLimits readbackLimits input = .error (.wrongUnit source.field.unit) := by
  simp [convert, read, unit, Except.mapError, Bind.bind, Except.bind]

/-- A schema-only stream and one with multiple batches report their respective counts. -/
theorem convert_batchCount {inputLimits : Arrow.Limits} {writerLimits : FlatInt32Writer.Limits}
    {readbackLimits : Date.Limits} {input : KBytes} {source : Arrow.DateStream.Stream}
    (read : Arrow.DateStream.read inputLimits input = .ok source)
    (unit : source.field.unit = .day) (count : source.batches.length ≠ 1) :
    convert inputLimits writerLimits readbackLimits input = .error (.batchCount source.batches.length) :=
  Proofs.Formats.Parquet.Date.FromIpc.convert_batchCount read unit count

end Silmaril.Formats.Parquet.Date.FromIpc
