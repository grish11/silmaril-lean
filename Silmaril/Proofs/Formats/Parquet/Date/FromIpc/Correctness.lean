module

public import Silmaril.Formats.Parquet.Date.FromIpc.Defs
import Silmaril.Formats.Parquet.Date.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.FromIpc

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Date.FromIpc

private theorem certify_ok {limits : Date.Limits} {wire output : Bytes}
    {field : Arrow.DateStream.Field} {dates : Arrow.DateValues.Column}
    (certified : Internal.certify limits wire field dates = .ok output) :
    ∃ checked group, Date.openChecked limits output = .ok checked ∧
      Date.readGroup limits output 0 = .ok group ∧ Matches checked group field dates := by
  cases opened : Date.openChecked limits wire with
  | error cause => simp [Internal.certify, opened, Except.mapError, Bind.bind, Except.bind] at certified
  | ok checked =>
    cases read : checked.readGroup limits 0 with
    | error cause =>
      simp [Internal.certify, opened, read, Except.mapError, Bind.bind, Except.bind] at certified
    | ok group =>
      by_cases agrees : Matches checked group field dates
      · simp [Internal.certify, opened, read, agrees, Except.mapError, Bind.bind, Except.bind] at certified
        subst output
        exact ⟨checked, group, opened, by simp [Date.readGroup, opened, read, Bind.bind, Except.bind],
          agrees⟩
      · simp [Internal.certify, opened, read, agrees, Except.mapError, Bind.bind, Except.bind] at certified

theorem convert_readback {inputLimits : Arrow.Limits} {writerLimits : FlatInt32Writer.Limits}
    {readbackLimits : Date.Limits} {input : KBytes} {wire : Bytes}
    (written : convert inputLimits writerLimits readbackLimits input = .ok wire) :
    ∃ source dates checked group,
      Arrow.DateStream.read inputLimits input = .ok source ∧
      source.field.unit = .day ∧ source.batches = [dates] ∧
      Date.openChecked readbackLimits wire = .ok checked ∧
      Date.readGroup readbackLimits wire 0 = .ok group ∧ Matches checked group source.field dates := by
  cases read : Arrow.DateStream.read inputLimits input with
  | error cause => simp [convert, read, Except.mapError, Bind.bind, Except.bind] at written
  | ok source =>
    by_cases day : source.field.unit = .day
    · cases batches : source.batches with
      | nil => simp [convert, read, day, batches, Except.mapError, Bind.bind, Except.bind] at written
      | cons dates tail =>
        cases tail with
        | cons other rest =>
          simp [convert, read, day, batches, Except.mapError, Bind.bind, Except.bind] at written
        | nil =>
          cases page : Internal.pageInput source.field.nullable dates with
          | error cause =>
            simp [convert, read, day, batches, page, Except.mapError, Bind.bind, Except.bind] at written
          | ok body =>
            cases write : FlatInt32Writer.emitAnnotated .date writerLimits
                ⟨dates.length, [⟨source.field.name, body⟩]⟩ with
            | error cause =>
              simp [convert, read, day, batches, page, write, Except.mapError, Bind.bind, Except.bind]
                at written
            | ok output =>
              simp [convert, read, day, batches, page, write, Except.mapError, Bind.bind, Except.bind]
                at written
              obtain ⟨checked, group, opened, decoded, agrees⟩ := certify_ok written
              exact ⟨source, dates, checked, group, rfl, day, batches, opened, decoded, agrees⟩
    · simp [convert, read, day, Except.mapError, Bind.bind, Except.bind] at written

theorem convert_batchCount {inputLimits : Arrow.Limits} {writerLimits : FlatInt32Writer.Limits}
    {readbackLimits : Date.Limits} {input : KBytes} {source : Arrow.DateStream.Stream}
    (read : Arrow.DateStream.read inputLimits input = .ok source)
    (unit : source.field.unit = .day) (count : source.batches.length ≠ 1) :
    convert inputLimits writerLimits readbackLimits input = .error (.batchCount source.batches.length) := by
  cases batches : source.batches with
  | nil => simp [convert, read, unit, batches, Except.mapError, Bind.bind, Except.bind]
  | cons first tail =>
    cases tail with
    | nil => simp [batches] at count
    | cons second rest =>
      simp [convert, read, unit, batches, Except.mapError, Bind.bind, Except.bind]

theorem Matches.exactWords {checked : Date.Checked} {group : Date.RowGroup}
    {field : Arrow.DateStream.Field} {dates : Arrow.DateValues.Column}
    (agrees : Matches checked group field dates) :
    group.date32Slots = dates.map (fun slot => slot.bind DateInterop.Date32.ofCivil?) := by
  rw [← group.date32_civil, agrees.2.2.2.2]

end Silmaril.Proofs.Formats.Parquet.Date.FromIpc
