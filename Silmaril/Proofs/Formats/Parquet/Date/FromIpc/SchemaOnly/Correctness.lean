module

public import Silmaril.Formats.Parquet.Date.FromIpc.SchemaOnly.Defs
public import Silmaril.Formats.Parquet.Date.RoundTrip.Defs
import Silmaril.Formats.Parquet.Date.Events.Thms
import Silmaril.Prelude.Bytes.Digits.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.FromIpc.SchemaOnly

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Date.FromIpc.SchemaOnly
open Silmaril.Formats.Parquet.Date.FromIpc.SchemaOnly.Internal

theorem encode_extent {limits : Limits} {field : Arrow.DateStream.Field} {wire : Bytes}
    (written : encode limits field = .ok wire) :
    ∃ footer, FlatInt32Writer.Compact.encodeGroups .date (footerLimit limits) [columnIndex field] [] =
        .ok footer ∧ wire = frame footer ∧ footer.length ≤ footerLimit limits ∧
      wire.length = footer.length + 12 ∧ wire.length ≤ fileLimit limits := by
  simp only [encode, Bind.bind, Except.bind] at written
  split at written
  · contradiction
  split at written
  · contradiction
  rename_i noSchema noRoom
  cases made : FlatInt32Writer.Compact.encodeGroups .date (footerLimit limits) [columnIndex field] [] with
  | error cause => simp [made, Except.mapError] at written
  | ok footer =>
    by_cases tooLong : footerLimit limits < footer.length
    · simp [made, tooLong, Except.mapError] at written
    · simp [made, tooLong, Except.mapError, Pure.pure, Except.pure] at written
      subst wire
      have exactLength : (frame footer).length = footer.length + 12 := by
        simp [frame, Footer.magic, KBytes.length_unpack]
        omega
      have bounded := Nat.le_of_not_gt tooLong
      refine ⟨footer, rfl, rfl, bounded, exactLength, ?_⟩
      have residual := bounded.trans (Nat.min_le_right _ _)
      rw [exactLength]
      omega

private theorem observes {limits : Date.Limits} {wire : Bytes} {checked : Date.Checked}
    {field : Arrow.DateStream.Field} (opened : Date.openChecked limits wire = .ok checked)
    (agrees : Matches checked field) :
    Date.RoundTrip.ParquetObserves limits wire ⟨field.name, field.nullable, []⟩ ∧
      Date.Events.readAll limits wire = .ok ⟨Date.Events.schema checked, ⟨[], .eos⟩⟩ := by
  have noGroups : (List.range checked.snapshot.groupCount).mapM (checked.readGroup limits) = .ok [] := by
    simp [agrees.2.1, Pure.pure, Except.pure]
  have label : checked.binding.leaf.name = field.name :=
    congrArg Footer.SchemaElement.name agrees.2.2.2.1
  have nullable : (checked.binding.leaf.repetition == some .optional) = field.nullable := by
    have same := congrArg (fun leaf : Footer.SchemaElement => leaf.repetition == some .optional)
      agrees.2.2.2.1
    cases flag : field.nullable <;> simpa [Date.FromIpc.leaf, flag] using same
  exact ⟨⟨checked, [], opened, noGroups, by simp [label, nullable]⟩,
    (Date.Events.readAll_eof_iff opened []).mpr ⟨[], noGroups, rfl⟩⟩

theorem convert_readback {inputLimits : Arrow.Limits} {writerLimits : Limits}
    {readbackLimits : Date.Limits} {input : KBytes} {wire : Bytes}
    (written : convert inputLimits writerLimits readbackLimits input = .ok wire) :
    ∃ field checked,
      Arrow.DateStream.read inputLimits input = .ok ⟨field, []⟩ ∧ field.unit = .day ∧
      encode writerLimits field = .ok wire ∧ Date.openChecked readbackLimits wire = .ok checked ∧
      Matches checked field ∧ Date.RoundTrip.ParquetObserves readbackLimits wire ⟨field.name, field.nullable, []⟩ ∧
      Date.Events.readAll readbackLimits wire = .ok ⟨Date.Events.schema checked, ⟨[], .eos⟩⟩ := by
  cases read : Arrow.DateStream.read inputLimits input with
  | error cause => simp [convert, read, Except.mapError, Bind.bind, Except.bind] at written
  | ok source =>
    by_cases day : source.field.unit = .day
    · cases batches : source.batches with
      | cons first rest =>
        simp [convert, read, day, batches, Except.mapError, Bind.bind, Except.bind] at written
      | nil =>
        cases encoded : encode writerLimits source.field with
        | error cause =>
          simp [convert, read, day, batches, encoded, Except.mapError, Bind.bind, Except.bind] at written
        | ok raw =>
          cases opened : Date.openChecked readbackLimits raw with
          | error cause =>
            simp [convert, read, day, batches, encoded, opened, Except.mapError, Bind.bind, Except.bind] at written
          | ok checked =>
            by_cases agrees : Matches checked source.field
            · simp [convert, read, day, batches, encoded, opened, agrees, Except.mapError,
                Bind.bind, Except.bind] at written
              subst wire
              have shape : source = ⟨source.field, []⟩ := by cases source; congr
              exact ⟨source.field, checked, congrArg Except.ok shape, day, encoded, opened, agrees,
                observes opened agrees⟩
            · simp [convert, read, day, batches, encoded, opened, agrees, Except.mapError,
                Bind.bind, Except.bind] at written
    · simp [convert, read, day, Except.mapError, Bind.bind, Except.bind] at written

theorem convert_nonempty {inputLimits : Arrow.Limits} {writerLimits : Limits}
    {readbackLimits : Date.Limits} {input : KBytes} {source : Arrow.DateStream.Stream}
    (read : Arrow.DateStream.read inputLimits input = .ok source)
    (day : source.field.unit = .day) (record : source.batches ≠ []) :
    convert inputLimits writerLimits readbackLimits input = .error (.batchCount source.batches.length) := by
  cases batches : source.batches with
  | nil => exact (record batches).elim
  | cons first rest => simp [convert, read, day, batches, Except.mapError, Bind.bind, Except.bind]

end Silmaril.Proofs.Formats.Parquet.Date.FromIpc.SchemaOnly
