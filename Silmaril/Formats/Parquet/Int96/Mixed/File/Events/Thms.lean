module

public import Silmaril.Formats.Parquet.Int96.Mixed.File.Events.Defs
public import Batteries.Data.List.Basic
import Silmaril.Proofs.Formats.Parquet.Int96.Mixed.File.Events.Read

public section

namespace Silmaril.Formats.Parquet.Int96.Mixed.File.Events

open Silmaril.Relational Silmaril.Numeric.Timestamp

variable {name : String} {layout : FlatColumn.Layout} {policy : Policy} {target : TickUnit}

/-- The requested unit and caller policy determine exact Arrow metadata. -/
theorem metadata_exact (policy : Policy) (target : TickUnit) :
    (metadata policy target).unit = target ∧
      (metadata policy target).timezone = (match policy with | .prolepticUtc => some "UTC" | .prolepticLocal => none) ∧
      (metadata policy target).kind = policy.kind :=
  Proofs.Formats.Parquet.Int96.Mixed.File.Events.metadata_exact policy target

/-- The one event field retains the selected name and layout. -/
theorem schema_field (checked : Mixed.File.Checked name layout policy) (target : TickUnit)
    (field : Fin (schema checked target).width) :
    (schema checked target).kind field = (name, ⟨metadata policy target, layout == .optional⟩) :=
  Proofs.Formats.Parquet.Int96.Mixed.File.Events.schema_field checked target field

/-- Success preserves a null or the exact signed nanosecond coordinate,
with a representable Arrow payload. -/
theorem narrowSlot_exact {input : Option (Int96.Page.Value policy)}
    {output : Option (Output policy target)} (decoded : narrowSlot policy target input = .ok output) :
    SlotMatches input output :=
  Proofs.Formats.Parquet.Int96.Mixed.File.Events.narrowSlot_exact decoded

/-- The original precision or range refusal passes through unchanged. -/
theorem narrowSlot_error_iff {input : Int96.Page.Value policy} {cause : ConversionError} :
    narrowSlot policy target (some input) = .error cause ↔ input.toInt64 target = .error cause :=
  Proofs.Formats.Parquet.Int96.Mixed.File.Events.narrowSlot_error_iff

/-- Successful narrowing preserves the entire ordered nullable slot list. -/
theorem narrowSlots_exact {input : Dictionary.Slots policy} {output : Slots policy target}
    {start : Nat} (decoded : narrowSlots policy target input start = .ok output) :
    List.Forall₂ SlotMatches input output :=
  Proofs.Formats.Parquet.Int96.Mixed.File.Events.narrowSlots_exact decoded

/-- A failed slot reports the first narrowing error and counts preceding nulls. -/
theorem narrowSlots_first_error {input : Dictionary.Slots policy} {start : Nat} {error : NarrowError}
    (failed : narrowSlots policy target input start = .error error) :
    ∃ before bad after, input = before ++ bad :: after ∧ error.slot = start + before.length ∧
      narrowSlot policy target bad = .error error.cause ∧
      ∃ outputs, narrowSlots policy target before start = .ok outputs :=
  Proofs.Formats.Parquet.Int96.Mixed.File.Events.narrowSlots_first_error failed

/-- A batch preserves every narrowed slot, including an empty successful group. -/
theorem batch_slots (checked : Mixed.File.Checked name layout policy) (target : TickUnit) (slots : Slots policy target)
    (field : Fin (schema checked target).width) :
    (AlignedColumns.ofRows (rows checked target slots)).rowCount = slots.length ∧
      (AlignedColumns.ofRows (rows checked target slots)).values field = slots :=
  Proofs.Formats.Parquet.Int96.Mixed.File.Events.batch_slots checked target slots field

/-- A failed original group read is returned before any group narrowing. -/
theorem slotsAt_source_error {checked : Mixed.File.Checked name layout policy} {index : Nat} {cause : Mixed.File.ReadError}
    (failed : checked.readGroup index = .error cause) :
    slotsAt checked target index = .error (.groupFailure index cause) :=
  Proofs.Formats.Parquet.Int96.Mixed.File.Events.slotsAt_source_error failed

/-- A successfully decoded group is narrowed in its original slot order. -/
theorem slotsAt_after_read {checked : Mixed.File.Checked name layout policy} {index : Nat} {slots : Dictionary.Slots policy}
    (decoded : checked.readGroup index = .ok slots) :
    slotsAt checked target index = (narrowSlots policy target slots).mapError (.narrowFailure index) :=
  Proofs.Formats.Parquet.Int96.Mixed.File.Events.slotsAt_after_read decoded

/-- The event trace has one batch per successful reference group read, in footer order. -/
theorem readAll_reference {limits : Mixed.File.Limits} {source : Bytes}
    {checked : Mixed.File.Checked name layout policy} (opened : Mixed.File.openFile limits source name layout policy = .ok checked) :
    let reference := Reader.denoteGroups (rowsAt checked target)
      (List.range checked.selection.bound.snapshot.groupCount)
    readAll limits name layout policy target source = .ok ⟨schema checked target,
      ⟨reference.1.map AlignedColumns.ofRows, reference.2⟩⟩ :=
  Proofs.Formats.Parquet.Int96.Mixed.File.Events.readAll_reference opened

/-- A failed original read or narrowing retains exactly the preceding batches. -/
theorem readAll_first_error {limits : Mixed.File.Limits} {source : Bytes} {checked : Mixed.File.Checked name layout policy}
    {before after : List Nat} {index : Nat} {groups : List (Slots policy target)} {cause : Error}
    (opened : Mixed.File.openFile limits source name layout policy = .ok checked)
    (split : List.range checked.selection.bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (slotsAt checked target) = .ok groups)
    (failed : slotsAt checked target index = .error cause) :
    readAll limits name layout policy target source = .ok ⟨schema checked target,
      ⟨groups.map (AlignedColumns.ofRows ∘ rows checked target), .readError cause⟩⟩ :=
  Proofs.Formats.Parquet.Int96.Mixed.File.Events.readAll_first_error opened split earlier failed

end Silmaril.Formats.Parquet.Int96.Mixed.File.Events
