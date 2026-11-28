module

public import Silmaril.Formats.Parquet.Int96.Mixed.File.Events.Defs
public import Batteries.Data.List.Basic
import Silmaril.Formats.Parquet.Reader.Thms
import Silmaril.Numeric.Timestamp.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Int96.Mixed.File.Events

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Int96
open Silmaril.Formats.Parquet.Int96.Mixed.File.Events
open Silmaril.Relational Silmaril.Numeric.Timestamp

variable {name : String} {layout : FlatColumn.Layout} {policy : Policy} {target : TickUnit}

theorem metadata_exact (policy : Policy) (target : TickUnit) :
    (metadata policy target).unit = target ∧
      (metadata policy target).timezone = (match policy with | .prolepticUtc => some "UTC" | .prolepticLocal => none) ∧
      (metadata policy target).kind = policy.kind := by
  cases policy <;> exact ⟨rfl, rfl, rfl⟩

theorem schema_field (checked : Mixed.File.Checked name layout policy) (target : TickUnit)
    (field : Fin (schema checked target).width) :
    (schema checked target).kind field = (name, ⟨metadata policy target, layout == .optional⟩) := by
  simp [schema, checked.selection.bound.binding.leafName]

theorem narrowSlot_exact {input : Option (Int96.Page.Value policy)}
    {output : Option (Output policy target)} (decoded : narrowSlot policy target input = .ok output) :
    SlotMatches input output := by
  cases input with
  | none => cases decoded; exact True.intro
  | some value =>
    cases converted : value.toInt64 target with
    | error cause => simp [narrowSlot, converted, Except.map] at decoded
    | ok word =>
      simp [narrowSlot, converted, Except.map] at decoded
      subst output
      refine ⟨?_, word, rfl⟩
      have exactTicks := congrArg Ticks.ticks (Ticks.toInt64_eq_ok_iff.mp converted).symm
      simpa [ColumnarTimestamp.Arrow.Metadata.decode, metadata, Ticks.denote,
        Ticks.ofInt64, TickUnit.nanosecondsPerTick] using exactTicks

theorem narrowSlot_error_iff {input : Int96.Page.Value policy} {cause : ConversionError} :
    narrowSlot policy target (some input) = .error cause ↔ input.toInt64 target = .error cause := by
  cases checked : input.toInt64 target <;> simp [narrowSlot, checked, Except.map]

private theorem narrowSlots_cons (policy : Policy) (target : TickUnit) (input : Option (Int96.Page.Value policy))
    (inputs : Dictionary.Slots policy) (start : Nat) :
    narrowSlots policy target (input :: inputs) start = (do
      let first ← (narrowSlot policy target input).mapError (NarrowError.mk start)
      let rest ← narrowSlots policy target inputs (start + 1)
      pure (first :: rest)) := by
  simp only [narrowSlots, List.zipIdx_cons, List.mapM_cons]

theorem narrowSlots_exact {input : Dictionary.Slots policy} {output : Slots policy target}
    {start : Nat} (decoded : narrowSlots policy target input start = .ok output) :
    List.Forall₂ SlotMatches input output := by
  induction input generalizing start output with
  | nil => cases decoded; exact .nil
  | cons head rest ih =>
    rw [narrowSlots_cons] at decoded
    cases first : narrowSlot policy target head with
    | error cause => simp [first, Bind.bind, Except.bind, Except.mapError] at decoded
    | ok value =>
      cases tail : narrowSlots policy target rest (start + 1) with
      | error cause => simp [first, tail, Bind.bind, Except.bind, Except.mapError] at decoded
      | ok values =>
        simp [first, tail, Bind.bind, Except.bind, Except.mapError, Pure.pure, Except.pure] at decoded
        subst output
        exact .cons (narrowSlot_exact first) (ih tail)

theorem narrowSlots_first_error {input : Dictionary.Slots policy} {start : Nat} {error : NarrowError}
    (failed : narrowSlots policy target input start = .error error) :
    ∃ before bad after, input = before ++ bad :: after ∧ error.slot = start + before.length ∧
      narrowSlot policy target bad = .error error.cause ∧
      ∃ outputs, narrowSlots policy target before start = .ok outputs := by
  induction input generalizing start with
  | nil => simp [narrowSlots, Pure.pure, Except.pure] at failed
  | cons head rest ih =>
    rw [narrowSlots_cons] at failed
    cases first : narrowSlot policy target head with
    | error cause =>
      simp [first, Bind.bind, Except.bind, Except.mapError] at failed
      subst error
      exact ⟨[], head, rest, rfl, by simp, first, [], rfl⟩
    | ok value =>
      have tail : narrowSlots policy target rest (start + 1) = .error error := by
        cases checked : narrowSlots policy target rest (start + 1) <;>
          simp_all [Bind.bind, Except.bind, Except.mapError, Pure.pure, Except.pure]
      obtain ⟨before, bad, after, rfl, position, invalid, outputs, checked⟩ := ih tail
      refine ⟨head :: before, bad, after, rfl, ?_, invalid, value :: outputs, ?_⟩
      · simpa [Nat.add_assoc, Nat.add_comm 1] using position
      · simp [narrowSlots_cons, first, checked, Bind.bind, Except.bind, Except.mapError,
          Pure.pure, Except.pure]

theorem batch_slots (checked : Mixed.File.Checked name layout policy) (target : TickUnit) (slots : Slots policy target)
    (field : Fin (schema checked target).width) :
    (AlignedColumns.ofRows (rows checked target slots)).rowCount = slots.length ∧
      (AlignedColumns.ofRows (rows checked target slots)).values field = slots := by
  constructor
  · exact List.length_map _
  · induction slots with
    | nil => rfl
    | cons head tail ih =>
      change head :: (AlignedColumns.ofRows (rows checked target tail)).values field = head :: tail
      rw [ih]

theorem slotsAt_source_error {checked : Mixed.File.Checked name layout policy} {index : Nat} {cause : Mixed.File.ReadError}
    (failed : checked.readGroup index = .error cause) :
    slotsAt checked target index = .error (.groupFailure index cause) := by
  simp [slotsAt, failed, Bind.bind, Except.bind, Except.mapError]

theorem slotsAt_after_read {checked : Mixed.File.Checked name layout policy} {index : Nat} {slots : Dictionary.Slots policy}
    (decoded : checked.readGroup index = .ok slots) :
    slotsAt checked target index = (narrowSlots policy target slots).mapError (.narrowFailure index) := by
  simp [slotsAt, decoded, Bind.bind, Except.bind, Except.mapError]

private theorem openSource_of_opened {limits : Mixed.File.Limits} {source : Bytes}
    {checked : Mixed.File.Checked name layout policy} (opened : Mixed.File.openFile limits source name layout policy = .ok checked) :
    openSource limits name layout policy target source = .ok ⟨schema checked target, groupSource checked target⟩ := by
  simp [openSource, opened, Except.mapError, Except.map]

theorem readAll_reference {limits : Mixed.File.Limits} {source : Bytes}
    {checked : Mixed.File.Checked name layout policy} (opened : Mixed.File.openFile limits source name layout policy = .ok checked) :
    let reference := Reader.denoteGroups (rowsAt checked target)
      (List.range checked.selection.bound.snapshot.groupCount)
    readAll limits name layout policy target source = .ok ⟨schema checked target,
      ⟨reference.1.map AlignedColumns.ofRows, reference.2⟩⟩ := by
  unfold readAll
  rw [openSource_of_opened opened, Reader.readAll_opened]
  rfl

private theorem denote_first_error {checked : Mixed.File.Checked name layout policy}
    {before after : List Nat} {index : Nat} {groups : List (Slots policy target)} {cause : Error}
    (earlier : before.mapM (slotsAt checked target) = .ok groups)
    (failed : slotsAt checked target index = .error cause) :
    Reader.denoteGroups (rowsAt checked target) (before ++ index :: after) =
      (groups.map (rows checked target), .readError cause) := by
  induction before generalizing groups with
  | nil =>
    simp [Pure.pure, Except.pure] at earlier
    subst groups
    simp [Reader.denoteGroups, rowsAt, failed, Except.map]
  | cons first rest ih =>
    cases observed : slotsAt checked target first with
    | error e => simp [List.mapM_cons, observed, Bind.bind, Except.bind] at earlier
    | ok slots =>
      cases tail : rest.mapM (slotsAt checked target) with
      | error e => simp [List.mapM_cons, observed, tail, Bind.bind, Except.bind] at earlier
      | ok remaining =>
        simp [List.mapM_cons, observed, tail, Bind.bind, Except.bind, Pure.pure, Except.pure] at earlier
        subst groups
        simp [Reader.denoteGroups, rowsAt, observed, Except.map, ih tail]

theorem readAll_first_error {limits : Mixed.File.Limits} {source : Bytes} {checked : Mixed.File.Checked name layout policy}
    {before after : List Nat} {index : Nat} {groups : List (Slots policy target)} {cause : Error}
    (opened : Mixed.File.openFile limits source name layout policy = .ok checked)
    (split : List.range checked.selection.bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (slotsAt checked target) = .ok groups)
    (failed : slotsAt checked target index = .error cause) :
    readAll limits name layout policy target source = .ok ⟨schema checked target,
      ⟨groups.map (AlignedColumns.ofRows ∘ rows checked target), .readError cause⟩⟩ := by
  rw [readAll_reference opened, split, denote_first_error earlier failed]
  simp only [List.map_map]

end Silmaril.Proofs.Formats.Parquet.Int96.Mixed.File.Events
