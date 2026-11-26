module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.Defs
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Events

public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Events

open Silmaril.Relational Silmaril.Numeric.Timestamp

/-- Exact unit and timezone policy, with the same epoch interpretation. -/
theorem metadata_exact (bound : Bound) :
    let descriptor := bound.binding.descriptor
    (metadata bound).unit = descriptor.unit.tickUnit ∧
      (metadata bound).timezone = (if descriptor.isAdjustedToUTC then some "UTC" else none) ∧
      (metadata bound).kind = descriptor.kind :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.metadata_exact bound

/-- The sole field retains the selected Parquet name and nullability. -/
theorem schema_field (bound : Bound) (field : Fin (schema bound).width) :
    (schema bound).kind field = (bound.binding.leaf.name,
      ⟨metadata bound, bound.binding.leaf.repetition == some .optional⟩) := rfl

/-- An emitted batch has one row per nullable slot, with the original counts. -/
theorem batch_slots (bound : Bound) (slots : Slots bound) (field : Fin (schema bound).width) :
    (AlignedColumns.ofRows (rows bound slots)).rowCount = slots.length ∧
      ((AlignedColumns.ofRows (rows bound slots)).values field).map (Option.map Ticks.ticks) =
        slots.map (Option.map Ticks.ticks) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.batch_slots bound slots field

/-- Open errors have no schema or batches. -/
theorem readAll_open_error {snapshotLimits : Snapshot.Limits} {limits : Leaf.Limits}
    {input : Bytes} {ordinal : Nat} {cause : Leaf.Error}
    (failure : Leaf.openLeaf snapshotLimits input ordinal = .error cause) :
    readAll snapshotLimits limits ordinal input = .error (.openFailure cause) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.readAll_open_error failure

/-- Events from a retained leaf agree with its checked footer-order reads
under the annotation selected at bind time. -/
theorem readBound_reference (limits : Leaf.Limits) (bound : Bound) :
    let reference := referenceGroups limits bound (List.range bound.snapshot.groupCount)
    readBound limits bound = .ok ⟨schema bound,
      ⟨reference.1.map (AlignedColumns.ofRows ∘ rows bound), reference.2⟩⟩ :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.readBound_reference limits bound

/-- The trace contains one batch per successful binder read in footer order,
including successful zero-row reads. -/
theorem readAll_reference {snapshotLimits : Snapshot.Limits} {limits : Leaf.Limits}
    {input : Bytes} {ordinal : Nat} {bound : Bound}
    (opened : Leaf.openLeaf snapshotLimits input ordinal = .ok bound) :
    let reference := referenceGroups limits bound (List.range bound.snapshot.groupCount)
    readAll snapshotLimits limits ordinal input = .ok ⟨schema bound,
      ⟨reference.1.map (AlignedColumns.ofRows ∘ rows bound), reference.2⟩⟩ :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.readAll_reference opened

/-- Collection observes the same schema, ordered nullable rows and terminal
outcome as the reference reads on the retained snapshot. -/
theorem collect_readAll {snapshotLimits : Snapshot.Limits} {limits : Leaf.Limits}
    {input : Bytes} {ordinal : Nat} {bound : Bound}
    (opened : Leaf.openLeaf snapshotLimits input ordinal = .ok bound) :
    let reference := referenceGroups limits bound (List.range bound.snapshot.groupCount)
    (readAll snapshotLimits limits ordinal input).collect = .ok
      ⟨⟨schema bound, reference.1.flatMap (rows bound)⟩, reference.2⟩ :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.collect_readAll opened

/-- A failed read on the retained leaf keeps every preceding complete batch. -/
theorem readBound_first_error {limits : Leaf.Limits} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List (Slots bound)} {cause : Leaf.Error}
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (Leaf.readGroup limits bound) = .ok groups)
    (failed : Leaf.readGroup limits bound index = .error cause) :
    readBound limits bound = .ok ⟨schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.readBound_first_error split earlier failed

/-- A failed binder read preserves the complete batches before its footer index. -/
theorem readAll_first_error {snapshotLimits : Snapshot.Limits} {limits : Leaf.Limits}
    {input : Bytes} {ordinal : Nat} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List (Slots bound)} {cause : Leaf.Error}
    (opened : Leaf.openLeaf snapshotLimits input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (Leaf.readGroup limits bound) = .ok groups)
    (failed : Leaf.readGroup limits bound index = .error cause) :
    readAll snapshotLimits limits ordinal input = .ok ⟨schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.readAll_first_error opened split earlier failed

end Silmaril.Formats.Parquet.Timestamp.Leaf.Events
