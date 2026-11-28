module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.Defs
import Silmaril.Formats.ColumnarTimestamp.Thms
import Silmaril.Formats.Parquet.Reader.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Events

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf.Events
open Silmaril.Relational Silmaril.Numeric.Timestamp

theorem metadata_exact (bound : Leaf.Bound) :
    let descriptor := bound.binding.descriptor
    (metadata bound).unit = descriptor.unit.tickUnit ∧
      (metadata bound).timezone = (if descriptor.isAdjustedToUTC then some "UTC" else none) ∧
      (metadata bound).kind = descriptor.kind :=
  ⟨rfl, rfl, bound.binding.descriptor.arrow_kind _⟩

theorem batch_slots (bound : Leaf.Bound) (slots : Leaf.Slots bound)
    (field : Fin (schema bound).width) :
    (AlignedColumns.ofRows (rows bound slots)).rowCount = slots.length ∧
      ((AlignedColumns.ofRows (rows bound slots)).values field).map (Option.map Ticks.ticks) =
        slots.map (Option.map Ticks.ticks) := by
  constructor
  · simp [AlignedColumns.ofRows, rows]
  · simp [AlignedColumns.ofRows, rows, List.map_map, Function.comp_def, Option.map_map]

private theorem openSource_of_opened {snapshotLimits : Snapshot.Limits} {limits : Leaf.Limits}
    {input : Bytes} {ordinal : Nat} {bound : Leaf.Bound}
    (opened : Leaf.openLeaf snapshotLimits input ordinal = .ok bound) :
    openSource snapshotLimits limits ordinal input = .ok ⟨schema bound, groupSource limits bound⟩ := by
  simp [openSource, opened, Except.mapError, Except.map]

theorem readAll_open_error {snapshotLimits : Snapshot.Limits} {limits : Leaf.Limits}
    {input : Bytes} {ordinal : Nat} {cause : Leaf.Error}
    (failure : Leaf.openLeaf snapshotLimits input ordinal = .error cause) :
    readAll snapshotLimits limits ordinal input = .error (.openFailure cause) := by
  simp [readAll, openSource, failure, Except.mapError, Except.map, Reader.readAll]

private theorem denoteGroups_eq_reference (bound : Leaf.Bound)
    (read : Nat → Except Leaf.Error (Leaf.Slots bound)) (indices : List Nat) :
    Reader.denoteGroups (rowsAtWith bound read) indices =
      let reference := referenceGroupsWith read indices
      (reference.1.map (rows bound), reference.2) := by
  induction indices with
  | nil => rfl
  | cons index following ih =>
    cases result : read index with
    | error => simp [Reader.denoteGroups, rowsAtWith, referenceGroupsWith, result, Except.map, Except.mapError]
    | ok slots =>
      simp [Reader.denoteGroups, rowsAtWith, referenceGroupsWith, result, Except.map, Except.mapError, ih]

theorem readBoundWith_reference (bound : Leaf.Bound) (read : Nat → Except Leaf.Error (Leaf.Slots bound)) :
    let reference := referenceGroupsWith read (List.range bound.snapshot.groupCount)
    readBoundWith bound read = .ok ⟨schema bound,
      ⟨reference.1.map (AlignedColumns.ofRows ∘ rows bound), reference.2⟩⟩ := by
  rw [readBoundWith, Reader.readAll_opened]
  simp [groupSourceWith, denoteGroups_eq_reference, List.map_map]

theorem readBound_reference (limits : Leaf.Limits) (bound : Leaf.Bound) :
    let reference := referenceGroups limits bound (List.range bound.snapshot.groupCount)
    readBound limits bound = .ok ⟨schema bound,
      ⟨reference.1.map (AlignedColumns.ofRows ∘ rows bound), reference.2⟩⟩ :=
  readBoundWith_reference bound (Leaf.readGroup limits bound)

theorem readAll_reference {snapshotLimits : Snapshot.Limits} {limits : Leaf.Limits}
    {input : Bytes} {ordinal : Nat} {bound : Leaf.Bound}
    (opened : Leaf.openLeaf snapshotLimits input ordinal = .ok bound) :
    let reference := referenceGroups limits bound (List.range bound.snapshot.groupCount)
    readAll snapshotLimits limits ordinal input = .ok ⟨schema bound,
      ⟨reference.1.map (AlignedColumns.ofRows ∘ rows bound), reference.2⟩⟩ := by
  unfold readAll
  rw [openSource_of_opened opened]
  exact readBound_reference limits bound

theorem collect_readAll {snapshotLimits : Snapshot.Limits} {limits : Leaf.Limits}
    {input : Bytes} {ordinal : Nat} {bound : Leaf.Bound}
    (opened : Leaf.openLeaf snapshotLimits input ordinal = .ok bound) :
    let reference := referenceGroups limits bound (List.range bound.snapshot.groupCount)
    (readAll snapshotLimits limits ordinal input).collect = .ok
      ⟨⟨schema bound, reference.1.flatMap (rows bound)⟩, reference.2⟩ := by
  unfold readAll
  rw [Reader.collect_readAll, openSource_of_opened opened]
  simp [Reader.denote, groupSource, groupSourceWith, referenceGroups, denoteGroups_eq_reference, Except.map, List.flatMap]

private theorem reference_prefix {bound : Leaf.Bound} (read : Nat → Except Leaf.Error (Leaf.Slots bound))
    {indices : List Nat} {groups : List (Leaf.Slots bound)}
    (decoded : indices.mapM read = .ok groups) (tail : List Nat) :
    referenceGroupsWith read (indices ++ tail) =
      let suffix := referenceGroupsWith read tail
      (groups ++ suffix.1, suffix.2) := by
  induction indices generalizing groups with
  | nil =>
    simp [pure, Except.pure] at decoded
    subst groups
    rfl
  | cons index indices ih =>
    cases first : read index with
    | error => simp [List.mapM_cons, first, Bind.bind, Except.bind] at decoded
    | ok group =>
      cases rest : indices.mapM read with
      | error => simp [List.mapM_cons, first, rest, Bind.bind, Except.bind] at decoded
      | ok following =>
        have ordered : group :: following = groups := by
          simpa [List.mapM_cons, first, rest, Bind.bind, Except.bind, pure, Except.pure] using decoded
        subst groups
        simp [referenceGroupsWith, first, ih rest]

theorem readBoundWith_first_error {bound : Leaf.Bound}
    {read : Nat → Except Leaf.Error (Leaf.Slots bound)}
    {before after : List Nat} {index : Nat} {groups : List (Leaf.Slots bound)} {cause : Leaf.Error}
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM read = .ok groups)
    (failed : read index = .error cause) :
    readBoundWith bound read = .ok ⟨schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ rows bound), .readError (.groupFailure index cause)⟩⟩ := by
  rw [readBoundWith_reference bound read, split, reference_prefix read earlier]
  simp [referenceGroupsWith, failed]

theorem readBound_first_error {limits : Leaf.Limits} {bound : Leaf.Bound}
    {before after : List Nat} {index : Nat} {groups : List (Leaf.Slots bound)} {cause : Leaf.Error}
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (Leaf.readGroup limits bound) = .ok groups)
    (failed : Leaf.readGroup limits bound index = .error cause) :
    readBound limits bound = .ok ⟨schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  readBoundWith_first_error split earlier failed

theorem readAll_first_error {snapshotLimits : Snapshot.Limits} {limits : Leaf.Limits}
    {input : Bytes} {ordinal : Nat} {bound : Leaf.Bound}
    {before after : List Nat} {index : Nat} {groups : List (Leaf.Slots bound)} {cause : Leaf.Error}
    (opened : Leaf.openLeaf snapshotLimits input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (Leaf.readGroup limits bound) = .ok groups)
    (failed : Leaf.readGroup limits bound index = .error cause) :
    readAll snapshotLimits limits ordinal input = .ok ⟨schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ rows bound), .readError (.groupFailure index cause)⟩⟩ := by
  unfold readAll
  rw [openSource_of_opened opened]
  exact readBound_first_error split earlier failed

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Events
