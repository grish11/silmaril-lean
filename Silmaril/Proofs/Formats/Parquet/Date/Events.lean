module

public import Silmaril.Formats.Parquet.Date.Events.Defs
import Silmaril.Formats.Parquet.Date.Thms
import Silmaril.Formats.Parquet.Reader.Thms
import Silmaril.Formats.Parquet.Reader.Pull.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.Events

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Date.Events
open Silmaril.Relational

theorem rowsAt_eq_readGroup {limits : Date.Limits} {source : Bytes} {checked : Date.Checked}
    (opened : Date.openChecked limits source = .ok checked) (index : Nat) :
    rowsAt limits checked index =
      ((Date.readGroup limits source index).map (rows checked)).mapError (.groupFailure index) := by
  rw [rowsAt, checked.readGroup_of_opened opened]

theorem batch_slots (checked : Date.Checked) (group : Date.RowGroup)
    (index : Fin (schema checked).width) :
    (AlignedColumns.ofRows (rows checked group)).values index = group.date32Slots := by
  simp [AlignedColumns.ofRows, rows, List.map_map, Function.comp_def]

theorem openSource_of_checked {limits : Date.Limits} {input : Bytes} {checked : Date.Checked}
    (opened : Date.openChecked limits input = .ok checked) :
    openSource limits input = .ok ⟨schema checked, groupSource limits checked⟩ := by
  simp [openSource, opened, Except.mapError, Except.map]

theorem readAll_open_error {limits : Date.Limits} {input : Bytes} {cause : Date.Error}
    (failure : Date.openChecked limits input = .error cause) :
    readAll limits input = .error (.openFailure cause) := by
  simp [readAll, openSource, failure, Except.mapError, Except.map, Reader.readAll]

theorem readAll_checked {limits : Date.Limits} {input : Bytes} {checked : Date.Checked}
    (opened : Date.openChecked limits input = .ok checked) :
    readAll limits input = .ok ⟨schema checked,
      ⟨(Reader.denoteGroups (rowsAt limits checked) (List.range checked.snapshot.groupCount)).1.map
          AlignedColumns.ofRows,
        (Reader.denoteGroups (rowsAt limits checked) (List.range checked.snapshot.groupCount)).2⟩⟩ := by
  unfold readAll
  rw [openSource_of_checked opened]
  exact Reader.readAll_opened (groupSource limits checked)

private theorem denote_prefix (limits : Date.Limits) (checked : Date.Checked)
    {indices : List Nat} {groups : List Date.RowGroup}
    (decoded : indices.mapM (checked.readGroup limits) = .ok groups) (tail : List Nat) :
    Reader.denoteGroups (rowsAt limits checked) (indices ++ tail) =
      let suffix := Reader.denoteGroups (rowsAt limits checked) tail
      (groups.map (rows checked) ++ suffix.1, suffix.2) := by
  induction indices generalizing groups with
  | nil =>
    simp [pure, Except.pure] at decoded
    subst groups
    rfl
  | cons index indices ih =>
    cases first : checked.readGroup limits index with
    | error => simp [List.mapM_cons, first, Bind.bind, Except.bind] at decoded
    | ok group =>
      cases rest : indices.mapM (checked.readGroup limits) with
      | error => simp [List.mapM_cons, first, rest, Bind.bind, Except.bind] at decoded
      | ok following =>
        have ordered : group :: following = groups := by
          simpa [List.mapM_cons, first, rest, Bind.bind, Except.bind, pure, Except.pure] using decoded
        subst groups
        simp [Reader.denoteGroups, rowsAt, first, Except.map, Except.mapError, ih rest]

private theorem mapM_of_eof (limits : Date.Limits) (checked : Date.Checked) (indices : List Nat)
    (finished : (Reader.denoteGroups (rowsAt limits checked) indices).2 = .eos) :
    ∃ groups, indices.mapM (checked.readGroup limits) = .ok groups := by
  induction indices with
  | nil => exact ⟨[], rfl⟩
  | cons index tail ih =>
    cases first : checked.readGroup limits index with
    | error =>
      simp [Reader.denoteGroups, rowsAt, first, Except.map, Except.mapError] at finished
    | ok group =>
      have trailing : (Reader.denoteGroups (rowsAt limits checked) tail).2 = .eos := by
        simpa [Reader.denoteGroups, rowsAt, first, Except.map, Except.mapError] using finished
      obtain ⟨groups, decoded⟩ := ih trailing
      exact ⟨group :: groups, by simp [List.mapM_cons, first, decoded, Bind.bind, Except.bind,
        pure, Except.pure]⟩

theorem readAll_eof_iff {limits : Date.Limits} {input : Bytes} {checked : Date.Checked}
    (opened : Date.openChecked limits input = .ok checked)
    (batches : List (Arrow.Events.Batch (schema checked) Cell)) :
    readAll limits input = .ok ⟨schema checked, ⟨batches, .eos⟩⟩ ↔
      ∃ groups, (List.range checked.snapshot.groupCount).mapM (checked.readGroup limits) = .ok groups ∧
        batches = groups.map (AlignedColumns.ofRows ∘ rows checked) := by
  let indices := List.range checked.snapshot.groupCount
  rw [readAll_checked opened]
  constructor
  · intro read
    have trace := eq_of_heq (Sigma.mk.inj (Except.ok.inj read)).2
    have finished : (Reader.denoteGroups (rowsAt limits checked) indices).2 = .eos :=
      congrArg Arrow.Events.Trace.termination trace
    obtain ⟨groups, decoded⟩ := mapM_of_eof limits checked indices finished
    have ordered := denote_prefix limits checked decoded []
    rw [List.append_nil] at ordered
    exact ⟨groups, decoded, by
      have same := congrArg Arrow.Events.Trace.batches trace
      simpa [indices, ordered, Reader.denoteGroups, List.map_map] using same.symm⟩
  · rintro ⟨groups, decoded, rfl⟩
    have ordered := denote_prefix limits checked decoded []
    rw [List.append_nil] at ordered
    simp [ordered, Reader.denoteGroups, List.map_map]

theorem readAll_first_error {limits : Date.Limits} {input : Bytes} {checked : Date.Checked}
    {before after : List Nat} {index : Nat} {groups : List Date.RowGroup} {cause : Date.Error}
    (opened : Date.openChecked limits input = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (checked.readGroup limits) = .ok groups)
    (failed : checked.readGroup limits index = .error cause) :
    readAll limits input = .ok ⟨schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ rows checked), .readError (.groupFailure index cause)⟩⟩ := by
  rw [readAll_checked opened, split, denote_prefix limits checked earlier]
  simp [Reader.denoteGroups, rowsAt, failed, Except.map, Except.mapError, List.map_map]

theorem read_prefix_closed {limits : Date.Limits} {input : Bytes} {checked : Date.Checked}
    {fuel : Nat} {groups : List Date.RowGroup}
    (opened : Date.openChecked limits input = .ok checked)
    (budget : fuel ≤ checked.snapshot.groupCount)
    (earlier : ((List.range checked.snapshot.groupCount).take fuel).mapM
      (checked.readGroup limits) = .ok groups) :
    (batchReader limits).read fuel input = .ok ⟨schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ rows checked), .closed⟩⟩ := by
  have ordered := denote_prefix limits checked earlier []
  simp [budget, Reader.denoteGroups] at ordered
  unfold batchReader
  rw [Reader.read_prefix_opened _ _ _ (openSource_of_checked opened)]
  simp [groupSource, ordered, budget, List.map_map]

end Silmaril.Proofs.Formats.Parquet.Date.Events
