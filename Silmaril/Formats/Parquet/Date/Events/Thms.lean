module

public import Silmaril.Formats.Parquet.Date.Events.Defs
import Silmaril.Proofs.Formats.Parquet.Date.Events

public section

namespace Silmaril.Formats.Parquet.Date.Events

open Silmaril.Relational

/-- The one-field Arrow schema retains the DATE leaf's label and repetition. -/
theorem schema_field (checked : Date.Checked) (index : Fin (schema checked).width) :
    (schema checked).kind index =
      (checked.binding.leaf.name, .date32 (checked.binding.leaf.repetition == some .optional)) :=
  rfl

/-- A source pull uses the existing DATE group observation and preserves its typed error. -/
theorem rowsAt_eq_readGroup {limits : Date.Limits} {source : Bytes} {checked : Date.Checked}
    (opened : Date.openChecked limits source = .ok checked) (index : Nat) :
    rowsAt limits checked index =
      ((Date.readGroup limits source index).map (rows checked)).mapError (.groupFailure index) :=
  Proofs.Formats.Parquet.Date.Events.rowsAt_eq_readGroup opened index

/-- Each Arrow batch exposes exactly its original nullable Date32 words in order. -/
theorem batch_slots (checked : Date.Checked) (group : Date.RowGroup)
    (index : Fin (schema checked).width) :
    (AlignedColumns.ofRows (rows checked group)).values index = group.date32Slots :=
  Proofs.Formats.Parquet.Date.Events.batch_slots checked group index

/-- The successful open retains the checked DATE capability in the source. -/
theorem openSource_of_checked {limits : Date.Limits} {input : Bytes} {checked : Date.Checked}
    (opened : Date.openChecked limits input = .ok checked) :
    openSource limits input = .ok ⟨schema checked, groupSource limits checked⟩ :=
  Proofs.Formats.Parquet.Date.Events.openSource_of_checked opened

/-- An open failure occurs before there is a schema or any batch. -/
theorem readAll_open_error {limits : Date.Limits} {input : Bytes} {cause : Date.Error}
    (failure : Date.openChecked limits input = .error cause) :
    readAll limits input = .error (.openFailure cause) :=
  Proofs.Formats.Parquet.Date.Events.readAll_open_error failure

/-- Read the retained snapshot indices through the generic ordered group denotation. -/
theorem readAll_checked {limits : Date.Limits} {input : Bytes} {checked : Date.Checked}
    (opened : Date.openChecked limits input = .ok checked) :
    readAll limits input = .ok ⟨schema checked,
      ⟨(Reader.denoteGroups (rowsAt limits checked) (List.range checked.snapshot.groupCount)).1.map
          AlignedColumns.ofRows,
        (Reader.denoteGroups (rowsAt limits checked) (List.range checked.snapshot.groupCount)).2⟩⟩ :=
  Proofs.Formats.Parquet.Date.Events.readAll_checked opened

/-- EOF certifies all footer groups and their exact ordered Arrow batches. -/
theorem readAll_eof_iff {limits : Date.Limits} {input : Bytes} {checked : Date.Checked}
    (opened : Date.openChecked limits input = .ok checked)
    (batches : List (Arrow.Events.Batch (schema checked) Cell)) :
    readAll limits input = .ok ⟨schema checked, ⟨batches, .eos⟩⟩ ↔
      ∃ groups, (List.range checked.snapshot.groupCount).mapM (checked.readGroup limits) = .ok groups ∧
        batches = groups.map (AlignedColumns.ofRows ∘ rows checked) :=
  Proofs.Formats.Parquet.Date.Events.readAll_eof_iff opened batches

/-- A late error preserves exactly the earlier complete batches and the indexed cause. -/
theorem readAll_first_error {limits : Date.Limits} {input : Bytes} {checked : Date.Checked}
    {before after : List Nat} {index : Nat} {groups : List Date.RowGroup} {cause : Date.Error}
    (opened : Date.openChecked limits input = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (checked.readGroup limits) = .ok groups)
    (failed : checked.readGroup limits index = .error cause) :
    readAll limits input = .ok ⟨schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ rows checked), .readError (.groupFailure index cause)⟩⟩ :=
  Proofs.Formats.Parquet.Date.Events.readAll_first_error opened split earlier failed

/-- Closing at the pull budget depends only on the decoded prefix. -/
theorem read_prefix_closed {limits : Date.Limits} {input : Bytes} {checked : Date.Checked}
    {fuel : Nat} {groups : List Date.RowGroup}
    (opened : Date.openChecked limits input = .ok checked)
    (budget : fuel ≤ checked.snapshot.groupCount)
    (earlier : ((List.range checked.snapshot.groupCount).take fuel).mapM
      (checked.readGroup limits) = .ok groups) :
    (batchReader limits).read fuel input = .ok ⟨schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ rows checked), .closed⟩⟩ :=
  Proofs.Formats.Parquet.Date.Events.read_prefix_closed opened budget earlier

end Silmaril.Formats.Parquet.Date.Events
