module

public import Silmaril.Formats.Parquet.Reader.Defs

public section

namespace Silmaril.Proofs.Formats.Parquet.Reader

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet.Reader

variable {Input Group Id Kind Error : Type*} {Value : Kind → Type*} {schema : Scan.Schema Id Kind}

private theorem pull_prefix (openInput : Input → OpenResult Group Id Value Error)
    (fuel : Nat) (groups : List Group)
    (readGroup : Group → Except Error (RowGroup schema Value))
    (close : List Group → Except Error Unit) (seen : List (Events.Batch schema Value)) :
    Events.BatchReader.read.pull (batchReader openInput) schema fuel ⟨groups, readGroup, close⟩ seen =
      let observed := denoteGroups readGroup (groups.take fuel)
      ⟨seen.reverse ++ observed.1.map AlignedColumns.ofRows,
        match observed.2 with
        | .eos =>
          if fuel ≤ groups.length then
            match close (groups.drop fuel) with
            | .ok () => .closed
            | .error error => .closeError error
          else .eos
        | termination => termination⟩ := by
  induction fuel generalizing groups seen with
  | zero =>
    simp [Events.BatchReader.read.pull, batchReader, denoteGroups]
    rfl
  | succ fuel ih =>
    cases groups with
    | nil => simp [Events.BatchReader.read.pull, batchReader, denoteGroups]
    | cons group groups =>
      cases decoded : readGroup group with
      | error error =>
        simp [Events.BatchReader.read.pull, batchReader, Except.map, denoteGroups, decoded]
      | ok rows =>
        simpa [Events.BatchReader.read.pull, batchReader, Except.map, denoteGroups,
          decoded, List.reverse_cons, List.append_assoc] using ih groups (AlignedColumns.ofRows rows :: seen)

/-- A bounded pull observes one batch per successful attempted group.
After the last budgeted pull it closes the unread suffix. EOS needs an
additional pull, and a failed read terminates with that exact error. -/
theorem read_prefix_opened (openInput : Input → OpenResult Group Id Value Error) (input : Input)
    (fuel : Nat) {source : Source Group schema Value Error} (opened : openInput input = .ok ⟨schema, source⟩) :
    (batchReader openInput).read fuel input =
      let observed := denoteGroups source.readGroup (source.groups.take fuel)
      .ok ⟨schema, ⟨observed.1.map AlignedColumns.ofRows,
        match observed.2 with
        | .eos =>
          if fuel ≤ source.groups.length then
            match source.close (source.groups.drop fuel) with
            | .ok () => .closed
            | .error error => .closeError error
          else .eos
        | termination => termination⟩⟩ := by
  unfold Events.BatchReader.read
  change (openInput input).map _ = _
  rw [opened]
  cases source with
  | mk groups readGroup close =>
    simp [Except.map, pull_prefix]
    rfl

end Silmaril.Proofs.Formats.Parquet.Reader
