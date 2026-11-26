module

public import Silmaril.Formats.Parquet.Snapshot.Defs
import Silmaril.Formats.Parquet.Reader.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Snapshot

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Snapshot

variable {Id Kind Failure : Type*} {Value : Kind → Type*} {schema : Scan.Schema Id Kind}

theorem readGroup_ok_iff (snapshot : Checked) (decode : DecodeGroup schema Value Failure)
    (index : Nat) (rows : Reader.RowGroup schema Value) :
    snapshot.readGroup decode index = .ok rows ↔ ∃ group,
      snapshot.groupAt index = some group ∧ decode snapshot index group = .ok rows ∧
        rows.length = group.numRows.toNat := by
  cases groupAt : snapshot.groupAt index with
  | none => simp [Checked.readGroup, groupAt]
  | some group =>
    cases decoded : decode snapshot index group with
    | error reason => simp [Checked.readGroup, groupAt, decoded]
    | ok actual =>
      by_cases count : actual.length = group.numRows.toNat
      · simp [Checked.readGroup, groupAt, decoded, count]
        intro equal
        rw [← equal, count]
      · simp [Checked.readGroup, groupAt, decoded, count]
        intro equal
        rw [← equal]
        exact count

private theorem denoteGroups_append (read : Nat → Except (Error Failure) (Reader.RowGroup schema Value))
    (before after : List Nat) (groups : List (Reader.RowGroup schema Value))
    (decoded : before.mapM read = .ok groups) :
    Reader.denoteGroups read (before ++ after) =
      (groups ++ (Reader.denoteGroups read after).1, (Reader.denoteGroups read after).2) := by
  induction before generalizing groups with
  | nil =>
    change Except.ok [] = Except.ok groups at decoded
    cases decoded
    simp
  | cons index before ih =>
    cases head : read index with
    | error reason =>
      rw [List.mapM_cons, head] at decoded
      change Except.error reason = Except.ok groups at decoded
      cases decoded
    | ok rows =>
      cases tail : before.mapM read with
      | error reason =>
        rw [List.mapM_cons, head, tail] at decoded
        change Except.error reason = Except.ok groups at decoded
        cases decoded
      | ok rest =>
        rw [List.mapM_cons, head, tail] at decoded
        change Except.ok (rows :: rest) = Except.ok groups at decoded
        cases decoded
        simp [Reader.denoteGroups, head, ih rest tail]

private theorem mapM_ok_of_eof (read : Nat → Except (Error Failure) (Reader.RowGroup schema Value))
    (indices : List Nat) (eof : (Reader.denoteGroups read indices).2 = .eos) :
    indices.mapM read = .ok (Reader.denoteGroups read indices).1 := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    cases head : read index with
    | error reason => simp [Reader.denoteGroups, head] at eof
    | ok rows =>
      simp only [Reader.denoteGroups, head] at eof
      rw [List.mapM_cons, head, ih eof, Reader.denoteGroups, head]
      rfl

theorem collect_readAll_success (snapshot : Checked) (decode : DecodeGroup schema Value Failure)
    (groups : List (Reader.RowGroup schema Value))
    (decoded : (List.range snapshot.groupCount).mapM (snapshot.readGroup decode) = .ok groups) :
    (snapshot.readAll decode).collect = .ok ⟨⟨schema, groups.flatten⟩, .eos⟩ := by
  have ordered := denoteGroups_append (snapshot.readGroup decode) (List.range snapshot.groupCount) [] groups decoded
  simp [Reader.denoteGroups] at ordered
  simp [Checked.readAll, Reader.collect_readAll, Reader.denote, Checked.source, Except.map, ordered]

theorem collect_readAll_eof (snapshot : Checked) (decode : DecodeGroup schema Value Failure)
    (observation : Events.Observation Id Value (Error Failure))
    (collected : (snapshot.readAll decode).collect = .ok observation)
    (eof : observation.termination = .eos) :
    ∃ groups, (List.range snapshot.groupCount).mapM (snapshot.readGroup decode) = .ok groups ∧
      observation = ⟨⟨schema, groups.flatten⟩, .eos⟩ := by
  simp [Checked.readAll, Reader.collect_readAll, Reader.denote, Checked.source, Except.map] at collected
  subst observation
  exact ⟨_, mapM_ok_of_eof _ _ eof, congrArg (Events.Observation.mk _) eof⟩

theorem collect_readAll_first_error (snapshot : Checked) (decode : DecodeGroup schema Value Failure)
    (before after : List Nat) (index : Nat) (groups : List (Reader.RowGroup schema Value))
    (error : Error Failure) (split : List.range snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (snapshot.readGroup decode) = .ok groups)
    (failed : snapshot.readGroup decode index = .error error) :
    (snapshot.readAll decode).collect = .ok ⟨⟨schema, groups.flatten⟩, .readError error⟩ := by
  simp [Checked.readAll, Reader.collect_readAll, Reader.denote, Checked.source, Except.map, split,
    denoteGroups_append _ before (index :: after) groups earlier, Reader.denoteGroups, failed]

end Silmaril.Proofs.Formats.Parquet.Snapshot
