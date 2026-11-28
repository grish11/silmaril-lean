module

public import Silmaril.Formats.Parquet.Snapshot.Defs
import all Silmaril.Formats.Parquet.Snapshot.Defs
import Silmaril.Formats.Parquet.Footer.Validation.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Snapshot

open Silmaril.Formats Silmaril.Formats.Parquet

private theorem bind_ok {ε : Type*} {α β : Type} {input : Except ε α} {f : α → Except ε β} {out : β}
    (success : (input >>= f) = .ok out) : ∃ a, input = .ok a ∧ f a = .ok out := by
  cases input with
  | error _ => cases success
  | ok a => exact ⟨a, rfl, success⟩

private theorem mapError_ok {ε δ α : Type*} {input : Except ε α} {f : ε → δ} {out : α}
    (success : input.mapError f = .ok out) : input = .ok out := by
  cases input with
  | error _ => cases success
  | ok a => cases success; rfl

theorem check_rowCounts {Failure : Type*} {limits : Snapshot.Limits} {source : Bytes}
    {snapshot : Snapshot.Checked}
    (checked : Snapshot.check (Failure := Failure) limits source = .ok snapshot) :
    snapshot.metadata.numRows.toNat = ((List.range snapshot.groupCount).map fun index =>
      ((snapshot.groupAt index).map (·.numRows.toNat)).getD 0).sum := by
  unfold Snapshot.check at checked
  obtain ⟨⟨footer, metadata⟩, _, checked⟩ := bind_ok checked
  obtain ⟨_, valid, checked⟩ := bind_ok checked
  cases checked
  rw [Footer.validate_rowCounts (mapError_ok valid)]
  congr 1
  apply List.ext_getElem
  · simp [Snapshot.Checked.groupCount]
  · intro index inGroups inRange
    have bounded : index < metadata.rowGroups.length := by simpa using inGroups
    simp [Snapshot.Checked.groupAt, getElem?_pos metadata.rowGroups index bounded]

end Silmaril.Proofs.Formats.Parquet.Snapshot
