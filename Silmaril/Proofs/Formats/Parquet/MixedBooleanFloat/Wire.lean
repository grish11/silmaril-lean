module

public import Silmaril.Formats.Parquet.MixedBooleanFloat.Defs
import all Silmaril.Formats.Parquet.MixedBooleanFloat.Defs
import Silmaril.Formats.Parquet.FlatColumn.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.MixedBooleanFloat

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.MixedBooleanFloat
open Silmaril.Relational

private theorem bind_ok {ε α β : Type} {input : Except ε α} {f : α → Except ε β} {out : β}
    (success : (input >>= f) = .ok out) : ∃ a, input = .ok a ∧ f a = .ok out := by
  cases input with
  | error _ => cases success
  | ok a => exact ⟨a, rfl, success⟩

private theorem mapError_ok {ε δ α : Type} {input : Except ε α} {f : ε → δ} {out : α}
    (success : input.mapError f = .ok out) : input = .ok out := by
  cases input with
  | error _ => cases success
  | ok a => cases success; rfl

theorem openFile_snapshot {limits : Limits} {source : Bytes} {booleanName floatName : String}
    {checked : Checked booleanName floatName} (opened : openFile limits source booleanName floatName = .ok checked) :
    Snapshot.check (Failure := Failure) limits.snapshot source = .ok checked.snapshot := by
  unfold openFile at opened
  split at opened <;> try contradiction
  obtain ⟨snapshot, checkedSnapshot, opened⟩ := bind_ok opened
  split at opened <;> try contradiction
  obtain ⟨_, _, opened⟩ := bind_ok opened
  obtain ⟨_, _, opened⟩ := bind_ok opened
  split at opened <;> try contradiction
  cases opened
  exact checkedSnapshot

private theorem align_order {booleanName floatName : String} {index n : Nat}
    {booleans : List (Option Bool)} {floats : List (Option UInt32)}
    {rows : Reader.RowGroup (schema booleanName floatName) Value}
    (aligned : align index n booleans floats = .ok rows) :
    rows.length = n ∧ ∀ i, i < n →
      rows[i]? = some (row (booleans[i]?.join) (floats[i]?.join)) := by
  unfold align at aligned
  dsimp only at aligned
  split at aligned <;> try contradiction
  rename_i lengths
  cases aligned
  refine ⟨List.length_ofFn, fun i h => ?_⟩
  simp only [assemble, List.getElem?_ofFn, h, dite_true, Option.some.injEq]
  have hb : i < booleans.length := by simpa [← lengths.1] using h
  have hf : i < floats.length := by simpa [← lengths.2] using h
  simp [Vector.get, getElem?_pos booleans i hb, getElem?_pos floats i hf]

theorem readGroup_wire {booleanName floatName : String} {checked : Checked booleanName floatName}
    {limits : FlatColumn.Limits} {index : Nat}
    {rows : Reader.RowGroup (schema booleanName floatName) Value}
    (read : checked.readGroup limits index = .ok rows) : checked.GroupWire limits index rows := by
  unfold Checked.readGroup at read
  split at read <;> try contradiction
  rename_i group groupAt
  obtain ⟨booleans, boolsRead, read⟩ := bind_ok read
  obtain ⟨floats, floatsRead, read⟩ := bind_ok read
  obtain ⟨boolGroup, boolWire⟩ := FlatColumn.readColumn_wire (mapError_ok boolsRead)
  obtain ⟨floatGroup, floatWire⟩ := FlatColumn.readColumn_wire (mapError_ok floatsRead)
  have sameGroup {other : Footer.RowGroup}
      (selected : checked.snapshot.groupAt index = some other) : other = group :=
    Option.some.inj (selected.symm.trans groupAt)
  have atBoolean : checked.snapshot.groupAt index = some boolGroup := by
    obtain ⟨_, _, _, _, selected, _⟩ := boolWire
    exact selected
  have atFloat : checked.snapshot.groupAt index = some floatGroup := by
    obtain ⟨_, _, _, _, selected, _⟩ := floatWire
    exact selected
  rw [sameGroup atBoolean] at boolWire
  rw [sameGroup atFloat] at floatWire
  exact ⟨group, booleans, floats, boolWire, floatWire, align_order read⟩

end Silmaril.Proofs.Formats.Parquet.MixedBooleanFloat
