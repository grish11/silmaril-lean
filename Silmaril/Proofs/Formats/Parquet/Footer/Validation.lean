module

public import Silmaril.Formats.Parquet.Footer.Validation.Defs
import all Silmaril.Formats.Parquet.Footer.Validation.Defs

public section

namespace Silmaril.Proofs.Formats.Parquet.Footer

open Silmaril.Formats.Parquet.Footer

private theorem bind_ok {ε α β : Type} {input : Except ε α} {f : α → Except ε β} {out : β}
    (success : (input >>= f) = .ok out) : ∃ a, input = .ok a ∧ f a = .ok out := by
  cases input with
  | error _ => cases success
  | ok a => exact ⟨a, rfl, success⟩

private theorem counts_loop (step : RowGroup → Int → Except ValidationError (ForInStep Int))
    (checkedStep : ∀ group n s, step group n = .ok s → 0 ≤ group.numRows ∧ s = .yield (n + group.numRows)) :
    ∀ (groups : List RowGroup) (initial : Int) {total : Int},
      forIn groups initial step = .ok total →
      total = initial + (groups.map (·.numRows)).sum ∧ ∀ group ∈ groups, 0 ≤ group.numRows
  | [], _, _, success => by
    cases success
    simp
  | group :: groups, initial, _, success => by
    rw [List.forIn_cons] at success
    obtain ⟨next, hstep, success⟩ := bind_ok success
    obtain ⟨positive, rfl⟩ := checkedStep group initial next hstep
    obtain ⟨sum, nonnegative⟩ := counts_loop step checkedStep groups (initial + group.numRows) success
    constructor
    · simpa [Int.add_assoc] using sum
    · intro other mem
      rcases List.mem_cons.mp mem with rfl | later
      · exact positive
      · exact nonnegative other later

private theorem validated_signed_sum {start depth : Nat} {metadata : Metadata}
    (success : validate start depth metadata = .ok ()) :
    metadata.numRows = (metadata.rowGroups.map (·.numRows)).sum ∧
    ∀ group ∈ metadata.rowGroups, 0 ≤ group.numRows := by
  unfold validate at success
  split at success <;> try contradiction
  obtain ⟨_, _, success⟩ := bind_ok success
  obtain ⟨_, iter, success⟩ := bind_ok success
  dsimp only at success
  split at success <;> try contradiction
  rename_i equal
  have checked := counts_loop _ ?_ _ _ iter
  · exact ⟨(not_not.mp equal).symm.trans (by simpa using checked.1), checked.2⟩
  · intro group rows next read
    dsimp only at read
    split at read <;> try contradiction
    rename_i nonnegative
    split at read <;> try contradiction
    split at read <;> try contradiction
    obtain ⟨_, _, read⟩ := bind_ok read
    cases read
    exact ⟨Int.le_of_not_gt nonnegative, rfl⟩

private theorem counts_toNat (groups : List RowGroup) (nonnegative : ∀ group ∈ groups, 0 ≤ group.numRows) :
    (0 ≤ (groups.map RowGroup.numRows).sum) ∧
    (groups.map RowGroup.numRows).sum.toNat = (groups.map (fun group : RowGroup => group.numRows.toNat)).sum := by
  induction groups with
  | nil => exact ⟨Int.le_refl 0, rfl⟩
  | cons group groups ih =>
    obtain ⟨tailSign, tail⟩ := ih (fun other mem => nonnegative other (List.mem_cons_of_mem _ mem))
    have head := nonnegative group List.mem_cons_self
    simp only [List.map_cons, List.sum_cons]
    exact ⟨Int.add_nonneg head tailSign, by rw [Int.toNat_add head tailSign, tail]⟩

theorem validate_rowCounts {start depth : Nat} {metadata : Metadata}
    (success : validate start depth metadata = .ok ()) :
    metadata.numRows.toNat = (metadata.rowGroups.map (·.numRows.toNat)).sum := by
  obtain ⟨h, nonnegative⟩ := validated_signed_sum success
  exact (congrArg Int.toNat h).trans (counts_toNat _ nonnegative).2

end Silmaril.Proofs.Formats.Parquet.Footer
