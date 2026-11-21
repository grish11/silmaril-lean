module

public import Silmaril.Wasm.Component.Reference.ABI.Layout.Defs

public section

namespace Silmaril.Proofs.Wasm.Component.Reference.LayoutBounds

open Silmaril.Wasm.Component.ABI

private theorem align_ge (cursor : Nat) (alignment : Alignment) : cursor ≤ alignTo cursor alignment := by
  cases alignment <;> simp only [alignTo, Alignment.bytes] <;> omega

private theorem align_mod (cursor : Nat) (alignment : Alignment) :
    alignTo cursor alignment % alignment.bytes = 0 := by
  simp only [alignTo, Nat.mul_mod_left]

private theorem align_shift (base cursor : Nat) (alignment : Alignment) (aligned : alignment.bytes ∣ base) :
    alignTo (base + cursor) alignment = base + alignTo cursor alignment := by
  obtain ⟨multiple, rfl⟩ := aligned
  have positive := alignment.bytes_pos
  have shift : alignment.bytes * multiple + cursor + alignment.bytes - 1 =
      (cursor + alignment.bytes - 1) + alignment.bytes * multiple := by omega
  simp only [alignTo, shift, Nat.add_mul_div_left _ _ positive, Nat.add_mul]
  rw [Nat.mul_comm multiple alignment.bytes, Nat.add_comm]

private theorem join_left (left right : Alignment) : left.bytes ∣ (left.join right).bytes := by
  cases left <;> cases right <;> decide

private theorem join_right (left right : Alignment) : right.bytes ∣ (left.join right).bytes := by
  cases left <;> cases right <;> decide

private theorem recordEnd_shift (fields : List Layout) (base cursor : Nat)
    (aligned : (recordAlignment fields).bytes ∣ base) :
    recordEnd (base + cursor) fields = base + recordEnd cursor fields := by
  induction fields generalizing cursor with
  | nil => rfl
  | cons field fields ih =>
    have head : field.alignment.bytes ∣ base := Nat.dvd_trans (join_left field.alignment (recordAlignment fields)) aligned
    have tail : (recordAlignment fields).bytes ∣ base :=
      Nat.dvd_trans (join_right field.alignment (recordAlignment fields)) aligned
    simp only [recordEnd, placeField, align_shift base cursor field.alignment head, Nat.add_assoc]
    exact ih _ tail

private theorem recordEnd_ge (fields : List Layout) (cursor : Nat) : cursor ≤ recordEnd cursor fields := by
  induction fields generalizing cursor with
  | nil => exact Nat.le_refl cursor
  | cons field fields ih =>
    apply Nat.le_trans _ (ih (placeField cursor field).2)
    have positioned := align_ge cursor field.alignment
    simp only [placeField]
    omega

private theorem field_bounds (fields : List Layout) (cursor index offset : Nat) (field : Layout)
    (member : fields[index]? = some field) (place : (fieldOffsets cursor fields)[index]? = some offset) :
    cursor ≤ offset ∧ offset % field.alignment.bytes = 0 ∧ offset + field.size ≤ recordEnd cursor fields := by
  induction fields generalizing cursor index with
  | nil => simp at member
  | cons first rest ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at member
      simp only [fieldOffsets, List.getElem?_cons_zero, Option.some.injEq] at place
      subst first
      subst offset
      exact ⟨align_ge cursor field.alignment, align_mod cursor field.alignment, recordEnd_ge rest _⟩
    | succ index =>
      have next := ih (placeField cursor first).2 index (by simpa only [List.getElem?_cons_succ] using member)
        (by simpa only [fieldOffsets, List.getElem?_cons_succ] using place)
      have positioned := align_ge cursor first.alignment
      simp only [placeField] at next
      exact ⟨by omega, next.2⟩

theorem field_fits (fields : List Layout) (base index offset : Nat) (field : Layout)
    (aligned : (recordAlignment fields).bytes ∣ base)
    (member : fields[index]? = some field) (place : (fieldOffsets base fields)[index]? = some offset) :
    base ≤ offset ∧ offset % field.alignment.bytes = 0 ∧ offset + field.size ≤ base + (recordLayout fields).size := by
  obtain ⟨start, alignedField, bound⟩ := field_bounds fields base index offset field member place
  have shifted : recordEnd base fields = base + recordEnd 0 fields := by
    simpa only [Nat.add_zero] using recordEnd_shift fields base 0 aligned
  refine ⟨start, alignedField, Nat.le_trans bound ?_⟩
  rw [shifted, recordLayout, Layout.size_rounded]
  exact Nat.add_le_add_left (align_ge _ _) _

end Silmaril.Proofs.Wasm.Component.Reference.LayoutBounds
