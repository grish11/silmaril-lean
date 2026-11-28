module

public import Silmaril.Formats.Parquet.Plain.Defs

namespace Silmaril.Proofs.Formats.Parquet.Plain

open Silmaril.Formats Silmaril.Formats.Parquet.Plain

private theorem mapM_checkSigned {α : Type} (halfRange : Int) (narrow : Int → α)
    (values : List Int) :
    values.mapM (checkSigned halfRange narrow) =
      if ∀ value ∈ values, -halfRange ≤ value ∧ value < halfRange then
        .ok (values.map narrow)
      else .error .integerOverflow := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    have allCons : (∀ n ∈ value :: rest, -halfRange ≤ n ∧ n < halfRange) ↔
        (-halfRange ≤ value ∧ value < halfRange) ∧
        (∀ n ∈ rest, -halfRange ≤ n ∧ n < halfRange) := List.forall_mem_cons
    rw [List.mapM_cons, ih]
    by_cases head : -halfRange ≤ value ∧ value < halfRange
    · by_cases tail : ∀ n ∈ rest, -halfRange ≤ n ∧ n < halfRange
      · have all := allCons.mpr ⟨head, tail⟩
        simp only [checkSigned, ite_eq_left head, ite_eq_left tail, ite_eq_left all]
        rfl
      · have notAll := fun h => tail (allCons.mp h).2
        simp only [checkSigned, ite_eq_left head, ite_eq_right tail, ite_eq_right notAll]
        rfl
    · have notAll := fun h => head (allCons.mp h).1
      simp only [checkSigned, ite_eq_right head, ite_eq_right notAll]
      rfl

public theorem encodeInt32Checked_eq (values : List Int) :
    encodeInt32Checked values =
      if ∀ value ∈ values, -(2 ^ 31 : Int) ≤ value ∧ value < 2 ^ 31 then
        .ok (encodeInt32 (values.map Int32.ofInt))
      else .error .integerOverflow := by
  unfold encodeInt32Checked
  rw [mapM_checkSigned]
  split <;> rfl

public theorem encodeInt64Checked_eq (values : List Int) :
    encodeInt64Checked values =
      if ∀ value ∈ values, -(2 ^ 63 : Int) ≤ value ∧ value < 2 ^ 63 then
        .ok (encodeInt64 (values.map Int64.ofInt))
      else .error .integerOverflow := by
  unfold encodeInt64Checked
  rw [mapM_checkSigned]
  split <;> rfl

end Silmaril.Proofs.Formats.Parquet.Plain
