module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Defs
import Mathlib.Data.Fintype.Pigeonhole

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration

open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration

variable {points results states : Nat} (rows : Fin points → Row points results states)

private def advance (p : Fin points) : Fin points :=
  match rows p with
  | .repeat q => q
  | .stop _ => p

/-- Total successor visits for the bounded scan. Terminal rows self-loop
in this auxiliary function. -/
def orbit (start : Fin points) : Nat → Fin points
  | 0 => start
  | k + 1 => advance rows (orbit start k)

@[simp] theorem orbit_zero (p : Fin points) : orbit rows p 0 = p := by rfl

private theorem orbit_shift (p : Fin points) (k : Nat) :
    orbit rows p (k + 1) = orbit rows (advance rows p) k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (advance rows) ih

private theorem repeat_of_none (fuel : Nat) (p : Fin points)
    (noneFound : search rows fuel p = none) (k : Nat) (lt : k < fuel) :
    rows (orbit rows p k) = .repeat (orbit rows p (k + 1)) := by
  induction fuel generalizing p k with
  | zero => omega
  | succ fuel ih =>
    cases row : rows p with
    | stop outcome => simp [search, row] at noneFound
    | «repeat» next =>
      have noLater : search rows fuel next = none := by simpa [search, row] using noneFound
      have step : advance rows p = next := by simp [advance, row]
      cases k with
      | zero => simpa [orbit, step] using row
      | succ k =>
        rw [orbit_shift, orbit_shift, step]
        exact ih next noLater k (by omega)

private theorem orbit_period {p : Fin points} {first second : Nat}
    (same : orbit rows p first = orbit rows p second) (k : Nat) :
    orbit rows p (first + k) = orbit rows p (second + k) := by
  induction k with
  | zero => exact same
  | succ k ih => exact congrArg (advance rows) ih

/-- After a full unsuccessful scan, all visits forever are genuine repeats.
A repetition among the first points + 1 visits gives the period. -/
theorem repeats_of_exhausted (p : Fin points) (noneFound : search rows points p = none) :
    ∀ k, rows (orbit rows p k) = .repeat (orbit rows p (k + 1)) := by
  obtain ⟨i, j, different, same⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (points + 1) => orbit rows p i.val) (by simp)
  have ordered : ∃ first second, first < second ∧ second ≤ points ∧
      orbit rows p first = orbit rows p second := by
    have differentNat : i.val ≠ j.val := fun eq => different (Fin.ext eq)
    rcases Nat.lt_or_gt_of_ne differentNat with lt | gt
    · exact ⟨i.val, j.val, lt, by omega, same⟩
    · exact ⟨j.val, i.val, gt, by omega, same.symm⟩
  obtain ⟨first, second, strict, bound, eq⟩ := ordered
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    by_cases lt : k < points
    · exact repeat_of_none rows points p noneFound k lt
    · have second_le : second ≤ k := by omega
      let offset := k - second
      have add : second + offset = k := by dsimp [offset]; omega
      have earlier : first + offset < k := by dsimp [offset]; omega
      have sameVisit := orbit_period rows eq offset
      have sameNext := orbit_period rows eq (offset + 1)
      rw [add] at sameVisit
      change orbit rows p (first + offset + 1) = orbit rows p (second + offset + 1) at sameNext
      rw [add] at sameNext
      rw [← sameVisit, ← sameNext]
      exact ih (first + offset) earlier

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
