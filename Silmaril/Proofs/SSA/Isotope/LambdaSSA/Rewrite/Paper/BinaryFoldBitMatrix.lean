module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.StructuralValues.ThreeCycle.MatrixBoundary.Binary.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldBitMatrix

open Silmaril.Calco2019.CounterSemiring.ThreeCycle
open Binary

theorem fold_output {E : Type} (e : Matrix Bit E Scalar) :
    foldMatrix * e = duplicate e := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  rcases i with i | i <;> fin_cases i <;> simp [foldMatrix, duplicate]

theorem fold_recurrence (r : Weight) : alternating r * foldMatrix = foldMatrix * r := by
  rw [fold_output r]
  ext i j
  have all : (Finset.univ : Finset PhaseState) = {Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1} := by
    decide
  rw [Matrix.mul_apply, all]
  rcases i with i | i <;> fin_cases j <;>
    simp [alternating, foldMatrix, duplicate, Finset.sum_insert]

private theorem star_expand (a b : Scalar) : b + a * Scalar.star a * b = Scalar.star a * b := by
  simpa only [Scalar.iterate, mul_assoc] using (Scalar.iterate_fixpoint a b).symm

theorem feedback_eq_mul {E : Type} (r : Weight) (e : Matrix Bit E Scalar) :
    feedback r e = closure r * e := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  let d := Scalar.star (r 1 1)
  let z := r 0 0 + r 0 1 * d * r 1 0
  let u := e 0 j + r 0 1 * d * e 1 j
  fin_cases i
  · change u + z * Scalar.star z * u = closure r 0 0 * e 0 j + closure r 0 1 * e 1 j
    rw [star_expand]
    change Scalar.star z * (e 0 j + r 0 1 * d * e 1 j) =
      Scalar.star z * e 0 j + (Scalar.star z * r 0 1 * d) * e 1 j
    simp only [mul_add, mul_assoc]
  · change (e 1 j + r 1 1 * d * e 1 j) + (r 1 0 + r 1 1 * d * r 1 0) * Scalar.star z * u =
      closure r 1 0 * e 0 j + closure r 1 1 * e 1 j
    rw [star_expand, star_expand]
    change d * e 1 j + (d * r 1 0) * Scalar.star z * (e 0 j + r 0 1 * d * e 1 j) =
      (d * r 1 0 * Scalar.star z) * e 0 j + (d + d * r 1 0 * Scalar.star z * r 0 1 * d) * e 1 j
    simp only [mul_add, add_mul]
    ac_rfl

private def multiply (r s : Weight) : Weight :=
  Matrix.of fun i j => r i 0 * s 0 j + r i 1 * s 1 j

private theorem multiply_eq (r s : Weight) : multiply r s = r * s := by
  ext i j
  simp only [multiply, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_two]

private theorem square_entries (a b c d : Scalar) :
    multiply (entries a b c d) (entries a b c d) =
      entries (a * a + b * c) (a * b + b * d) (c * a + d * c) (c * b + d * d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem plus_entries (a b c d : Scalar) :
    (1 : Weight) + entries a b c d = entries (1 + a) b c (1 + d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [entries, Matrix.add_apply]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
private theorem table_double (a b c d : Scalar) :
    closure (entries a b c d * entries a b c d) * (1 + entries a b c d) = closure (entries a b c d) := by
  rw [← multiply_eq, ← multiply_eq, square_entries, plus_entries]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    revert a b c d
    decide +kernel

theorem closure_double (r : Weight) : closure (r * r) * (1 + r) = closure r := by
  have coords : entries (r 0 0) (r 0 1) (r 1 0) (r 1 1) = r := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [← coords]
  apply table_double

theorem feedback_double {E : Type} (r : Weight) (e : Matrix Bit E Scalar) :
    feedback (r * r) (e + r * e) = feedback r e := by
  rw [feedback_eq_mul, feedback_eq_mul,
    show e + r * e = (1 + r) * e by rw [Matrix.add_mul, Matrix.one_mul],
    ← Matrix.mul_assoc, closure_double]

/-- A retained two-state network may have a separate external entry row. -/
private def entryNetwork {I E : Type} (r : Weight) (e : Matrix Bit E Scalar)
    (next : I → Bit → Scalar) (direct : I → E → Scalar) :
    (I ⊕ Bit) → (E ⊕ Bit) → Scalar
  | .inl i, .inl j => direct i j
  | .inl i, .inr j => next i j
  | .inr i, .inl j => e i j
  | .inr i, .inr j => r i j

private theorem entry_result {I E : Type} (r : Weight) (e : Matrix Bit E Scalar)
    (next : I → Bit → Scalar) (direct : I → E → Scalar) (i : I) (j : E) :
    eliminate 0 (eliminate 1 (entryNetwork r e next direct)) (.inl i) (.inl j) =
      direct i j + (next i 0 * feedback r e 0 j + next i 1 * feedback r e 1 j) := by
  let d := Scalar.star (r 1 1)
  let z := r 0 0 + r 0 1 * d * r 1 0
  let u := e 0 j + r 0 1 * d * e 1 j
  have left : feedback r e 0 j = Scalar.star z * u := by
    change u + z * Scalar.star z * u = _
    apply star_expand
  have right : feedback r e 1 j = d * e 1 j + (d * r 1 0) * Scalar.star z * u := by
    change (e 1 j + r 1 1 * d * e 1 j) + (r 1 0 + r 1 1 * d * r 1 0) * Scalar.star z * u = _
    rw [star_expand, star_expand]
  rw [left, right]
  change (direct i j + next i 1 * d * e 1 j) + (next i 0 + next i 1 * d * r 1 0) * Scalar.star z * u = _
  simp only [mul_add, add_mul]
  ac_rfl

private theorem feedback_fixpoint {E : Type} (r : Weight) (e : Matrix Bit E Scalar) (i : Bit) (j : E) :
    feedback r e i j = e i j + (r i 0 * feedback r e 0 j + r i 1 * feedback r e 1 j) := by
  have same : entryNetwork r e r e = network r e := by
    funext x y
    cases x <;> cases y <;> rfl
  change eliminate 0 (eliminate 1 (network r e)) (.inl i) (.inl j) = _
  rw [← same]
  exact entry_result r e r e i j

private def keepLeft {I E : Type} (f : (I ⊕ PhaseState) → (E ⊕ PhaseState) → Scalar) :
    (I ⊕ Bit) → (E ⊕ Bit) → Scalar :=
  fun x y => f (x.map id Sum.inl) (y.map id Sum.inl)

private theorem keepLeft_eliminate {I E : Type} (f : (I ⊕ PhaseState) → (E ⊕ PhaseState) → Scalar)
    (i : Bit) : keepLeft (eliminate (.inl i) f) = eliminate i (keepLeft f) := rfl

private theorem phase_reduce {E : Type} (r : Weight) (e : Matrix Bit E Scalar) :
    keepLeft (eliminate (.inr 0) (eliminate (.inr 1) (network (alternating r) (duplicate e)))) =
      entryNetwork (r * r) (e + r * e) (Sum.elim (r * r) r) (Sum.elim (e + r * e) e) := by
  have star0 : Scalar.star 0 = 1 := by decide
  funext i j
  rcases i with (i | i) | i <;> cases j <;>
    simp [keepLeft, eliminate, network, alternating, duplicate, entryNetwork, star0,
      Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_two, Sum.elim_inl, Sum.elim_inr] <;> try rfl
  · rename_i j
    change e i j + r i 1 * e 1 j + r i 0 * e 0 j = (e + r * e) i j
    rw [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
    ac_rfl
  · rename_i j
    change r i 1 * r 1 j + r i 0 * r 0 j = (r * r) i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    exact add_comm _ _
  · ac_rfl
  · exact add_comm _ _

theorem phase_feedback {E : Type} (r : Weight) (e : Matrix Bit E Scalar) :
    phaseFeedback r e = duplicate (feedback r e) := by
  have eval (i : PhaseState) (j : E) :
      phaseFeedback r e i j =
        eliminate 0 (eliminate 1 (entryNetwork (r * r) (e + r * e)
          (Sum.elim (r * r) r) (Sum.elim (e + r * e) e))) (.inl i) (.inl j) := by
    let f := eliminate (.inr 0) (eliminate (.inr 1) (network (alternating r) (duplicate e)))
    change keepLeft (eliminate (.inl 0) (eliminate (.inl 1) f)) (.inl i) (.inl j) = _
    rw [keepLeft_eliminate, keepLeft_eliminate, show keepLeft f = _ from phase_reduce r e]
  ext i j
  rw [eval, entry_result, feedback_double]
  cases i with
  | inl i =>
    -- Before replacing the doubled feedback, the left entry is itself a
    -- doubled round. Apply fixpoint to that round, then use doubling.
    rw [← feedback_double r e]
    change (e + r * e) i j + ((r * r) i 0 * feedback (r * r) (e + r * e) 0 j +
      (r * r) i 1 * feedback (r * r) (e + r * e) 1 j) = feedback (r * r) (e + r * e) i j
    exact (feedback_fixpoint _ _ _ _).symm
  | inr i => exact (feedback_fixpoint r e i j).symm

theorem phase_fold {E : Type} (r : Weight) (e : Matrix Bit E Scalar) :
    phaseFeedback r e = foldMatrix * feedback r e := by
  rw [phase_feedback, fold_output]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldBitMatrix
