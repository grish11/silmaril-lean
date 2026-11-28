module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.StructuralValues.ThreeCycle.MatrixBoundary.Defs

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldMatrixBoundary

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.WithCaseReturns.BinaryFold.MatrixBoundary
open Paper.Extension.Singleton
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open Silmaril.Calco2019.CounterSemiring.ThreeCycle (Scalar)

local notation "R" => Paper.TypeCategory.discardArrow (Φ := Op) U
local notation "F" => projection Seed

set_option backward.isDefEq.respectTransparency false

theorem reset_input : R ≫ nativeRound = nativeRound := by
  have idem : R ≫ R = R := Paper.TypeCategory.discard_comp_branchValue (.unit (Γ := [U]))
  simp only [nativeRound, ← Category.assoc R R, idem]

theorem reset_output : nativeRound ≫ coprod.map (𝟙 (Native U)) R = nativeRound := by
  have idem : R ≫ R = R := Paper.TypeCategory.discard_comp_branchValue (.unit (Γ := [U]))
  simp only [nativeRound, Category.assoc, coprod.map_map, Category.id_comp, idem]

theorem nativeRound_project :
    projectStep Seed nativeRound = request ≫ (sumIso Seed U U).hom := by
  have resetId : (F).map R = 𝟙 _ := unit_eta_of_include Seed (fun h => .inl (Paper.WithCaseReturns.includeUnit false h))
  let q : Native U ⟶ Native U ⨿ Native U :=
    Paper.TypeCategory.primitiveReturn Op.poll ≫ (Paper.TypeCategory.sumIso U U).hom
  have eq : projectStep Seed q = request ≫ (sumIso Seed U U).hom := by
    apply (cancel_mono (sumIso Seed U U).inv).mp
    rw [projectStep_comp_sumIso_inv Seed (A := U) (B := U) q]
    simp [request, q]
  have hn : nativeRound = R ≫ q ≫ coprod.map (𝟙 (Native U)) R := by simp [nativeRound, q]
  rw [hn]
  change (F).map (R ≫ q ≫ coprod.map (𝟙 (Native U)) R) ≫ _ = _
  rw [Functor.map_comp, Functor.map_comp, resetId, Category.id_comp, Category.assoc,
    ← coprodComparison_inv_map Seed (X := Native U) (Y := Native U) (X' := Native U) (Y' := Native U)
      (𝟙 _) R]
  simp only [(F).map_id, resetId, coprod.map_id_id, Category.comp_id]
  exact eq

private theorem exactCopair_leg_left (g : Obj U ⟶ Obj Reply) :
    (sumCofan Seed U U).inl ≫ exactCopair Seed (sumCofan Seed U U).inl g = (sumCofan Seed U U).inl :=
  (sumCofanIsColimit Seed U U).fac (BinaryCofan.mk (sumCofan Seed U U).inl g) ⟨WalkingPair.left⟩

private theorem exactCopair_leg_right (g : Obj U ⟶ Obj Reply) :
    (sumCofan Seed U U).inr ≫ exactCopair Seed (sumCofan Seed U U).inl g = g :=
  (sumCofanIsColimit Seed U U).fac (BinaryCofan.mk (sumCofan Seed U U).inl g) ⟨WalkingPair.right⟩

private theorem chain_chosen (f g : Obj U ⟶ Obj Reply) :
    chain f g ≫ (sumIso Seed U U).hom =
      (f ≫ (sumIso Seed U U).hom) ≫ coprod.desc coprod.inl (g ≫ (sumIso Seed U U).hom) := by
  simp only [chain, Category.assoc]
  congr 1
  apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit Seed U U)
  · rw [← Category.assoc, exactCopair_leg_left, sumCofan_inl_sumIso_hom,
      ← Category.assoc (sumCofan Seed U U).inl (sumIso Seed U U).hom,
      sumCofan_inl_sumIso_hom, coprod.inl_desc]
  · rw [← Category.assoc, exactCopair_leg_right,
      ← Category.assoc (sumCofan Seed U U).inr (sumIso Seed U U).hom,
      sumCofan_inr_sumIso_hom, coprod.inr_desc]

theorem typed_tripling :
    iterateSum Seed (chain request (chain request request)) = iterateSum Seed request := by
  let g := request ≫ (sumIso Seed U U).hom
  have coords : projectStep Seed nativeRound = g := nativeRound_project
  have h : iterateChosen Seed (ThreeCycle.triple g) = iterateChosen Seed g :=
    (congrArg (fun q => iterateChosen Seed (ThreeCycle.triple q)) coords.symm).trans
      ((ThreeCycle.triple_step_of_native_reset Seed (fun e => .inl (Paper.WithCaseReturns.includeUnit false e))
        nativeRound reset_input reset_output).trans
        (congrArg (iterateChosen Seed) coords))
  have b : chain request (chain request request) ≫ (sumIso Seed U U).hom = ThreeCycle.triple g := by
    rw [chain_chosen, chain_chosen]
  have exactIter (f : Obj U ⟶ Obj Reply) :
      iterateChosen Seed (f ≫ (sumIso Seed U U).hom) = iterateSum Seed f := by
    change iterateSum Seed ((f ≫ (sumIso Seed U U).hom) ≫ (sumIso Seed U U).inv) = _
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  calc
    _ = iterateChosen Seed (chain request (chain request request) ≫ (sumIso Seed U U).hom) :=
      (exactIter _).symm
    _ = iterateChosen Seed (ThreeCycle.triple g) := congrArg (iterateChosen Seed) b
    _ = iterateChosen Seed g := h
    _ = _ := exactIter _

theorem chain_matrix (lift : Lift) (f g : Obj U ⟶ Obj Reply) (j : Fin 2) :
    lift.map (chain f g) 0 j =
      lift.map f 0 0 * (if j = 0 then 1 else 0) + lift.map f 0 1 * lift.map g 0 j := by
  let k : Obj Reply ⟶ Obj Reply := exactCopair Seed (sumCofan Seed U U).inl g
  have l := congrArg (fun m : Weight U Reply => m 0 j) (lift.map_comp (sumCofan Seed U U).inl k)
  have r := congrArg (fun m : Weight U Reply => m 0 j) (lift.map_comp (sumCofan Seed U U).inr k)
  change lift.map ((sumCofan Seed U U).inl ≫ k) 0 j = _ at l
  change lift.map ((sumCofan Seed U U).inr ≫ k) 0 j = _ at r
  rw [show (sumCofan Seed U U).inl ≫ k = _ from exactCopair_leg_left g] at l
  rw [show (sumCofan Seed U U).inr ≫ k = _ from exactCopair_leg_right g] at r
  simp [lift.inl, Matrix.mul_apply] at l
  simp [lift.inr, Matrix.mul_apply] at r
  change lift.map (f ≫ k) 0 j = _
  rw [lift.map_comp, Matrix.mul_apply]
  change (∑ i : Fin 2, lift.map f 0 i * lift.map k i j) = _
  rw [Fin.sum_univ_two, ← l, ← r]

theorem scalar_doubling_compatible (lift : Lift) (f : Obj U ⟶ Obj Reply) :
    lift.map (iterateSum Seed (chain f f)) 0 0 = lift.map (iterateSum Seed f) 0 0 := by
  rw [lift.feedback, lift.feedback, chain_matrix lift, chain_matrix lift]
  simpa using Scalar.iterate_double (lift.map f 0 1) (lift.map f 0 0)

/-- The candidate's square already commutes at the step matrices. -/
theorem matrix_square :
    cycleMatrix * forgetOutputMatrix = forgetMatrix * pollMatrix :=
  Matrix.ext (by decide)

/-- The failed comparison is at feedback, where the candidate gives
the three-copy cycle and the folded step different weights. -/
theorem matrix_uniformity_ne :
    cycleFeedback cycleMatrix ≠ forgetMatrix * feedbackMatrix pollMatrix := by
  intro eq
  exact (by decide : cycleFeedback cycleMatrix 0 0 ≠ (forgetMatrix * feedbackMatrix pollMatrix) 0 0)
    (congrArg (fun m : Matrix (Fin 3) (Fin 1) _ => m 0 0) eq)

/-- All one-state step matrices agree with their doubled feedback. -/
theorem matrix_doubling (a : Weight U Reply) :
    feedbackMatrix (sequenceMatrix a a) = feedbackMatrix a := by
  apply Matrix.ext
  intro i j
  simpa [feedbackMatrix, sequenceMatrix] using
    Silmaril.Calco2019.CounterSemiring.ThreeCycle.Scalar.iterate_double (a 0 1) (a 0 0)

/-- BinaryFold doubling also holds on the candidate's concrete three-state matrix. -/
theorem matrix_cycle_doubling :
    cycleFeedback (cycleMatrix * cycleContinuation cycleMatrix) = cycleFeedback cycleMatrix := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> decide

theorem no_lift : IsEmpty Lift := by
  refine ⟨fun lift => ?_⟩
  have eq := congrArg (fun f => lift.map f 0 0) typed_tripling
  simp [Lift.feedback, chain_matrix, lift.poll, pollMatrix] at eq
  exact Scalar.iterate_triple_ne (by simpa [mul_assoc] using eq)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldMatrixBoundary
