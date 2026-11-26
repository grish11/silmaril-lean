module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CyclicStructuralFold

/-! # Cyclic uniformity for a fold of two Unit states -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open Extension.Singleton (TypeCategory ofType iterateChosen)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper
open scoped Paper.BoundSimulation.Obstruction

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (S : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop) (R : τ)

local notation "X" => ofType S (Silmaril.unit : τ)
local notation "C" => ofType S R
local notation "Q" => Extension.Singleton.TypeCategory S
local notation "F" => foldState S R

/-- The written fold is the identity on the retained state and codiagonal on the two copies of Unit. -/
theorem fold_coordinates :
    (sourceIso S R).hom ≫ coprod.map (𝟙 C) (coprod.desc (𝟙 X) (𝟙 X)) = F ≫ (targetIso S R).hom :=
  CyclicStructuralFold.fold_coordinates S R

/-- This is the same fold as the instruction-free native replay witness. -/
theorem foldState_eq_audit : foldState Seed UnitTy = stateMap := rfl

/-- The fold preserves all three structural value equations. -/
theorem fold_structural : Extension.Singleton.StructuralValues.HomProperty S F :=
  Extension.Singleton.StructuralValues.copair_mem S
    (Extension.Singleton.StructuralValues.sum_inl_mem S Silmaril.unit R)
    ((Extension.Singleton.StructuralValues.HomProperty S).id_mem _)

/-- The block square and the square on exact syntax state objects are equivalent. -/
theorem fold_square_iff {B : Q}
    (d : C ⨿ (X ⨿ X) ⟶ (B ⨿ C) ⨿ (X ⨿ X))
    (e : C ⨿ X ⟶ (B ⨿ C) ⨿ X) :
    realize S (sourceIso S R) d ≫ coprod.map (𝟙 B) F = F ≫ realize S (targetIso S R) e ↔
      d ≫ coprod.map (𝟙 (B ⨿ C)) (coprod.desc (𝟙 X) (𝟙 X)) =
        coprod.map (𝟙 C) (coprod.desc (𝟙 X) (𝟙 X)) ≫ e :=
  CyclicStructuralFold.fold_square_iff S R d e

/-- The exact square is uniform when the second Unit mode sends every
Unit recurrence to the first copy. The other rows can use arbitrary quotient computations. -/
theorem uniformity_of_right_switch
    (includeUnit : ∀ {Γ : VCtx τ} {r q : Region Φ} {L : LCtx τ},
      Paper.WithUnitEta.Step Γ r q L → S Γ r q L)
    {B : Q} (d : C ⨿ (X ⨿ X) ⟶ (B ⨿ C) ⨿ (X ⨿ X))
    (e : C ⨿ X ⟶ (B ⨿ C) ⨿ X)
    (square : realize S (sourceIso S R) d ≫ coprod.map (𝟙 B) F = F ≫ realize S (targetIso S R) e)
    (switch : coprod.inr ≫ (coprod.inr ≫ d) =
      (coprod.inr ≫ e) ≫ coprod.map (𝟙 (B ⨿ C)) (coprod.inl : X ⟶ X ⨿ X)) :
    iterateChosen S (realize S (sourceIso S R) d) =
      F ≫ iterateChosen S (realize S (targetIso S R) e) :=
  CyclicStructuralFold.uniformity_of_right_switch S R includeUnit d e square switch

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic
