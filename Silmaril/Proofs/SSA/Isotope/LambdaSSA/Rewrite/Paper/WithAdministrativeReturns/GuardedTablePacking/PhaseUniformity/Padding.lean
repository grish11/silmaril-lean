module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Composite
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Padding.Thms

/-! # Folds with unequal fibres, by unreachable padding -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity (Step)
open Paper.Extension.Singleton (projection)
open Paper.TypeCategory

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "π" => projection (Step (τ := τ) (Φ := Φ) pe)

set_option backward.isDefEq.respectTransparency false

theorem padded (n : Nat) {X U Z Y : τ} (h : ofType (Φ := Φ) X ⟶ ofType Z) (u : ofType (Φ := Φ) U ⟶ ofType Z)
    (s : ofType (Φ := Φ) Z ⟶ ofType X) (sect : s ≫ h = 𝟙 _)
    (ψ : ofType (Φ := Φ) (Silmaril.coprod U X) ≅ ofType (phaseType Z n))
    (fold : ψ.hom ≫ phaseFold Z n = sumDesc u h)
    (J : ofType (Φ := Φ) X ⟶ ofType Y ⨿ ofType X) (T : ofType (Φ := Φ) Z ⟶ ofType Y ⨿ ofType Z)
    (square : J ≫ coprod.map (𝟙 _) h = h ≫ T) :
    (π).map (iterate J) = (π).map (h ≫ iterate T) := by
  have enter := iterate_padStep U u s J T
  have sq := padStep_square U u s J T h sect square
  have comp := iso_fold pe n ψ (padStep U u s J T) T (by rw [fold]; exact sq)
  rw [fold] at comp
  calc
    (π).map (iterate J) = (π).map (sumInr U X) ≫ (π).map (iterate (padStep U u s J T)) :=
      (congrArg (π).map enter).trans ((π).map_comp _ _)
    _ = (π).map (sumInr U X) ≫ (π).map (sumDesc u h ≫ iterate T) := by rw [comp]
    _ = (π).map ((sumInr U X ≫ sumDesc u h) ≫ iterate T) := by
      rw [← Functor.map_comp, Category.assoc]
    _ = (π).map (h ≫ iterate T) := by rw [sumInr_sumDesc]

theorem pair_short (A B : τ) (n : Nat) {Y : τ}
    (J : ofType (Φ := Φ) (Silmaril.coprod B (pairPhases A B n)) ⟶
      ofType Y ⨿ ofType (Silmaril.coprod B (pairPhases A B n)))
    (T : ofType (Φ := Φ) (Silmaril.coprod A B) ⟶ ofType Y ⨿ ofType (Silmaril.coprod A B))
    (square : J ≫ coprod.map (𝟙 _) (shortFold A B n) = shortFold A B n ≫ T) :
    (π).map (iterate J) = (π).map (shortFold A B n ≫ iterate T) :=
  padded pe (n + 1) (U := A) (shortFold A B n) (sumInl A B) (shortSection A B n)
    (shortSection_fold A B n) (pairIso A B (n + 1))
    ((pairIso_fold A B (n + 1)).trans (pairFold_split A B n)) J T square

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity
