module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Rounds
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Classes.Thms

/-! # Folds of several classes at once, from one overall square -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity (Step)
open Paper.Extension.Singleton (projection)
open Paper.TypeCategory (ofType iterate phaseType phaseFold pairPhases pairFold pairIso pairIso_fold
  iterate_uniformity_iso)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "π" => projection (Step (τ := τ) (Φ := Φ) pe)

set_option backward.isDefEq.respectTransparency false

variable {X Z Y : τ} (n : Nat)

theorem through (e : ofType (Φ := Φ) X ⟶ ofType (phaseType Z n))
    (J : ofType (Φ := Φ) X ⟶ ofType Y ⨿ ofType X)
    (G : ofType (Φ := Φ) (phaseType Z n) ⟶ ofType Y ⨿ ofType (phaseType Z n))
    (T : ofType (Φ := Φ) Z ⟶ ofType Y ⨿ ofType Z)
    (enter : iterate J = e ≫ iterate G)
    (square : G ≫ coprod.map (𝟙 _) (phaseFold Z n) = phaseFold Z n ≫ T) :
    (π).map (iterate J) = (π).map (e ≫ phaseFold Z n ≫ iterate T) := by
  rw [enter, Functor.map_comp, fold_uniform pe n G T square, ← Functor.map_comp]

theorem iso_fold (ψ : ofType (Φ := Φ) X ≅ ofType (phaseType Z n))
    (J : ofType (Φ := Φ) X ⟶ ofType Y ⨿ ofType X) (T : ofType (Φ := Φ) Z ⟶ ofType Y ⨿ ofType Z)
    (square : J ≫ coprod.map (𝟙 _) (ψ.hom ≫ phaseFold Z n) = (ψ.hom ≫ phaseFold Z n) ≫ T) :
    (π).map (iterate J) = (π).map ((ψ.hom ≫ phaseFold Z n) ≫ iterate T) := by
  have conj : (ψ.inv ≫ J ≫ coprod.map (𝟙 _) ψ.hom) ≫ coprod.map (𝟙 _) (phaseFold Z n) =
      phaseFold Z n ≫ T := by
    have split : coprod.map (𝟙 (ofType (Φ := Φ) Y)) ψ.hom ≫ coprod.map (𝟙 _) (phaseFold Z n) =
        coprod.map (𝟙 _) (ψ.hom ≫ phaseFold Z n) := by
      rw [coprod.map_map, Category.id_comp]
    rw [Category.assoc, Category.assoc, split, square, Category.assoc, Iso.inv_hom_id_assoc]
  exact (through pe n ψ.hom J _ T (iterate_uniformity_iso ψ J) conj).trans
    (congrArg (π).map (Category.assoc _ _ _).symm)

theorem pair_fold (A B : τ) (J : ofType (Φ := Φ) (pairPhases A B n) ⟶ ofType Y ⨿ ofType (pairPhases A B n))
    (T : ofType (Φ := Φ) (Silmaril.coprod A B) ⟶ ofType Y ⨿ ofType (Silmaril.coprod A B))
    (square : J ≫ coprod.map (𝟙 _) (pairFold A B n) = pairFold A B n ≫ T) :
    (π).map (iterate J) = (π).map (pairFold A B n ≫ iterate T) := by
  have fold := pairIso_fold (Φ := Φ) A B n
  have comp := iso_fold pe n (pairIso A B n) J T (by rw [fold]; exact square)
  rwa [fold] at comp

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity
