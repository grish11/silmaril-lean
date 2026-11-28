module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Padding
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Completion.Thms

/-! # One-square uniformity along the class map of a surjective tag map -/

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

theorem padding_uniform {X Z Y : τ} {h : ofType (Φ := Φ) X ⟶ ofType Z} (c : Padding h)
    (s : ofType (Φ := Φ) Z ⟶ ofType X) (sect : s ≫ h = 𝟙 _)
    (J : ofType (Φ := Φ) X ⟶ ofType Y ⨿ ofType X) (T : ofType (Φ := Φ) Z ⟶ ofType Y ⨿ ofType Z)
    (square : J ≫ coprod.map (𝟙 _) h = h ≫ T) :
    (π).map (iterate J) = (π).map (h ≫ iterate T) :=
  padded pe c.phases h c.cls s sect c.iso c.fold J T square

theorem tag_uniform {m N : Nat} {Y : τ} (A : Fin (m + 2) → τ) (f : Fin (N + 1) → Fin (m + 2))
    (surj : Function.Surjective f)
    (J : ofType (Φ := Φ) (famSum N fun k => A (f k)) ⟶ ofType Y ⨿ ofType (famSum N fun k => A (f k)))
    (T : ofType (Φ := Φ) (famSum (m + 1) A) ⟶ ofType Y ⨿ ofType (famSum (m + 1) A))
    (square : J ≫ coprod.map (𝟙 _) (tagFold A f) = tagFold A f ≫ T) :
    (π).map (iterate J) = (π).map (tagFold A f ≫ iterate T) :=
  padding_uniform pe (tagPadding A N f) (tagSection A f (Function.surjInv surj) (Function.surjInv_eq surj))
    (tagSection_fold A f _ _) J T square

/-- Uniformity along a map is stable under isos of default Paper on both
sides. -/
theorem conj {X X' Z Z' Y : τ} (α : ofType (Φ := Φ) X ≅ ofType X') (β : ofType (Φ := Φ) Z' ≅ ofType Z)
    (h' : ofType (Φ := Φ) X' ⟶ ofType Z')
    (uni : ∀ (J' : ofType (Φ := Φ) X' ⟶ ofType Y ⨿ ofType X') (T' : ofType (Φ := Φ) Z' ⟶ ofType Y ⨿ ofType Z'),
      J' ≫ coprod.map (𝟙 _) h' = h' ≫ T' → (π).map (iterate J') = (π).map (h' ≫ iterate T'))
    (J : ofType (Φ := Φ) X ⟶ ofType Y ⨿ ofType X) (T : ofType (Φ := Φ) Z ⟶ ofType Y ⨿ ofType Z)
    (square : J ≫ coprod.map (𝟙 _) (α.hom ≫ h' ≫ β.hom) = (α.hom ≫ h' ≫ β.hom) ≫ T) :
    (π).map (iterate J) = (π).map ((α.hom ≫ h' ≫ β.hom) ≫ iterate T) := by
  have left := iterate_uniformity_iso α J
  have right := iterate_uniformity_iso β.symm T
  have back : coprod.map (𝟙 (ofType (Φ := Φ) Y)) (α.hom ≫ h' ≫ β.hom) ≫ coprod.map (𝟙 _) β.inv =
      coprod.map (𝟙 _) α.hom ≫ coprod.map (𝟙 _) h' := by
    simp only [coprod.map_map, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have sq : (α.inv ≫ J ≫ coprod.map (𝟙 _) α.hom) ≫ coprod.map (𝟙 _) h' =
      h' ≫ (β.hom ≫ T ≫ coprod.map (𝟙 _) β.inv) := by
    rw [Category.assoc, Category.assoc, ← back, reassoc_of% square]
    simp only [Iso.inv_hom_id_assoc]
  have inner := uni _ _ sq
  calc
    (π).map (iterate J) = (π).map α.hom ≫ (π).map (iterate (α.inv ≫ J ≫ coprod.map (𝟙 _) α.hom)) :=
      (congrArg (π).map left).trans ((π).map_comp _ _)
    _ = (π).map α.hom ≫ (π).map (h' ≫ iterate (β.hom ≫ T ≫ coprod.map (𝟙 _) β.inv)) := by rw [inner]
    _ = (π).map ((α.hom ≫ h' ≫ β.hom) ≫ β.inv ≫ iterate (β.hom ≫ T ≫ coprod.map (𝟙 _) β.inv)) := by
      rw [← Functor.map_comp]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = (π).map ((α.hom ≫ h' ≫ β.hom) ≫ iterate T) := by rw [right]; rfl

theorem class_uniform (A : τ) {K m : Nat} {Y : τ} (cls : Fin (K + 1) → Fin (m + 2))
    (surj : Function.Surjective cls)
    (J : ofType (Φ := Φ) (phaseType A K) ⟶ ofType Y ⨿ ofType (phaseType A K))
    (T : ofType (Φ := Φ) (phaseType A (m + 1)) ⟶ ofType Y ⨿ ofType (phaseType A (m + 1)))
    (square : J ≫ coprod.map (𝟙 _) (classFold A cls) = classFold A cls ≫ T) :
    (π).map (iterate J) = (π).map (classFold A cls ≫ iterate T) :=
  conj pe (constIso A K).symm (constIso A (m + 1)) (tagFold (fun _ => A) cls)
    (fun J' T' sq => tag_uniform pe (fun _ => A) cls surj J' T' sq) J T square

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity
