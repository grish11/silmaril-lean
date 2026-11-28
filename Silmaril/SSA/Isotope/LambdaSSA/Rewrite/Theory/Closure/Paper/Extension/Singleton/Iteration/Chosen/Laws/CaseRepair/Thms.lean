module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.CaseRepair.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseRepair

/-! # Repair the source of a corrected square by restoring each arm -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.CaseRepair

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Comp" => Paper.TypeCategory (τ := τ) Φ

/-- Restoring and then mapping the recursive payload preserves the observed
step exactly when it preserves that step on each input arm. -/
theorem restore_post_iff {X Y A B D : Comp} (split : X ⨿ Y ≅ A) (left right : D ⟶ A)
    (h : A ⟶ D) (p : A ⟶ B ⨿ D) :
    restore split left right p ≫ coprod.map (𝟙 B) h = p ↔
      (coprod.inl ≫ split.hom ≫ p ≫ coprod.map (𝟙 B) (left ≫ h) =
        coprod.inl ≫ split.hom ≫ p) ∧
      (coprod.inr ≫ split.hom ≫ p ≫ coprod.map (𝟙 B) (right ≫ h) =
        coprod.inr ≫ split.hom ≫ p) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseRepair.restore_post_iff split left right h p

variable (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "J" => projection Seed

/-- A corrected square repairs the source if the source class can be
recovered from its observed step by the two restorations. For the target
composite the restorations must preserve the observed step in standard
Paper, as characterized arm by arm by `restore_post_iff`. -/
theorem repairSource {X Y A B D : Comp} (split : X ⨿ Y ≅ A) (left right : D ⟶ A)
    (h : A ⟶ D) (f : A ⟶ B ⨿ A) (g : D ⟶ B ⨿ D)
    (square : projectStep Seed f ≫ coprod.map (𝟙 ((J).obj B)) ((J).map h) =
      (J).map h ≫ projectStep Seed g)
    (sourceImage : (J).map f = (J).map (restore split left right (f ≫ coprod.map (𝟙 B) h)))
    (targetImage : restore split left right (h ≫ g) ≫ coprod.map (𝟙 B) h = h ≫ g) :
    let f' := restore split left right (h ≫ g)
    projectStep Seed f' = projectStep Seed f ∧ f' ≫ coprod.map (𝟙 B) h = h ≫ g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseRepair.repairSource
    Seed split left right h f g square sourceImage targetImage

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.CaseRepair
