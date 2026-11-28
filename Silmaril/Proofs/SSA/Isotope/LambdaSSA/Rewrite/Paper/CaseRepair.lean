module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.CaseRepair.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Thms

/-! # Source repair with an exact coproduct decomposition -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseRepair

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton (projection projectStep projectSquare_iff projection_map_desc_congr)
open Paper.Extension.Singleton.CaseRepair (restore)

set_option backward.isDefEq.respectTransparency false

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Comp" => Paper.TypeCategory (τ := τ) Φ

theorem restore_post_iff {X Y A B D : Comp} (split : X ⨿ Y ≅ A) (left right : D ⟶ A)
    (h : A ⟶ D) (p : A ⟶ B ⨿ D) :
    restore split left right p ≫ coprod.map (𝟙 B) h = p ↔
      (coprod.inl ≫ split.hom ≫ p ≫ coprod.map (𝟙 B) (left ≫ h) =
        coprod.inl ≫ split.hom ≫ p) ∧
      (coprod.inr ≫ split.hom ≫ p ≫ coprod.map (𝟙 B) (right ≫ h) =
        coprod.inr ≫ split.hom ≫ p) := by
  have hl :
      coprod.inl ≫ split.hom ≫ restore split left right p ≫ coprod.map (𝟙 B) h =
        coprod.inl ≫ split.hom ≫ p ≫ coprod.map (𝟙 B) (left ≫ h) := by
    simp only [restore, Category.assoc, Iso.hom_inv_id_assoc, coprod.inl_desc_assoc, coprod.map_map,
      Category.id_comp]
  have hr :
      coprod.inr ≫ split.hom ≫ restore split left right p ≫ coprod.map (𝟙 B) h =
        coprod.inr ≫ split.hom ≫ p ≫ coprod.map (𝟙 B) (right ≫ h) := by
    simp only [restore, Category.assoc, Iso.hom_inv_id_assoc, coprod.inr_desc_assoc, coprod.map_map,
      Category.id_comp]
  constructor
  · intro eq
    constructor
    · rw [← hl, eq]
    · rw [← hr, eq]
  · rintro ⟨el, er⟩
    apply (cancel_epi split.hom).1
    apply coprod.hom_ext
    · simpa only [Category.assoc, hl] using el
    · simpa only [Category.assoc, hr] using er

variable (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "J" => projection Seed

theorem restore_congr {X Y A B D : Comp} (split : X ⨿ Y ≅ A) (left right : D ⟶ A) {p q : A ⟶ B ⨿ D}
    (eq : (J).map p = (J).map q) :
    (J).map (restore split left right p) = (J).map (restore split left right q) := by
  simp only [restore, Functor.map_comp]
  apply congrArg ((J).map split.inv ≫ ·)
  apply projection_map_desc_congr Seed <;> simp only [Functor.map_comp, eq]

theorem repairSource {X Y A B D : Comp} (split : X ⨿ Y ≅ A) (left right : D ⟶ A)
    (h : A ⟶ D) (f : A ⟶ B ⨿ A) (g : D ⟶ B ⨿ D)
    (square : projectStep Seed f ≫ coprod.map (𝟙 ((J).obj B)) ((J).map h) =
      (J).map h ≫ projectStep Seed g)
    (sourceImage : (J).map f = (J).map (restore split left right (f ≫ coprod.map (𝟙 B) h)))
    (targetImage : restore split left right (h ≫ g) ≫ coprod.map (𝟙 B) h = h ≫ g) :
    let f' := restore split left right (h ≫ g)
    projectStep Seed f' = projectStep Seed f ∧ f' ≫ coprod.map (𝟙 B) h = h ≫ g := by
  have eq := restore_congr Seed split left right ((projectSquare_iff Seed f g h).1 square)
  refine ⟨?_, targetImage⟩
  change (J).map (restore split left right (h ≫ g)) ≫ _ = (J).map f ≫ _
  rw [← eq, ← sourceImage]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseRepair
