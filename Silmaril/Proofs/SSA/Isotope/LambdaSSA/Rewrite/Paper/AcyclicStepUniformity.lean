module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Acyclic.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.Thms

/-! # Unique fixed points of finitely stratified guarded steps -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.AcyclicStepUniformity

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => TypeCategory Seed

theorem fixedPoint_unique {A B : Q} {f : A ⟶ B ⨿ A} (bound : AcyclicStep Seed B f)
    (u v : A ⟶ B)
    (hu : u = f ≫ coprod.desc (𝟙 B) u) (hv : v = f ≫ coprod.desc (𝟙 B) v) : u = v := by
  induction bound with
  | @exits A step =>
    have exit (w : A ⟶ B) : (step ≫ coprod.inl) ≫ coprod.desc (𝟙 B) w = step := by
      simp only [Category.assoc, coprod.inl_desc, Category.comp_id]
    exact (hu.trans (exit u)).trans (hv.trans (exit v)).symm
  | @extend A X Y split f row bounded ih =>
    let left : A ⟶ X := coprod.inl ≫ split.inv
    let right : Y ⟶ X := coprod.inr ≫ split.inv
    have lower (w : X ⟶ B)
        (hw : w = (split.hom ≫ coprod.desc f row ≫ coprod.map (𝟙 B) left) ≫ coprod.desc (𝟙 B) w) :
        left ≫ w = f ≫ coprod.desc (𝟙 B) (left ≫ w) := calc
      left ≫ w = left ≫ (split.hom ≫ coprod.desc f row ≫ coprod.map (𝟙 B) left) ≫
          coprod.desc (𝟙 B) w := congrArg (left ≫ ·) hw
      _ = _ := by
        simp only [left, Category.assoc, Iso.inv_hom_id_assoc, coprod.inl_desc_assoc, coprod.map_desc,
          Category.id_comp]
    have upper (w : X ⟶ B)
        (hw : w = (split.hom ≫ coprod.desc f row ≫ coprod.map (𝟙 B) left) ≫ coprod.desc (𝟙 B) w) :
        right ≫ w = row ≫ coprod.desc (𝟙 B) (left ≫ w) := calc
      right ≫ w = right ≫ (split.hom ≫ coprod.desc f row ≫ coprod.map (𝟙 B) left) ≫
          coprod.desc (𝟙 B) w := congrArg (right ≫ ·) hw
      _ = _ := by
        simp only [left, right, Category.assoc, Iso.inv_hom_id_assoc, coprod.inr_desc_assoc, coprod.map_desc,
          Category.id_comp]
    have hl : left ≫ u = left ≫ v := ih _ _ (lower u hu) (lower v hv)
    have hr : right ≫ u = right ≫ v := (upper u hu).trans (congrArg
      (fun w => row ≫ coprod.desc (𝟙 B) w) hl |>.trans (upper v hv).symm)
    apply (cancel_epi split.inv).mp
    apply coprod.hom_ext
    · exact (Category.assoc _ _ _).symm.trans (hl.trans (Category.assoc _ _ _))
    · exact (Category.assoc _ _ _).symm.trans (hr.trans (Category.assoc _ _ _))

theorem uniformity_of_acyclic {A B D : Q} (h : A ⟶ D)
    {f : A ⟶ B ⨿ A} (bound : AcyclicStep Seed B f) (g : D ⟶ B ⨿ D)
    (comm : f ≫ coprod.map (𝟙 B) h = h ≫ g) :
    iterateChosen Seed f = h ≫ iterateChosen Seed g :=
  fixedPoint_unique Seed bound _ _ (iterateChosen_fixpoint Seed f)
    (iterate_solution_of_square Seed h f g comm)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.AcyclicStepUniformity
