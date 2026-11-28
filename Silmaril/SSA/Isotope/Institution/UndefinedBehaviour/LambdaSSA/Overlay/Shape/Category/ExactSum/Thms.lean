module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.ExactSum.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryFan
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.ExactSum.Laws

/-! # Universal properties of exact sum and empty types -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category

open CategoryTheory CategoryTheory.Limits

universe v w x

variable {α : Type w} {σ : Type x} {κ : Type v} {atomType : α → κ → Prop}
  {A B : Ty κ} {Z : Interface α σ atomType}

@[simp] theorem sumDesc_inl_run (f : single A ⟶ Z) (g : single B ⟶ Z)
    (a : (single (σ := σ) (atomType := atomType) A).Payload 0) (s : σ) :
    (sumDesc f g).run 0 ⟨.inl a.val, .inl a.property⟩ s = f.run 0 a s := rfl

@[simp] theorem sumDesc_inr_run (f : single A ⟶ Z) (g : single B ⟶ Z)
    (b : (single (σ := σ) (atomType := atomType) B).Payload 0) (s : σ) :
    (sumDesc f g).run 0 ⟨.inr b.val, .inr b.property⟩ s = g.run 0 b s := rfl

@[simp] theorem sumInl_desc (f : single A ⟶ Z) (g : single B ⟶ Z) : sumInl A B ≫ sumDesc f g = f :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.ExactSum.sumInl_desc f g

@[simp] theorem sumInr_desc (f : single A ⟶ Z) (g : single B ⟶ Z) : sumInr A B ≫ sumDesc f g = g :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.ExactSum.sumInr_desc f g

theorem sum_hom_ext {f g : single (.coprod A B) ⟶ Z}
    (hl : sumInl A B ≫ f = sumInl A B ≫ g) (hr : sumInr A B ≫ f = sumInr A B ≫ g) : f = g :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.ExactSum.sum_hom_ext hl hr

/-- Exact sum types give binary coproducts of the corresponding singleton
interfaces, with the universal property against arbitrary shaped targets. -/
noncomputable def sumIsColimit (A B : Ty κ) :
    IsColimit (BinaryCofan.mk (sumInl (σ := σ) (atomType := atomType) A B) (sumInr A B)) :=
  BinaryCofan.isColimitMk (fun s => sumDesc s.inl s.inr) (fun _ => sumInl_desc _ _)
    (fun _ => sumInr_desc _ _) (fun _ _ hl hr => sum_hom_ext (hl.trans (sumInl_desc _ _).symm)
      (hr.trans (sumInr_desc _ _).symm))

theorem empty_hom_ext (f g : single .empty ⟶ Z) : f = g :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.ExactSum.empty_hom_ext f g

/-- Initiality uses the fact that no runtime value has the free empty shape. -/
noncomputable def emptyIsInitial : IsInitial (single .empty : Interface α σ atomType) :=
  IsInitial.ofUniqueHom emptyElim (fun _ f => empty_hom_ext f _)

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category
