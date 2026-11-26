module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Monad.Adjunction

public section

namespace Silmaril.Proofs.MLIR.Signature.ChosenGenerators

open CategoryTheory CategoryTheory.Limits

universe v u

variable {D : Type u} [Category.{v} D] [HasBinaryCoproducts D] (C S : D)

theorem unit_app : (Under.costarAdjForget C).unit.app S = coprod.inr := by
  rw [Under.costarAdjForget, Adjunction.comp_unit_app]
  change (coprod.inr ≫ 𝟙 _) ≫ 𝟙 _ = coprod.inr
  simp only [Category.comp_id]

theorem homEquiv_apply (X : Under C) (f : (Under.costar C).obj S ⟶ X) :
    (Under.costarAdjForget C).homEquiv S X f = coprod.inr ≫ f.right := by
  rw [Adjunction.homEquiv_apply, unit_app]
  rfl

theorem homEquiv_symm_right (X : Under C) (f : S ⟶ X.right) :
    (((Under.costarAdjForget C).homEquiv S X).symm f).right = coprod.desc X.hom f := by
  let g := ((Under.costarAdjForget C).homEquiv S X).symm f
  apply coprod.hom_ext
  · rw [coprod.inl_desc]
    have h := coprod.inl_desc (coprod.inl : C ⟶ C ⨿ S) (𝟙 (C ⨿ S))
    exact (congrArg (fun k => k ≫ g.right) h).symm.trans (Under.w g)
  · rw [coprod.inr_desc]
    exact (homEquiv_apply C S X g).symm.trans
      (((Under.costarAdjForget C).homEquiv S X).apply_symm_apply f)

private theorem counit_right (X : Under C) :
    ((Under.costarAdjForget C).counit.app X).right = coprod.desc X.hom (𝟙 X.right) :=
  (congrArg (fun f => f.right) ((Under.costarAdjForget C).homEquiv_symm_id X)).symm.trans
    (homEquiv_symm_right C X.right X (𝟙 X.right))

theorem mul_app :
    (Under.costarAdjForget C).toMonad.μ.app S = coprod.desc coprod.inl (𝟙 (C ⨿ S)) := by
  change ((Under.costarAdjForget C).counit.app ((Under.costar C).obj S)).right = _
  refine (counit_right C ((Under.costar C).obj S)).trans ?_
  exact congrArg (fun f => coprod.desc f (𝟙 (C ⨿ S)))
    (coprod.inl_desc (coprod.inl : C ⟶ C ⨿ S) (𝟙 (C ⨿ S)))

end Silmaril.Proofs.MLIR.Signature.ChosenGenerators
