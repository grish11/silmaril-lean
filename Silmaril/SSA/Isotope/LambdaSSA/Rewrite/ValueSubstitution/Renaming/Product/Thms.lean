module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.ProductLet.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.EnvironmentNaturality

/-! # Change captured inputs and route exits through the native product bind -/

public section

universe v₁ v₂ u₁ u₂ u

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) [DistributiveFreydCategory J] {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {Γ Δ : VCtx τ} {A B : τ}

set_option backward.isDefEq.respectTransparency false in
/-- Changing the captured environment extends the map under both fields in
their exact order. -/
theorem bindProduct_pre_map {X : V} (p : ctxObj M Δ ⟶ ctxObj M Γ)
    (value : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj (Silmaril.product A B)))
    (body : J.obj (ctxObj M (B :: A :: Γ)) ⟶ J.obj X) :
    bindProduct J M (J.map p ≫ value) (J.map ((p ▷ M.obj A) ▷ M.obj B) ≫ body) =
      J.map p ≫ bindProduct J M value body := by
  simpa only [bindProduct, MonoidalCategory.id_tensorHom, ctxPairIso, Iso.symm_hom, Category.assoc, ctxObj] using
    Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.bindPair_pre_map J p (M.productIso A B).hom value body

set_option backward.isDefEq.respectTransparency false in
/-- Route the labels after the product bind while preserving its initializer
and the captured input map of its two-field body. -/
theorem bindProduct_transfer {B₁ Q X : V} (p : ctxObj M Δ ⟶ ctxObj M Γ)
    (value : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj (Silmaril.product A B)))
    {actual : J.obj (ctxObj M (B :: A :: Δ)) ⟶ J.obj Q}
    {body : J.obj (ctxObj M (B :: A :: Γ)) ⟶ J.obj B₁}
    {cut : J.obj Q ⟶ J.obj X} {route : J.obj B₁ ⟶ J.obj X}
    (body_eq : actual ≫ cut = J.map ((p ▷ M.obj A) ▷ M.obj B) ≫ body ≫ route) :
    bindProduct J M (J.map p ≫ value) actual ≫ cut =
      J.map p ≫ bindProduct J M value body ≫ route := by
  rw [bindProduct_postcomp, body_eq,
    ← Category.assoc (J.map ((p ▷ M.obj A) ▷ M.obj B)) body route,
    ← bindProduct_postcomp, bindProduct_pre_map, Category.assoc]

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
