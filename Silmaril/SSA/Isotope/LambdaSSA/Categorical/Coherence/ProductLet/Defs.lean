module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Defs

/-! # The native product binding arrow -/

@[expose] public section

universe u u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V]
  (J : V ⥤ C) [FreydCategory J] {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)

/-- The graph rule's bind, unpacking the product with the right field newest. -/
noncomputable def bindProduct {Γ : VCtx τ} {A B : τ} {X : V}
    (value : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj (Silmaril.product A B)))
    (body : J.obj (ctxObj M (B :: A :: Γ)) ⟶ J.obj X) :
    J.obj (ctxObj M Γ) ⟶ J.obj X :=
  Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind J value
    (J.map ((𝟙 _) ⊗ₘ (M.productIso A B).hom) ≫ J.map (ctxPairIso M Γ A B).hom ≫ body)

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
