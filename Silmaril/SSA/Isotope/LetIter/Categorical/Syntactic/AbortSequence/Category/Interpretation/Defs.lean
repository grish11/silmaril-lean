module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Thms

/-! # Singleton inputs to categorical LetIter interpretation -/

@[expose] public section

universe u u₁ v₁

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  {τ : Type u} [TypeFormers τ]

/-- Remove the two empty-context unit factors from a singleton bound environment. -/
def singletonEnvIso (M : TypeModel τ V) (A : τ) :
    envObj M (Ctx.nil : Ctx Empty τ) (.snoc .nil A) ≅ M.obj A :=
  (λ_ _).trans (λ_ _)

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
