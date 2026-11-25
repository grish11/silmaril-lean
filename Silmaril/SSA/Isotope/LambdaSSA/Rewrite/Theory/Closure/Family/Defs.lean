module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Defs

/-! # Typed continuation families with value branches -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Each continuation body is typed with its label argument and captures,
and passes constructor values to its own labels. -/
@[expose] def LSubst.ValueFamily (Γ : VCtx τ) (L K : LCtx τ) (σ : Nat → Region Φ) : Prop :=
  ∀ ⦃ℓ A⦄, At L ℓ A → ValueBranches (A :: Γ) (σ ℓ) K

end Silmaril.Isotope.LambdaSSA.Region
