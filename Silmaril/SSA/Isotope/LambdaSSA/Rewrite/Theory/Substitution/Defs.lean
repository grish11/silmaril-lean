module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Defs
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Continuation

/-! # Typed branch forwarding substitutions -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v}

/-- Each replacement forwards to a label with a constructor-valued argument
in the context of the original argument and the captured values. -/
@[expose] def LSubst.Forwards (Γ : VCtx τ) (L K : LCtx τ) (σ : Nat → Region Φ) : Prop :=
  ∀ ⦃ℓ A⦄, At L ℓ A →
    ∃ (j : Nat) (b : Tm Φ) (B : τ), σ ℓ = .br j b ∧ At K j B ∧ Tm.BranchValue (A :: Γ) b B

end Silmaril.Isotope.LambdaSSA.Region
