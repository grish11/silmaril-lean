module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Defs

/-! # Native quotient for the CFG entry equations -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Region syntax with fixed input and exit contexts. -/
def TypedRegion (Γ : VCtx τ) (L : LCtx τ) := {r : Region Φ // HasType Γ r L}

/-- Equivalence of typed representatives under the CFG entry equations. -/
def cfgSetoid (Γ : VCtx τ) (L : LCtx τ) : Setoid (TypedRegion (Φ := Φ) Γ L) where
  r r s := CfgEquiv Γ r.val s.val L
  iseqv := ⟨fun r => .refl r.property, .symm, .trans⟩

/-- The contextual carrier of regions modulo the checked CFG entry equations. -/
abbrev CfgQuotient (Γ : VCtx τ) (L : LCtx τ) := Quotient (cfgSetoid (Φ := Φ) Γ L)

end Silmaril.Isotope.LambdaSSA.Region
