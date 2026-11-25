module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Thms

/-! # Typed continuation families modulo native rewrite equivalence -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- An exit interface with a fixed captured context and instruction signature. -/
structure ContinuationContext (Φ : Type v) (Γ : VCtx τ) where
  labels : LCtx τ

/-- A typed continuation family before taking the rewrite quotient. -/
abbrev ContinuationFamily (Γ : VCtx τ) (L K : LCtx τ) :=
  {σ : Nat → Region Φ // LSubst.ValueFamily Γ L K σ}

@[expose] def continuationSetoid (Γ : VCtx τ) (L K : LCtx τ) :
    Setoid (ContinuationFamily (Φ := Φ) Γ L K) where
  r σ υ := ∀ ⦃ℓ A⦄, At L ℓ A → SubstitutionEquiv (A :: Γ) (σ.val ℓ) (υ.val ℓ) K
  iseqv := ⟨fun σ _ _ hℓ => .base (.refl (σ.property hℓ).hasType),
    fun h _ _ hℓ => (h hℓ).symm, fun h h' _ _ hℓ => (h hℓ).trans (h' hℓ)⟩

/-- Continuation families identified at every well-typed source label. -/
abbrev ContinuationHom (Γ : VCtx τ) (L K : LCtx τ) :=
  Quotient (continuationSetoid (Φ := Φ) Γ L K)

variable {Γ : VCtx τ} {L K P : LCtx τ}

@[expose] def ContinuationFamily.identity (Γ : VCtx τ) (L : LCtx τ) :
    ContinuationFamily (Φ := Φ) Γ L L :=
  ⟨labelId, LSubst.ValueFamily.id Γ L⟩

@[expose] def ContinuationFamily.compose
    (σ : ContinuationFamily (Φ := Φ) Γ L K) (υ : ContinuationFamily (Φ := Φ) Γ K P) :
    ContinuationFamily (Φ := Φ) Γ L P :=
  ⟨compLSubst σ.val υ.val, σ.property.comp υ.property⟩

@[expose] def ContinuationHom.identity (Γ : VCtx τ) (L : LCtx τ) : ContinuationHom (Φ := Φ) Γ L L :=
  Quotient.mk _ (ContinuationFamily.identity Γ L)

@[expose] def ContinuationHom.compose
    (f : ContinuationHom (Φ := Φ) Γ L K) (g : ContinuationHom (Φ := Φ) Γ K P) :
    ContinuationHom (Φ := Φ) Γ L P :=
  Quotient.map₂ ContinuationFamily.compose
    (fun σ _ hσ _ _ hυ => LSubst.comp_substitutionEquiv hσ hυ σ.property) f g

end Silmaril.Isotope.LambdaSSA.Region
