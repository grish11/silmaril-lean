module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Rules.Defs

@[expose] public section

/-!
# Context-respecting variable maps

A renaming preserves declaration lookup. A simultaneous substitution provides
an actual derivation for each source declaration instantiated in its target.
These are syntactic premises, with no semantic soundness assumption.
-/

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT

/-- A variable renaming that preserves the types retrieved from a telescope. -/
def Renaming {n m : ℕ} (Γ : Context n) (Δ : Context m) (ρ : Fin n → Fin m) : Prop :=
  ∀ {i A}, Lookup Γ i A → Lookup Δ (ρ i) (A.rename ρ)

/-- A simultaneous substitution with derivations for its variable assignments. -/
def Substitution {n m : ℕ} (Γ : Context n) (Δ : Context m) (σ : Fin n → Term m) : Type :=
  ∀ {i A}, Lookup Γ i A → Derivation Δ (σ i) (A.subst σ)

end Silmaril.Logic.TypeTheory.IntensionalMLTT
