module

public import Silmaril.Logic.TypeTheory.LambdaPi.Encoding.Thms

@[expose] public section

/-!
# Typed substitutions for closed λΠ derivations

Contexts store each declaration relative to its older tail. A lookup therefore
includes the shifts needed to use that type in the whole context. Typed
substitutions give actual target derivations for those lookup types.
-/

namespace Silmaril.Logic.TypeTheory.LambdaPi

/-- A local context built from actual Type-sorted domain derivations. -/
inductive ContextOK (C : Calculus) : List Term → Prop where
  | nil : ContextOK C []
  | cons {Γ A} : ContextOK C Γ → Derives C ∅ ⟨Γ, A, Term.univ .type⟩ → ContextOK C (A :: Γ)

/-- The type of a variable, shifted into the entire newest-first context. -/
inductive Lookup : List Term → ℕ → Term → Prop where
  | zero (Γ A) : Lookup (A :: Γ) 0 (A.rename Nat.succ)
  | succ {Γ i A} (B) : Lookup Γ i A → Lookup (B :: Γ) (i + 1) (A.rename Nat.succ)

/-- A simultaneous substitution certified on all source variables, into a well-formed target. -/
structure TypedSubstitution (C : Calculus) (Γ Δ : List Term) (σ : ℕ → Term) : Prop where
  target : ContextOK C Δ
  entries : ∀ {i A}, Lookup Γ i A → Derives C ∅ ⟨Δ, σ i, A.subst σ⟩

end Silmaril.Logic.TypeTheory.LambdaPi
