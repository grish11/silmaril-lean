module

public import Silmaril.Logic.TypeTheory.LambdaPi.ContextConversion.Defs
public import Silmaril.Proofs.Logic.TypeTheory.LambdaPi.ContextConversion

@[expose] public section

namespace Silmaril.Logic.TypeTheory.LambdaPi

open CategoryTheory Silmaril.Calculi.LambdaCube
open Silmaril.Proofs.Logic.TypeTheory.LambdaPi

/-- Raw β/rewrite conversion is stable under capture-avoiding renaming. -/
theorem Calculus.Conversion.rename {C : Calculus} {t u : Term}
    (h : C.Conversion t u) (ρ : ℕ → ℕ) : C.Conversion (t.rename ρ) (u.rename ρ) := conversion_rename h ρ

/-- Both sides of a context conversion have actual domain-formation derivations. -/
theorem ContextConversion.contexts {C : Calculus} {Γ Δ : List Term}
    (h : ContextConversion C Γ Δ) : ContextOK C Γ ∧ ContextOK C Δ := context_conversion_contexts h

theorem ContextConversion.refl {C : Calculus} {Γ : List Term} (h : ContextOK C Γ) :
    ContextConversion C Γ Γ := context_conversion_id h

theorem ContextConversion.symm {C : Calculus} {Γ Δ : List Term} (h : ContextConversion C Γ Δ) :
    ContextConversion C Δ Γ := context_conversion_symm h

theorem ContextConversion.trans {C : Calculus} {Γ Δ Θ : List Term}
    (h : ContextConversion C Γ Δ) (h' : ContextConversion C Δ Θ) : ContextConversion C Γ Θ :=
  context_conversion_trans h h'

/-- The unchanged variables form a typed substitution between convertible contexts. -/
theorem ContextConversion.typed {C : Calculus} {Γ Δ : List Term} (h : ContextConversion C Γ Δ) :
    TypedSubstitution C Γ Δ Pseudo.var := context_conversion_typed h

/-- Replacing convertible local declaration types preserves every closed typing derivation. -/
theorem Derives.changeContext {C : Calculus} {Γ Δ : List Term} {t A : Term}
    (h : Derives C ∅ ⟨Γ, t, A⟩) (hc : ContextConversion C Γ Δ) : Derives C ∅ ⟨Δ, t, A⟩ := by
  simpa only [Pseudo.subst_var _ _ (fun _ => rfl)] using h.subst hc.typed

/-- The two directions of context conversion are inverse context morphisms. -/
def LocalContext.isoOfConversion {C : Calculus} (Γ Δ : LocalContext C)
    (h : ContextConversion C Γ.terms Δ.terms) : Γ ≅ Δ where
  hom := ⟨Pseudo.var, h.symm.typed⟩
  inv := ⟨Pseudo.var, h.typed⟩
  hom_inv_id := by apply ContextMap.ext; rfl
  inv_hom_id := by apply ContextMap.ext; rfl

end Silmaril.Logic.TypeTheory.LambdaPi
