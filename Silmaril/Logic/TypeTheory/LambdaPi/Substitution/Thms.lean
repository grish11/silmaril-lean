module

public import Silmaril.Logic.TypeTheory.LambdaPi.Substitution.Defs
public import Silmaril.Proofs.Logic.TypeTheory.LambdaPi.Substitution

@[expose] public section

namespace Silmaril.Logic.TypeTheory.LambdaPi

open CategoryTheory Silmaril.Calculi.LambdaCube
open Silmaril.Proofs.Logic.TypeTheory.LambdaPi

/-- Capture-avoiding renaming preserves an explicit free-variable budget. -/
theorem Term.Scoped.rename {t : Term} {n m : ℕ} (h : t.Scoped n)
    (ρ : ℕ → ℕ) (hρ : ∀ i < n, ρ i < m) : Term.Scoped m (t.rename ρ) :=
  scoped_rename t ρ h hρ

/-- Without judgment hypotheses, both the subject and its type obey the context's variable budget. -/
theorem Derives.scoped {C : Calculus} {J : Judgment} (h : Derives C ∅ J) :
    J.term.Scoped J.context.length ∧ J.type.Scoped J.context.length := derives_scoped h

/-- Every closed derivation has a context built from actual domain-formation proofs. -/
theorem Derives.contextOK {C : Calculus} {J : Judgment} (h : Derives C ∅ J) :
    ContextOK C J.context := derives_context h

/-- Closed terms and types can be used in any well-formed local context. -/
theorem Derives.weaken_closed {C : Calculus} {Δ : List Term} {t A : Term}
    (h : Derives C ∅ ⟨[], t, A⟩) (hΔ : ContextOK C Δ) : Derives C ∅ ⟨Δ, t, A⟩ :=
  derives_closed_weaken hΔ h

/-- A looked-up variable has its properly shifted type. -/
theorem Lookup.derives {C : Calculus} {Γ : List Term} {i : ℕ} {A : Term}
    (h : Lookup Γ i A) (hΓ : ContextOK C Γ) : Derives C ∅ ⟨Γ, .var i, A⟩ := lookup_derives hΓ h

/-- Any derivable product term has a Type-sorted domain, including through conversion. -/
theorem Derives.pi_domain {C : Calculus} {Γ : List Term} {A B T : Term}
    (h : Derives C ∅ ⟨Γ, .pi A B, T⟩) : Derives C ∅ ⟨Γ, A, Term.univ .type⟩ :=
  derives_pi_domain h A B rfl

/-- Simultaneous substitution preserves every closed λΠ typing rule.

Here closed means no judgment hypotheses; source and target local contexts may be nonempty.
-/
theorem Derives.subst {C : Calculus} {Γ Δ : List Term} {t A : Term} {σ : ℕ → Term}
    (h : Derives C ∅ ⟨Γ, t, A⟩) (hσ : TypedSubstitution C Γ Δ σ) :
    Derives C ∅ ⟨Δ, t.subst σ, A.subst σ⟩ := derives_substitution h hσ

/-- Identity assignments are typed in every well-formed context. -/
theorem TypedSubstitution.identity {C : Calculus} {Γ : List Term} (hΓ : ContextOK C Γ) :
    TypedSubstitution C Γ Γ Pseudo.var := typed_substitution_id hΓ

/-- Typed substitutions compose by substituting every image. -/
theorem TypedSubstitution.comp {C : Calculus} {Γ Δ Θ : List Term} {σ τ : ℕ → Term}
    (hσ : TypedSubstitution C Γ Δ σ) (hτ : TypedSubstitution C Δ Θ τ) :
    TypedSubstitution C Γ Θ (fun i => (σ i).subst τ) := typed_substitution_comp hσ hτ

/-- Extend a typed substitution beneath a well-formed new target domain. -/
theorem TypedSubstitution.lift {C : Calculus} {Γ Δ : List Term} {A : Term} {σ : ℕ → Term}
    (hσ : TypedSubstitution C Γ Δ σ) (hA : Derives C ∅ ⟨Δ, A.subst σ, Term.univ .type⟩) :
    TypedSubstitution C (A :: Γ) (A.subst σ :: Δ) (Pseudo.liftSub σ) := typed_substitution_lift hσ hA

/-- A typed argument discharges the newest local variable. -/
theorem TypedSubstitution.single {C : Calculus} {Γ : List Term} {A a : Term}
    (ha : Derives C ∅ ⟨Γ, a, A⟩) :
    TypedSubstitution C (A :: Γ) Γ (fun | 0 => a | i + 1 => .var i) := typed_substitution_single ha

/-- Dependent one-variable substitution, including substitution in the result type. -/
theorem Derives.substOne {C : Calculus} {Γ : List Term} {A B a b : Term}
    (hb : Derives C ∅ ⟨A :: Γ, b, B⟩) (ha : Derives C ∅ ⟨Γ, a, A⟩) :
    Derives C ∅ ⟨Γ, b.substOne a, B.substOne a⟩ := hb.subst (TypedSubstitution.single ha)

/-- A local context with actual domain-formation evidence. -/
structure LocalContext (C : Calculus) where
  terms : List Term
  valid : ContextOK C terms

/-- A context map Γ → Δ interprets Δ's variables by terms in Γ.

Assignments are compared syntactically, including their values beyond the finite context.
-/
structure ContextMap {C : Calculus} (Γ Δ : LocalContext C) where
  assignment : ℕ → Term
  typed : TypedSubstitution C Δ.terms Γ.terms assignment

@[ext] theorem ContextMap.ext {C : Calculus} {Γ Δ : LocalContext C} {F G : ContextMap Γ Δ}
    (h : F.assignment = G.assignment) : F = G := by
  cases F
  cases G
  cases h
  rfl

/-- The usual contravariant direction of context substitution, with actual category laws. -/
instance {C : Calculus} : Category (LocalContext C) where
  Hom := ContextMap
  id Γ := ⟨Pseudo.var, TypedSubstitution.identity Γ.valid⟩
  comp F G := ⟨fun i => (G.assignment i).subst F.assignment, G.typed.comp F.typed⟩
  id_comp F := by
    apply ContextMap.ext
    funext i
    exact Pseudo.subst_var _ _ (fun _ => rfl)
  comp_id F := by apply ContextMap.ext; rfl
  assoc F G H := by
    apply ContextMap.ext
    funext i
    exact (Pseudo.subst_subst (H.assignment i) F.assignment G.assignment).symm

end Silmaril.Logic.TypeTheory.LambdaPi
