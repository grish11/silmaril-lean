module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.Substitution.Defs
import Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualitySubstitution

public section

/-!
# Source typed substitution for checked LF equality

Assignments contain actual source equality derivations for every variable
image. Lifting them beneath a binder uses the source weakening theorem.
Every checked equality rule is stable under these assignments, including
dependent beta and eta. No result here is inferred from target interpretation.
-/

namespace Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality

open Silmaril.Logic.TypeTheory.IntensionalMLTT

/-- Assign a genuinely typed source term to the newest declaration. -/
theorem TypedSubstitution.cons {n l m : ℕ} {Γ : Context n} {T : Context l} {Δ : Context m}
    {σ : Fin n → Term m} {A : Term n} {a : Term m}
    (hσ : TypedSubstitution Γ T Δ σ) (ha : Equality T Δ a a (A.subst σ)) :
    TypedSubstitution (Γ.snoc A) T Δ (Fin.cons a σ) :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualitySubstitution.cons hσ ha

/-- Lookup-preserving renamings supply genuinely typed variable images. -/
theorem TypedSubstitution.ofRenaming {n l m : ℕ} {Γ : Context n} {T : Context l} {Δ : Context m}
    (hΔ : ContextFormed T Δ) (ρ : Fin n → Fin m) (hρ : Renaming Γ Δ ρ) :
    TypedSubstitution Γ T Δ (fun i => .var (ρ i)) := by
  intro i A hi
  simpa only [Term.subst_renaming] using Equality.var hΔ (hρ hi)

/-- Extend a source typed substitution beneath a genuinely formed local binder. -/
theorem TypedSubstitution.lift {n l m : ℕ} {Γ : Context n} {T : Context l} {Δ : Context m}
    {σ : Fin n → Term m} {A : Term n} (hσ : TypedSubstitution Γ T Δ σ)
    (hA : Equality T Δ (A.subst σ) (A.subst σ) (.univ 0)) :
    TypedSubstitution (Γ.snoc A) T (Δ.snoc (A.subst σ)) (Term.upSub σ) :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualitySubstitution.lift hσ hA

/-- Every checked source rule is preserved by actually source-typed variable images. -/
theorem Equality.subst {k n l m : ℕ} {S : Context k} {T : Context l}
    {Γ : Context n} {Δ : Context m} {t u A : Term n}
    (h : Equality S Γ t u A) (hΔ : ContextFormed T Δ)
    (σ : Fin n → Term m) (hσ : TypedSubstitution Γ T Δ σ) :
    Equality T Δ (t.subst σ) (u.subst σ) (A.subst σ) :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualitySubstitution.subst h hΔ σ hσ

end Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality
