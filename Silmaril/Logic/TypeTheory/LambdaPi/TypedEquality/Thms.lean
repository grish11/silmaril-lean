module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.Defs
public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Extensional.Assignment
public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Extensional.Syntax.Thms
import Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEquality

public section

namespace Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality

open Silmaril.Logic.TypeTheory.IntensionalMLTT
open Silmaril.Logic.TypeTheory.IntensionalMLTT.Extensional
open Silmaril.Logic.TypeTheory.ExtensionalMLTT

/-- Every independently generated source equality translates under an actual assignment.
This checks all source rules, including dependent beta and eta. It does not assert
completeness for ordinary LF raw conversion or source context transport.
-/
theorem Equality.translate {k n : ℕ} {S : Context k} {Γ : Context n} {t u A : Term n}
    (h : Equality S Γ t u A) (Δ : ECtx) (σ : Fin n → ETm 0)
    (hσ : TypedAssignment Γ Δ σ) (hΔ : ECtx.JEqH ∅ Δ .unit .star .star) :
    ECtx.JEqH ∅ Δ (term σ A) (term σ t) (term σ u) :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEquality.translate h Δ σ hσ hΔ

/-- Every source equality has an independently formed source context. -/
theorem Equality.context {k n : ℕ} {S : Context k} {Γ : Context n} {t u A : Term n}
    (h : Equality S Γ t u A) : ContextFormed S Γ :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEquality.source_context h

/-- Source context formation constructs actual target context and variable typings. -/
theorem ContextFormed.realizes {k n : ℕ} {S : Context k} {Γ : Context n}
    (h : ContextFormed S Γ) (ι : Fin n → String) (hι : Function.Injective ι) :
    ECtx.JEqH ∅ (Extensional.context Γ ι) .unit .star .star ∧
      TypedAssignment Γ (Extensional.context Γ ι) (fun i => .fv (ι i)) :=
  (Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEquality.realizes Γ).2 h ι hι

/-- Naming a checked source derivation produces an actual target derivation. -/
theorem Equality.named {k n : ℕ} {S : Context k} {Γ : Context n} {t u A : Term n}
    (h : Equality S Γ t u A) (ι : Fin n → String) (hι : Function.Injective ι) :
    ECtx.JEqH ∅ (Extensional.context Γ ι) (Extensional.named ι A)
      (Extensional.named ι t) (Extensional.named ι u) := by
  obtain ⟨hΓ, hσ⟩ := h.context.realizes ι hι
  exact h.translate _ _ hσ hΓ

end Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality
