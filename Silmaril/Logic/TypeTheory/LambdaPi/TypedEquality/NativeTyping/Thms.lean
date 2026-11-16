module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeTyping.Defs
import Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeTyping

public section
namespace Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeTyping
open NativeConversion

/-- Extend an actual native assignment by the freshly bound local variable. -/
theorem Assignment.lift {n : ℕ} {Γ : IntensionalMLTT.Context n}
    {declared : String → LambdaPi.Term → Prop} {Δ : List LambdaPi.Term}
    {σ : Fin n → LambdaPi.Term} {A : IntensionalMLTT.Term n}
    (hσ : Assignment Γ declared Δ σ)
    (hA : Derives (Calculus.lfBetaEta declared) ∅ ⟨Δ, term σ A, LambdaPi.Term.univ .type⟩) :
    Assignment (Γ.snoc A) declared (term σ A :: Δ) (NativeConversion.lift σ) :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeTyping.assignment_lift hσ hA

/-- Both endpoints of any independent source equality have actual native LF
beta-eta typings under an actual native context and assignment of all variables.
Global declarations are included in the assignment; no endpoint certificate is assumed. -/
theorem endpoints {k n : ℕ} {S : IntensionalMLTT.Context k} {Γ : IntensionalMLTT.Context n}
    {t u A : IntensionalMLTT.Term n} (h : Equality S Γ t u A)
    {declared : String → LambdaPi.Term → Prop} {Δ : List LambdaPi.Term}
    (hΔ : ContextOK (Calculus.lfBetaEta declared) Δ) (σ : Fin n → LambdaPi.Term)
    (hσ : Assignment Γ declared Δ σ) :
    Derives (Calculus.lfBetaEta declared) ∅ ⟨Δ, term σ t, term σ A⟩ ∧
      Derives (Calculus.lfBetaEta declared) ∅ ⟨Δ, term σ u, term σ A⟩ :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeTyping.endpoints h hΔ σ hσ

end Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeTyping
