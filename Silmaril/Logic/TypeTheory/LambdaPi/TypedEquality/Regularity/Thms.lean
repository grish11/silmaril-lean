module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.Substitution.Thms
import Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityRegularity

public section
namespace Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality
open Silmaril.Logic.TypeTheory.IntensionalMLTT

/-- Every global declaration type is independently formed at one of LF's two sorts. -/
theorem SignatureFormed.lookup {n : ℕ} {S : Context n} (hS : SignatureFormed S)
    {i : Fin n} {A : Term n} (hi : Lookup S i A) :
    ∃ s : LFSort, Equality S S A A (.univ s.val) :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityRegularity.signature_lookup hS hi

/-- Lookup formation covers global declarations and local Type-only binders. -/
theorem ContextFormed.lookup {k n : ℕ} {S : Context k} {Γ : Context n}
    (hΓ : ContextFormed S Γ) {i : Fin n} {A : Term n} (hi : Lookup Γ i A) :
    ∃ s : LFSort, Equality S Γ A A (.univ s.val) :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityRegularity.context_lookup hΓ hi

/-- The carrier of a checked equality is independently formed, or is unsorted Kind. -/
theorem Equality.regularity {k n : ℕ} {S : Context k} {Γ : Context n} {t u A : Term n}
    (h : Equality S Γ t u A) :
    A = .univ 1 ∨ ∃ s : LFSort, Equality S Γ A A (.univ s.val) :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityRegularity.regularity h

end Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality
