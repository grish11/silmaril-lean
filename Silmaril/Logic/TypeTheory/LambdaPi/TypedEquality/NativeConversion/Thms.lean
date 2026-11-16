module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeConversion.Defs
import Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeConversion

public section

namespace Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeConversion

open Silmaril.Calculi.LambdaCube

/-- Renaming a source term composes its variable assignment. -/
theorem term_rename {n m : ℕ} (t : SourceTerm n) (r : Fin n → Fin m)
    (σ : Fin m → LambdaPi.Term) : term σ (t.rename r) = term (σ ∘ r) t :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeConversion.term_rename t r σ

/-- Native renaming acts on the explicit source-variable assignment. -/
theorem term_nativeRename {n : ℕ} (t : SourceTerm n) (σ : Fin n → LambdaPi.Term)
    (r : ℕ → ℕ) : (term σ t).rename r = term (fun i => (σ i).rename r) t :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeConversion.term_nativeRename t σ r

/-- Native substitution acts on the explicit source-variable assignment. -/
theorem term_nativeSubst {n : ℕ} (t : SourceTerm n) (σ : Fin n → LambdaPi.Term)
    (τ : ℕ → LambdaPi.Term) : (term σ t).subst τ = term (fun i => (σ i).subst τ) t :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeConversion.term_nativeSubst t σ τ

/-- Source substitution composes compiled assignments. -/
theorem term_subst {n m : ℕ} (t : SourceTerm n) (τ : Fin n → SourceTerm m)
    (σ : Fin m → LambdaPi.Term) :
    term σ (t.subst τ) = term (fun i => term σ (τ i)) t :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeConversion.term_subst t τ σ

/-- Source binder discharge is native capture-avoiding beta substitution. -/
theorem term_instantiate {n : ℕ} (b : SourceTerm (n + 1)) (a : SourceTerm n)
    (σ : Fin n → LambdaPi.Term) :
    term σ (b.instantiate a) = (term (lift σ) b).substOne (term σ a) :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeConversion.term_instantiate b a σ

/-- Every independently checked LF equality gives native raw beta-eta conversion.
The assignment may use named constants for globals and native variables for locals.
This theorem supplies conversion, not native endpoint typing or its converse. -/
theorem equality {k n : ℕ} {S : IntensionalMLTT.Context k}
    {Γ : IntensionalMLTT.Context n} {t u A : SourceTerm n}
    (h : Equality S Γ t u A) (σ : Fin n → LambdaPi.Term) :
    BetaEtaConversion (term σ t) (term σ u) :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeConversion.equality h σ

/-- The same forward equality theorem in the existing named beta-eta calculus. -/
theorem equality_conversion {k n : ℕ} {S : IntensionalMLTT.Context k}
    {Γ : IntensionalMLTT.Context n} {t u A : SourceTerm n}
    (h : Equality S Γ t u A) (σ : Fin n → LambdaPi.Term)
    (declared : String → LambdaPi.Term → Prop) :
    (Calculus.lfBetaEta declared).Conversion (term σ t) (term σ u) :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeConversion.equality_conversion h σ declared

end Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeConversion
