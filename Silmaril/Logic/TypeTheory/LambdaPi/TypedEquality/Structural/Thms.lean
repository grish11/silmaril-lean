module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.Thms
public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Substitution.Thms
import Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityStructural

public section

/-!
# Source structural transport for checked LF equality

Renaming preserves source equality when it preserves source declaration lookup
and the destination context is independently source-formed. This covers all
source rules, including dependent beta and eta, and permits different source
and destination signatures. Local weakening follows as a special case.

These results use no target interpretation. Downstream modules provide typed
substitutions and conversion of context declarations; native raw-conversion
completeness remains a separate problem.
-/

namespace Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality

open Silmaril.Logic.TypeTheory.IntensionalMLTT

/-- Lookup-preserving scope maps transport every independently checked source rule. -/
theorem Equality.rename {k n l m : ℕ} {S : Context k} {T : Context l}
    {Γ : Context n} {Δ : Context m} {t u A : Term n}
    (h : Equality S Γ t u A) (hΔ : ContextFormed T Δ)
    (ρ : Fin n → Fin m) (hρ : Renaming Γ Δ ρ) :
    Equality T Δ (t.rename ρ) (u.rename ρ) (A.rename ρ) :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityStructural.rename h hΔ ρ hρ

/-- Adding a genuinely formed local variable preserves every source equality. -/
theorem Equality.weaken {k n : ℕ} {S : Context k} {Γ : Context n} {t u A B : Term n}
    (h : Equality S Γ t u A) (hB : Equality S Γ B B (.univ 0)) :
    Equality S (Γ.snoc B) t.weaken u.weaken A.weaken :=
  h.rename (.snoc h.context hB) Fin.succ (Renaming.weaken Γ B)

end Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality
