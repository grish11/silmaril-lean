module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.Substitution.Thms
import Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityContextConversion

public section

/-!
# Source conversion of the newest local declaration

A proved source equality A = A' at Type allows the newest local declaration
to change from x : A to x : A'. Endpoints and their dependent carrier retain
the same syntax. The proof constructs a source-typed identity assignment:
the newest variable uses weakened source conversion; older lookups persist.

This does not yet provide conversion of an earlier declaration under an
arbitrary dependent context suffix, or native raw-LF completeness.
-/

namespace Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality

open Silmaril.Logic.TypeTheory.IntensionalMLTT

/-- The actual source-typed identity assignment between converted local contexts. -/
theorem TypedSubstitution.convertLast {k n : ℕ} {S : Context k} {Γ : Context n} {A A' : Term n}
    (hAA' : Equality S Γ A A' (.univ 0)) :
    TypedSubstitution (Γ.snoc A) S (Γ.snoc A') Term.var :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityContextConversion.identity hAA'

/-- Replace the newest declaration by a judgmentally equal source type. -/
theorem Equality.convertLast {k n : ℕ} {S : Context k} {Γ : Context n} {A A' : Term n}
    {t u B : Term (n + 1)} (h : Equality S (Γ.snoc A) t u B)
    (hAA' : Equality S Γ A A' (.univ 0)) : Equality S (Γ.snoc A') t u B :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityContextConversion.convertLast h hAA'

/-- The converted contexts prove precisely the same checked equality sentences. -/
theorem Equality.convertLast_iff {k n : ℕ} {S : Context k} {Γ : Context n} {A A' : Term n}
    {t u B : Term (n + 1)} (hAA' : Equality S Γ A A' (.univ 0)) :
    Equality S (Γ.snoc A) t u B ↔ Equality S (Γ.snoc A') t u B :=
  ⟨fun h => h.convertLast hAA', fun h => h.convertLast (.symm hAA')⟩

end Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality
