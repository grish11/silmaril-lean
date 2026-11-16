module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.Substitution.Thms

public section

namespace Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityContextConversion

open Silmaril.Logic.TypeTheory.IntensionalMLTT
open Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality

theorem identity {k n : ℕ} {S : Context k} {Γ : Context n} {A A' : Term n}
    (hAA' : Equality S Γ A A' (.univ 0)) :
    TypedSubstitution (Γ.snoc A) S (Γ.snoc A') Term.var := by
  have hA' : Equality S Γ A' A' (.univ 0) := .trans (.symm hAA') hAA'
  have hΔ : ContextFormed S (Γ.snoc A') := .snoc hAA'.context hA'
  intro i B hi
  simp only [Term.subst_var]
  cases hi with
  | here => exact .conv (s := 0) (.var hΔ .here) (.symm (hAA'.weaken hA'))
  | there hi => exact .var hΔ (.there hi)

theorem convertLast {k n : ℕ} {S : Context k} {Γ : Context n} {A A' : Term n}
    {t u B : Term (n + 1)} (h : Equality S (Γ.snoc A) t u B)
    (hAA' : Equality S Γ A A' (.univ 0)) : Equality S (Γ.snoc A') t u B := by
  have hA' : Equality S Γ A' A' (.univ 0) := .trans (.symm hAA') hAA'
  have hΔ : ContextFormed S (Γ.snoc A') := .snoc hAA'.context hA'
  simpa only [Term.subst_var] using h.subst hΔ Term.var (identity hAA')

end Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityContextConversion
