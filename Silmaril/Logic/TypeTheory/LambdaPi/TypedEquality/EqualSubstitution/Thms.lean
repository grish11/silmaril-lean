module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.EqualSubstitution.Defs
import Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityEqualSubstitution

public section
namespace Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality
open Silmaril.Logic.TypeTheory.IntensionalMLTT

theorem EqualSubstitution.left {n l m : ℕ} {Γ : Context n} {T : Context l} {Δ : Context m}
    {σ τ : Fin n → Term m} (h : EqualSubstitution Γ T Δ σ τ) : TypedSubstitution Γ T Δ σ :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityEqualSubstitution.left h

theorem TypedSubstitution.diagonal {n l m : ℕ} {Γ : Context n} {T : Context l} {Δ : Context m}
    {σ : Fin n → Term m} (h : TypedSubstitution Γ T Δ σ) : EqualSubstitution Γ T Δ σ σ :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityEqualSubstitution.diagonal h

theorem EqualSubstitution.cons {n l m : ℕ} {Γ : Context n} {T : Context l} {Δ : Context m}
    {σ τ : Fin n → Term m} {A : Term n} {a a' : Term m}
    (h : EqualSubstitution Γ T Δ σ τ) (ha : Equality T Δ a a' (A.subst σ)) :
    EqualSubstitution (Γ.snoc A) T Δ (Fin.cons a σ) (Fin.cons a' τ) :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityEqualSubstitution.cons h ha

theorem EqualSubstitution.lift {n l m : ℕ} {Γ : Context n} {T : Context l} {Δ : Context m}
    {σ τ : Fin n → Term m} {A : Term n} (h : EqualSubstitution Γ T Δ σ τ)
    (hA : Equality T Δ (A.subst σ) (A.subst σ) (.univ 0)) :
    EqualSubstitution (Γ.snoc A) T (Δ.snoc (A.subst σ)) (Term.upSub σ) (Term.upSub τ) :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityEqualSubstitution.lift h hA

/-- Both original endpoints respect coherent source-equal substitutions at the
original left substituted carrier. This includes beta, eta and Kind-valued families. -/
theorem Equality.substEndpoints {k n l m : ℕ} {S : Context k} {Γ : Context n}
    {T : Context l} {Δ : Context m} {t u C : Term n} (h : Equality S Γ t u C)
    (hΔ : ContextFormed T Δ) (σ τ : Fin n → Term m) (hστ : EqualSubstitution Γ T Δ σ τ) :
    Equality T Δ (t.subst σ) (t.subst τ) (C.subst σ) ∧
      Equality T Δ (u.subst σ) (u.subst τ) (C.subst σ) :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityEqualSubstitution.endpoints h hΔ σ τ hστ

/-- Source equality itself respects coherent equal substitutions, retaining the
left carrier. Every global is covered because globals are telescope variables. -/
theorem Equality.substCongr {k n l m : ℕ} {S : Context k} {Γ : Context n}
    {T : Context l} {Δ : Context m} {t u C : Term n} (h : Equality S Γ t u C)
    (hΔ : ContextFormed T Δ) (σ τ : Fin n → Term m) (hστ : EqualSubstitution Γ T Δ σ τ) :
    Equality T Δ (t.subst σ) (u.subst τ) (C.subst σ) :=
  .trans (h.subst hΔ σ hστ.left) (h.substEndpoints hΔ σ τ hστ).2

/-- Equal-argument substitution works at every source carrier, including
Kind-sorted dependent carriers. No carrier-formation certificate is assumed. -/
theorem Equality.instantiateAll {k n : ℕ} {S : Context k} {Γ : Context n}
    {A a a' : Term n} {B b b' : Term (n + 1)}
    (hb : Equality S (Γ.snoc A) b b' B)
    (hA : Equality S Γ A A (.univ 0)) (ha : Equality S Γ a a' A) :
    Equality S Γ (b.instantiate a) (b'.instantiate a') (B.instantiate a) := by
  have identity : TypedSubstitution Γ S Γ Term.var := by
    intro i C hi
    simpa only [Term.subst_var] using Equality.var hA.context hi
  have images : EqualSubstitution (Γ.snoc A) S Γ
      (Fin.cons a Term.var) (Fin.cons a' Term.var) :=
    EqualSubstitution.cons (TypedSubstitution.diagonal identity) (by simpa only [Term.subst_var] using ha)
  exact hb.substCongr hA.context _ _ images

end Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality
