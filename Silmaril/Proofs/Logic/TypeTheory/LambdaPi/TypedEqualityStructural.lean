module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.Thms
public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Substitution.Thms

public section

namespace Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityStructural

open Silmaril.Logic.TypeTheory.IntensionalMLTT
open Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality

theorem rename {k n : ℕ} {S : Context k} {Γ : Context n} {t u A : Term n}
    (h : Equality S Γ t u A) :
    ∀ {l m : ℕ} {T : Context l} {Δ : Context m}, ContextFormed T Δ →
      ∀ (ρ : Fin n → Fin m), Renaming Γ Δ ρ →
        Equality T Δ (t.rename ρ) (u.rename ρ) (A.rename ρ) := by
  induction h using Equality.rec (motive_1 := fun _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
  case nil => trivial
  case snoc => trivial
  case signature => trivial
  case snoc => intros; trivial
  all_goals intro l m T Δ hΔ ρ hρ
  case type => exact .type hΔ
  case var k n S Γ i A hΓ hi ihΓ => exact .var hΔ (hρ hi)
  case pi k n S s Γ A A' B B' hA hB ihA ihB =>
    have hAρ : Equality T Δ (A.rename ρ) (A'.rename ρ) (.univ 0) := ihA hΔ ρ hρ
    have hΔA : ContextFormed T (Δ.snoc (A.rename ρ)) := .snoc hΔ (.trans hAρ (.symm hAρ))
    exact .pi hAρ (ihB hΔA (Term.upRen ρ) (hρ.lift A))
  case lam k n S s Γ A B b b' hA hB hb ihA ihB ihb =>
    have hAρ : Equality T Δ (A.rename ρ) (A.rename ρ) (.univ 0) := ihA hΔ ρ hρ
    have hΔA : ContextFormed T (Δ.snoc (A.rename ρ)) := .snoc hΔ hAρ
    exact .lam hAρ (ihB hΔA (Term.upRen ρ) (hρ.lift A))
      (ihb hΔA (Term.upRen ρ) (hρ.lift A))
  case app k n S s Γ A f f' a a' B hA hB hf ha ihA ihB ihf iha =>
    have hAρ : Equality T Δ (A.rename ρ) (A.rename ρ) (.univ 0) := ihA hΔ ρ hρ
    have hΔA : ContextFormed T (Δ.snoc (A.rename ρ)) := .snoc hΔ hAρ
    simpa only [Term.rename, Term.rename_instantiate] using
      Equality.app hAρ (ihB hΔA (Term.upRen ρ) (hρ.lift A)) (ihf hΔ ρ hρ) (iha hΔ ρ hρ)
  case beta k n S s Γ A a B b hA hB hb ha ihA ihB ihb iha =>
    have hAρ : Equality T Δ (A.rename ρ) (A.rename ρ) (.univ 0) := ihA hΔ ρ hρ
    have hΔA : ContextFormed T (Δ.snoc (A.rename ρ)) := .snoc hΔ hAρ
    simpa only [Term.rename, Term.rename_instantiate] using
      Equality.beta hAρ (ihB hΔA (Term.upRen ρ) (hρ.lift A))
        (ihb hΔA (Term.upRen ρ) (hρ.lift A)) (iha hΔ ρ hρ)
  case eta k n S s Γ A f B hA hB hf ihA ihB ihf =>
    have hAρ : Equality T Δ (A.rename ρ) (A.rename ρ) (.univ 0) := ihA hΔ ρ hρ
    have hΔA : ContextFormed T (Δ.snoc (A.rename ρ)) := .snoc hΔ hAρ
    have hzero : Term.upRen ρ 0 = 0 := by simp [Term.upRen]
    simpa only [Term.rename, Term.rename_weaken, hzero] using
      Equality.eta hAρ (ihB hΔA (Term.upRen ρ) (hρ.lift A)) (ihf hΔ ρ hρ)
  case conv k n S s Γ t u A B ht hAB iht ihAB =>
    exact .conv (iht hΔ ρ hρ) (ihAB hΔ ρ hρ)
  case symm k n S Γ t u A h ih => exact .symm (ih hΔ ρ hρ)
  case trans k n S Γ t u v A h h' ih ih' => exact .trans (ih hΔ ρ hρ) (ih' hΔ ρ hρ)

end Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityStructural
