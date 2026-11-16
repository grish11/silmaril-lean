module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.Substitution.Defs
public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Substitution.Thms

public section

namespace Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualitySubstitution

open Silmaril.Logic.TypeTheory.IntensionalMLTT
open Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality

theorem cons {n l m : ℕ} {Γ : Context n} {T : Context l} {Δ : Context m}
    {σ : Fin n → Term m} {A : Term n} {a : Term m}
    (hσ : TypedSubstitution Γ T Δ σ) (ha : Equality T Δ a a (A.subst σ)) :
    TypedSubstitution (Γ.snoc A) T Δ (Fin.cons a σ) := by
  intro i B hi
  cases hi with
  | here =>
    change Equality T Δ a a ((A.rename Fin.succ).subst (Fin.cons a σ))
    rw [Term.subst_rename]
    exact ha
  | there hi =>
    simpa only [Term.weaken, Term.subst_rename, Function.comp_def, Fin.cons_succ] using hσ hi

theorem lift {n l m : ℕ} {Γ : Context n} {T : Context l} {Δ : Context m}
    {σ : Fin n → Term m} {A : Term n} (hσ : TypedSubstitution Γ T Δ σ)
    (hA : Equality T Δ (A.subst σ) (A.subst σ) (.univ 0)) :
    TypedSubstitution (Γ.snoc A) T (Δ.snoc (A.subst σ)) (Term.upSub σ) := by
  intro j B hj
  cases hj with
  | here =>
    rw [Term.subst_weaken]
    exact .var (.snoc hA.context hA) .here
  | there hj =>
    rw [Term.subst_weaken]
    exact (hσ hj).weaken hA

theorem subst {k n : ℕ} {S : Context k} {Γ : Context n} {t u A : Term n}
    (h : Equality S Γ t u A) :
    ∀ {l m : ℕ} {T : Context l} {Δ : Context m}, ContextFormed T Δ →
      ∀ (σ : Fin n → Term m), TypedSubstitution Γ T Δ σ →
        Equality T Δ (t.subst σ) (u.subst σ) (A.subst σ) := by
  induction h using Equality.rec (motive_1 := fun _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
  case nil => trivial
  case snoc => trivial
  case signature => trivial
  case snoc => intros; trivial
  all_goals intro l m T Δ hΔ σ hσ
  case type => exact .type hΔ
  case var k n S Γ i A hΓ hi ihΓ => exact hσ hi
  case pi k n S s Γ A A' B B' hA hB ihA ihB =>
    have hAσ : Equality T Δ (A.subst σ) (A'.subst σ) (.univ 0) := ihA hΔ σ hσ
    have hAf : Equality T Δ (A.subst σ) (A.subst σ) (.univ 0) := .trans hAσ (.symm hAσ)
    have hΔA : ContextFormed T (Δ.snoc (A.subst σ)) := .snoc hΔ hAf
    exact .pi hAσ (ihB hΔA (Term.upSub σ) (lift hσ hAf))
  case lam k n S s Γ A B b b' hA hB hb ihA ihB ihb =>
    have hAσ : Equality T Δ (A.subst σ) (A.subst σ) (.univ 0) := ihA hΔ σ hσ
    have hΔA : ContextFormed T (Δ.snoc (A.subst σ)) := .snoc hΔ hAσ
    exact .lam hAσ (ihB hΔA (Term.upSub σ) (lift hσ hAσ))
      (ihb hΔA (Term.upSub σ) (lift hσ hAσ))
  case app k n S s Γ A f f' a a' B hA hB hf ha ihA ihB ihf iha =>
    have hAσ : Equality T Δ (A.subst σ) (A.subst σ) (.univ 0) := ihA hΔ σ hσ
    have hΔA : ContextFormed T (Δ.snoc (A.subst σ)) := .snoc hΔ hAσ
    simpa only [Term.subst, Term.subst_instantiate] using
      Equality.app hAσ (ihB hΔA (Term.upSub σ) (lift hσ hAσ)) (ihf hΔ σ hσ) (iha hΔ σ hσ)
  case beta k n S s Γ A a B b hA hB hb ha ihA ihB ihb iha =>
    have hAσ : Equality T Δ (A.subst σ) (A.subst σ) (.univ 0) := ihA hΔ σ hσ
    have hΔA : ContextFormed T (Δ.snoc (A.subst σ)) := .snoc hΔ hAσ
    simpa only [Term.subst, Term.subst_instantiate] using
      Equality.beta hAσ (ihB hΔA (Term.upSub σ) (lift hσ hAσ))
        (ihb hΔA (Term.upSub σ) (lift hσ hAσ)) (iha hΔ σ hσ)
  case eta k n S s Γ A f B hA hB hf ihA ihB ihf =>
    have hAσ : Equality T Δ (A.subst σ) (A.subst σ) (.univ 0) := ihA hΔ σ hσ
    have hΔA : ContextFormed T (Δ.snoc (A.subst σ)) := .snoc hΔ hAσ
    have hzero : Term.upSub σ 0 = .var 0 := by simp [Term.upSub]
    simpa only [Term.subst, Term.subst_weaken, hzero] using
      Equality.eta hAσ (ihB hΔA (Term.upSub σ) (lift hσ hAσ)) (ihf hΔ σ hσ)
  case conv k n S s Γ t u A B ht hAB iht ihAB =>
    exact .conv (iht hΔ σ hσ) (ihAB hΔ σ hσ)
  case symm k n S Γ t u A h ih => exact .symm (ih hΔ σ hσ)
  case trans k n S Γ t u v A h h' ih ih' => exact .trans (ih hΔ σ hσ) (ih' hΔ σ hσ)

end Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualitySubstitution
