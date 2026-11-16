module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeTyping.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

public section
namespace Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeTyping
open Silmaril.Logic.TypeTheory
open Silmaril.Logic.TypeTheory.LambdaPi
open Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality
open NativeConversion NativeTyping

private def sort (s : LFSort) : SortTag := if s.val = 0 then .type else .kind

private theorem term_sort {n : ℕ} (σ : Fin n → LambdaPi.Term) (s : LFSort) :
    term σ (.univ s.val) = LambdaPi.Term.univ (sort s) := by
  fin_cases s <;> rfl

private theorem term_weaken {n : ℕ} (σ : Fin n → LambdaPi.Term) (A : IntensionalMLTT.Term n) :
    term (lift σ) A.weaken = (term σ A).rename Nat.succ := by
  rw [IntensionalMLTT.Term.weaken, term_rename, term_nativeRename]
  rfl

theorem assignment_lift {n : ℕ} {Γ : IntensionalMLTT.Context n}
    {declared : String → LambdaPi.Term → Prop} {Δ : List LambdaPi.Term}
    {σ : Fin n → LambdaPi.Term} {A : IntensionalMLTT.Term n}
    (hσ : Assignment Γ declared Δ σ)
    (hA : Derives (Calculus.lfBetaEta declared) ∅ ⟨Δ, term σ A, LambdaPi.Term.univ .type⟩) :
    Assignment (Γ.snoc A) declared (term σ A :: Δ) (lift σ) := by
  intro i B hi
  cases hi with
  | here =>
    rw [term_weaken]
    exact Derives.var hA
  | there hi =>
    rw [term_weaken]
    exact Derives.weak (hσ hi) hA

/-- Every actual independent LF equality has both native beta-eta endpoint
typings under a genuinely typed interpretation of all source variables. -/
theorem endpoints {k n : ℕ} {S : IntensionalMLTT.Context k} {Γ : IntensionalMLTT.Context n}
    {t u A : IntensionalMLTT.Term n} (h : Equality S Γ t u A)
    {declared : String → LambdaPi.Term → Prop} {Δ : List LambdaPi.Term}
    (hΔ : ContextOK (Calculus.lfBetaEta declared) Δ) (σ : Fin n → LambdaPi.Term)
    (hσ : Assignment Γ declared Δ σ) :
    Derives (Calculus.lfBetaEta declared) ∅ ⟨Δ, term σ t, term σ A⟩ ∧
      Derives (Calculus.lfBetaEta declared) ∅ ⟨Δ, term σ u, term σ A⟩ := by
  induction h using Equality.rec (motive_1 := fun _ _ => True)
      (motive_2 := fun _ _ _ _ => True) generalizing Δ
  case nil => trivial
  case snoc => trivial
  case signature => trivial
  case snoc => intros; trivial
  case type => exact ⟨Derives.type.weaken_closed hΔ, Derives.type.weaken_closed hΔ⟩
  case var _ hi _ => exact ⟨hσ hi, hσ hi⟩
  case pi k n S s Γ A A' B B' hA hB ihA ihB =>
    show Derives (Calculus.lfBetaEta declared) ∅ ⟨Δ, term σ (.pi A B), term σ (.univ s.val)⟩ ∧
      Derives (Calculus.lfBetaEta declared) ∅ ⟨Δ, term σ (.pi A' B'), term σ (.univ s.val)⟩
    have domains := ihA hΔ σ hσ
    have hExt : Assignment (Γ.snoc A) declared (term σ A :: Δ) (lift σ) := assignment_lift hσ domains.1
    have bodies := ihB (.cons hΔ domains.1) (lift σ) hExt
    have leftBody : Derives (Calculus.lfBetaEta declared) ∅
        ⟨term σ A :: Δ, term (lift σ) B, LambdaPi.Term.univ (sort s)⟩ := by
      simpa only [term_sort] using bodies.1
    have rightBody : Derives (Calculus.lfBetaEta declared) ∅
        ⟨term σ A :: Δ, term (lift σ) B', LambdaPi.Term.univ (sort s)⟩ := by
      simpa only [term_sort] using bodies.2
    have context : ContextConversion (Calculus.lfBetaEta declared) (term σ A :: Δ) (term σ A' :: Δ) :=
      .cons (.refl hΔ) domains.1 domains.2 (equality_conversion hA σ declared)
    exact ⟨by simpa only [term, term_sort] using Derives.pi domains.1 leftBody,
      by simpa only [term, term_sort] using Derives.pi domains.2 (rightBody.changeContext context)⟩
  case lam k n S s Γ A B b b' hA hB hb ihA ihB ihb =>
    show Derives (Calculus.lfBetaEta declared) ∅ ⟨Δ, term σ (.lam A b), term σ (.pi A B)⟩ ∧
      Derives (Calculus.lfBetaEta declared) ∅ ⟨Δ, term σ (.lam A b'), term σ (.pi A B)⟩
    have domain := (ihA hΔ σ hσ).1
    have hExt : Assignment (Γ.snoc A) declared (term σ A :: Δ) (lift σ) := assignment_lift hσ domain
    have formedBody : Derives (Calculus.lfBetaEta declared) ∅
        ⟨term σ A :: Δ, term (lift σ) B, LambdaPi.Term.univ (sort s)⟩ := by
      simpa only [term_sort] using (ihB (.cons hΔ domain) _ hExt).1
    have bodies := ihb (.cons hΔ domain) _ hExt
    exact ⟨Derives.lam bodies.1 (Derives.pi domain formedBody),
      Derives.lam bodies.2 (Derives.pi domain formedBody)⟩
  case app k n S s Γ A f f' a a' B hA hB hf ha ihA ihB ihf iha =>
    show Derives (Calculus.lfBetaEta declared) ∅ ⟨Δ, term σ (.app f a), term σ (B.instantiate a)⟩ ∧
      Derives (Calculus.lfBetaEta declared) ∅ ⟨Δ, term σ (.app f' a'), term σ (B.instantiate a)⟩
    have domain := (ihA hΔ σ hσ).1
    have hExt : Assignment (Γ.snoc A) declared (term σ A :: Δ) (lift σ) := assignment_lift hσ domain
    have formedBody : Derives (Calculus.lfBetaEta declared) ∅
        ⟨term σ A :: Δ, term (lift σ) B, LambdaPi.Term.univ (sort s)⟩ := by
      simpa only [term_sort] using (ihB (.cons hΔ domain) _ hExt).1
    have functions := ihf hΔ σ hσ
    have arguments := iha hΔ σ hσ
    have originalResult : Derives (Calculus.lfBetaEta declared) ∅
        ⟨Δ, term σ (B.instantiate a), LambdaPi.Term.univ (sort s)⟩ := by
      have result : Derives (Calculus.lfBetaEta declared) ∅
          ⟨Δ, (term (lift σ) B).substOne (term σ a), LambdaPi.Term.univ (sort s)⟩ :=
        formedBody.substOne arguments.1
      simpa only [term_instantiate] using result
    have carriers := equality_conversion (hB.instantiateAll hA ha) σ declared
    exact ⟨by simpa only [term, term_instantiate] using Derives.app functions.1 arguments.1,
      Derives.conv (by simpa only [term, term_instantiate] using Derives.app functions.2 arguments.2)
        carriers.symm originalResult⟩
  case beta k n S s Γ A a B b hA hB hb ha ihA ihB ihb iha =>
    show Derives (Calculus.lfBetaEta declared) ∅ ⟨Δ, term σ (.app (.lam A b) a), term σ (B.instantiate a)⟩ ∧
      Derives (Calculus.lfBetaEta declared) ∅ ⟨Δ, term σ (b.instantiate a), term σ (B.instantiate a)⟩
    have domain := (ihA hΔ σ hσ).1
    have hExt : Assignment (Γ.snoc A) declared (term σ A :: Δ) (lift σ) := assignment_lift hσ domain
    have formedBody : Derives (Calculus.lfBetaEta declared) ∅
        ⟨term σ A :: Δ, term (lift σ) B, LambdaPi.Term.univ (sort s)⟩ := by
      simpa only [term_sort] using (ihB (.cons hΔ domain) _ hExt).1
    have body := (ihb (.cons hΔ domain) _ hExt).1
    have argument := (iha hΔ σ hσ).1
    exact ⟨by simpa only [term, term_instantiate] using
        Derives.app (Derives.lam body (Derives.pi domain formedBody)) argument,
      by simpa only [term_instantiate] using body.substOne argument⟩
  case eta k n S s Γ A f B hA hB hf ihA ihB ihf =>
    have function := (ihf hΔ σ hσ).1
    have hzero : lift σ 0 = (.var 0 : LambdaPi.Term) := rfl
    exact ⟨by simpa only [term, term_weaken, hzero] using function.etaExpansion, function⟩
  case conv k n S s Γ t u A B ht hAB iht ihAB =>
    have terms := iht hΔ σ hσ
    have formed : Derives (Calculus.lfBetaEta declared) ∅
        ⟨Δ, term σ B, LambdaPi.Term.univ (sort s)⟩ := by
      simpa only [term_sort] using (ihAB hΔ σ hσ).2
    exact ⟨.conv terms.1 (equality_conversion hAB σ declared) formed,
      .conv terms.2 (equality_conversion hAB σ declared) formed⟩
  case symm _ ih => exact (ih hΔ σ hσ).symm
  case trans _ _ ih ik => exact ⟨(ih hΔ σ hσ).1, (ik hΔ σ hσ).2⟩

end Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeTyping
