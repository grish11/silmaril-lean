module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.Substitution.Thms

public section
namespace Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityRegularity
open Silmaril.Logic.TypeTheory.IntensionalMLTT
open Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality

theorem signature_lookup {n : ℕ} {S : Context n} (hS : SignatureFormed S)
    {i : Fin n} {A : Term n} (hi : Lookup S i A) :
    ∃ s : LFSort, Equality S S A A (.univ s.val) := by
  cases hS with
  | nil => cases hi
  | @snoc n S B s hS hB =>
    have hΓ : ContextFormed (S.snoc B) (S.snoc B) := .signature (.snoc hS hB)
    cases hi with
    | here =>
      exact ⟨s, hB.rename hΓ Fin.succ (Renaming.weaken S B)⟩
    | there hi =>
      obtain ⟨r, hA⟩ := signature_lookup hS hi
      exact ⟨r, hA.rename hΓ Fin.succ (Renaming.weaken S B)⟩

theorem context_lookup {k n : ℕ} {S : Context k} {Γ : Context n}
    (hΓ : ContextFormed S Γ) : ∀ {i : Fin n} {A : Term n}, Lookup Γ i A →
      ∃ s : LFSort, Equality S Γ A A (.univ s.val) := by
  induction hΓ using ContextFormed.rec (motive_1 := fun _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
  case nil => trivial
  case snoc => trivial
  case signature k S hS _ => exact fun hi => signature_lookup hS hi
  case snoc k n S Γ B hΓ hB ihΓ =>
    intro _ i A hi
    cases hi with
    | here => exact ⟨0, hB.weaken hB⟩
    | there hi =>
      obtain ⟨s, hA⟩ := ihΓ hi
      exact ⟨s, hA.weaken hB⟩
  all_goals trivial

theorem instantiate {k n : ℕ} {S : Context k} {Γ : Context n}
    {A a : Term n} {B : Term (n + 1)} {s : LFSort}
    (hB : Equality S (Γ.snoc A) B B (.univ s.val))
    (ha : Equality S Γ a a A) :
    Equality S Γ (B.instantiate a) (B.instantiate a) (.univ s.val) := by
  have hid : TypedSubstitution Γ S Γ Term.var := fun hi => by
    simpa only [Term.subst_var] using Equality.var ha.context hi
  have hs : TypedSubstitution (Γ.snoc A) S Γ (Fin.cons a Term.var) :=
    hid.cons (by simpa only [Term.subst_var] using ha)
  exact hB.subst ha.context (Fin.cons a Term.var) hs

/-- Every independently checked equality has a formed carrier or the unsorted top sort. -/
theorem regularity {k n : ℕ} {S : Context k} {Γ : Context n} {t u A : Term n}
    (h : Equality S Γ t u A) :
    A = .univ 1 ∨ ∃ s : LFSort, Equality S Γ A A (.univ s.val) := by
  induction h using Equality.rec (motive_1 := fun _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
  case nil => trivial
  case snoc => trivial
  case signature => trivial
  case snoc => intros; trivial
  case type => exact Or.inl rfl
  case var k n S Γ i A hΓ hi _ => exact Or.inr (context_lookup hΓ hi)
  case pi k n S s Γ A A' B B' hA hB _ _ =>
    rcases s with ⟨s, hs⟩
    have hcases : s = 0 ∨ s = 1 := by omega
    rcases hcases with hzero | hone
    · exact Or.inr ⟨⟨1, by decide⟩, by simpa only [hzero] using Equality.type hA.context⟩
    · exact Or.inl (by simp only [hone])
  case lam k n S s Γ A B b b' hA hB hb _ _ _ =>
    exact Or.inr ⟨s, .pi hA hB⟩
  case app k n S s Γ A f f' a a' B hA hB hf ha _ _ _ _ =>
    have haa : Equality S Γ a a A := .trans ha (.symm ha)
    exact Or.inr ⟨s, instantiate hB haa⟩
  case beta k n S s Γ A a B b hA hB hb ha _ _ _ _ =>
    exact Or.inr ⟨s, instantiate hB ha⟩
  case eta k n S s Γ A f B hA hB hf _ _ _ => exact Or.inr ⟨s, .pi hA hB⟩
  case conv k n S s Γ t u A B ht hAB _ _ =>
    exact Or.inr ⟨s, .trans (.symm hAB) hAB⟩
  case symm k n S Γ t u A ht ih => exact ih
  case trans k n S Γ t u v A ht hu ih _ => exact ih

end Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityRegularity
