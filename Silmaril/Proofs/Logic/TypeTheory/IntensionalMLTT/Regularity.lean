module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Substitution

public section

namespace Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Regularity

open Silmaril.Logic.TypeTheory.IntensionalMLTT

noncomputable def derivation_context {n : ℕ} {Γ : Context n} {t A : Term n}
    (h : Derivation Γ t A) : ContextDerivation Γ := by
  induction h using Derivation.rec (motive_1 := fun Γ _ => ContextDerivation Γ) with
  | nil => exact .nil
  | snoc hΓ hA ihΓ _ => exact .snoc ihΓ hA
  | univ _ _ ihΓ => exact ihΓ
  | nat _ ihΓ => exact ihΓ
  | empty _ ihΓ => exact ihΓ
  | unit _ ihΓ => exact ihΓ
  | var _ _ ihΓ => exact ihΓ
  | pi _ _ ihA _ => exact ihA
  | sigma _ _ ihA _ => exact ihA
  | lam _ _ _ ihA _ _ => exact ihA
  | app _ _ ihf _ => exact ihf
  | pair _ _ _ _ ihA _ _ _ => exact ihA
  | fst _ ihp => exact ihp
  | snd _ ihp => exact ihp
  | zero _ ihΓ => exact ihΓ
  | succ _ iht => exact iht
  | natrec _ _ _ _ ihC _ _ _ => cases ihC with | snoc hΓ _ => exact hΓ
  | star _ ihΓ => exact ihΓ
  | absurd _ _ ihA _ => exact ihA
  | id _ _ _ ihA _ _ => exact ihA
  | refl _ _ ihA _ => exact ihA
  | j _ _ _ _ _ _ ihA _ _ _ _ _ => exact ihA
  | conv _ _ _ iht _ => exact iht
  | cumulative _ _ ihA => exact ihA

theorem lookup_formation {n : ℕ} {Γ : Context n} {i : Fin n} {A : Term n}
    (hi : Lookup Γ i A) (hΓ : ContextDerivation Γ) :
    ∃ level, Typing Γ A (.univ level) := by
  induction hi with
  | here =>
    cases hΓ with
    | snoc hΓ hA => exact ⟨_, ⟨hA.weaken hΓ hA⟩⟩
  | there hi ih =>
    cases hΓ with
    | snoc hΓ hB =>
      obtain ⟨level, ⟨hA⟩⟩ := ih hΓ
      exact ⟨level, ⟨hA.weaken hΓ hB⟩⟩

theorem pi_formation {n : ℕ} {Γ : Context n} {t T : Term n} (h : Derivation Γ t T) :
    ∀ {A : Term n} {B : Term (n + 1)}, t = .pi A B →
      ∃ i j, Typing Γ A (.univ i) ∧ Typing (Γ.snoc A) B (.univ j) := by
  induction h using Derivation.rec (motive_1 := fun _ _ => True) with
  | nil => trivial
  | snoc _ _ _ _ => trivial
  | pi hA hB _ _ => intro A B he; cases he; exact ⟨_, _, ⟨hA⟩, ⟨hB⟩⟩
  | conv _ _ _ iht _ => intro A B he; exact iht he
  | cumulative _ _ ihA => intro A B he; exact ihA he
  | univ _ _ _ => intro A B he; cases he
  | nat _ _ => intro A B he; cases he
  | empty _ _ => intro A B he; cases he
  | unit _ _ => intro A B he; cases he
  | var _ _ _ => intro A B he; cases he
  | sigma _ _ _ _ => intro A B he; cases he
  | lam _ _ _ _ _ _ => intro A B he; cases he
  | app _ _ _ _ => intro A B he; cases he
  | pair _ _ _ _ _ _ _ _ => intro A B he; cases he
  | fst _ _ => intro A B he; cases he
  | snd _ _ => intro A B he; cases he
  | zero _ _ => intro A B he; cases he
  | succ _ _ => intro A B he; cases he
  | natrec _ _ _ _ _ _ _ _ => intro A B he; cases he
  | star _ _ => intro A B he; cases he
  | absurd _ _ _ _ => intro A B he; cases he
  | id _ _ _ _ _ _ => intro A B he; cases he
  | refl _ _ _ _ => intro A B he; cases he
  | j _ _ _ _ _ _ _ _ _ _ _ _ => intro A B he; cases he

theorem sigma_formation {n : ℕ} {Γ : Context n} {t T : Term n} (h : Derivation Γ t T) :
    ∀ {A : Term n} {B : Term (n + 1)}, t = .sigma A B →
      ∃ i j, Typing Γ A (.univ i) ∧ Typing (Γ.snoc A) B (.univ j) := by
  induction h using Derivation.rec (motive_1 := fun _ _ => True) with
  | nil => trivial
  | snoc _ _ _ _ => trivial
  | sigma hA hB _ _ => intro A B he; cases he; exact ⟨_, _, ⟨hA⟩, ⟨hB⟩⟩
  | conv _ _ _ iht _ => intro A B he; exact iht he
  | cumulative _ _ ihA => intro A B he; exact ihA he
  | univ _ _ _ => intro A B he; cases he
  | nat _ _ => intro A B he; cases he
  | empty _ _ => intro A B he; cases he
  | unit _ _ => intro A B he; cases he
  | var _ _ _ => intro A B he; cases he
  | pi _ _ _ _ => intro A B he; cases he
  | lam _ _ _ _ _ _ => intro A B he; cases he
  | app _ _ _ _ => intro A B he; cases he
  | pair _ _ _ _ _ _ _ _ => intro A B he; cases he
  | fst _ _ => intro A B he; cases he
  | snd _ _ => intro A B he; cases he
  | zero _ _ => intro A B he; cases he
  | succ _ _ => intro A B he; cases he
  | natrec _ _ _ _ _ _ _ _ => intro A B he; cases he
  | star _ _ => intro A B he; cases he
  | absurd _ _ _ _ => intro A B he; cases he
  | id _ _ _ _ _ _ => intro A B he; cases he
  | refl _ _ _ _ => intro A B he; cases he
  | j _ _ _ _ _ _ _ _ _ _ _ _ => intro A B he; cases he

noncomputable def motive_substitution {n : ℕ} {Γ : Context n} {A a b p : Term n}
    (hΓ : ContextDerivation Γ) (hb : Derivation Γ b A) (hp : Derivation Γ p (.id A a b)) :
    Substitution (motiveContext Γ A a) Γ (Fin.cons p (Fin.cons b Term.var)) := by
  have hb' : Derivation Γ b (A.subst Term.var) := by simpa only [Term.subst_var] using hb
  have hσ : Substitution (Γ.snoc A) Γ (Fin.cons b Term.var) :=
    Substitution.cons (Substitution.identity hΓ) hb'
  have hp' : Derivation Γ p ((Term.id A.weaken a.weaken (.var 0)).subst (Fin.cons b Term.var)) := by
    change Derivation Γ p (.id (A.weaken.instantiate b) (a.weaken.instantiate b) b)
    simpa only [Term.instantiate_weaken] using hp
  intro i T hi
  exact Substitution.cons hσ hp' hi

theorem id_formation {n : ℕ} {Γ : Context n} {t T : Term n} (h : Derivation Γ t T) :
    ∀ {A a b : Term n}, t = .id A a b →
      ∃ i, Typing Γ A (.univ i) ∧ Typing Γ a A ∧ Typing Γ b A := by
  induction h using Derivation.rec (motive_1 := fun _ _ => True) with
  | nil => trivial
  | snoc _ _ _ _ => trivial
  | id hA ha hb _ _ _ =>
    intro A a b he
    cases he
    exact ⟨_, ⟨hA⟩, ⟨ha⟩, ⟨hb⟩⟩
  | conv _ _ _ iht _ => intro A a b he; exact iht he
  | cumulative _ _ iht => intro A a b he; exact iht he
  | _ => intro A a b he; cases he

theorem type_formation {n : ℕ} {Γ : Context n} {t A : Term n} (h : Derivation Γ t A) :
    ∃ level, Typing Γ A (.univ level) := by
  induction h using Derivation.rec (motive_1 := fun _ _ => True) with
  | nil => trivial
  | snoc _ _ _ _ => trivial
  | univ hΓ i _ => exact ⟨i + 2, ⟨.univ hΓ (i + 1)⟩⟩
  | nat hΓ _ => exact ⟨1, ⟨.univ hΓ 0⟩⟩
  | empty hΓ _ => exact ⟨1, ⟨.univ hΓ 0⟩⟩
  | unit hΓ _ => exact ⟨1, ⟨.univ hΓ 0⟩⟩
  | var hΓ hi _ => exact lookup_formation hi hΓ
  | pi hA _ _ _ => exact ⟨_, ⟨.univ (derivation_context hA) _⟩⟩
  | sigma hA _ _ _ => exact ⟨_, ⟨.univ (derivation_context hA) _⟩⟩
  | lam hA hB _ _ _ _ => exact ⟨_, ⟨.pi hA hB⟩⟩
  | app hf ha ihf _ =>
    obtain ⟨_, ⟨hPi⟩⟩ := ihf
    obtain ⟨_, _, _, ⟨hB⟩⟩ := pi_formation hPi rfl
    exact ⟨_, ⟨hB.instantiate (derivation_context hf) ha⟩⟩
  | pair hA hB _ _ _ _ _ _ => exact ⟨_, ⟨.sigma hA hB⟩⟩
  | fst _ ihp =>
    obtain ⟨_, ⟨hSigma⟩⟩ := ihp
    obtain ⟨i, _, hA, _⟩ := sigma_formation hSigma rfl
    exact ⟨i, hA⟩
  | snd hp ihp =>
    obtain ⟨_, ⟨hSigma⟩⟩ := ihp
    obtain ⟨_, _, _, ⟨hB⟩⟩ := sigma_formation hSigma rfl
    exact ⟨_, ⟨hB.instantiate (derivation_context hp) (.fst hp)⟩⟩
  | zero hΓ _ => exact ⟨0, ⟨.nat hΓ⟩⟩
  | succ ht _ => exact ⟨0, ⟨.nat (derivation_context ht)⟩⟩
  | natrec hC _ _ ht _ _ _ _ =>
    exact ⟨_, ⟨hC.instantiate (derivation_context ht) ht⟩⟩
  | star hΓ _ => exact ⟨0, ⟨.unit hΓ⟩⟩
  | absurd hA _ _ _ => exact ⟨_, ⟨hA⟩⟩
  | id hA _ _ _ _ _ => exact ⟨_, ⟨.univ (derivation_context hA) _⟩⟩
  | refl hA ha _ _ => exact ⟨_, ⟨.id hA ha ha⟩⟩
  | j hA _ hC _ hb hp _ _ _ _ _ _ =>
    exact ⟨_, ⟨hC.subst (derivation_context hA) _
      (motive_substitution (derivation_context hA) hb hp)⟩⟩
  | conv _ hB _ _ _ => exact ⟨_, ⟨hB⟩⟩
  | cumulative hA _ _ => exact ⟨_, ⟨.univ (derivation_context hA) _⟩⟩

end Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Regularity
