module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawHeadSeparation.Defs
public import Silmaril.Logic.TypeTheory.IntensionalMLTT.LinearJ.Thms
public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Regularity

public section

namespace Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawHeadSeparation

open Silmaril.Logic.TypeTheory.IntensionalMLTT

theorem parallel_head {n : ℕ} {t u : Term n} {k : RigidHead}
    (h : LinearJ.Parallel t u) (ht : Term.rigidHead t = some k) : Term.rigidHead u = some k := by
  cases h <;> cases ht <;> rfl

theorem reduces_head {n : ℕ} {t u : Term n} {k : RigidHead}
    (h : LinearJ.Reduces t u) (ht : Term.rigidHead t = some k) : Term.rigidHead u = some k := by
  induction h with
  | refl => exact ht
  | tail h hstep ih => exact parallel_head hstep ih

theorem convertible_head_eq {n : ℕ} {t u : Term n} {k l : RigidHead}
    (h : Convertible t u) (ht : Term.rigidHead t = some k) (hu : Term.rigidHead u = some l) : k = l := by
  obtain ⟨v, htv, huv⟩ := LinearJ.convertible_iff_join.mp (LinearJ.ofConvertible h)
  have hk : Term.rigidHead v = some k := reduces_head htv ht
  have hl : Term.rigidHead v = some l := reduces_head huv hu
  exact Option.some.inj (hk.symm.trans hl)

theorem not_convertible_of_head_ne {n : ℕ} {t u : Term n} {k l : RigidHead}
    (ht : Term.rigidHead t = some k) (hu : Term.rigidHead u = some l) (hkl : k ≠ l) : ¬ Convertible t u :=
  fun h => hkl (convertible_head_eq h ht hu)

theorem convertible_univ_iff {n i j : ℕ} :
    Convertible (.univ i : Term n) (.univ j) ↔ i = j := by
  constructor
  · intro h
    exact RigidHead.univ.inj (convertible_head_eq h rfl rfl)
  · intro h
    cases h
    exact ⟨.refl _⟩

theorem universe_generation {n : ℕ} {Γ : Context n} {t A : Term n} (h : Derivation Γ t A) :
    ∀ i, t = .univ i → ∃ j, i < j ∧ Convertible A (.univ j) := by
  induction h using Derivation.rec (motive_1 := fun _ _ => True) with
  | nil => trivial
  | snoc _ _ _ _ => trivial
  | @univ n Γ hΓ i ihΓ =>
    intro k heq
    cases heq
    exact ⟨i + 1, Nat.lt_succ_self i, ⟨.refl _⟩⟩
  | @conv n i Γ t A B ht hB hAB iht ihB =>
    intro k heq
    obtain ⟨j, hkj, ⟨hAj⟩⟩ := iht k heq
    exact ⟨j, hkj, ⟨.trans (.symm hAB) hAj⟩⟩
  | @cumulative n i j Γ A hA hij ihA =>
    intro k heq
    obtain ⟨l, hkl, hil⟩ := ihA k heq
    have hil' : i = l := convertible_univ_iff.mp hil
    exact ⟨j, (hkl.trans_le (hil' ▸ hij)), ⟨.refl _⟩⟩
  | nat _ _ => intro k heq; cases heq
  | empty _ _ => intro k heq; cases heq
  | unit _ _ => intro k heq; cases heq
  | var _ _ _ => intro k heq; cases heq
  | pi _ _ _ _ => intro k heq; cases heq
  | sigma _ _ _ _ => intro k heq; cases heq
  | lam _ _ _ _ _ _ => intro k heq; cases heq
  | app _ _ _ _ => intro k heq; cases heq
  | pair _ _ _ _ _ _ _ _ => intro k heq; cases heq
  | fst _ _ => intro k heq; cases heq
  | snd _ _ => intro k heq; cases heq
  | zero _ _ => intro k heq; cases heq
  | succ _ _ => intro k heq; cases heq
  | natrec _ _ _ _ _ _ _ _ => intro k heq; cases heq
  | star _ _ => intro k heq; cases heq
  | absurd _ _ _ _ => intro k heq; cases heq
  | id _ _ _ _ _ _ => intro k heq; cases heq
  | refl _ _ _ _ => intro k heq; cases heq
  | j _ _ _ _ _ _ _ _ _ _ _ _ => intro k heq; cases heq

theorem typing_univ_iff {n i j : ℕ} {Γ : Context n} :
    Typing Γ (.univ i) (.univ j) ↔ WellFormed Γ ∧ i < j := by
  constructor
  · rintro ⟨h⟩
    obtain ⟨k, hik, hjk⟩ := universe_generation h i rfl
    have heq : j = k := convertible_univ_iff.mp hjk
    exact ⟨⟨h.context⟩, heq ▸ hik⟩
  · rintro ⟨⟨hΓ⟩, hij⟩
    exact ⟨.cumulative (.univ hΓ i) hij⟩


theorem not_convertible_univ_pi {n i : ℕ} (A : Term n) (B : Term (n + 1)) :
    ¬ Convertible (.univ i) (.pi A B) := not_convertible_of_head_ne rfl rfl (by intro h; cases h)

theorem not_convertible_univ_sigma {n i : ℕ} (A : Term n) (B : Term (n + 1)) :
    ¬ Convertible (.univ i) (.sigma A B) := not_convertible_of_head_ne rfl rfl (by intro h; cases h)

theorem not_convertible_univ_id {n i : ℕ} (A a b : Term n) :
    ¬ Convertible (.univ i) (.id A a b) := not_convertible_of_head_ne rfl rfl (by intro h; cases h)

theorem not_convertible_pi_sigma {n : ℕ} (A A' : Term n) (B B' : Term (n + 1)) :
    ¬ Convertible (.pi A B) (.sigma A' B') := not_convertible_of_head_ne rfl rfl (by intro h; cases h)

theorem not_convertible_nat_empty {n : ℕ} :
    ¬ Convertible (.nat : Term n) .empty := not_convertible_of_head_ne rfl rfl (by intro h; cases h)

theorem not_convertible_nat_unit {n : ℕ} :
    ¬ Convertible (.nat : Term n) .unit := not_convertible_of_head_ne rfl rfl (by intro h; cases h)

theorem not_convertible_empty_unit {n : ℕ} :
    ¬ Convertible (.empty : Term n) .unit := not_convertible_of_head_ne rfl rfl (by intro h; cases h)

theorem not_typing_univ_self {n i : ℕ} (Γ : Context n) : ¬ Typing Γ (.univ i) (.univ i) :=
  fun h => Nat.lt_irrefl i (typing_univ_iff.mp h).2


end Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawHeadSeparation
