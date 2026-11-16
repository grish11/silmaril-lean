module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawHeadSeparation.Thms

public section

namespace Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawValueGeneration

open Silmaril.Logic.TypeTheory.IntensionalMLTT

private def Premises {n : ℕ} (Γ : Context n) (t T : Term n) : Prop :=
  match t with
  | .lam A body => ∃ i j B, Typing Γ A (.univ i) ∧ Typing (Γ.snoc A) B (.univ j) ∧
      Typing (Γ.snoc A) body B ∧ Convertible T (.pi A B)
  | .pair a b => ∃ i j A B, Typing Γ A (.univ i) ∧ Typing (Γ.snoc A) B (.univ j) ∧
      Typing Γ a A ∧ Typing Γ b (B.instantiate a) ∧ Convertible T (.sigma A B)
  | .zero => Convertible T .nat
  | .succ a => Typing Γ a .nat ∧ Convertible T .nat
  | .star => Convertible T .unit
  | .refl a => ∃ i A, Typing Γ A (.univ i) ∧ Typing Γ a A ∧ Convertible T (.id A a a)
  | _ => True

private theorem convert_left {n : ℕ} {A B T : Term n} (h : Convertible A T)
    (k : Conversion A B) : Convertible B T := by
  obtain ⟨h⟩ := h
  exact ⟨.trans (.symm k) h⟩

private theorem transport {n : ℕ} {Γ : Context n} {t A B : Term n}
    (h : Premises Γ t A) (hAB : Conversion A B) : Premises Γ t B := by
  cases t with
  | lam D body =>
    obtain ⟨i, j, C, hD, hC, ht, hT⟩ := h
    exact ⟨i, j, C, hD, hC, ht, convert_left hT hAB⟩
  | pair a b =>
    obtain ⟨i, j, D, C, hD, hC, ha, hb, hT⟩ := h
    exact ⟨i, j, D, C, hD, hC, ha, hb, convert_left hT hAB⟩
  | zero => exact convert_left h hAB
  | succ a => exact ⟨h.1, convert_left h.2 hAB⟩
  | star => exact convert_left h hAB
  | refl a =>
    obtain ⟨i, D, hD, ha, hT⟩ := h
    exact ⟨i, D, hD, ha, convert_left hT hAB⟩
  | _ => trivial

private theorem cumulative {n i j : ℕ} {Γ : Context n} {t : Term n}
    (h : Premises Γ t (.univ i)) : Premises Γ t (.univ j) := by
  cases t with
  | lam A body =>
    obtain ⟨_, _, B, _, _, _, hT⟩ := h
    exact (not_convertible_univ_pi A B hT).elim
  | pair a b =>
    obtain ⟨_, _, A, B, _, _, _, _, hT⟩ := h
    exact (not_convertible_univ_sigma A B hT).elim
  | zero => exact (not_convertible_of_rigidHead_ne rfl rfl (by intro h; cases h) h).elim
  | succ a => exact (not_convertible_of_rigidHead_ne rfl rfl (by intro h; cases h) h.2).elim
  | star => exact (not_convertible_of_rigidHead_ne rfl rfl (by intro h; cases h) h).elim
  | refl a =>
    obtain ⟨_, A, _, _, hT⟩ := h
    exact (not_convertible_univ_id A a a hT).elim
  | _ => trivial

private theorem generation {n : ℕ} {Γ : Context n} {t T : Term n}
    (h : Derivation Γ t T) : Premises Γ t T := by
  induction h using Derivation.rec (motive_1 := fun _ _ => True) with
  | lam hA hB ht _ _ _ => exact ⟨_, _, _, ⟨hA⟩, ⟨hB⟩, ⟨ht⟩, ⟨.refl _⟩⟩
  | pair hA hB ha hb _ _ _ _ => exact ⟨_, _, _, _, ⟨hA⟩, ⟨hB⟩, ⟨ha⟩, ⟨hb⟩, ⟨.refl _⟩⟩
  | zero hΓ _ => exact ⟨.refl _⟩
  | succ ht _ => exact ⟨⟨ht⟩, ⟨.refl _⟩⟩
  | star hΓ _ => exact ⟨.refl _⟩
  | refl hA ha _ _ => exact ⟨_, _, ⟨hA⟩, ⟨ha⟩, ⟨.refl _⟩⟩
  | conv ht hB hAB iht _ => exact transport iht hAB
  | cumulative hA hij ihA => exact cumulative ihA
  | _ => trivial

theorem lam_generation {n : ℕ} {Γ : Context n} {A T : Term n} {body : Term (n + 1)}
    (h : Derivation Γ (.lam A body) T) :
    ∃ i j B, Typing Γ A (.univ i) ∧ Typing (Γ.snoc A) B (.univ j) ∧
      Typing (Γ.snoc A) body B ∧ Convertible T (.pi A B) := generation h

theorem pair_generation {n : ℕ} {Γ : Context n} {a b T : Term n}
    (h : Derivation Γ (.pair a b) T) :
    ∃ i j A B, Typing Γ A (.univ i) ∧ Typing (Γ.snoc A) B (.univ j) ∧
      Typing Γ a A ∧ Typing Γ b (B.instantiate a) ∧ Convertible T (.sigma A B) := generation h

theorem zero_generation {n : ℕ} {Γ : Context n} {T : Term n}
    (h : Derivation Γ .zero T) : Convertible T .nat := generation h

theorem succ_generation {n : ℕ} {Γ : Context n} {a T : Term n}
    (h : Derivation Γ (.succ a) T) : Typing Γ a .nat ∧ Convertible T .nat := generation h

theorem star_generation {n : ℕ} {Γ : Context n} {T : Term n}
    (h : Derivation Γ .star T) : Convertible T .unit := generation h

theorem refl_generation {n : ℕ} {Γ : Context n} {a T : Term n}
    (h : Derivation Γ (.refl a) T) :
    ∃ i A, Typing Γ A (.univ i) ∧ Typing Γ a A ∧ Convertible T (.id A a a) := generation h

end Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawValueGeneration
