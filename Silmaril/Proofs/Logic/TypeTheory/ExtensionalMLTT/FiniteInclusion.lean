module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Inclusion.Defs
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Thms
public import Silmaril.Logic.Institution.Borrowing

public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Finite

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.SetTheory
open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite

universe u

theorem restrict_refl {n : ℕ} (T : FiniteTower.{u} n) :
    T.restrict (Nat.le_refl n) = T := rfl

theorem restrict_comp {n m k : ℕ} (T : FiniteTower.{u} k)
    (hnm : n ≤ m) (hmk : m ≤ k) :
    (T.restrict hmk).restrict hnm = T.restrict (hnm.trans hmk) := rfl

theorem inclusion_refl (n : ℕ) :
    inclusion.{u} (Nat.le_refl n) = Inst.CoHom.id (bundled.{u} n) := by
  refine Inst.CoHom.ext (f := inclusion (Nat.le_refl n)) (g := Inst.CoHom.id (bundled n)) rfl ?_
  apply NatTrans.ext
  funext S
  apply Corridor.ext
  · rfl
  · apply Discrete.functor_ext
    intro T
    cases T
    rfl

theorem inclusion_comp {n m k : ℕ} (hnm : n ≤ m) (hmk : m ≤ k) :
    inclusion.{u} (hnm.trans hmk) =
      Inst.CoHom.comp (inclusion hnm) (inclusion hmk) := rfl

theorem modelsExtend_refl (n : ℕ) : ModelsExtend.{u} (Nat.le_refl n) := by
  intro T
  exact ⟨T, fun _ _ => rfl⟩

theorem modelsExtend_zero (m : ℕ) [HasFiniteTower.{u} m] :
    ModelsExtend.{u} (Nat.zero_le m) := by
  intro T
  refine ⟨HasFiniteTower.tower m, ?_⟩
  intro i hi
  exact (Nat.not_lt_zero i hi).elim

theorem inclusion_observationalExpansion {n m : ℕ} {h : n ≤ m}
    (hext : ModelsExtend.{u} h) (T : (room.{u} n).Mod) :
    ∃ T' : (room.{u} m).Mod, ∀ j : Sentence n,
      (room m).Sat T' (includeSentence h j) ↔ (room n).Sat T j := by
  obtain ⟨T', hT'⟩ : ∃ T' : FiniteTower.{u} m, ∀ i < n, T'.U i = T.as.U i := hext T.as
  refine ⟨Discrete.mk T', ?_⟩
  intro j
  exact j.val.validIn_congr j.property hT'

theorem inclusion_entails_iff {n m : ℕ} (h : n ≤ m)
    (hext : ModelsExtend.{u} h) (H : Set (Sentence n)) (j : Sentence n) :
    (room.{u} n).Entails H j ↔
      (room.{u} m).Entails (includeSentence h '' H) (includeSentence h j) := by
  constructor
  · intro hj
    exact (inclusion.{u} h).entails_map (S := Discrete.mk ()) hj
  · intro hj T hT
    obtain ⟨T', hSat⟩ : ∃ T' : (room.{u} m).Mod, ∀ k : Sentence n,
        (room m).Sat T' (includeSentence h k) ↔ (room n).Sat T k :=
      inclusion_observationalExpansion hext T
    have hT' : ∀ k ∈ includeSentence h '' H, (room m).Sat T' k := by
      intro k hk
      obtain ⟨l, hl, rfl⟩ := hk
      exact (hSat l).mpr (hT l hl)
    exact (hSat j).mp (hj T' hT')

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Finite
