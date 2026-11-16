module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Finite.Defs
public import Silmaril.Logic.SetTheory.Universes.Finite

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

open Silmaril.Logic.TypeTheory.ExtensionalMLTT Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

universe u

theorem denoteIn_eq_denote (T : SetHierarchy.{u}) (ρ : String → ZFSet.{u})
    {k : ℕ} (β : Fin k → ZFSet.{u}) (t : Tm k) :
    t.denoteIn T.U ρ β = t.denote T ρ β := by
  induction t <;> simp_all [Tm.denoteIn, Tm.denote]

theorem satIn_iff_sat (T : SetHierarchy.{u}) (ρ : String → ZFSet.{u}) (Γ : Ctx) :
    Γ.SatIn T.U ρ ↔ Γ.Sat T ρ := by
  induction Γ <;> simp_all [Ctx.SatIn, Ctx.Sat, denoteIn_eq_denote]

theorem validIn_iff_valid (T : SetHierarchy.{u}) (j : Jdg) :
    j.ValidIn T.U ↔ j.Valid T := by
  simp only [Jdg.ValidIn, Jdg.Valid, satIn_iff_sat, denoteIn_eq_denote]

theorem denoteIn_congr {U V : ℕ → ZFSet.{u}} (ρ : String → ZFSet.{u})
    {n k : ℕ} (β : Fin k → ZFSet.{u}) (t : Tm k) (ht : t.UsesBelow n)
    (hUV : ∀ i < n, U i = V i) : t.denoteIn U ρ β = t.denoteIn V ρ β := by
  induction t <;>
    simp_all only [Tm.denoteIn, Tm.UsesBelow, Tm.universeBound, max_le_iff]
  case univ i => exact hUV i (by omega)

theorem satIn_congr {U V : ℕ → ZFSet.{u}} (ρ : String → ZFSet.{u})
    {n : ℕ} (Γ : Ctx) (hΓ : Γ.UsesBelow n) (hUV : ∀ i < n, U i = V i) :
    Γ.SatIn U ρ ↔ Γ.SatIn V ρ := by
  induction Γ with
  | nil => rfl
  | cons Γ x A ih =>
    obtain ⟨hΓ, hA⟩ := max_le_iff.mp hΓ
    simp only [Ctx.SatIn, ih hΓ, denoteIn_congr ρ Fin.elim0 A hA hUV]

theorem validIn_congr {U V : ℕ → ZFSet.{u}} {n : ℕ}
    (j : Jdg) (hj : j.UsesBelow n) (hUV : ∀ i < n, U i = V i) :
    j.ValidIn U ↔ j.ValidIn V := by
  have h : (j.Γ.universeBound ≤ n ∧ j.A.universeBound ≤ n) ∧
      j.a.universeBound ≤ n ∧ j.b.universeBound ≤ n := by
    simpa only [Jdg.UsesBelow, Jdg.universeBound, max_le_iff] using hj
  obtain ⟨⟨hΓ, hA⟩, ha, hb⟩ := h
  simp only [Jdg.ValidIn, satIn_congr _ j.Γ hΓ hUV,
    denoteIn_congr _ Fin.elim0 j.A hA hUV,
    denoteIn_congr _ Fin.elim0 j.a ha hUV,
    denoteIn_congr _ Fin.elim0 j.b hb hUV]

theorem model_nonempty (n : ℕ) [Silmaril.Logic.SetTheory.HasFiniteTower.{u} n] :
    Nonempty (Finite.room.{u} n).Mod :=
  ⟨CategoryTheory.Discrete.mk (Silmaril.Logic.SetTheory.HasFiniteTower.tower n)⟩

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
