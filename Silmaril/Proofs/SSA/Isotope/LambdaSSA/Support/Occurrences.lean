module

public import Silmaril.SSA.Isotope.LambdaSSA.Support.Defs
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.RegionScope

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Support

open Silmaril.Isotope.LambdaSSA (Tm)
open Silmaril.DeBruijn (lift liftN liftN_lt liftN_ge liftN_add_index)

universe u
variable {Φ : Type u}

private theorem lift_uses {p : Nat → Prop} {ρ : Nat → Nat} {i d : Nat} :
    (∃ j, p j ∧ liftN d ρ j = i + d) ↔ ∃ j, p (j + d) ∧ ρ j = i := by
  constructor
  · rintro ⟨j, used, eq⟩
    by_cases younger : j < d
    · rw [liftN_lt _ younger] at eq
      omega
    · have older : d ≤ j := by omega
      have index : j - d + d = j := Nat.sub_add_cancel older
      rw [liftN_ge _ older] at eq
      exact ⟨j - d, by rwa [index], by omega⟩
  · rintro ⟨j, used, eq⟩
    refine ⟨j + d, used, ?_⟩
    rw [Nat.add_comm j d, liftN_add_index, eq, Nat.add_comm]

theorem usesVar_rename (t : Tm Φ) (ρ : Nat → Nat) (i : Nat) :
    (t.rename ρ).UsesVar i ↔ ∃ j, t.UsesVar j ∧ ρ j = i := by
  induction t generalizing ρ i with
  | var j => simp [Tm.rename, Tm.UsesVar, eq_comm]
  | op _ _ ih | inl _ ih | inr _ ih | abort _ ih => exact ih _ _
  | unit => simp [Tm.rename, Tm.UsesVar]
  | pair _ _ left right =>
    simp only [Tm.rename, Tm.UsesVar, left, right, or_and_right, exists_or]
  | let₁ _ _ arg tail =>
    simp only [Tm.rename, Tm.UsesVar, arg, tail, or_and_right, exists_or]
    rw [show lift ρ = liftN 1 ρ from rfl, lift_uses]
  | let₂ _ _ arg tail =>
    simp only [Tm.rename, Tm.UsesVar, arg, tail, lift_uses, or_and_right, exists_or]
  | case _ _ _ discr left right =>
    simp only [Tm.rename, Tm.UsesVar, discr, left, right, or_and_right, exists_or]
    rw [show lift ρ = liftN 1 ρ from rfl]
    simp only [lift_uses]

theorem older_bound (p : Nat → Prop) (n d : Nat) :
    (∀ i, p i → i < n + d) ↔ ∀ i, p (i + d) → i < n := by
  constructor
  · intro bounded i used
    have := bounded (i + d) used
    omega
  · intro bounded i used
    by_cases younger : i < d
    · omega
    · have idx : i - d + d = i := Nat.sub_add_cancel (by omega)
      have := bounded (i - d) (by rwa [idx])
      omega

theorem scoped_iff (t : Tm Φ) (n : Nat) : t.Scoped n ↔ ∀ i, t.UsesVar i → i < n := by
  induction t generalizing n with
  | var j => simp [Tm.Scoped, Tm.UsesVar]
  | op _ _ ih | inl _ ih | inr _ ih | abort _ ih => exact ih _
  | unit => simp [Tm.Scoped, Tm.UsesVar]
  | pair _ _ left right =>
    simp only [Tm.Scoped, Tm.UsesVar, left, right, or_imp, forall_and]
  | let₁ _ _ arg tail | let₂ _ _ arg tail =>
    simp only [Tm.Scoped, Tm.UsesVar, arg, tail, older_bound, or_imp, forall_and]
  | case _ _ _ discr left right =>
    simp only [Tm.Scoped, Tm.UsesVar, discr, left, right, older_bound, or_imp, forall_and]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Support
