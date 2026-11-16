module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.SimultaneousSubstitution.Defs

public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.SimultaneousSubstitution

open Silmaril.Logic.TypeTheory.ExtensionalMLTT

variable (σ : String → ETm 0)

theorem fmap_castLE {n m : ℕ} (t : ETm n) (h : n ≤ m) :
    (t.castLE h).fmap σ = (t.fmap σ).castLE h := by
  induction t generalizing m <;> simp_all [ETm.fmap, ETm.castLE, ETm.castLE_comp]

theorem fmap_wkn {k : ℕ} (t : ETm k) (j : ℕ) :
    (t.wkn j).fmap σ = (t.fmap σ).wkn j := by
  induction t generalizing j with
  | fv y => exact (ETm.closed_castLE_wkn (σ y) j).symm
  | bv i => simp only [ETm.wkn, ETm.fmap]; split <;> rfl
  | _ => simp_all [ETm.fmap, ETm.wkn]

theorem fmap_open {k : ℕ} (t : ETm (k + 1)) {y : String} (hy : σ y = .fv y) :
    (t.open y).fmap σ = (t.fmap σ).open y := by
  fun_induction ETm.open t y with
  | case1 k z => exact (ETm.open_castLE (σ z) (Nat.zero_le k) y).symm
  | case2 k i =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [ETm.open, Fin.lastCases_last, ETm.fmap, hy, ETm.castLE]
    · simp only [ETm.open, Fin.lastCases_castSucc, ETm.fmap]
  | _ => simp_all [ETm.open, ETm.fmap]

theorem fmap_lst {k : ℕ} (t : ETm (k + 1)) (a : ETm 0) :
    (t.lst a).fmap σ = (t.fmap σ).lst (a.fmap σ) := by
  fun_induction ETm.lst t a with
  | case1 k z => exact (ETm.lst_castLE (σ z) (Nat.zero_le k) (a.fmap σ)).symm
  | case2 k i =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [ETm.fmap, ETm.lst, Fin.lastCases_last, fmap_castLE]
    · simp only [ETm.lst, Fin.lastCases_castSucc, ETm.fmap]
  | _ => simp_all [ETm.lst, ETm.fmap]

theorem fmap_arr {k : ℕ} (A B : ETm k) :
    (ETm.arr A B).fmap σ = .arr (A.fmap σ) (B.fmap σ) := by
  simp only [ETm.arr, ETm.fmap, ETm.wk0, fmap_wkn]

theorem fmap_congr {k : ℕ} (t : ETm k) {τ : String → ETm 0}
    (h : ∀ x ∈ t.fvs, σ x = τ x) : t.fmap σ = t.fmap τ := by
  induction t <;> simp_all [ETm.fmap, ETm.fvs]

theorem fmap_id {k : ℕ} (t : ETm k) : t.fmap ETm.fv = t := by
  induction t <;> simp_all [ETm.fmap, ETm.castLE]

theorem fmap_update_fresh {k : ℕ} (t : ETm k) (x : String) (v : ETm 0)
    (hx : x ∉ t.fvs) : t.fmap (Function.update σ x v) = t.fmap σ := by
  apply fmap_congr
  intro y hy
  exact Function.update_of_ne (by intro h; subst y; exact hx hy) _ _

theorem fmap_update_open {k : ℕ} (t : ETm (k + 1)) (x : String) (v : ETm 0)
    (hx : x ∉ t.fvs) :
    (t.open x).fmap (Function.update σ x v) = (t.fmap σ).lst v := by
  fun_induction ETm.open t x with
  | case1 k z =>
    have hz : z ≠ x := by simpa only [ETm.fvs, Finset.mem_singleton, ne_eq, eq_comm] using hx
    simp only [ETm.fmap, Function.update_of_ne hz]
    exact (ETm.lst_castLE (σ z) (Nat.zero_le k) v).symm
  | case2 k i =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.lastCases_last, ETm.fmap, Function.update_self,
        ETm.lst, Fin.lastCases_last]
    · simp only [Fin.lastCases_castSucc, ETm.fmap, ETm.lst, Fin.lastCases_castSucc]
  | _ => simp_all [ETm.fvs, ETm.fmap, ETm.lst]

theorem supported_update {K : Finset String} (hσ : ETm.Supported σ K) (x : String) (v : ETm 0) :
    ETm.Supported (Function.update σ x v) (insert x K) := by
  intro y hy
  have hs : y ≠ x ∧ y ∉ K := by simpa only [Finset.mem_insert, not_or] using hy
  rw [Function.update_of_ne hs.1]
  exact hσ y hs.2

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.SimultaneousSubstitution
