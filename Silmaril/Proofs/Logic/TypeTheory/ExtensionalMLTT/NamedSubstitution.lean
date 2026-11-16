module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.NamedSubstitution.Defs

public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.NamedSubstitution

open Silmaril.Logic.TypeTheory.ExtensionalMLTT

theorem castLE_refl {k : ℕ} (t : ETm k) : t.castLE (Nat.le_refl k) = t := by
  induction t <;> simp_all [ETm.castLE]

theorem castLE_comp {n m k : ℕ} (t : ETm n) (h : n ≤ m) (h' : m ≤ k) :
    (t.castLE h).castLE h' = t.castLE (h.trans h') := by
  induction t generalizing m k <;> simp_all [ETm.castLE]

theorem wkn_past {k : ℕ} (t : ETm k) (j : ℕ) (hkj : k ≤ j) :
    t.wkn j = t.castLE (Nat.le_succ k) := by
  induction t generalizing j with
  | bv i =>
    simp only [ETm.wkn, ETm.castLE, show (i : ℕ) < j by omega, ↓reduceIte]
    rfl
  | _ => simp_all [ETm.wkn, ETm.castLE]

theorem wkn_castLE {n m : ℕ} (t : ETm n) (h : n ≤ m) (j : ℕ) :
    (t.castLE h).wkn j = (t.wkn j).castLE (Nat.succ_le_succ h) := by
  induction t generalizing m j <;> simp_all [ETm.castLE, ETm.wkn]
  split <;> rfl

theorem closed_castLE_wkn {k : ℕ} (t : ETm 0) (j : ℕ) :
    (t.castLE (Nat.zero_le k)).wkn j = t.castLE (Nat.zero_le (k + 1)) := by
  rw [wkn_castLE, wkn_past t j (Nat.zero_le j), castLE_comp]

theorem open_castLE {n m : ℕ} (t : ETm n) (h : n ≤ m) (x : String) :
    (t.castLE (Nat.le_succ_of_le h)).open x = t.castLE h := by
  induction t generalizing m with
  | bv i =>
    simp only [ETm.castLE, ETm.open]
    change Fin.lastCases (.fv x) ETm.bv (i.castLE h).castSucc = ETm.bv (i.castLE h)
    exact Fin.lastCases_castSucc _
  | _ => simp_all [ETm.castLE, ETm.open]

theorem open_wkn {k : ℕ} (t : ETm (k + 1)) (x : String) (j : ℕ) (hj : j ≤ k) :
    (t.wkn j).open x = (t.open x).wkn j := by
  fun_induction ETm.open t x generalizing j with
  | case1 k y => simp only [ETm.wkn, ETm.open]
  | case2 k i =>
    refine Fin.lastCases ?_ (fun l => ?_) i
    · simp only [ETm.wkn, Fin.val_last, show ¬k < j by omega, ite_false,
        Fin.succ_last, ETm.open, Fin.lastCases_last]
    · by_cases hl : (l : ℕ) < j
      · simp only [ETm.wkn, Fin.val_castSucc, hl, ite_true, ETm.open, Fin.lastCases_castSucc]
      · simp only [ETm.wkn, Fin.val_castSucc, hl, ite_false, ETm.open,
          Fin.lastCases_castSucc, Fin.succ_castSucc]
  | _ => simp_all [ETm.wkn, ETm.open]

theorem lst_castLE {n m : ℕ} (t : ETm n) (h : n ≤ m) (v : ETm 0) :
    (t.castLE (Nat.le_succ_of_le h)).lst v = t.castLE h := by
  induction t generalizing m with
  | bv i =>
    simp only [ETm.castLE, ETm.lst]
    change Fin.lastCases (v.castLE (Nat.zero_le m)) ETm.bv (i.castLE h).castSucc = ETm.bv (i.castLE h)
    exact Fin.lastCases_castSucc _
  | _ => simp_all [ETm.castLE, ETm.lst]

variable (x : String) (v : ETm 0)

theorem fsubst_castLE {n m : ℕ} (t : ETm n) (h : n ≤ m) :
    (t.castLE h).fsubst x v = (t.fsubst x v).castLE h := by
  induction t generalizing m <;> simp_all [ETm.fsubst, ETm.castLE]
  split <;> simp_all [ETm.castLE, castLE_comp]

theorem fsubst_wkn {k : ℕ} (t : ETm k) (j : ℕ) :
    (t.wkn j).fsubst x v = (t.fsubst x v).wkn j := by
  induction t generalizing j with
  | fv y =>
    simp only [ETm.wkn, ETm.fsubst]
    split
    · exact (closed_castLE_wkn v j).symm
    · rfl
  | bv i => simp only [ETm.wkn, ETm.fsubst]; split <;> rfl
  | _ => simp_all [ETm.fsubst, ETm.wkn]

theorem fsubst_open {k : ℕ} (t : ETm (k + 1)) {y : String} (hy : y ≠ x) :
    (t.open y).fsubst x v = (t.fsubst x v).open y := by
  fun_induction ETm.open t y with
  | case1 k z =>
    simp only [ETm.fsubst]
    split
    · exact (open_castLE v (Nat.zero_le k) y).symm
    · simp only [ETm.open]
  | case2 k i =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [ETm.open, Fin.lastCases_last, ETm.fsubst, hy, ite_false]
    · simp only [ETm.open, Fin.lastCases_castSucc, ETm.fsubst]
  | _ => simp_all [ETm.open, ETm.fsubst]

theorem fsubst_lst {k : ℕ} (t : ETm (k + 1)) (a : ETm 0) :
    (t.lst a).fsubst x v = (t.fsubst x v).lst (a.fsubst x v) := by
  fun_induction ETm.lst t a with
  | case1 k z =>
    simp only [ETm.fsubst]
    split
    · exact (lst_castLE v (Nat.zero_le k) (a.fsubst x v)).symm
    · simp only [ETm.lst]
  | case2 k i =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [ETm.fsubst, ETm.lst, Fin.lastCases_last, fsubst_castLE]
    · simp only [ETm.lst, Fin.lastCases_castSucc, ETm.fsubst]
  | _ => simp_all [ETm.lst, ETm.fsubst]

theorem fsubst_arr {k : ℕ} (A B : ETm k) :
    (ETm.arr A B).fsubst x v = .arr (A.fsubst x v) (B.fsubst x v) := by
  simp only [ETm.arr, ETm.fsubst, ETm.wk0, fsubst_wkn]

theorem fsubst_fresh {k : ℕ} (t : ETm k) (hx : x ∉ t.fvs) : t.fsubst x v = t := by
  induction t <;> simp_all [ETm.fsubst, ETm.fvs]
  intro h
  exact (hx h.symm).elim

theorem fsubst_open_self {k : ℕ} (t : ETm (k + 1)) (hx : x ∉ t.fvs) :
    (t.open x).fsubst x v = t.lst v := by
  fun_induction ETm.open t x with
  | case1 k z => simp_all [ETm.fsubst, ETm.lst, ETm.fvs, eq_comm]
  | case2 k i =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [ETm.lst, Fin.lastCases_last, ETm.fsubst, ite_true]
    · simp only [ETm.lst, Fin.lastCases_castSucc, ETm.fsubst]
  | _ => simp_all [ETm.fsubst, ETm.lst, ETm.fvs]

theorem lookup_typeFvs {Γ : ECtx} {y : String} {A : ETm 0} (h : Γ.Lookup y A) :
    A.fvs ⊆ Γ.typeFvs := by
  induction h with
  | here => exact Finset.subset_union_right
  | there _ _ _ _ _ h hy ih => exact ih.trans Finset.subset_union_left

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.NamedSubstitution
