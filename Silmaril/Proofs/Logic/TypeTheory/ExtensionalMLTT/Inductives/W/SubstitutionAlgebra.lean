module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Thms

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

theorem wkn_wkn {k : ℕ} (t : Tm k) (i j : ℕ) (hij : i ≤ j) :
    (t.wkn i).wkn (j + 1) = (t.wkn j).wkn i := by
  induction t generalizing i j <;>
    simp_all only [Tm.wkn, Nat.add_le_add_iff_right]
  case bv x =>
    by_cases hxi : (x : ℕ) < i
    · have hxj : (x : ℕ) < j := lt_of_lt_of_le hxi hij
      have hxj' : (x : ℕ) < j + 1 := by omega
      simp [Tm.wkn, hxi, hxj, hxj']
    · by_cases hxj : (x : ℕ) < j
      · have hxj' : (x : ℕ) + 1 < j + 1 := by omega
        simp [Tm.wkn, hxi, hxj, hxj']
      · have hxj' : ¬ (x : ℕ) + 1 < j + 1 := by omega
        have hxi' : ¬ (x : ℕ) + 1 < i := by omega
        simp [Tm.wkn, hxi, hxj, hxj', hxi']

private theorem liftSub_shift {n m : ℕ} (σ : Fin (n + 1) → Tm m) (j : ℕ) :
    (fun i : Fin (n + 1) =>
      Tm.liftSub σ (if (i : ℕ) < j + 1 then i.castSucc else i.succ)) =
      Tm.liftSub (fun i : Fin n => σ (if (i : ℕ) < j then i.castSucc else i.succ)) := by
  funext i
  cases i using Fin.cases with
  | zero => simp [Tm.liftSub]
  | succ i =>
    by_cases hi : (i : ℕ) < j <;> simp [Tm.liftSub, hi]

theorem bsubst_wkn {n m : ℕ} (t : Tm n) (σ : Fin (n + 1) → Tm m) (j : ℕ) :
    (t.wkn j).bsubst σ =
      t.bsubst (fun i => σ (if (i : ℕ) < j then i.castSucc else i.succ)) := by
  induction t generalizing m j <;> simp_all only [Tm.wkn, Tm.bsubst, liftSub_shift]
  case bv i => split <;> rfl

private theorem liftSub_wkn {n m : ℕ} (σ : Fin n → Tm m) (j : ℕ) :
    (fun i => (Tm.liftSub σ i).wkn (j + 1)) =
      Tm.liftSub (fun i => (σ i).wkn j) := by
  funext i
  cases i using Fin.cases with
  | zero => simp [Tm.liftSub, Tm.wkn]
  | succ i =>
    simpa only [Tm.liftSub, Fin.cases_succ, Tm.wk0] using
      wkn_wkn (σ i) 0 j (Nat.zero_le j)

theorem wkn_bsubst {n m : ℕ} (t : Tm n) (σ : Fin n → Tm m) (j : ℕ) :
    (t.bsubst σ).wkn j = t.bsubst (fun i => (σ i).wkn j) := by
  induction t generalizing m j <;> simp_all only [Tm.bsubst, Tm.wkn, liftSub_wkn]

private theorem liftSub_bsubst {n m k : ℕ} (σ : Fin n → Tm m) (τ : Fin m → Tm k) :
    (fun i => (Tm.liftSub σ i).bsubst (Tm.liftSub τ)) =
      Tm.liftSub (fun i => (σ i).bsubst τ) := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    simpa only [Tm.liftSub, Fin.cases_succ, Tm.wk0, bsubst_wkn,
      Nat.not_lt_zero, ↓reduceIte] using (wkn_bsubst (σ i) τ 0).symm

/-- Composition of arbitrary capture-avoiding simultaneous bound substitutions. -/
theorem bsubst_comp {n m k : ℕ} (t : Tm n) (σ : Fin n → Tm m) (τ : Fin m → Tm k) :
    (t.bsubst σ).bsubst τ = t.bsubst (fun i => (σ i).bsubst τ) := by
  induction t generalizing m k <;> simp_all only [Tm.bsubst, liftSub_bsubst]

theorem castLE_refl {k : ℕ} (t : Tm k) : t.castLE (Nat.le_refl k) = t := by
  induction t <;> simp_all [Tm.castLE]

theorem castLE_comp {n m k : ℕ} (t : Tm n) (h : n ≤ m) (h' : m ≤ k) :
    (t.castLE h).castLE h' = t.castLE (h.trans h') := by
  induction t generalizing m k <;> simp_all [Tm.castLE]

theorem wkn_past {k : ℕ} (t : Tm k) (j : ℕ) (hkj : k ≤ j) :
    t.wkn j = t.castLE (Nat.le_succ k) := by
  induction t generalizing j <;>
    simp_all only [Tm.wkn, Tm.castLE, Nat.add_le_add_iff_right]
  case bv i =>
    rw [ite_eq_left (lt_of_lt_of_le i.isLt hkj)]
    rfl

theorem wkn_castLE {n m : ℕ} (t : Tm n) (h : n ≤ m) (j : ℕ) :
    (t.castLE h).wkn j = (t.wkn j).castLE (Nat.succ_le_succ h) := by
  induction t generalizing m j <;> simp_all only [Tm.castLE, Tm.wkn]
  case bv i =>
    by_cases hi : (i : ℕ) < j <;> simp [hi, Tm.castLE]

private theorem liftSub_castLE {n m k : ℕ} (h : n ≤ m) (σ : Fin m → Tm k) :
    (fun i : Fin (n + 1) => Tm.liftSub σ (i.castLE (Nat.succ_le_succ h))) =
      Tm.liftSub (fun i : Fin n => σ (i.castLE h)) := by
  funext i
  cases i using Fin.cases <;> rfl

theorem bsubst_castLE {n m k : ℕ} (t : Tm n) (h : n ≤ m) (σ : Fin m → Tm k) :
    (t.castLE h).bsubst σ = t.bsubst (fun i => σ (i.castLE h)) := by
  induction t generalizing m k <;>
    simp_all only [Tm.castLE, Tm.bsubst, liftSub_castLE]

theorem castLE_eq_bsubst {n m : ℕ} (t : Tm n) (h : n ≤ m) :
    t.castLE h = t.bsubst (fun i => .bv (i.castLE h)) := by
  simpa only [Tm.bsubst_id] using bsubst_castLE t h (fun i => .bv i)

theorem closed_bsubst {m : ℕ} (t : Tm 0) (σ : Fin 0 → Tm m) :
    t.bsubst σ = t.castLE (Nat.zero_le m) := by
  rw [castLE_eq_bsubst]
  congr 1
  funext i
  exact i.elim0

theorem bsubst_closed_castLE {n m : ℕ} (t : Tm 0) (σ : Fin n → Tm m) :
    (t.castLE (Nat.zero_le n)).bsubst σ = t.castLE (Nat.zero_le m) := by
  rw [bsubst_castLE, closed_bsubst]

theorem closed_wk0_open (t : Tm 0) (x : String) : t.wk0.open x = t := by
  rw [Tm.wk0, wkn_past t 0 (Nat.le_refl 0), Tm.open_castLE t (Nat.le_refl 0), castLE_refl]

private theorem liftSub_last (k : ℕ) (x : String) :
    Tm.liftSub (Fin.lastCases (.fv x : Tm k) .bv) =
      Fin.lastCases (.fv x : Tm (k + 1)) .bv := by
  funext i
  cases i using Fin.cases with
  | zero =>
    change (.bv 0 : Tm (k + 1)) =
      Fin.lastCases (.fv x) .bv ((0 : Fin (k + 1)).castSucc)
    rw [Fin.lastCases_castSucc]
  | succ i =>
    simp only [Tm.liftSub, Fin.cases_succ]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.lastCases_last, Fin.succ_last, Tm.wk0, Tm.wkn]
    · rw [Fin.lastCases_castSucc, Fin.succ_castSucc, Fin.lastCases_castSucc]
      rfl

theorem open_eq_bsubst {k : ℕ} (t : Tm (k + 1)) (x : String) :
    t.open x = t.bsubst (Fin.lastCases (.fv x) .bv) := by
  fun_induction Tm.open t x <;> simp_all only [Tm.bsubst, liftSub_last]

private theorem liftSub_lastTerm (k : ℕ) (v : Tm 0) :
    Tm.liftSub (Fin.lastCases (v.castLE (Nat.zero_le k)) .bv) =
      Fin.lastCases (v.castLE (Nat.zero_le (k + 1))) .bv := by
  funext i
  cases i using Fin.cases with
  | zero =>
    change (.bv 0 : Tm (k + 1)) =
      Fin.lastCases (v.castLE (Nat.zero_le (k + 1))) .bv ((0 : Fin (k + 1)).castSucc)
    rw [Fin.lastCases_castSucc]
  | succ i =>
    simp only [Tm.liftSub, Fin.cases_succ]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.lastCases_last, Fin.succ_last, Tm.wk0]
      rw [wkn_castLE, wkn_past v 0 (Nat.le_refl 0), castLE_comp]
    · rw [Fin.lastCases_castSucc, Fin.succ_castSucc, Fin.lastCases_castSucc]
      rfl

theorem lst_eq_bsubst {k : ℕ} (t : Tm (k + 1)) (v : Tm 0) :
    t.lst v = t.bsubst (Fin.lastCases (v.castLE (Nat.zero_le k)) .bv) := by
  fun_induction Tm.lst t v <;> simp_all only [Tm.bsubst, liftSub_lastTerm]

theorem open_bsubst {n m : ℕ} (t : Tm n) (σ : Fin n → Tm (m + 1)) (x : String) :
    (t.bsubst σ).open x = t.bsubst (fun i => (σ i).open x) := by
  rw [open_eq_bsubst, bsubst_comp]
  congr 1
  funext i
  exact (open_eq_bsubst (σ i) x).symm

theorem bsubst_open {n m : ℕ} (t : Tm (n + 1)) (σ : Fin n → Tm m) (x : String) :
    (t.open x).bsubst σ = t.bsubst (Fin.lastCases (.fv x) σ) := by
  rw [open_eq_bsubst, bsubst_comp]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Tm.bsubst]

theorem lst_bsubst {n m : ℕ} (t : Tm n) (σ : Fin n → Tm (m + 1)) (v : Tm 0) :
    (t.bsubst σ).lst v = t.bsubst (fun i => (σ i).lst v) := by
  rw [lst_eq_bsubst, bsubst_comp]
  congr 1
  funext i
  exact (lst_eq_bsubst (σ i) v).symm

theorem bsubst_lst {n m : ℕ} (t : Tm (n + 1)) (σ : Fin n → Tm m) (v : Tm 0) :
    (t.lst v).bsubst σ = t.bsubst (Fin.lastCases (v.castLE (Nat.zero_le m)) σ) := by
  rw [lst_eq_bsubst, bsubst_comp]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.lastCases_last, bsubst_closed_castLE]
  · simp only [Fin.lastCases_castSucc, Tm.bsubst]

theorem wkn_eq_bsubst {k : ℕ} (t : Tm k) (j : ℕ) :
    t.wkn j = t.bsubst (fun i => .bv (if (i : ℕ) < j then i.castSucc else i.succ)) := by
  simpa only [Tm.bsubst_id, Tm.wkn, apply_ite] using wkn_bsubst t (fun i => .bv i) j

theorem closed_wk0_lst (t v : Tm 0) : t.wk0.lst v = t := by
  rw [Tm.wk0, wkn_past t 0 (Nat.le_refl 0), lst_eq_bsubst,
    bsubst_closed_castLE, castLE_refl]

theorem closed_castLE_wkn {k : ℕ} (t : Tm 0) (j : ℕ) :
    (t.castLE (Nat.zero_le k)).wkn j = t.castLE (Nat.zero_le (k + 1)) := by
  rw [wkn_castLE, wkn_past t j (Nat.zero_le j), castLE_comp]

theorem closed_castLE_open {k : ℕ} (t : Tm 0) (x : String) :
    (t.castLE (Nat.zero_le (k + 1))).open x = t.castLE (Nat.zero_le k) :=
  Tm.open_castLE t (Nat.zero_le k) x

/-- Insertion below the outermost binder commutes with opening that binder. -/
theorem open_wkn {k : ℕ} (t : Tm (k + 1)) (x : String) (j : ℕ) (hj : j ≤ k) :
    (t.wkn j).open x = (t.open x).wkn j := by
  rw [open_eq_bsubst, bsubst_wkn, open_eq_bsubst, wkn_bsubst]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun l => ?_) i
  · simp [Fin.lastCases_last, show ¬k < j by omega, Tm.wkn]
  · by_cases h : (l : ℕ) < j
    · simp [h, Fin.lastCases_castSucc, Tm.wkn]
    · simp only [Fin.lastCases_castSucc, Tm.wkn, Fin.val_castSucc, h, ite_false]
      change Fin.lastCases (Tm.fv x) Tm.bv l.succ.castSucc = Tm.bv l.succ
      exact Fin.lastCases_castSucc _

theorem lst_wkn {k : ℕ} (t : Tm (k + 1)) (a : Tm 0) (j : ℕ) (hj : j ≤ k) :
    (t.wkn j).lst a = (t.lst a).wkn j := by
  rw [lst_eq_bsubst, bsubst_wkn, lst_eq_bsubst, wkn_bsubst]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun l => ?_) i
  · simp only [Fin.val_last, show ¬ k < j by omega, ite_false, Fin.succ_last,
      Fin.lastCases_last, closed_castLE_wkn]
  · by_cases h : (l : ℕ) < j
    · simp only [Fin.val_castSucc, h, ite_true, Fin.lastCases_castSucc, Tm.wkn]
    · simp only [Fin.val_castSucc, h, ite_false, Fin.lastCases_castSucc, Tm.wkn]
      change Fin.lastCases (a.castLE (Nat.zero_le (k + 1))) Tm.bv l.succ.castSucc = Tm.bv l.succ
      exact Fin.lastCases_castSucc _

theorem closed_castLE_lst {k : ℕ} (t a : Tm 0) :
    (t.castLE (Nat.zero_le (k + 1))).lst a = t.castLE (Nat.zero_le k) := by
  rw [lst_eq_bsubst, bsubst_closed_castLE]

theorem arrow_lst {k : ℕ} (A B : Tm (k + 1)) (a : Tm 0) :
    (Tm.arr A B).lst a = Tm.arr (A.lst a) (B.lst a) := by
  simp only [Tm.arr, Tm.lst, Tm.wk0, lst_wkn _ a 0 (Nat.zero_le _)]


theorem lst_castLE {n m : ℕ} (t : Tm n) (h : n ≤ m) (a : Tm 0) :
    (t.castLE (Nat.le_succ_of_le h)).lst a = t.castLE h := by
  rw [lst_eq_bsubst, bsubst_castLE]
  conv_rhs => rw [castLE_eq_bsubst]
  congr 1
  funext i
  change (Fin.lastCases (a.castLE (Nat.zero_le m)) Tm.bv (i.castLE h).castSucc : Tm m) = Tm.bv (i.castLE h)
  exact Fin.lastCases_castSucc _


end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
