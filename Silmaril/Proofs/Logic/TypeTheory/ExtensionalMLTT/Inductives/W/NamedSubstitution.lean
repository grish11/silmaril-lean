module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.NamedSubstitution.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

variable (x : String) (v : Tm 0)

theorem fsubst_castLE {n m : ℕ} (t : Tm n) (h : n ≤ m) :
    (t.castLE h).fsubst x v = (t.fsubst x v).castLE h := by
  induction t generalizing m <;> simp_all [Tm.fsubst, Tm.castLE]
  split <;> simp_all [Tm.castLE, Tm.castLE_comp]

theorem fsubst_wkn {k : ℕ} (t : Tm k) (j : ℕ) :
    (t.wkn j).fsubst x v = (t.fsubst x v).wkn j := by
  induction t generalizing j <;> simp_all [Tm.fsubst, Tm.wkn]
  all_goals split <;> simp_all [Tm.fsubst, Tm.wkn]

private theorem fsubst_liftSub {n m : ℕ} (σ : Fin n → Tm m) :
    (fun i => (Tm.liftSub σ i).fsubst x v) = Tm.liftSub (fun i => (σ i).fsubst x v) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [Tm.liftSub, Fin.cases_succ, Tm.wk0, fsubst_wkn]

theorem fsubst_bsubst {n m : ℕ} (t : Tm n) (σ : Fin n → Tm m) :
    (t.bsubst σ).fsubst x v = (t.fsubst x v).bsubst (fun i => (σ i).fsubst x v) := by
  induction t generalizing m <;>
    simp_all [Tm.bsubst, Tm.fsubst, fsubst_liftSub]
  split <;> simp_all [Tm.bsubst, Tm.bsubst_closed_castLE]

theorem fsubst_open {k : ℕ} (t : Tm (k + 1)) {y : String} (hy : y ≠ x) :
    (t.open y).fsubst x v = (t.fsubst x v).open y := by
  rw [Tm.open_eq_bsubst, fsubst_bsubst, Tm.open_eq_bsubst]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Tm.fsubst, hy]

theorem fsubst_lst {k : ℕ} (t : Tm (k + 1)) (a : Tm 0) :
    (t.lst a).fsubst x v = (t.fsubst x v).lst (a.fsubst x v) := by
  rw [Tm.lst_eq_bsubst, fsubst_bsubst, Tm.lst_eq_bsubst]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.lastCases_last, fsubst_castLE]
  · simp only [Fin.lastCases_castSucc, Tm.fsubst]

theorem fsubst_arr {k : ℕ} (A B : Tm k) :
    (Tm.arr A B).fsubst x v = .arr (A.fsubst x v) (B.fsubst x v) := by
  simp only [Tm.arr, Tm.fsubst, Tm.wk0, fsubst_wkn]

theorem fsubst_wStepType (A : Tm 0) (B C : Tm 1) :
    (Tm.wStepType A B C).fsubst x v =
      Tm.wStepType (A.fsubst x v) (B.fsubst x v) (C.fsubst x v) := by
  simp only [Tm.wStepType, Tm.fsubst, fsubst_castLE, fsubst_bsubst]

theorem fsubst_recChildren (A s a f : Tm 0) (B C : Tm 1) :
    (Tm.recChildren A B C s a f).fsubst x v =
      Tm.recChildren (A.fsubst x v) (B.fsubst x v) (C.fsubst x v)
        (s.fsubst x v) (a.fsubst x v) (f.fsubst x v) := by
  simp only [Tm.recChildren, Tm.fsubst, fsubst_lst, Tm.wk0, fsubst_wkn]

theorem fsubst_fresh {k : ℕ} (t : Tm k) (hx : x ∉ t.fvs) : t.fsubst x v = t := by
  induction t <;> simp_all [Tm.fsubst, Tm.fvs]
  intro h
  exact (hx h.symm).elim

theorem fsubst_open_self {k : ℕ} (t : Tm (k + 1)) (hx : x ∉ t.fvs) :
    (t.open x).fsubst x v = t.lst v := by
  rw [Tm.open_eq_bsubst, fsubst_bsubst, fsubst_fresh x v t hx, Tm.lst_eq_bsubst]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Tm.fsubst]

theorem lookup_typeFvs {Γ : Ctx} {y : String} {A : Tm 0} (h : Γ.Lookup y A) :
    A.fvs ⊆ Γ.typeFvs := by
  induction h with
  | here => exact Finset.subset_union_right
  | there _ _ _ _ _ h hy ih => exact ih.trans Finset.subset_union_left

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
