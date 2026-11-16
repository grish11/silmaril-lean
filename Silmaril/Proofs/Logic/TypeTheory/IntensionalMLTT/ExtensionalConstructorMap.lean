module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Extensional.Syntax.Defs
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.NamedSubstitution.Thms

public section

namespace Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.ExtensionalSyntax

open Silmaril.Logic.TypeTheory.IntensionalMLTT
open Silmaril.Logic.TypeTheory.IntensionalMLTT.Extensional
open Silmaril.Logic.TypeTheory.ExtensionalMLTT

theorem open_wkn {k : ℕ} (t : ETm (k + 1)) (x : String) (j : ℕ) (hj : j ≤ k) :
    (t.wkn j).open x = (t.open x).wkn j :=
  ETm.open_wkn t x j hj

theorem lst_wkn {k : ℕ} (t : ETm (k + 1)) (v : ETm 0) (j : ℕ) (hj : j ≤ k) :
    (t.wkn j).lst v = (t.lst v).wkn j := by
  fun_induction ETm.lst t v generalizing j with
  | case1 k y => simp only [ETm.wkn, ETm.lst]
  | case2 k i =>
    refine Fin.lastCases ?_ (fun l => ?_) i
    · simp only [ETm.wkn, Fin.val_last, show ¬k < j by omega, ite_false,
        Fin.succ_last, ETm.lst, Fin.lastCases_last, ETm.closed_castLE_wkn]
    · by_cases hl : (l : ℕ) < j
      · simp only [ETm.wkn, Fin.val_castSucc, hl, ite_true, ETm.lst, Fin.lastCases_castSucc]
      · simp only [ETm.wkn, Fin.val_castSucc, hl, ite_false, ETm.lst,
          Fin.lastCases_castSucc, Fin.succ_castSucc]
  | _ => simp_all [ETm.wkn, ETm.lst]


private theorem open_bv_zero (k : ℕ) (x : String) :
    (ETm.bv (0 : Fin (k + 2))).open x = .bv (0 : Fin (k + 1)) := by
  simp only [ETm.open]
  change Fin.lastCases (ETm.fv x : ETm (k + 1)) ETm.bv (0 : Fin (k + 1)).castSucc = ETm.bv 0
  exact Fin.lastCases_castSucc _

private theorem lst_bv_zero (k : ℕ) (v : ETm 0) :
    (ETm.bv (0 : Fin (k + 2))).lst v = .bv (0 : Fin (k + 1)) := by
  simp only [ETm.lst]
  change Fin.lastCases (v.castLE (Nat.zero_le (k + 1))) ETm.bv (0 : Fin (k + 1)).castSucc = ETm.bv 0
  exact Fin.lastCases_castSucc _

theorem lift_open {n k : ℕ} (σ : Fin n → ETm (k + 1)) (x : String) :
    (fun i => (lift σ i).open x) = lift (fun i => (σ i).open x) := by
  funext i
  cases i using Fin.cases with
  | zero => exact open_bv_zero k x
  | succ i => exact open_wkn (σ i) x 0 (Nat.zero_le k)

theorem lift_lst {n k : ℕ} (σ : Fin n → ETm (k + 1)) (v : ETm 0) :
    (fun i => (lift σ i).lst v) = lift (fun i => (σ i).lst v) := by
  funext i
  cases i using Fin.cases with
  | zero => exact lst_bv_zero k v
  | succ i => exact lst_wkn (σ i) v 0 (Nat.zero_le k)

theorem term_open {n k : ℕ} (σ : Fin n → ETm (k + 1)) (t : Term n) (x : String) :
    (term σ t).open x = term (fun i => (σ i).open x) t := by
  induction t generalizing k <;>
    simp_all [term, ETm.open, lift_open, ETm.wk0, open_wkn, open_bv_zero]

theorem term_lst {n k : ℕ} (σ : Fin n → ETm (k + 1)) (t : Term n) (v : ETm 0) :
    (term σ t).lst v = term (fun i => (σ i).lst v) t := by
  induction t generalizing k <;>
    simp_all [term, ETm.lst, lift_lst, ETm.wk0, lst_wkn, lst_bv_zero]

private theorem lift_rename {n m k : ℕ} (σ : Fin m → ETm k) (ρ : Fin n → Fin m) :
    lift (σ ∘ ρ) = lift σ ∘ Term.upRen ρ := by
  funext i
  cases i using Fin.cases <;> rfl

theorem term_rename {n m k : ℕ} (σ : Fin m → ETm k) (ρ : Fin n → Fin m) (t : Term n) :
    term σ (t.rename ρ) = term (σ ∘ ρ) t := by
  induction t generalizing m k <;> simp_all [Term.rename, term, lift_rename]

theorem wkn_wkn {k : ℕ} (t : ETm k) (i j : ℕ) (hij : i ≤ j) :
    (t.wkn i).wkn (j + 1) = (t.wkn j).wkn i := by
  induction t generalizing i j <;>
    simp_all only [ETm.wkn, Nat.add_le_add_iff_right]
  case bv x =>
    by_cases hxi : (x : ℕ) < i
    · have hxj : (x : ℕ) < j := lt_of_lt_of_le hxi hij
      have hxj' : (x : ℕ) < j + 1 := by omega
      simp [ETm.wkn, hxi, hxj, hxj']
    · by_cases hxj : (x : ℕ) < j
      · have hxj' : (x : ℕ) + 1 < j + 1 := by omega
        simp [ETm.wkn, hxi, hxj, hxj']
      · have hxj' : ¬ (x : ℕ) + 1 < j + 1 := by omega
        have hxi' : ¬ (x : ℕ) + 1 < i := by omega
        simp [ETm.wkn, hxi, hxj, hxj', hxi']

private theorem lift_wkn {n k : ℕ} (σ : Fin n → ETm k) (j : ℕ) :
    (fun i => (lift σ i).wkn (j + 1)) = lift (fun i => (σ i).wkn j) := by
  funext i
  cases i using Fin.cases with
  | zero => simp [lift, ETm.wkn]
  | succ i =>
    simpa only [lift, Fin.cons_succ, ETm.wk0] using wkn_wkn (σ i) 0 j (Nat.zero_le j)

theorem term_wkn {n k : ℕ} (σ : Fin n → ETm k) (t : Term n) (j : ℕ) :
    (term σ t).wkn j = term (fun i => (σ i).wkn j) t := by
  induction t generalizing k j <;>
    simp_all [term, ETm.wkn, lift_wkn, ETm.wk0, wkn_wkn]

private theorem lift_subst {n m k : ℕ} (σ : Fin m → ETm k) (τ : Fin n → Term m) :
    (fun i => term (lift σ) (Term.upSub τ i)) = lift (fun i => term σ (τ i)) := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    simpa only [Term.upSub, Fin.cons_succ, Term.weaken, term_rename, lift, Function.comp_def,
      ETm.wk0] using (term_wkn σ (τ i) 0).symm

theorem term_subst {n m k : ℕ} (σ : Fin m → ETm k) (τ : Fin n → Term m) (t : Term n) :
    term σ (t.subst τ) = term (fun i => term σ (τ i)) t := by
  induction t generalizing m k <;> simp_all [Term.subst, term, lift_subst]

theorem closed_wk0_open (t : ETm 0) (x : String) : t.wk0.open x = t := by
  rw [ETm.wk0, ETm.wkn_past t 0 (Nat.le_refl 0), ETm.open_castLE t (Nat.le_refl 0), ETm.castLE_refl]

theorem closed_wk0_lst (t v : ETm 0) : t.wk0.lst v = t := by
  rw [ETm.wk0, ETm.wkn_past t 0 (Nat.le_refl 0), ETm.lst_castLE t (Nat.le_refl 0), ETm.castLE_refl]

theorem lastCases_zero {α : Sort _} (a : α) (f : Fin 0 → α) :
    Fin.lastCases a f (0 : Fin 1) = a := Fin.lastCases_last

theorem term_lift_open {n : ℕ} (σ : Fin n → ETm 0) (t : Term (n + 1)) (x : String) :
    (term (lift σ) t).open x = term (Fin.cons (.fv x) σ) t := by
  rw [term_open]
  congr 1
  funext i
  cases i using Fin.cases <;> simp [lift, ETm.open, lastCases_zero, closed_wk0_open]

theorem term_instantiate {n : ℕ} (σ : Fin n → ETm 0) (t : Term (n + 1)) (a : Term n) :
    term σ (t.instantiate a) = (term (lift σ) t).lst (term σ a) := by
  rw [Term.instantiate, term_subst, term_lst]
  congr 1
  funext i
  cases i using Fin.cases <;>
    simp [lift, term, ETm.lst, lastCases_zero, closed_wk0_lst]



end Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.ExtensionalSyntax
