module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Thms
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.SubstitutionAlgebra

@[expose] public section

/-!
# Capture-avoiding substitution algebra for all W object terms

These are syntactic equalities, including the existing outermost-binder `open`
and `lst` operations. They do not yet assert substitution of derivations or
of free named variables. Bound variables inserted by substitutions are lifted
under each Π/Σ/W binder.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Tm

theorem wkn_wkn {k : ℕ} (t : Tm k) (i j : ℕ) (hij : i ≤ j) :
    (t.wkn i).wkn (j + 1) = (t.wkn j).wkn i :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.wkn_wkn t i j hij

theorem bsubst_wkn {n m : ℕ} (t : Tm n) (σ : Fin (n + 1) → Tm m) (j : ℕ) :
    (t.wkn j).bsubst σ =
      t.bsubst (fun i => σ (if (i : ℕ) < j then i.castSucc else i.succ)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.bsubst_wkn t σ j

theorem wkn_bsubst {n m : ℕ} (t : Tm n) (σ : Fin n → Tm m) (j : ℕ) :
    (t.bsubst σ).wkn j = t.bsubst (fun i => (σ i).wkn j) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.wkn_bsubst t σ j

theorem bsubst_comp {n m k : ℕ} (t : Tm n) (σ : Fin n → Tm m) (τ : Fin m → Tm k) :
    (t.bsubst σ).bsubst τ = t.bsubst (fun i => (σ i).bsubst τ) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.bsubst_comp t σ τ

@[simp] theorem castLE_refl {k : ℕ} (t : Tm k) : t.castLE (Nat.le_refl k) = t :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.castLE_refl t

theorem castLE_comp {n m k : ℕ} (t : Tm n) (h : n ≤ m) (h' : m ≤ k) :
    (t.castLE h).castLE h' = t.castLE (h.trans h') :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.castLE_comp t h h'

theorem wkn_past {k : ℕ} (t : Tm k) (j : ℕ) (hkj : k ≤ j) :
    t.wkn j = t.castLE (Nat.le_succ k) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.wkn_past t j hkj

theorem wkn_castLE {n m : ℕ} (t : Tm n) (h : n ≤ m) (j : ℕ) :
    (t.castLE h).wkn j = (t.wkn j).castLE (Nat.succ_le_succ h) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.wkn_castLE t h j

theorem bsubst_castLE {n m k : ℕ} (t : Tm n) (h : n ≤ m) (σ : Fin m → Tm k) :
    (t.castLE h).bsubst σ = t.bsubst (fun i => σ (i.castLE h)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.bsubst_castLE t h σ

theorem castLE_eq_bsubst {n m : ℕ} (t : Tm n) (h : n ≤ m) :
    t.castLE h = t.bsubst (fun i => .bv (i.castLE h)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.castLE_eq_bsubst t h

theorem closed_bsubst {m : ℕ} (t : Tm 0) (σ : Fin 0 → Tm m) :
    t.bsubst σ = t.castLE (Nat.zero_le m) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.closed_bsubst t σ

@[simp] theorem bsubst_closed_castLE {n m : ℕ} (t : Tm 0) (σ : Fin n → Tm m) :
    (t.castLE (Nat.zero_le n)).bsubst σ = t.castLE (Nat.zero_le m) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.bsubst_closed_castLE t σ

@[simp] theorem closed_wk0_open (t : Tm 0) (x : String) : t.wk0.open x = t :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.closed_wk0_open t x

theorem open_eq_bsubst {k : ℕ} (t : Tm (k + 1)) (x : String) :
    t.open x = t.bsubst (Fin.lastCases (.fv x) .bv) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.open_eq_bsubst t x

theorem lst_eq_bsubst {k : ℕ} (t : Tm (k + 1)) (v : Tm 0) :
    t.lst v = t.bsubst (Fin.lastCases (v.castLE (Nat.zero_le k)) .bv) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.lst_eq_bsubst t v

theorem open_bsubst {n m : ℕ} (t : Tm n) (σ : Fin n → Tm (m + 1)) (x : String) :
    (t.bsubst σ).open x = t.bsubst (fun i => (σ i).open x) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.open_bsubst t σ x

theorem bsubst_open {n m : ℕ} (t : Tm (n + 1)) (σ : Fin n → Tm m) (x : String) :
    (t.open x).bsubst σ = t.bsubst (Fin.lastCases (.fv x) σ) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.bsubst_open t σ x

theorem lst_bsubst {n m : ℕ} (t : Tm n) (σ : Fin n → Tm (m + 1)) (v : Tm 0) :
    (t.bsubst σ).lst v = t.bsubst (fun i => (σ i).lst v) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.lst_bsubst t σ v

theorem bsubst_lst {n m : ℕ} (t : Tm (n + 1)) (σ : Fin n → Tm m) (v : Tm 0) :
    (t.lst v).bsubst σ = t.bsubst (Fin.lastCases (v.castLE (Nat.zero_le m)) σ) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.bsubst_lst t σ v

theorem wkn_eq_bsubst {k : ℕ} (t : Tm k) (j : ℕ) :
    t.wkn j = t.bsubst (fun i => .bv (if (i : ℕ) < j then i.castSucc else i.succ)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.wkn_eq_bsubst t j

@[simp] theorem closed_wk0_lst (t v : Tm 0) : t.wk0.lst v = t :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.closed_wk0_lst t v

theorem open_wkn {k : ℕ} (t : Tm (k + 1)) (x : String) (j : ℕ) (hj : j ≤ k) :
    (t.wkn j).open x = (t.open x).wkn j :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.open_wkn t x j hj

@[simp] theorem closed_castLE_wkn {k : ℕ} (t : Tm 0) (j : ℕ) :
    (t.castLE (Nat.zero_le k)).wkn j = t.castLE (Nat.zero_le (k + 1)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.closed_castLE_wkn t j

@[simp] theorem closed_castLE_open {k : ℕ} (t : Tm 0) (x : String) :
    (t.castLE (Nat.zero_le (k + 1))).open x = t.castLE (Nat.zero_le k) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.closed_castLE_open t x

theorem lst_wkn {k : ℕ} (t : Tm (k + 1)) (a : Tm 0) (j : ℕ) (hj : j ≤ k) :
    (t.wkn j).lst a = (t.lst a).wkn j :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.lst_wkn t a j hj

theorem closed_castLE_lst {k : ℕ} (t a : Tm 0) :
    (t.castLE (Nat.zero_le (k + 1))).lst a = t.castLE (Nat.zero_le k) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.closed_castLE_lst t a

theorem arrow_lst {k : ℕ} (A B : Tm (k + 1)) (a : Tm 0) :
    (Tm.arr A B).lst a = Tm.arr (A.lst a) (B.lst a) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.arrow_lst A B a

theorem lst_castLE {n m : ℕ} (t : Tm n) (h : n ≤ m) (a : Tm 0) :
    (t.castLE (Nat.le_succ_of_le h)).lst a = t.castLE h :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.lst_castLE t h a

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Tm
