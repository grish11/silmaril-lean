module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.NamedSubstitution.Defs
import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.NamedSubstitution

public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

@[simp] theorem ETm.castLE_refl {k : ℕ} (t : ETm k) : t.castLE (Nat.le_refl k) = t :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.NamedSubstitution.castLE_refl t

theorem ETm.castLE_comp {n m k : ℕ} (t : ETm n) (h : n ≤ m) (h' : m ≤ k) :
    (t.castLE h).castLE h' = t.castLE (h.trans h') :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.NamedSubstitution.castLE_comp t h h'

@[simp] theorem ETm.closed_castLE_wkn {k : ℕ} (t : ETm 0) (j : ℕ) :
    (t.castLE (Nat.zero_le k)).wkn j = t.castLE (Nat.zero_le (k + 1)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.NamedSubstitution.closed_castLE_wkn t j

theorem ETm.open_castLE {n m : ℕ} (t : ETm n) (h : n ≤ m) (x : String) :
    (t.castLE (Nat.le_succ_of_le h)).open x = t.castLE h :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.NamedSubstitution.open_castLE t h x

/-- Opening the outermost index commutes with weakening at any earlier position. -/
theorem ETm.open_wkn {k : ℕ} (t : ETm (k + 1)) (x : String) (j : ℕ) (hj : j ≤ k) :
    (t.wkn j).open x = (t.open x).wkn j :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.NamedSubstitution.open_wkn t x j hj

theorem ETm.lst_castLE {n m : ℕ} (t : ETm n) (h : n ≤ m) (v : ETm 0) :
    (t.castLE (Nat.le_succ_of_le h)).lst v = t.castLE h :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.NamedSubstitution.lst_castLE t h v

/-- Weakening past every bound index only changes the ambient scope. -/
theorem ETm.wkn_past {k : ℕ} (t : ETm k) (j : ℕ) (hkj : k ≤ j) :
    t.wkn j = t.castLE (Nat.le_succ k) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.NamedSubstitution.wkn_past t j hkj

variable (x : String) (v : ETm 0)

@[simp] theorem ETm.fsubst_castLE {n m : ℕ} (t : ETm n) (h : n ≤ m) :
    (t.castLE h).fsubst x v = (t.fsubst x v).castLE h :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.NamedSubstitution.fsubst_castLE x v t h

@[simp] theorem ETm.fsubst_wkn {k : ℕ} (t : ETm k) (j : ℕ) :
    (t.wkn j).fsubst x v = (t.fsubst x v).wkn j :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.NamedSubstitution.fsubst_wkn x v t j

@[simp] theorem ETm.fsubst_open {k : ℕ} (t : ETm (k + 1)) {y : String} (hy : y ≠ x) :
    (t.open y).fsubst x v = (t.fsubst x v).open y :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.NamedSubstitution.fsubst_open x v t hy

@[simp] theorem ETm.fsubst_lst {k : ℕ} (t : ETm (k + 1)) (a : ETm 0) :
    (t.lst a).fsubst x v = (t.fsubst x v).lst (a.fsubst x v) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.NamedSubstitution.fsubst_lst x v t a

@[simp] theorem ETm.fsubst_arr {k : ℕ} (A B : ETm k) :
    (ETm.arr A B).fsubst x v = .arr (A.fsubst x v) (B.fsubst x v) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.NamedSubstitution.fsubst_arr x v A B

theorem ETm.fsubst_fresh {k : ℕ} (t : ETm k) (hx : x ∉ t.fvs) : t.fsubst x v = t :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.NamedSubstitution.fsubst_fresh x v t hx

theorem ETm.fsubst_open_self {k : ℕ} (t : ETm (k + 1)) (hx : x ∉ t.fvs) :
    (t.open x).fsubst x v = t.lst v :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.NamedSubstitution.fsubst_open_self x v t hx

theorem ECtx.Lookup.typeFvs {Γ : ECtx} {y : String} {A : ETm 0} (h : Γ.Lookup y A) :
    A.fvs ⊆ Γ.typeFvs :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.NamedSubstitution.lookup_typeFvs h

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
