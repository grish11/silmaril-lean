module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.SimultaneousSubstitution.Defs
import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.SimultaneousSubstitution

public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

variable (σ : String → ETm 0)

@[simp] theorem ETm.fmap_castLE {n m : ℕ} (t : ETm n) (h : n ≤ m) :
    (t.castLE h).fmap σ = (t.fmap σ).castLE h :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.SimultaneousSubstitution.fmap_castLE σ t h

@[simp] theorem ETm.fmap_wkn {k : ℕ} (t : ETm k) (j : ℕ) :
    (t.wkn j).fmap σ = (t.fmap σ).wkn j :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.SimultaneousSubstitution.fmap_wkn σ t j

@[simp] theorem ETm.fmap_open {k : ℕ} (t : ETm (k + 1)) {y : String} (hy : σ y = .fv y) :
    (t.open y).fmap σ = (t.fmap σ).open y :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.SimultaneousSubstitution.fmap_open σ t hy

@[simp] theorem ETm.fmap_lst {k : ℕ} (t : ETm (k + 1)) (a : ETm 0) :
    (t.lst a).fmap σ = (t.fmap σ).lst (a.fmap σ) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.SimultaneousSubstitution.fmap_lst σ t a

@[simp] theorem ETm.fmap_arr {k : ℕ} (A B : ETm k) :
    (ETm.arr A B).fmap σ = .arr (A.fmap σ) (B.fmap σ) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.SimultaneousSubstitution.fmap_arr σ A B

theorem ETm.fmap_congr {k : ℕ} (t : ETm k) {τ : String → ETm 0}
    (h : ∀ x ∈ t.fvs, σ x = τ x) : t.fmap σ = t.fmap τ :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.SimultaneousSubstitution.fmap_congr σ t h

@[simp] theorem ETm.fmap_id {k : ℕ} (t : ETm k) : t.fmap ETm.fv = t :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.SimultaneousSubstitution.fmap_id t

theorem ETm.fmap_update_fresh {k : ℕ} (t : ETm k) (x : String) (v : ETm 0)
    (hx : x ∉ t.fvs) : t.fmap (Function.update σ x v) = t.fmap σ :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.SimultaneousSubstitution.fmap_update_fresh σ t x v hx

theorem ETm.fmap_update_open {k : ℕ} (t : ETm (k + 1)) (x : String) (v : ETm 0)
    (hx : x ∉ t.fvs) :
    (t.open x).fmap (Function.update σ x v) = (t.fmap σ).lst v :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.SimultaneousSubstitution.fmap_update_open σ t x v hx

theorem ETm.Supported.update {K : Finset String} (hσ : ETm.Supported σ K) (x : String) (v : ETm 0) :
    ETm.Supported (Function.update σ x v) (insert x K) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.SimultaneousSubstitution.supported_update σ hσ x v

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
