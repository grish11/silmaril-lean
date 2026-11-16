module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.NamedSubstitution.Defs
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.NamedSubstitution

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

theorem HypothesisSubstitution.empty (levels : RuleBudget) (H : Set Jdg) (x : String) (v : Tm 0) :
    HypothesisSubstitution levels ∅ H x v := fun hj _ _ => False.elim hj

theorem StructuralTheory.empty (levels : RuleBudget) : StructuralTheory levels ∅ :=
  ⟨HypothesisTransport.empty levels ∅, HypothesisSubstitution.empty levels ∅⟩

variable (x : String) (v : Tm 0)

@[simp] theorem Tm.fsubst_castLE {n m : ℕ} (t : Tm n) (h : n ≤ m) :
    (t.castLE h).fsubst x v = (t.fsubst x v).castLE h :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.fsubst_castLE x v t h

@[simp] theorem Tm.fsubst_wkn {k : ℕ} (t : Tm k) (j : ℕ) :
    (t.wkn j).fsubst x v = (t.fsubst x v).wkn j :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.fsubst_wkn x v t j

@[simp] theorem Tm.fsubst_bsubst {n m : ℕ} (t : Tm n) (σ : Fin n → Tm m) :
    (t.bsubst σ).fsubst x v = (t.fsubst x v).bsubst (fun i => (σ i).fsubst x v) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.fsubst_bsubst x v t σ

@[simp] theorem Tm.fsubst_open {k : ℕ} (t : Tm (k + 1)) {y : String} (hy : y ≠ x) :
    (t.open y).fsubst x v = (t.fsubst x v).open y :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.fsubst_open x v t hy

@[simp] theorem Tm.fsubst_lst {k : ℕ} (t : Tm (k + 1)) (a : Tm 0) :
    (t.lst a).fsubst x v = (t.fsubst x v).lst (a.fsubst x v) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.fsubst_lst x v t a

@[simp] theorem Tm.fsubst_arr {k : ℕ} (A B : Tm k) :
    (Tm.arr A B).fsubst x v = .arr (A.fsubst x v) (B.fsubst x v) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.fsubst_arr x v A B

@[simp] theorem Tm.fsubst_wStepType (A : Tm 0) (B C : Tm 1) :
    (Tm.wStepType A B C).fsubst x v =
      Tm.wStepType (A.fsubst x v) (B.fsubst x v) (C.fsubst x v) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.fsubst_wStepType x v A B C

@[simp] theorem Tm.fsubst_recChildren (A s a f : Tm 0) (B C : Tm 1) :
    (Tm.recChildren A B C s a f).fsubst x v =
      Tm.recChildren (A.fsubst x v) (B.fsubst x v) (C.fsubst x v)
        (s.fsubst x v) (a.fsubst x v) (f.fsubst x v) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.fsubst_recChildren x v A s a f B C

theorem Tm.fsubst_fresh {k : ℕ} (t : Tm k) (hx : x ∉ t.fvs) : t.fsubst x v = t :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.fsubst_fresh x v t hx

theorem Tm.fsubst_open_self {k : ℕ} (t : Tm (k + 1)) (hx : x ∉ t.fvs) :
    (t.open x).fsubst x v = t.lst v :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.fsubst_open_self x v t hx

theorem Ctx.Lookup.typeFvs {Γ : Ctx} {y : String} {A : Tm 0} (h : Γ.Lookup y A) :
    A.fvs ⊆ Γ.typeFvs :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.lookup_typeFvs h

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
