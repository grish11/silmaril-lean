module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Computation.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.ConstantStepComputation
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.WCoherenceComputation

@[expose] public section

/-! Normalized computation of the original coherence predicate at arbitrary actual W nodes. -/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

variable {H : Set Jdg} {S : Description} {levels : RuleBudget} {n : ℕ} {Γ : Ctx}

theorem coherence_sup_beta_iterated_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f) :
    let R := Tm.recChildren S.totalShape S.positions (.univ n) (S.coherenceStep n) l f
    Γ.JEqB levels H (.univ n) (S.coherence n (.sup S.totalShape S.positions l f))
      (((S.coherenceBody.lst l).lst f).lst R) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherence_sup_beta_iterated_of_hypotheses hH D hl hf

theorem coherence_sup_beta_recursive_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f) :
    let R := Tm.recChildren S.totalShape S.positions (.univ n) (S.coherenceStep n) l f
    Γ.JEqB levels H (.univ n) (S.coherence n (.sup S.totalShape S.positions l f))
      (.pi (S.positions.lst l)
        (.sigma (.id S.index.wk0 (S.root (.app f.wk0 (.bv 0))) (S.childIndexAt l.wk0 (.bv 0)))
          (.app (R.castLE (by decide)) (.bv 1)))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherence_sup_beta_recursive_of_hypotheses hH D hl hf

theorem coherence_sup_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f) :
    Γ.JEqB levels H (.univ n) (S.coherence n (.sup S.totalShape S.positions l f))
      (.pi (S.positions.lst l)
        (.sigma (.id S.index.wk0 (S.root (.app f.wk0 (.bv 0))) (S.childIndexAt l.wk0 (.bv 0)))
          (S.coherence n (.app f.wk0 (.bv 0))).wk0)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherence_sup_beta_of_hypotheses hH D hl hf

theorem root_lst {k : ℕ} (S : Description) (t : Tm (k + 1)) (a : Tm 0) :
    (S.root t).lst a = S.root (t.lst a) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.root_lst S t a

theorem coherence_lst {k : ℕ} (S : Description) (n : ℕ) (t : Tm (k + 1)) (a : Tm 0) :
    (S.coherence n t).lst a = S.coherence n (t.lst a) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherence_lst S n t a

theorem childIndexAt_lst {k : ℕ} (S : Description) (l p : Tm (k + 1)) (a : Tm 0) :
    (S.childIndexAt l p).lst a = S.childIndexAt (l.lst a) (p.lst a) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.childIndexAt_lst S l p a

theorem coherenceBody_lst (S : Description) (l f r : Tm 0) :
    ((S.coherenceBody.lst l).lst f).lst r =
      .pi (S.positions.lst l)
        (.sigma (.id S.index.wk0
          (S.root (.app f.wk0 (.bv 0)))
          (S.childIndexAt l.wk0 (.bv 0)))
          (.app (r.castLE (by decide)) (.bv 1))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherenceBody_lst S l f r

theorem coherence_sup_beta_iterated (D : IndexedFormationData S levels n Γ) {l f : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f) :
    let R := Tm.recChildren S.totalShape S.positions (.univ n) (S.coherenceStep n) l f
    Γ.JEqB levels ∅ (.univ n) (S.coherence n (.sup S.totalShape S.positions l f))
      (((S.coherenceBody.lst l).lst f).lst R) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherence_sup_beta_iterated D hl hf

theorem coherence_sup_beta_recursive (D : IndexedFormationData S levels n Γ) {l f : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f) :
    let R := Tm.recChildren S.totalShape S.positions (.univ n) (S.coherenceStep n) l f
    Γ.JEqB levels ∅ (.univ n) (S.coherence n (.sup S.totalShape S.positions l f))
      (.pi (S.positions.lst l)
        (.sigma (.id S.index.wk0 (S.root (.app f.wk0 (.bv 0))) (S.childIndexAt l.wk0 (.bv 0)))
          (.app (R.castLE (by decide)) (.bv 1)))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherence_sup_beta_recursive D hl hf

theorem coherence_sup_beta (D : IndexedFormationData S levels n Γ) {l f : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f) :
    Γ.JEqB levels ∅ (.univ n) (S.coherence n (.sup S.totalShape S.positions l f))
      (.pi (S.positions.lst l)
        (.sigma (.id S.index.wk0 (S.root (.app f.wk0 (.bv 0))) (S.childIndexAt l.wk0 (.bv 0)))
          (S.coherence n (.app f.wk0 (.bv 0))).wk0)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherence_sup_beta D hl hf

theorem normalizedLayer_open (S : Description) (n : ℕ) (l f : Tm 0) (p : String) :
    ((.sigma
      (.id S.index.wk0 (S.root (.app f.wk0 (.bv 0))) (S.childIndexAt l.wk0 (.bv 0)))
      (S.coherence n (.app f.wk0 (.bv 0))).wk0 : Tm 1).open p) =
    .sigma (.id S.index (S.root (.app f (.fv p))) (S.childIndexAt l (.fv p)))
      (S.coherence n (.app f (.fv p))).wk0 :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.normalizedLayer_open S n l f p

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
