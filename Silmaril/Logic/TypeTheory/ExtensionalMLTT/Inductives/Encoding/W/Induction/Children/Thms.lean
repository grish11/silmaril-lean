module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Induction.Children.Defs
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.WInductionChildren

@[expose] public section

/-! Full original child values and dependent IHs reconstructed from ordinary W data. -/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

variable {H : Set Jdg} {S : Description} {levels : RuleBudget} {n : ℕ} {Γ : Ctx}


theorem positions_instance_formation_of_hypotheses (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) {l : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l) :
    Γ.JEqB levels H (.univ n) (S.positions.lst l) (S.positions.lst l) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.positions_instance_formation_of_hypotheses hH D hl

theorem coherentChild_witness_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f c p : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hp : Γ.JEqB levels H (S.positions.lst l) p p) :
    Γ.JEqB levels H
      (.sigma (.id S.index (S.root (.app f p)) (S.childIndexAt l p)) (S.coherence n (.app f p)).wk0)
      (.app c p) (.app c p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherentChild_witness_typing_of_hypotheses hH D hl hf hc hp

theorem coherentChild_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f c p : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hp : Γ.JEqB levels H (S.positions.lst l) p p) :
    Γ.JEqB levels H (S.fibre n (S.childIndexAt l p))
      (.pair (.app f p) (.app c p)) (.pair (.app f p) (.app c p)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherentChild_typing_of_hypotheses hH D hl hf hc hp

theorem reifyChildren_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f c : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    Γ.JEqB levels H (.pi (S.positions.lst l) (S.childFibres n l))
      (S.reifyChildren l f c) (S.reifyChildren l f c) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.reifyChildren_typing_of_hypotheses hH D hl hf hc

theorem reifyChildren_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f c p : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hp : Γ.JEqB levels H (S.positions.lst l) p p) :
    Γ.JEqB levels H (S.fibre n (S.childIndexAt l p))
      (.app (S.reifyChildren l f c) p) (.pair (.app f p) (.app c p)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.reifyChildren_beta_of_hypotheses hH D hl hf hc hp

theorem coherentHypothesis_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {m : ℕ}
    (hm : RuleBudget.Allows levels (m + 1)) {C l f c r p : Tm 0}
    (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hr : Γ.JEqB levels H (.pi (S.positions.lst l)
      ((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0)))) r r)
    (hp : Γ.JEqB levels H (S.positions.lst l) p p) :
    Γ.JEqB levels H
      (.app (.app C (S.childIndexAt l p)) (.pair (.app f p) (.app c p)))
      (.app (.app r p) (.snd (.app c p)))
      (.app (.app r p) (.snd (.app c p))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherentHypothesis_typing_of_hypotheses hH D hm hC hl hf hc hr hp

theorem reifyHypotheses_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {m : ℕ}
    (hm : RuleBudget.Allows levels (m + 1)) {C l f c r : Tm 0}
    (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hr : Γ.JEqB levels H (.pi (S.positions.lst l)
      ((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0)))) r r) :
    Γ.JEqB levels H (.pi (S.positions.lst l)
      (.app (.app C.wk0 (S.childIndexAt l.wk0 (.bv 0))) (.app (S.reifyChildren l f c).wk0 (.bv 0))))
      (S.reifyHypotheses l c r) (S.reifyHypotheses l c r) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.reifyHypotheses_typing_of_hypotheses hH D hm hC hl hf hc hr

theorem reifyHypotheses_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {m : ℕ}
    (hm : RuleBudget.Allows levels (m + 1)) {C l f c r p : Tm 0}
    (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hr : Γ.JEqB levels H (.pi (S.positions.lst l)
      ((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0)))) r r)
    (hp : Γ.JEqB levels H (S.positions.lst l) p p) :
    Γ.JEqB levels H (.app (.app C (S.childIndexAt l p)) (.app (S.reifyChildren l f c) p))
      (.app (S.reifyHypotheses l c r) p) (.app (.app r p) (.snd (.app c p))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.reifyHypotheses_beta_of_hypotheses hH D hm hC hl hf hc hr hp

theorem coherenceWitness_formation_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f) :
    ∀ p ∉ Γ.dv, (Γ.cons p (S.positions.lst l)).JEqB levels H (.univ n)
      ((.sigma (.id S.index.wk0 (S.root (.app f.wk0 (.bv 0))) (S.childIndexAt l.wk0 (.bv 0)))
        (S.coherence n (.app f.wk0 (.bv 0))).wk0 : Tm 1).open p) ((.sigma (.id S.index.wk0 (S.root (.app f.wk0 (.bv 0))) (S.childIndexAt l.wk0 (.bv 0)))
        (S.coherence n (.app f.wk0 (.bv 0))).wk0 : Tm 1).open p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherenceWitness_formation_of_hypotheses hH D hl hf

theorem positions_instance_formation (D : FormationData S levels n Γ) {l : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l) :
    Γ.JEqB levels ∅ (.univ n) (S.positions.lst l) (S.positions.lst l) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.positions_instance_formation D hl

theorem coherentChild_witness_typing (D : IndexedFormationData S levels n Γ) {l f c p : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hp : Γ.JEqB levels ∅ (S.positions.lst l) p p) :
    Γ.JEqB levels ∅
      (.sigma (.id S.index (S.root (.app f p)) (S.childIndexAt l p)) (S.coherence n (.app f p)).wk0)
      (.app c p) (.app c p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherentChild_witness_typing D hl hf hc hp

theorem coherentChild_typing (D : IndexedFormationData S levels n Γ) {l f c p : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hp : Γ.JEqB levels ∅ (S.positions.lst l) p p) :
    Γ.JEqB levels ∅ (S.fibre n (S.childIndexAt l p))
      (.pair (.app f p) (.app c p)) (.pair (.app f p) (.app c p)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherentChild_typing D hl hf hc hp

theorem reifyChildren_typing (D : IndexedFormationData S levels n Γ) {l f c : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    Γ.JEqB levels ∅ (.pi (S.positions.lst l) (S.childFibres n l))
      (S.reifyChildren l f c) (S.reifyChildren l f c) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.reifyChildren_typing D hl hf hc

theorem reifyChildren_beta (D : IndexedFormationData S levels n Γ) {l f c p : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hp : Γ.JEqB levels ∅ (S.positions.lst l) p p) :
    Γ.JEqB levels ∅ (S.fibre n (S.childIndexAt l p))
      (.app (S.reifyChildren l f c) p) (.pair (.app f p) (.app c p)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.reifyChildren_beta D hl hf hc hp

theorem coherentHypothesis_typing (D : IndexedFormationData S levels n Γ) {m : ℕ}
    (hm : RuleBudget.Allows levels (m + 1)) {C l f c r p : Tm 0}
    (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hr : Γ.JEqB levels ∅ (.pi (S.positions.lst l)
      ((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0)))) r r)
    (hp : Γ.JEqB levels ∅ (S.positions.lst l) p p) :
    Γ.JEqB levels ∅
      (.app (.app C (S.childIndexAt l p)) (.pair (.app f p) (.app c p)))
      (.app (.app r p) (.snd (.app c p)))
      (.app (.app r p) (.snd (.app c p))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherentHypothesis_typing D hm hC hl hf hc hr hp

theorem reifyHypotheses_typing (D : IndexedFormationData S levels n Γ) {m : ℕ}
    (hm : RuleBudget.Allows levels (m + 1)) {C l f c r : Tm 0}
    (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hr : Γ.JEqB levels ∅ (.pi (S.positions.lst l)
      ((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0)))) r r) :
    Γ.JEqB levels ∅ (.pi (S.positions.lst l)
      (.app (.app C.wk0 (S.childIndexAt l.wk0 (.bv 0))) (.app (S.reifyChildren l f c).wk0 (.bv 0))))
      (S.reifyHypotheses l c r) (S.reifyHypotheses l c r) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.reifyHypotheses_typing D hm hC hl hf hc hr

theorem reifyHypotheses_beta (D : IndexedFormationData S levels n Γ) {m : ℕ}
    (hm : RuleBudget.Allows levels (m + 1)) {C l f c r p : Tm 0}
    (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hr : Γ.JEqB levels ∅ (.pi (S.positions.lst l)
      ((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0)))) r r)
    (hp : Γ.JEqB levels ∅ (S.positions.lst l) p p) :
    Γ.JEqB levels ∅ (.app (.app C (S.childIndexAt l p)) (.app (S.reifyChildren l f c) p))
      (.app (S.reifyHypotheses l c r) p) (.app (.app r p) (.snd (.app c p))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.reifyHypotheses_beta D hm hC hl hf hc hr hp

theorem coherenceWitness_formation (D : IndexedFormationData S levels n Γ) {l f : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f) :
    ∀ p ∉ Γ.dv, (Γ.cons p (S.positions.lst l)).JEqB levels ∅ (.univ n)
      ((.sigma (.id S.index.wk0 (S.root (.app f.wk0 (.bv 0))) (S.childIndexAt l.wk0 (.bv 0)))
        (S.coherence n (.app f.wk0 (.bv 0))).wk0 : Tm 1).open p) ((.sigma (.id S.index.wk0 (S.root (.app f.wk0 (.bv 0))) (S.childIndexAt l.wk0 (.bv 0)))
        (S.coherence n (.app f.wk0 (.bv 0))).wk0 : Tm 1).open p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherenceWitness_formation D hl hf

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
