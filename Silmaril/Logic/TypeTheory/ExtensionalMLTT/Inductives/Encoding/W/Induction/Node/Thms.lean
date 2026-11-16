module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Induction.Children.Thms
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.WInductionNode

@[expose] public section

/-! The exact original indexed node reconstructs the original raw node and coherence. -/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

variable {H : Set Jdg} {S : Description} {levels : RuleBudget} {n : ℕ} {Γ : Ctx}


theorem canonical_congr_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {t u c d : Tm 0}
    (htu : Γ.JEqB levels H S.raw t u) (hcd : Γ.JEqB levels H (S.coherence n t) c d) :
    Γ.JEqB levels H (S.fibre n (S.root t)) (S.canonical t c) (S.canonical u d) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.canonical_congr_of_hypotheses hH D htu hcd

theorem reifiedNode_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f c : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    Γ.JEqB levels H (S.fibre n (.fst l))
      (S.node (.fst l) (.snd l) (S.reifyChildren l f c))
      (S.node (.fst l) (.snd l) (S.reifyChildren l f c)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.reifiedNode_typing_of_hypotheses hH D hl hf hc

theorem reifyChildren_fst_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f c p : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hp : Γ.JEqB levels H (S.positions.lst l) p p) :
    Γ.JEqB levels H S.raw (.fst (.app (S.reifyChildren l f c) p)) (.app f p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.reifyChildren_fst_beta_of_hypotheses hH D hl hf hc hp

theorem eraseReifiedChildren_eq_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f c : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    Γ.JEqB levels H (.arr (S.positions.lst l) S.raw)
      (.abs (S.positions.lst l) (.fst (.app (S.reifyChildren l f c).wk0 (.bv 0)))) f :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.eraseReifiedChildren_eq_of_hypotheses hH D hl hf hc

theorem reifiedNode_raw_eq_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f c : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    Γ.JEqB levels H S.raw
      (.sup S.totalShape S.positions (.pair (.fst l) (.snd l))
        (.abs (S.positionAt (.fst l) (.snd l)) (.fst (.app (S.reifyChildren l f c).wk0 (.bv 0)))))
      (.sup S.totalShape S.positions l f) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.reifiedNode_raw_eq_of_hypotheses hH D hl hf hc

theorem fibreTail_congr_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i t u : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (htu : Γ.JEqB levels H S.raw t u) :
    Γ.JEqB levels H (.univ n)
      (.sigma (.id S.index (S.root t) i) (S.coherence n t).wk0)
      (.sigma (.id S.index (S.root u) i) (S.coherence n u).wk0) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.fibreTail_congr_of_hypotheses hH D hi htu

theorem reifyChildren_snd_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f c p : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hp : Γ.JEqB levels H (S.positions.lst l) p p) :
    Γ.JEqB levels H
      (.sigma (.id S.index (S.root (.app f p)) (S.childIndexAt l p)) (S.coherence n (.app f p)).wk0)
      (.snd (.app (S.reifyChildren l f c) p)) (.app c p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.reifyChildren_snd_beta_of_hypotheses hH D hl hf hc hp

theorem witnessReifiedChildren_eq_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f c : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f))
      (.abs (S.positionAt (.fst l) (.snd l)) (.snd (.app (S.reifyChildren l f c).wk0 (.bv 0)))) c :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.witnessReifiedChildren_eq_of_hypotheses hH D hl hf hc

theorem reifiedNode_eq_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f c : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    Γ.JEqB levels H (S.fibre n (.fst l))
      (S.node (.fst l) (.snd l) (S.reifyChildren l f c))
      (S.canonical (.sup S.totalShape S.positions l f) c) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.reifiedNode_eq_of_hypotheses hH D hl hf hc

theorem motive_reifiedNode_eq_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {m : ℕ}
    (hm : RuleBudget.Allows levels (m + 1)) {C l f c : Tm 0}
    (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    Γ.JEqB levels H (.univ m)
      (.app (.app C (.fst l)) (S.node (.fst l) (.snd l) (S.reifyChildren l f c)))
      (.app (.app C (S.root (.sup S.totalShape S.positions l f)))
        (S.canonical (.sup S.totalShape S.positions l f) c)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.motive_reifiedNode_eq_of_hypotheses hH D hm hC hl hf hc

theorem next_retaining_position (N : Tm 3) (i a : Tm 0) :
    (N.lst i).lst a = N.bsubst (Fin.cases (.bv 0) (Fin.cases a.wk0 (fun _ => i.wk0))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.next_retaining_position N i a

theorem canonical_congr (D : IndexedFormationData S levels n Γ) {t u c d : Tm 0}
    (htu : Γ.JEqB levels ∅ S.raw t u) (hcd : Γ.JEqB levels ∅ (S.coherence n t) c d) :
    Γ.JEqB levels ∅ (S.fibre n (S.root t)) (S.canonical t c) (S.canonical u d) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.canonical_congr D htu hcd

theorem childFibres_as_source (S : Description) (n : ℕ) (l : Tm 0) :
    S.childFibres n l = S.fibreAt n ((S.next.lst (.fst l)).lst (.snd l)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.childFibres_as_source S n l

theorem reifiedNode_typing (D : IndexedFormationData S levels n Γ) {l f c : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    Γ.JEqB levels ∅ (S.fibre n (.fst l))
      (S.node (.fst l) (.snd l) (S.reifyChildren l f c))
      (S.node (.fst l) (.snd l) (S.reifyChildren l f c)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.reifiedNode_typing D hl hf hc

theorem reifyChildren_fst_beta (D : IndexedFormationData S levels n Γ) {l f c p : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hp : Γ.JEqB levels ∅ (S.positions.lst l) p p) :
    Γ.JEqB levels ∅ S.raw (.fst (.app (S.reifyChildren l f c) p)) (.app f p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.reifyChildren_fst_beta D hl hf hc hp

theorem eraseReifiedChildren_eq (D : IndexedFormationData S levels n Γ) {l f c : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw)
      (.abs (S.positions.lst l) (.fst (.app (S.reifyChildren l f c).wk0 (.bv 0)))) f :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.eraseReifiedChildren_eq D hl hf hc

theorem reifiedNode_raw_eq (D : IndexedFormationData S levels n Γ) {l f c : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    Γ.JEqB levels ∅ S.raw
      (.sup S.totalShape S.positions (.pair (.fst l) (.snd l))
        (.abs (S.positionAt (.fst l) (.snd l)) (.fst (.app (S.reifyChildren l f c).wk0 (.bv 0)))))
      (.sup S.totalShape S.positions l f) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.reifiedNode_raw_eq D hl hf hc

theorem fibreTail_congr (D : IndexedFormationData S levels n Γ) {i t u : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (htu : Γ.JEqB levels ∅ S.raw t u) :
    Γ.JEqB levels ∅ (.univ n)
      (.sigma (.id S.index (S.root t) i) (S.coherence n t).wk0)
      (.sigma (.id S.index (S.root u) i) (S.coherence n u).wk0) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.fibreTail_congr D hi htu

theorem reifyChildren_snd_beta (D : IndexedFormationData S levels n Γ) {l f c p : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hp : Γ.JEqB levels ∅ (S.positions.lst l) p p) :
    Γ.JEqB levels ∅
      (.sigma (.id S.index (S.root (.app f p)) (S.childIndexAt l p)) (S.coherence n (.app f p)).wk0)
      (.snd (.app (S.reifyChildren l f c) p)) (.app c p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.reifyChildren_snd_beta D hl hf hc hp

theorem witnessReifiedChildren_eq (D : IndexedFormationData S levels n Γ) {l f c : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f))
      (.abs (S.positionAt (.fst l) (.snd l)) (.snd (.app (S.reifyChildren l f c).wk0 (.bv 0)))) c :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.witnessReifiedChildren_eq D hl hf hc

theorem reifiedNode_eq (D : IndexedFormationData S levels n Γ) {l f c : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    Γ.JEqB levels ∅ (S.fibre n (.fst l))
      (S.node (.fst l) (.snd l) (S.reifyChildren l f c))
      (S.canonical (.sup S.totalShape S.positions l f) c) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.reifiedNode_eq D hl hf hc

theorem motive_reifiedNode_eq (D : IndexedFormationData S levels n Γ) {m : ℕ}
    (hm : RuleBudget.Allows levels (m + 1)) {C l f c : Tm 0}
    (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    Γ.JEqB levels ∅ (.univ m)
      (.app (.app C (.fst l)) (S.node (.fst l) (.snd l) (S.reifyChildren l f c)))
      (.app (.app C (S.root (.sup S.totalShape S.positions l f)))
        (S.canonical (.sup S.totalShape S.positions l f) c)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.motive_reifiedNode_eq D hm hC hl hf hc

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
