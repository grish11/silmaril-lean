module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Fibres
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.WNodeTyping

@[expose] public section

/-! Actual derivability of the original indexed-W constructor from its child fibres. -/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

variable {H : Set Jdg} {S : Description} {levels : RuleBudget} {n : ℕ} {Γ : Ctx}

theorem root_congr_of_hypotheses (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) {t u : Tm 0}
    (ht : Γ.JEqB levels H S.raw t u) :
    Γ.JEqB levels H S.index (S.root t) (S.root u) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.root_congr_of_hypotheses hH D ht

theorem coherence_congr_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {t u : Tm 0}
    (ht : Γ.JEqB levels H S.raw t u) :
    Γ.JEqB levels H (.univ n) (S.coherence n t) (S.coherence n u) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherence_congr_of_hypotheses hH D ht

theorem fibreTail_formation_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) :
    ∀ x ∉ Γ.dv, (Γ.cons x S.raw).JEqB levels H (.univ n)
      ((.sigma (.id S.index.wk0 (S.root (.bv 0)) i.wk0)
        (S.coherence n (.bv 1)) : Tm 1).open x)
      ((.sigma (.id S.index.wk0 (S.root (.bv 0)) i.wk0)
        (S.coherence n (.bv 1)) : Tm 1).open x) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.fibreTail_formation_of_hypotheses hH D hi

theorem childFibres_formation_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l A : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l) (hA : Γ.JEqB levels H (.univ n) A A)
    (hP : Γ.JEqB levels H (.univ n) A (S.positions.lst l)) :
    ∀ p ∉ Γ.dv, (Γ.cons p A).JEqB levels H (.univ n)
      ((S.childFibres n l).open p) ((S.childFibres n l).open p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.childFibres_formation_of_hypotheses hH D hl hA hP

theorem childValue_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l A f p : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l) (hA : Γ.JEqB levels H (.univ n) A A)
    (hP : Γ.JEqB levels H (.univ n) A (S.positions.lst l))
    (hf : Γ.JEqB levels H (.pi A (S.childFibres n l)) f f)
    (hp : Γ.JEqB levels H A p p) :
    Γ.JEqB levels H (S.fibre n (S.childIndexAt l p)) (.app f p) (.app f p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.childValue_typing_of_hypotheses hH D hl hA hP hf hp

theorem fibre_fst_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i t : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ht : Γ.JEqB levels H (S.fibre n i) t t) :
    Γ.JEqB levels H S.raw (.fst t) (.fst t) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.fibre_fst_typing_of_hypotheses hH D hi ht

theorem fibre_snd_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i t : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ht : Γ.JEqB levels H (S.fibre n i) t t) :
    Γ.JEqB levels H
      (.sigma (.id S.index (S.root (.fst t)) i) (S.coherence n (.fst t)).wk0)
      (.snd t) (.snd t) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.fibre_snd_typing_of_hypotheses hH D hi ht

theorem eraseChildren_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l A f : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l) (hA : Γ.JEqB levels H (.univ n) A A)
    (hP : Γ.JEqB levels H (.univ n) A (S.positions.lst l))
    (hf : Γ.JEqB levels H (.pi A (S.childFibres n l)) f f) :
    Γ.JEqB levels H (.arr A S.raw)
      (.abs A (.fst (.app f.wk0 (.bv 0)))) (.abs A (.fst (.app f.wk0 (.bv 0)))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.eraseChildren_typing_of_hypotheses hH D hl hA hP hf

theorem eraseChildren_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l A f p : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l) (hA : Γ.JEqB levels H (.univ n) A A)
    (hP : Γ.JEqB levels H (.univ n) A (S.positions.lst l))
    (hf : Γ.JEqB levels H (.pi A (S.childFibres n l)) f f)
    (hp : Γ.JEqB levels H A p p) :
    Γ.JEqB levels H S.raw
      (.app (.abs A (.fst (.app f.wk0 (.bv 0)))) p) (.fst (.app f p)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.eraseChildren_beta_of_hypotheses hH D hl hA hP hf hp

theorem witnessChildren_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l A f : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l) (hA : Γ.JEqB levels H (.univ n) A A)
    (hP : Γ.JEqB levels H (.univ n) A (S.positions.lst l))
    (hf : Γ.JEqB levels H (.pi A (S.childFibres n l)) f f) :
    let F : Tm 0 := .abs A (.fst (.app f.wk0 (.bv 0)))
    Γ.JEqB levels H
      (.pi A (.sigma
        (.id S.index.wk0 (S.root (.app F.wk0 (.bv 0))) (S.childIndexAt l.wk0 (.bv 0)))
        (S.coherence n (.app F.wk0 (.bv 0))).wk0))
      (.abs A (.snd (.app f.wk0 (.bv 0)))) (.abs A (.snd (.app f.wk0 (.bv 0)))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.witnessChildren_typing_of_hypotheses hH D hl hA hP hf

/-- Computing the original node's coherence child retains its exact dependent witness type. -/
theorem witnessChildren_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l A f p : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l) (hA : Γ.JEqB levels H (.univ n) A A)
    (hP : Γ.JEqB levels H (.univ n) A (S.positions.lst l))
    (hf : Γ.JEqB levels H (.pi A (S.childFibres n l)) f f)
    (hp : Γ.JEqB levels H A p p) :
    let F : Tm 0 := .abs A (.fst (.app f.wk0 (.bv 0)))
    Γ.JEqB levels H
      (.sigma (.id S.index (S.root (.app F p)) (S.childIndexAt l p))
        (S.coherence n (.app F p)).wk0)
      (.app (.abs A (.snd (.app f.wk0 (.bv 0)))) p) (.snd (.app f p)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.witnessChildren_beta_of_hypotheses hH D hl hA hP hf hp

theorem node_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i a f : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hf : Γ.JEqB levels H (.pi (S.positionAt i a) (S.childFibres n (.pair i a))) f f) :
    Γ.JEqB levels H (S.fibre n i) (S.node i a f) (S.node i a f) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.node_typing_of_hypotheses hH D hi ha hf

theorem node_fst_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i a f : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hf : Γ.JEqB levels H (.pi (S.positionAt i a) (S.childFibres n (.pair i a))) f f) :
    Γ.JEqB levels H S.raw (.fst (S.node i a f))
      (.sup S.totalShape S.positions (.pair i a)
        (.abs (S.positionAt i a) (.fst (.app f.wk0 (.bv 0))))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.node_fst_beta_of_hypotheses hH D hi ha hf

theorem node_snd_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i a f : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hf : Γ.JEqB levels H (.pi (S.positionAt i a) (S.childFibres n (.pair i a))) f f) :
    Γ.JEqB levels H
      ((.sigma (.id S.index.wk0 (S.root (.bv 0)) i.wk0) (S.coherence n (.bv 1)) : Tm 1).lst
        (.sup S.totalShape S.positions (.pair i a)
          (.abs (S.positionAt i a) (.fst (.app f.wk0 (.bv 0))))))
      (.snd (S.node i a f))
      (.pair (.refl i) (.abs (S.positionAt i a) (.snd (.app f.wk0 (.bv 0))))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.node_snd_beta_of_hypotheses hH D hi ha hf

theorem node_coherence_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i a f : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hf : Γ.JEqB levels H (.pi (S.positionAt i a) (S.childFibres n (.pair i a))) f f) :
    Γ.JEqB levels H
      (S.coherence n (.sup S.totalShape S.positions (.pair i a)
        (.abs (S.positionAt i a) (.fst (.app f.wk0 (.bv 0))))))
      (.snd (.snd (S.node i a f))) (.abs (S.positionAt i a) (.snd (.app f.wk0 (.bv 0)))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.node_coherence_beta_of_hypotheses hH D hi ha hf

theorem root_congr (D : FormationData S levels n Γ) {t u : Tm 0}
    (ht : Γ.JEqB levels ∅ S.raw t u) :
    Γ.JEqB levels ∅ S.index (S.root t) (S.root u) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.root_congr D ht

theorem coherence_congr (D : IndexedFormationData S levels n Γ) {t u : Tm 0}
    (ht : Γ.JEqB levels ∅ S.raw t u) :
    Γ.JEqB levels ∅ (.univ n) (S.coherence n t) (S.coherence n u) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherence_congr D ht

theorem fibreTail_formation (D : IndexedFormationData S levels n Γ) {i : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) :
    ∀ x ∉ Γ.dv, (Γ.cons x S.raw).JEqB levels ∅ (.univ n)
      ((.sigma (.id S.index.wk0 (S.root (.bv 0)) i.wk0)
        (S.coherence n (.bv 1)) : Tm 1).open x)
      ((.sigma (.id S.index.wk0 (S.root (.bv 0)) i.wk0)
        (S.coherence n (.bv 1)) : Tm 1).open x) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.fibreTail_formation D hi

theorem childFibres_open (S : Description) (n : ℕ) (l : Tm 0) (p : String) :
    (S.childFibres n l).open p = S.fibre n (S.childIndexAt l (.fv p)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.childFibres_open S n l p

theorem childFibres_lst (S : Description) (n : ℕ) (l p : Tm 0) :
    (S.childFibres n l).lst p = S.fibre n (S.childIndexAt l p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.childFibres_lst S n l p

theorem childFibres_formation (D : IndexedFormationData S levels n Γ) {l A : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l) (hA : Γ.JEqB levels ∅ (.univ n) A A)
    (hP : Γ.JEqB levels ∅ (.univ n) A (S.positions.lst l)) :
    ∀ p ∉ Γ.dv, (Γ.cons p A).JEqB levels ∅ (.univ n)
      ((S.childFibres n l).open p) ((S.childFibres n l).open p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.childFibres_formation D hl hA hP

theorem childValue_typing (D : IndexedFormationData S levels n Γ) {l A f p : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l) (hA : Γ.JEqB levels ∅ (.univ n) A A)
    (hP : Γ.JEqB levels ∅ (.univ n) A (S.positions.lst l))
    (hf : Γ.JEqB levels ∅ (.pi A (S.childFibres n l)) f f)
    (hp : Γ.JEqB levels ∅ A p p) :
    Γ.JEqB levels ∅ (S.fibre n (S.childIndexAt l p)) (.app f p) (.app f p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.childValue_typing D hl hA hP hf hp

theorem fibre_fst_typing (D : IndexedFormationData S levels n Γ) {i t : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ht : Γ.JEqB levels ∅ (S.fibre n i) t t) :
    Γ.JEqB levels ∅ S.raw (.fst t) (.fst t) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.fibre_fst_typing D hi ht

theorem fibre_snd_typing (D : IndexedFormationData S levels n Γ) {i t : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ht : Γ.JEqB levels ∅ (S.fibre n i) t t) :
    Γ.JEqB levels ∅
      (.sigma (.id S.index (S.root (.fst t)) i) (S.coherence n (.fst t)).wk0)
      (.snd t) (.snd t) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.fibre_snd_typing D hi ht

theorem eraseChildren_typing (D : IndexedFormationData S levels n Γ) {l A f : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l) (hA : Γ.JEqB levels ∅ (.univ n) A A)
    (hP : Γ.JEqB levels ∅ (.univ n) A (S.positions.lst l))
    (hf : Γ.JEqB levels ∅ (.pi A (S.childFibres n l)) f f) :
    Γ.JEqB levels ∅ (.arr A S.raw)
      (.abs A (.fst (.app f.wk0 (.bv 0)))) (.abs A (.fst (.app f.wk0 (.bv 0)))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.eraseChildren_typing D hl hA hP hf

theorem eraseChildren_beta (D : IndexedFormationData S levels n Γ) {l A f p : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l) (hA : Γ.JEqB levels ∅ (.univ n) A A)
    (hP : Γ.JEqB levels ∅ (.univ n) A (S.positions.lst l))
    (hf : Γ.JEqB levels ∅ (.pi A (S.childFibres n l)) f f)
    (hp : Γ.JEqB levels ∅ A p p) :
    Γ.JEqB levels ∅ S.raw
      (.app (.abs A (.fst (.app f.wk0 (.bv 0)))) p) (.fst (.app f p)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.eraseChildren_beta D hl hA hP hf hp

theorem witnessChildren_typing (D : IndexedFormationData S levels n Γ) {l A f : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l) (hA : Γ.JEqB levels ∅ (.univ n) A A)
    (hP : Γ.JEqB levels ∅ (.univ n) A (S.positions.lst l))
    (hf : Γ.JEqB levels ∅ (.pi A (S.childFibres n l)) f f) :
    let F : Tm 0 := .abs A (.fst (.app f.wk0 (.bv 0)))
    Γ.JEqB levels ∅
      (.pi A (.sigma
        (.id S.index.wk0 (S.root (.app F.wk0 (.bv 0))) (S.childIndexAt l.wk0 (.bv 0)))
        (S.coherence n (.app F.wk0 (.bv 0))).wk0))
      (.abs A (.snd (.app f.wk0 (.bv 0)))) (.abs A (.snd (.app f.wk0 (.bv 0)))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.witnessChildren_typing D hl hA hP hf

/-- Computing the original node's coherence child retains its exact dependent witness type. -/
theorem witnessChildren_beta (D : IndexedFormationData S levels n Γ) {l A f p : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l) (hA : Γ.JEqB levels ∅ (.univ n) A A)
    (hP : Γ.JEqB levels ∅ (.univ n) A (S.positions.lst l))
    (hf : Γ.JEqB levels ∅ (.pi A (S.childFibres n l)) f f)
    (hp : Γ.JEqB levels ∅ A p p) :
    let F : Tm 0 := .abs A (.fst (.app f.wk0 (.bv 0)))
    Γ.JEqB levels ∅
      (.sigma (.id S.index (S.root (.app F p)) (S.childIndexAt l p))
        (S.coherence n (.app F p)).wk0)
      (.app (.abs A (.snd (.app f.wk0 (.bv 0)))) p) (.snd (.app f p)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.witnessChildren_beta D hl hA hP hf hp

theorem node_typing (D : IndexedFormationData S levels n Γ) {i a f : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hf : Γ.JEqB levels ∅ (.pi (S.positionAt i a) (S.childFibres n (.pair i a))) f f) :
    Γ.JEqB levels ∅ (S.fibre n i) (S.node i a f) (S.node i a f) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.node_typing D hi ha hf

def nullaryChildren : Tm 0 :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.nullaryChildren

theorem nullaryChildren_typing : Ctx.JEqB 2 ∅ .nil
    (.pi (nullaryDescription.positionAt .star .star)
      (nullaryDescription.childFibres 0 (.pair .star .star))) nullaryChildren nullaryChildren :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.nullaryChildren_typing

theorem nullary_node_typing : Ctx.JEqB 2 ∅ .nil (nullaryDescription.fibre 0 .star)
    (nullaryDescription.node .star .star nullaryChildren)
    (nullaryDescription.node .star .star nullaryChildren) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.nullary_node_typing

theorem node_fst_beta (D : IndexedFormationData S levels n Γ) {i a f : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hf : Γ.JEqB levels ∅ (.pi (S.positionAt i a) (S.childFibres n (.pair i a))) f f) :
    Γ.JEqB levels ∅ S.raw (.fst (S.node i a f))
      (.sup S.totalShape S.positions (.pair i a)
        (.abs (S.positionAt i a) (.fst (.app f.wk0 (.bv 0))))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.node_fst_beta D hi ha hf

theorem node_snd_beta (D : IndexedFormationData S levels n Γ) {i a f : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hf : Γ.JEqB levels ∅ (.pi (S.positionAt i a) (S.childFibres n (.pair i a))) f f) :
    Γ.JEqB levels ∅
      ((.sigma (.id S.index.wk0 (S.root (.bv 0)) i.wk0) (S.coherence n (.bv 1)) : Tm 1).lst
        (.sup S.totalShape S.positions (.pair i a)
          (.abs (S.positionAt i a) (.fst (.app f.wk0 (.bv 0))))))
      (.snd (S.node i a f))
      (.pair (.refl i) (.abs (S.positionAt i a) (.snd (.app f.wk0 (.bv 0))))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.node_snd_beta D hi ha hf

theorem node_coherence_beta (D : IndexedFormationData S levels n Γ) {i a f : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hf : Γ.JEqB levels ∅ (.pi (S.positionAt i a) (S.childFibres n (.pair i a))) f f) :
    Γ.JEqB levels ∅
      (S.coherence n (.sup S.totalShape S.positions (.pair i a)
        (.abs (S.positionAt i a) (.fst (.app f.wk0 (.bv 0))))))
      (.snd (.snd (S.node i a f))) (.abs (S.positionAt i a) (.snd (.app f.wk0 (.bv 0)))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.node_coherence_beta D hi ha hf

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
