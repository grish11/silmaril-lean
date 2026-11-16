module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Induction.Node.Thms
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.WIndexedStep

@[expose] public section

/-! Actual original indexed step application, from full reified children and dependent IHs. -/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

variable {H : Set Jdg} {S : Description} {levels : RuleBudget} {n m : ℕ} {Γ : Ctx}


theorem shapeAt_congr_of_hypotheses (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) {i j : Tm 0}
    (hij : Γ.JEqB levels H S.index i j) :
    Γ.JEqB levels H (.univ n) (S.shape.lst i) (S.shape.lst j) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.shapeAt_congr_of_hypotheses hH D hij

theorem sourceChildren_formation_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i a : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a) :
    Γ.JEqB levels H (.univ n)
      (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a)))
      (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.sourceChildren_formation_of_hypotheses hH D hi ha

theorem sourceIH_formation_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C i a g : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hg : Γ.JEqB levels H (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g) :
    Γ.JEqB levels H (.univ (max n m))
      (.pi (S.positionAt i a) (.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0))))
      (.pi (S.positionAt i a) (.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0)))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.sourceIH_formation_of_hypotheses hH D hm hC hi ha hg

/-- Formation of the full dependent method tail at each actual source index. -/

theorem indexedStepBody_formation_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C) :
    ∀ i ∉ Γ.dv, (Γ.cons i S.index).JEqB levels H (.univ (max n m))
      ((S.indexedStepBody n C).open i) ((S.indexedStepBody n C).open i) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.indexedStepBody_formation_of_hypotheses hH D hm hC

theorem indexedStepType_formation_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C) :
    Γ.JEqB levels H (.univ (max n m)) (S.indexedStepType n C) (S.indexedStepType n C) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.indexedStepType_formation_of_hypotheses hH D hm hC

/-- Source-step introduction from an ordinary scoped body under its four source declarations. -/

theorem indexedStep_abstraction_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C : Tm 0} {b : Tm 4} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hb : ∀ i ∉ Γ.dv, ∀ a ∉ (Γ.cons i S.index).dv,
      ∀ g ∉ ((Γ.cons i S.index).cons a (S.shape.open i)).dv,
      ∀ h ∉ (((Γ.cons i S.index).cons a (S.shape.open i)).cons g
        (.pi (S.positionAt (.fv i) (.fv a)) (S.fibreAt n ((S.next.lst (.fv i)).lst (.fv a))))).dv,
      ((((Γ.cons i S.index).cons a (S.shape.open i)).cons g
        (.pi (S.positionAt (.fv i) (.fv a)) (S.fibreAt n ((S.next.lst (.fv i)).lst (.fv a))))).cons h
          (.pi (S.positionAt (.fv i) (.fv a))
            (.app (.app C.wk0 ((S.next.lst (.fv i)).lst (.fv a))) (.app (Tm.fv g).wk0 (.bv 0))))).JEqB levels H
        (.app (.app C (.fv i)) (S.node (.fv i) (.fv a) (.fv g)))
        ((((b.open i).open a).open g).open h) ((((b.open i).open a).open g).open h)) :
    Γ.JEqB levels H (S.indexedStepType n C)
      (S.indexedStepAbstraction n C b) (S.indexedStepAbstraction n C b) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.indexedStep_abstraction_of_hypotheses hH D hm hC hb

theorem indexedStep_apply_congr_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C s i i' a a' g g' h h' : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hs : Γ.JEqB levels H (S.indexedStepType n C) s s)
    (hi : Γ.JEqB levels H S.index i i') (ha : Γ.JEqB levels H (S.shape.lst i) a a')
    (hg : Γ.JEqB levels H (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g')
    (hh : Γ.JEqB levels H (.pi (S.positionAt i a)
      (.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0)))) h h') :
    Γ.JEqB levels H (.app (.app C i) (S.node i a g))
      (.app (.app (.app (.app s i) a) g) h) (.app (.app (.app (.app s i') a') g') h') :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.indexedStep_apply_congr_of_hypotheses hH D hm hC hs hi ha hg hh

theorem indexedStep_apply_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C s i a g h : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hs : Γ.JEqB levels H (S.indexedStepType n C) s s)
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hg : Γ.JEqB levels H (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g)
    (hh : Γ.JEqB levels H (.pi (S.positionAt i a)
      (.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0)))) h h) :
    Γ.JEqB levels H (.app (.app C i) (S.node i a g))
      (.app (.app (.app (.app s i) a) g) h) (.app (.app (.app (.app s i) a) g) h) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.indexedStep_apply_of_hypotheses hH D hm hC hs hi ha hg hh

theorem reifyChildren_source_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f c : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    Γ.JEqB levels H (.pi (S.positionAt (.fst l) (.snd l))
      (S.fibreAt n ((S.next.lst (.fst l)).lst (.snd l))))
      (S.reifyChildren l f c) (S.reifyChildren l f c) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.reifyChildren_source_typing_of_hypotheses hH D hl hf hc

theorem reifyHypotheses_source_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C l f c r : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hr : Γ.JEqB levels H (.pi (S.positions.lst l)
      ((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0)))) r r) :
    Γ.JEqB levels H (.pi (S.positionAt (.fst l) (.snd l))
      (.app (.app C.wk0 ((S.next.lst (.fst l)).lst (.snd l)))
        (.app (S.reifyChildren l f c).wk0 (.bv 0))))
      (S.reifyHypotheses l c r) (S.reifyHypotheses l c r) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.reifyHypotheses_source_typing_of_hypotheses hH D hm hC hl hf hc hr

theorem indexedStep_reified_apply_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C s l f c r : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hs : Γ.JEqB levels H (S.indexedStepType n C) s s)
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hr : Γ.JEqB levels H (.pi (S.positions.lst l)
      ((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0)))) r r) :
    Γ.JEqB levels H
      (.app (.app C (S.root (.sup S.totalShape S.positions l f)))
        (S.canonical (.sup S.totalShape S.positions l f) c))
      (.app (.app (.app (.app s (.fst l)) (.snd l)) (S.reifyChildren l f c)) (S.reifyHypotheses l c r))
      (.app (.app (.app (.app s (.fst l)) (.snd l)) (S.reifyChildren l f c)) (S.reifyHypotheses l c r)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.indexedStep_reified_apply_of_hypotheses hH D hm hC hs hl hf hc hr

theorem sourceChildren_codomain_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i a : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a) :
    ∀ p ∉ Γ.dv, (Γ.cons p (S.positionAt i a)).JEqB levels H (.univ n)
      ((S.fibreAt n ((S.next.lst i).lst a)).open p)
      ((S.fibreAt n ((S.next.lst i).lst a)).open p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.sourceChildren_codomain_of_hypotheses hH D hi ha

theorem sourceChild_value_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i a g p : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hg : Γ.JEqB levels H (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g)
    (hp : Γ.JEqB levels H (S.positionAt i a) p p) :
    Γ.JEqB levels H (S.fibre n (S.next.bsubst (Fin.cases p (Fin.cases a (fun _ => i)))))
      (.app g p) (.app g p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.sourceChild_value_of_hypotheses hH D hi ha hg hp

theorem sourceIH_codomain_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C i a g : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hg : Γ.JEqB levels H (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g) :
    ∀ p ∉ Γ.dv, (Γ.cons p (S.positionAt i a)).JEqB levels H (.univ m)
      ((.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0)) : Tm 1).open p)
      ((.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0)) : Tm 1).open p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.sourceIH_codomain_of_hypotheses hH D hm hC hi ha hg

theorem nodeAt_open {k : ℕ} (S : Description) (i a f : Tm (k + 1)) (x : String) :
    (S.nodeAt i a f).open x = S.nodeAt (i.open x) (a.open x) (f.open x) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.nodeAt_open S i a f x

theorem nodeAt_lst {k : ℕ} (S : Description) (i a f : Tm (k + 1)) (v : Tm 0) :
    (S.nodeAt i a f).lst v = S.nodeAt (i.lst v) (a.lst v) (f.lst v) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.nodeAt_lst S i a f v

theorem shapeAt_congr (D : FormationData S levels n Γ) {i j : Tm 0}
    (hij : Γ.JEqB levels ∅ S.index i j) :
    Γ.JEqB levels ∅ (.univ n) (S.shape.lst i) (S.shape.lst j) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.shapeAt_congr D hij

theorem sourceChildren_formation (D : IndexedFormationData S levels n Γ) {i a : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a) :
    Γ.JEqB levels ∅ (.univ n)
      (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a)))
      (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.sourceChildren_formation D hi ha

theorem sourceIH_formation (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C i a g : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hg : Γ.JEqB levels ∅ (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g) :
    Γ.JEqB levels ∅ (.univ (max n m))
      (.pi (S.positionAt i a) (.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0))))
      (.pi (S.positionAt i a) (.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0)))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.sourceIH_formation D hm hC hi ha hg

/-- Formation of the full dependent method tail at each actual source index. -/
theorem indexedStepBody_formation (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C) :
    ∀ i ∉ Γ.dv, (Γ.cons i S.index).JEqB levels ∅ (.univ (max n m))
      ((S.indexedStepBody n C).open i) ((S.indexedStepBody n C).open i) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.indexedStepBody_formation D hm hC

theorem indexedStepType_formation (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C) :
    Γ.JEqB levels ∅ (.univ (max n m)) (S.indexedStepType n C) (S.indexedStepType n C) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.indexedStepType_formation D hm hC

/-- Source-step introduction from an ordinary scoped body under its four source declarations. -/
theorem indexedStep_abstraction (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C : Tm 0} {b : Tm 4} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hb : ∀ i ∉ Γ.dv, ∀ a ∉ (Γ.cons i S.index).dv,
      ∀ g ∉ ((Γ.cons i S.index).cons a (S.shape.open i)).dv,
      ∀ h ∉ (((Γ.cons i S.index).cons a (S.shape.open i)).cons g
        (.pi (S.positionAt (.fv i) (.fv a)) (S.fibreAt n ((S.next.lst (.fv i)).lst (.fv a))))).dv,
      ((((Γ.cons i S.index).cons a (S.shape.open i)).cons g
        (.pi (S.positionAt (.fv i) (.fv a)) (S.fibreAt n ((S.next.lst (.fv i)).lst (.fv a))))).cons h
          (.pi (S.positionAt (.fv i) (.fv a))
            (.app (.app C.wk0 ((S.next.lst (.fv i)).lst (.fv a))) (.app (Tm.fv g).wk0 (.bv 0))))).JEqB levels ∅
        (.app (.app C (.fv i)) (S.node (.fv i) (.fv a) (.fv g)))
        ((((b.open i).open a).open g).open h) ((((b.open i).open a).open g).open h)) :
    Γ.JEqB levels ∅ (S.indexedStepType n C)
      (S.indexedStepAbstraction n C b) (S.indexedStepAbstraction n C b) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.indexedStep_abstraction D hm hC hb

theorem indexedStep_apply_congr (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C s i i' a a' g g' h h' : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hs : Γ.JEqB levels ∅ (S.indexedStepType n C) s s)
    (hi : Γ.JEqB levels ∅ S.index i i') (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a')
    (hg : Γ.JEqB levels ∅ (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g')
    (hh : Γ.JEqB levels ∅ (.pi (S.positionAt i a)
      (.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0)))) h h') :
    Γ.JEqB levels ∅ (.app (.app C i) (S.node i a g))
      (.app (.app (.app (.app s i) a) g) h) (.app (.app (.app (.app s i') a') g') h') :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.indexedStep_apply_congr D hm hC hs hi ha hg hh

theorem indexedStep_apply (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C s i a g h : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hs : Γ.JEqB levels ∅ (S.indexedStepType n C) s s)
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hg : Γ.JEqB levels ∅ (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g)
    (hh : Γ.JEqB levels ∅ (.pi (S.positionAt i a)
      (.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0)))) h h) :
    Γ.JEqB levels ∅ (.app (.app C i) (S.node i a g))
      (.app (.app (.app (.app s i) a) g) h) (.app (.app (.app (.app s i) a) g) h) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.indexedStep_apply D hm hC hs hi ha hg hh

theorem reifyChildren_source_typing (D : IndexedFormationData S levels n Γ) {l f c : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    Γ.JEqB levels ∅ (.pi (S.positionAt (.fst l) (.snd l))
      (S.fibreAt n ((S.next.lst (.fst l)).lst (.snd l))))
      (S.reifyChildren l f c) (S.reifyChildren l f c) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.reifyChildren_source_typing D hl hf hc

theorem reifyHypotheses_source_typing (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C l f c r : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hr : Γ.JEqB levels ∅ (.pi (S.positions.lst l)
      ((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0)))) r r) :
    Γ.JEqB levels ∅ (.pi (S.positionAt (.fst l) (.snd l))
      (.app (.app C.wk0 ((S.next.lst (.fst l)).lst (.snd l)))
        (.app (S.reifyChildren l f c).wk0 (.bv 0))))
      (S.reifyHypotheses l c r) (S.reifyHypotheses l c r) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.reifyHypotheses_source_typing D hm hC hl hf hc hr

theorem indexedStep_reified_apply (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C s l f c r : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hs : Γ.JEqB levels ∅ (S.indexedStepType n C) s s)
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hr : Γ.JEqB levels ∅ (.pi (S.positions.lst l)
      ((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0)))) r r) :
    Γ.JEqB levels ∅
      (.app (.app C (S.root (.sup S.totalShape S.positions l f)))
        (S.canonical (.sup S.totalShape S.positions l f) c))
      (.app (.app (.app (.app s (.fst l)) (.snd l)) (S.reifyChildren l f c)) (S.reifyHypotheses l c r))
      (.app (.app (.app (.app s (.fst l)) (.snd l)) (S.reifyChildren l f c)) (S.reifyHypotheses l c r)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.indexedStep_reified_apply D hm hC hs hl hf hc hr

theorem sourceChildren_codomain (D : IndexedFormationData S levels n Γ) {i a : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a) :
    ∀ p ∉ Γ.dv, (Γ.cons p (S.positionAt i a)).JEqB levels ∅ (.univ n)
      ((S.fibreAt n ((S.next.lst i).lst a)).open p)
      ((S.fibreAt n ((S.next.lst i).lst a)).open p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.sourceChildren_codomain D hi ha

theorem sourceChild_value (D : IndexedFormationData S levels n Γ) {i a g p : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hg : Γ.JEqB levels ∅ (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g)
    (hp : Γ.JEqB levels ∅ (S.positionAt i a) p p) :
    Γ.JEqB levels ∅ (S.fibre n (S.next.bsubst (Fin.cases p (Fin.cases a (fun _ => i)))))
      (.app g p) (.app g p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.sourceChild_value D hi ha hg hp

theorem sourceIH_codomain (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C i a g : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hg : Γ.JEqB levels ∅ (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g) :
    ∀ p ∉ Γ.dv, (Γ.cons p (S.positionAt i a)).JEqB levels ∅ (.univ m)
      ((.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0)) : Tm 1).open p)
      ((.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0)) : Tm 1).open p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.sourceIH_codomain D hm hC hi ha hg

theorem sourceNext_open (S : Description) (i a : Tm 0) (p : String) :
    ((S.next.lst i).lst a).open p = S.next.bsubst (Fin.cases (.fv p) (Fin.cases a (fun _ => i))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.nextBody_open S i a p

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
