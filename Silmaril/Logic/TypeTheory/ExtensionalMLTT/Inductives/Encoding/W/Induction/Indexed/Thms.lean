module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Induction.Computation.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Induction.Computation.Defs
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.WIndexedComputation

@[expose] public section

/-! Normalized dependent elimination computation for the exact original indexed-W constructor. -/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

variable {H : Set Jdg} {S : Description} {levels : RuleBudget} {n m : ℕ} {Γ : Ctx}


theorem sourceStepValue_tagged_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C s i a f c r : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hs : Γ.JEqB levels H (S.indexedStepType n C) s s)
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst (.pair i a)) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions (.pair i a) f)) c c)
    (hr : Γ.JEqB levels H (.pi (S.positions.lst (.pair i a))
      ((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0)))) r r) :
    Γ.JEqB levels H
      (.app (.app C (S.root (.sup S.totalShape S.positions (.pair i a) f)))
        (S.canonical (.sup S.totalShape S.positions (.pair i a) f) c))
      (S.sourceStepValue s (.pair i a) f c r)
      (.app (.app (.app (.app s i) a) (S.reifyChildren (.pair i a) f c))
        (S.reifyHypotheses (.pair i a) c r)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.sourceStepValue_tagged_beta_of_hypotheses hH D hm hC hs hi ha hf hc hr

theorem reifySourceChildren_recovery_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i a g : Tm 0}
    (hi : Γ.JEqB levels H S.index i i)
    (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hg : Γ.JEqB levels H (.pi (S.positionAt i a) (S.childFibres n (.pair i a))) g g) :
    let P := S.positionAt i a
    let L : Tm 0 := .pair i a
    let F : Tm 0 := .abs P (.fst (.app g.wk0 (.bv 0)))
    let c : Tm 0 := .abs P (.snd (.app g.wk0 (.bv 0)))
    Γ.JEqB levels H (.pi P (S.childFibres n L)) (S.reifyChildren L F c) g :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.reifySourceChildren_recovery_of_hypotheses hH D hi ha hg

theorem indexedHypotheses_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C s i a g : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hs : Γ.JEqB levels H (S.indexedStepType n C) s s)
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hg : Γ.JEqB levels H (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g) :
    Γ.JEqB levels H (.pi (S.positionAt i a)
      (.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0))))
      (S.indexedHypotheses n C s i a g) (S.indexedHypotheses n C s i a g) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.indexedHypotheses_typing_of_hypotheses hH D hm hC hs hi ha hg

theorem indexedHypotheses_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C s i a g p : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hs : Γ.JEqB levels H (S.indexedStepType n C) s s)
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hg : Γ.JEqB levels H (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g)
    (hp : Γ.JEqB levels H (S.positionAt i a) p p) :
    Γ.JEqB levels H
      (.app (.app C (S.next.bsubst (Fin.cases p (Fin.cases a (fun _ => i))))) (.app g p))
      (.app (S.indexedHypotheses n C s i a g) p) (S.indexedInduction n C s (.app g p)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.indexedHypotheses_beta_of_hypotheses hH D hm hC hs hi ha hg hp

theorem reifySourceHypothesis_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C s i a g p : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hs : Γ.JEqB levels H (S.indexedStepType n C) s s)
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hg : Γ.JEqB levels H (.pi (S.positionAt i a) (S.childFibres n (.pair i a))) g g)
    (hp : Γ.JEqB levels H (S.positionAt i a) p p) :
    let F : Tm 0 := .abs (S.positionAt i a) (.fst (.app g.wk0 (.bv 0)))
    let c : Tm 0 := .abs (S.positionAt i a) (.snd (.app g.wk0 (.bv 0)))
    let R := Tm.recChildren S.totalShape S.positions (S.inductionMotive n C) (S.inductionStep n C s) (.pair i a) F
    Γ.JEqB levels H
      (.app (.app C (S.next.bsubst (Fin.cases p (Fin.cases a (fun _ => i))))) (.app g p))
      (.app (S.reifyHypotheses (.pair i a) c R) p) (S.indexedInduction n C s (.app g p)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.reifySourceHypothesis_beta_of_hypotheses hH D hm hC hs hi ha hg hp

theorem reifySourceHypotheses_recovery_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C s i a g : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hs : Γ.JEqB levels H (S.indexedStepType n C) s s)
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hg : Γ.JEqB levels H (.pi (S.positionAt i a) (S.childFibres n (.pair i a))) g g) :
    let F : Tm 0 := .abs (S.positionAt i a) (.fst (.app g.wk0 (.bv 0)))
    let c : Tm 0 := .abs (S.positionAt i a) (.snd (.app g.wk0 (.bv 0)))
    let R := Tm.recChildren S.totalShape S.positions (S.inductionMotive n C) (S.inductionStep n C s) (.pair i a) F
    Γ.JEqB levels H (.pi (S.positionAt i a)
      (.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0))))
      (S.reifyHypotheses (.pair i a) c R) (S.indexedHypotheses n C s i a g) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.reifySourceHypotheses_recovery_of_hypotheses hH D hm hC hs hi ha hg

theorem indexedInduction_node_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C s i a g : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hs : Γ.JEqB levels H (S.indexedStepType n C) s s)
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hg : Γ.JEqB levels H (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g) :
    Γ.JEqB levels H (.app (.app C i) (S.node i a g))
      (S.indexedInduction n C s (S.node i a g))
      (.app (.app (.app (.app s i) a) g) (S.indexedHypotheses n C s i a g)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.indexedInduction_node_beta_of_hypotheses hH D hm hC hs hi ha hg

theorem sourceStepValue_tagged_beta (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C s i a f c r : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hs : Γ.JEqB levels ∅ (S.indexedStepType n C) s s)
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst (.pair i a)) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions (.pair i a) f)) c c)
    (hr : Γ.JEqB levels ∅ (.pi (S.positions.lst (.pair i a))
      ((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0)))) r r) :
    Γ.JEqB levels ∅
      (.app (.app C (S.root (.sup S.totalShape S.positions (.pair i a) f)))
        (S.canonical (.sup S.totalShape S.positions (.pair i a) f) c))
      (S.sourceStepValue s (.pair i a) f c r)
      (.app (.app (.app (.app s i) a) (S.reifyChildren (.pair i a) f c))
        (S.reifyHypotheses (.pair i a) c r)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.sourceStepValue_tagged_beta D hm hC hs hi ha hf hc hr

theorem reifySourceChildren_recovery (D : IndexedFormationData S levels n Γ) {i a g : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i)
    (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hg : Γ.JEqB levels ∅ (.pi (S.positionAt i a) (S.childFibres n (.pair i a))) g g) :
    let P := S.positionAt i a
    let L : Tm 0 := .pair i a
    let F : Tm 0 := .abs P (.fst (.app g.wk0 (.bv 0)))
    let c : Tm 0 := .abs P (.snd (.app g.wk0 (.bv 0)))
    Γ.JEqB levels ∅ (.pi P (S.childFibres n L)) (S.reifyChildren L F c) g :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.reifySourceChildren_recovery D hi ha hg

theorem indexedHypothesisBody_open (S : Description) (n : ℕ) (C s g : Tm 0) (p : String) :
    (S.indexedHypothesisBody n C s g).open p = S.indexedInduction n C s (.app g (.fv p)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.indexedHypothesisBody_open S n C s g p

theorem indexedHypothesisBody_lst (S : Description) (n : ℕ) (C s g p : Tm 0) :
    (S.indexedHypothesisBody n C s g).lst p = S.indexedInduction n C s (.app g p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.indexedHypothesisBody_lst S n C s g p

theorem indexedHypotheses_typing (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C s i a g : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hs : Γ.JEqB levels ∅ (S.indexedStepType n C) s s)
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hg : Γ.JEqB levels ∅ (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g) :
    Γ.JEqB levels ∅ (.pi (S.positionAt i a)
      (.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0))))
      (S.indexedHypotheses n C s i a g) (S.indexedHypotheses n C s i a g) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.indexedHypotheses_typing D hm hC hs hi ha hg

theorem indexedHypotheses_beta (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C s i a g p : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hs : Γ.JEqB levels ∅ (S.indexedStepType n C) s s)
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hg : Γ.JEqB levels ∅ (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g)
    (hp : Γ.JEqB levels ∅ (S.positionAt i a) p p) :
    Γ.JEqB levels ∅
      (.app (.app C (S.next.bsubst (Fin.cases p (Fin.cases a (fun _ => i))))) (.app g p))
      (.app (S.indexedHypotheses n C s i a g) p) (S.indexedInduction n C s (.app g p)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.indexedHypotheses_beta D hm hC hs hi ha hg hp

theorem reifySourceHypothesis_beta (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C s i a g p : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hs : Γ.JEqB levels ∅ (S.indexedStepType n C) s s)
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hg : Γ.JEqB levels ∅ (.pi (S.positionAt i a) (S.childFibres n (.pair i a))) g g)
    (hp : Γ.JEqB levels ∅ (S.positionAt i a) p p) :
    let F : Tm 0 := .abs (S.positionAt i a) (.fst (.app g.wk0 (.bv 0)))
    let c : Tm 0 := .abs (S.positionAt i a) (.snd (.app g.wk0 (.bv 0)))
    let R := Tm.recChildren S.totalShape S.positions (S.inductionMotive n C) (S.inductionStep n C s) (.pair i a) F
    Γ.JEqB levels ∅
      (.app (.app C (S.next.bsubst (Fin.cases p (Fin.cases a (fun _ => i))))) (.app g p))
      (.app (S.reifyHypotheses (.pair i a) c R) p) (S.indexedInduction n C s (.app g p)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.reifySourceHypothesis_beta D hm hC hs hi ha hg hp

theorem reifySourceHypotheses_recovery (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C s i a g : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hs : Γ.JEqB levels ∅ (S.indexedStepType n C) s s)
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hg : Γ.JEqB levels ∅ (.pi (S.positionAt i a) (S.childFibres n (.pair i a))) g g) :
    let F : Tm 0 := .abs (S.positionAt i a) (.fst (.app g.wk0 (.bv 0)))
    let c : Tm 0 := .abs (S.positionAt i a) (.snd (.app g.wk0 (.bv 0)))
    let R := Tm.recChildren S.totalShape S.positions (S.inductionMotive n C) (S.inductionStep n C s) (.pair i a) F
    Γ.JEqB levels ∅ (.pi (S.positionAt i a)
      (.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0))))
      (S.reifyHypotheses (.pair i a) c R) (S.indexedHypotheses n C s i a g) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.reifySourceHypotheses_recovery D hm hC hs hi ha hg

theorem indexedInduction_node_beta (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C s i a g : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hs : Γ.JEqB levels ∅ (S.indexedStepType n C) s s)
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hg : Γ.JEqB levels ∅ (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g) :
    Γ.JEqB levels ∅ (.app (.app C i) (S.node i a g))
      (S.indexedInduction n C s (S.node i a g))
      (.app (.app (.app (.app s i) a) g) (S.indexedHypotheses n C s i a g)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.indexedInduction_node_beta D hm hC hs hi ha hg

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
