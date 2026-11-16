module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Induction.RawStep.Defs
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.WInductionStep

@[expose] public section

/-! Generic dependent elimination from the exact original indexed encoding and actual source step. -/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

variable {H : Set Jdg} {S : Description} {levels : RuleBudget} {n m : ℕ} {Γ : Ctx}


theorem coherentStep_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C s l f r : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hs : Γ.JEqB levels H (S.indexedStepType n C) s s)
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hr : Γ.JEqB levels H (.pi (S.positions.lst l)
      ((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0)))) r r) :
    Γ.JEqB levels H ((S.inductionMotive n C).lst (.sup S.totalShape S.positions l f))
      (S.coherentStep n s l f r) (S.coherentStep n s l f r) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherentStep_typing_of_hypotheses hH D hm hC hs hl hf hr

theorem coherentStep_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
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
      (.app (S.coherentStep n s l f r) c) (S.sourceStepValue s l f c r) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherentStep_beta_of_hypotheses hH D hm hC hs hl hf hc hr

theorem inductionStep_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C s : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hs : Γ.JEqB levels H (S.indexedStepType n C) s s) :
    Γ.JEqB levels H (Tm.wStepType S.totalShape S.positions (S.inductionMotive n C))
      (S.inductionStep n C s) (S.inductionStep n C s) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.inductionStep_typing_of_hypotheses hH D hm hC hs

theorem indexedInduction_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C s i t : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hs : Γ.JEqB levels H (S.indexedStepType n C) s s)
    (hi : Γ.JEqB levels H S.index i i) (ht : Γ.JEqB levels H (S.fibre n i) t t) :
    Γ.JEqB levels H (.app (.app C i) t)
      (S.indexedInduction n C s t) (S.indexedInduction n C s t) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.indexedInduction_typing_of_hypotheses hH D hm hC hs hi ht

theorem inductionStep_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C s l f r : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hs : Γ.JEqB levels H (S.indexedStepType n C) s s)
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hr : Γ.JEqB levels H (.pi (S.positions.lst l)
      ((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0)))) r r) :
    Γ.JEqB levels H ((S.inductionMotive n C).lst (.sup S.totalShape S.positions l f))
      (.app (.app (.app (S.inductionStep n C s) l) f) r) (S.coherentStep n s l f r) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.inductionStep_beta_of_hypotheses hH D hm hC hs hl hf hr

theorem reifyChildren_open {k : ℕ} (S : Description) (l f c : Tm (k + 1)) (x : String) :
    (S.reifyChildren l f c).open x = S.reifyChildren (l.open x) (f.open x) (c.open x) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.reifyChildren_open S l f c x

theorem reifyChildren_lst {k : ℕ} (S : Description) (l f c : Tm (k + 1)) (v : Tm 0) :
    (S.reifyChildren l f c).lst v = S.reifyChildren (l.lst v) (f.lst v) (c.lst v) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.reifyChildren_lst S l f c v

theorem reifyHypotheses_open {k : ℕ} (S : Description) (l c r : Tm (k + 1)) (x : String) :
    (S.reifyHypotheses l c r).open x = S.reifyHypotheses (l.open x) (c.open x) (r.open x) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.reifyHypotheses_open S l c r x

theorem reifyHypotheses_lst {k : ℕ} (S : Description) (l c r : Tm (k + 1)) (v : Tm 0) :
    (S.reifyHypotheses l c r).lst v = S.reifyHypotheses (l.lst v) (c.lst v) (r.lst v) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.reifyHypotheses_lst S l c r v

theorem sourceStepValue_open {k : ℕ} (S : Description) (s l f c r : Tm (k + 1)) (x : String) :
    (S.sourceStepValue s l f c r).open x =
      S.sourceStepValue (s.open x) (l.open x) (f.open x) (c.open x) (r.open x) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.sourceStepValue_open S s l f c r x

theorem sourceStepValue_lst {k : ℕ} (S : Description) (s l f c r : Tm (k + 1)) (v : Tm 0) :
    (S.sourceStepValue s l f c r).lst v =
      S.sourceStepValue (s.lst v) (l.lst v) (f.lst v) (c.lst v) (r.lst v) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.sourceStepValue_lst S s l f c r v

theorem coherentStep_open {k : ℕ} (S : Description) (n : ℕ) (s l f r : Tm (k + 1)) (x : String) :
    (S.coherentStep n s l f r).open x =
      S.coherentStep n (s.open x) (l.open x) (f.open x) (r.open x) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherentStep_open S n s l f r x

theorem coherentStep_lst {k : ℕ} (S : Description) (n : ℕ) (s l f r : Tm (k + 1)) (v : Tm 0) :
    (S.coherentStep n s l f r).lst v =
      S.coherentStep n (s.lst v) (l.lst v) (f.lst v) (r.lst v) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherentStep_lst S n s l f r v

theorem coherentStep_typing (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C s l f r : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hs : Γ.JEqB levels ∅ (S.indexedStepType n C) s s)
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hr : Γ.JEqB levels ∅ (.pi (S.positions.lst l)
      ((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0)))) r r) :
    Γ.JEqB levels ∅ ((S.inductionMotive n C).lst (.sup S.totalShape S.positions l f))
      (S.coherentStep n s l f r) (S.coherentStep n s l f r) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherentStep_typing D hm hC hs hl hf hr

theorem coherentStep_beta (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
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
      (.app (S.coherentStep n s l f r) c) (S.sourceStepValue s l f c r) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherentStep_beta D hm hC hs hl hf hc hr

theorem inductionStep_typing (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C s : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hs : Γ.JEqB levels ∅ (S.indexedStepType n C) s s) :
    Γ.JEqB levels ∅ (Tm.wStepType S.totalShape S.positions (S.inductionMotive n C))
      (S.inductionStep n C s) (S.inductionStep n C s) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.inductionStep_typing D hm hC hs

theorem indexedInduction_typing (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C s i t : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hs : Γ.JEqB levels ∅ (S.indexedStepType n C) s s)
    (hi : Γ.JEqB levels ∅ S.index i i) (ht : Γ.JEqB levels ∅ (S.fibre n i) t t) :
    Γ.JEqB levels ∅ (.app (.app C i) t)
      (S.indexedInduction n C s t) (S.indexedInduction n C s t) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.indexedInduction_typing D hm hC hs hi ht

theorem inductionStep_beta (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C s l f r : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hs : Γ.JEqB levels ∅ (S.indexedStepType n C) s s)
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hr : Γ.JEqB levels ∅ (.pi (S.positions.lst l)
      ((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0)))) r r) :
    Γ.JEqB levels ∅ ((S.inductionMotive n C).lst (.sup S.totalShape S.positions l f))
      (.app (.app (.app (S.inductionStep n C s) l) f) r) (S.coherentStep n s l f r) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.inductionStep_beta D hm hC hs hl hf hr

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
