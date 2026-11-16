module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Induction.RawStep.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.DependentChildren
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.WInductionComputation

@[expose] public section

/-! Actual W recursion, dependent recursive children and synthesized source-step computation. -/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

variable {H : Set Jdg} {S : Description} {levels : RuleBudget} {n m : ℕ} {Γ : Ctx}


theorem inductionChildren_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C s l f : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hs : Γ.JEqB levels H (S.indexedStepType n C) s s)
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f) :
    Γ.JEqB levels H (.pi (S.positions.lst l)
      ((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0))))
      (Tm.recChildren S.totalShape S.positions (S.inductionMotive n C) (S.inductionStep n C s) l f)
      (Tm.recChildren S.totalShape S.positions (S.inductionMotive n C) (S.inductionStep n C s) l f) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.inductionChildren_typing_of_hypotheses hH D hm hC hs hl hf

theorem inductionChildren_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C s l f p : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hs : Γ.JEqB levels H (S.indexedStepType n C) s s)
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hp : Γ.JEqB levels H (S.positions.lst l) p p) :
    Γ.JEqB levels H ((S.inductionMotive n C).lst (.app f p))
      (.app (Tm.recChildren S.totalShape S.positions (S.inductionMotive n C) (S.inductionStep n C s) l f) p)
      (.wrec S.totalShape S.positions (S.inductionMotive n C) (S.inductionStep n C s) (.app f p)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.inductionChildren_beta_of_hypotheses hH D hm hC hs hl hf hp

theorem rawInduction_source_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C s l f c : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hs : Γ.JEqB levels H (S.indexedStepType n C) s s)
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    let R := Tm.recChildren S.totalShape S.positions (S.inductionMotive n C) (S.inductionStep n C s) l f
    Γ.JEqB levels H
      (.app (.app C (S.root (.sup S.totalShape S.positions l f)))
        (S.canonical (.sup S.totalShape S.positions l f) c))
      (.app (.wrec S.totalShape S.positions (S.inductionMotive n C) (S.inductionStep n C s)
        (.sup S.totalShape S.positions l f)) c)
      (S.sourceStepValue s l f c R) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.rawInduction_source_beta_of_hypotheses hH D hm hC hs hl hf hc

theorem inductionChildren_typing (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C s l f : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hs : Γ.JEqB levels ∅ (S.indexedStepType n C) s s)
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f) :
    Γ.JEqB levels ∅ (.pi (S.positions.lst l)
      ((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0))))
      (Tm.recChildren S.totalShape S.positions (S.inductionMotive n C) (S.inductionStep n C s) l f)
      (Tm.recChildren S.totalShape S.positions (S.inductionMotive n C) (S.inductionStep n C s) l f) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.inductionChildren_typing D hm hC hs hl hf

theorem inductionChildren_beta (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C s l f p : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hs : Γ.JEqB levels ∅ (S.indexedStepType n C) s s)
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hp : Γ.JEqB levels ∅ (S.positions.lst l) p p) :
    Γ.JEqB levels ∅ ((S.inductionMotive n C).lst (.app f p))
      (.app (Tm.recChildren S.totalShape S.positions (S.inductionMotive n C) (S.inductionStep n C s) l f) p)
      (.wrec S.totalShape S.positions (S.inductionMotive n C) (S.inductionStep n C s) (.app f p)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.inductionChildren_beta D hm hC hs hl hf hp

theorem rawInduction_source_beta (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C s l f c : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hs : Γ.JEqB levels ∅ (S.indexedStepType n C) s s)
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    let R := Tm.recChildren S.totalShape S.positions (S.inductionMotive n C) (S.inductionStep n C s) l f
    Γ.JEqB levels ∅
      (.app (.app C (S.root (.sup S.totalShape S.positions l f)))
        (S.canonical (.sup S.totalShape S.positions l f) c))
      (.app (.wrec S.totalShape S.positions (S.inductionMotive n C) (S.inductionStep n C s)
        (.sup S.totalShape S.positions l f)) c)
      (S.sourceStepValue s l f c R) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.rawInduction_source_beta D hm hC hs hl hf hc

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
