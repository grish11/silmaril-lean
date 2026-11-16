module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Induction.RawStep.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.DependentChildren

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

variable {H : Set Jdg} {S : Description} {levels : RuleBudget} {n m : ℕ} {Γ : Ctx}

private theorem lastCases_zero {α : Sort _} (a : α) (f : Fin 0 → α) :
    Fin.lastCases a f (0 : Fin 1) = a := Fin.lastCases_last

/-- The actual recursive child lambda is typed at the full dependent canonical raw motive. -/
theorem inductionChildren_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C s l f : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hs : Γ.JEqB levels H (S.indexedStepType n C) s s)
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f) :
    Γ.JEqB levels H (.pi (S.positions.lst l)
      ((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0))))
      (Tm.recChildren S.totalShape S.positions (S.inductionMotive n C) (S.inductionStep n C s) l f)
      (Tm.recChildren S.totalShape S.positions (S.inductionMotive n C) (S.inductionStep n C s) l f) := by
  have hq : RuleBudget.Allows levels (max n m) := RuleBudget.Allows.max (by have := D.bound; budget_omega) (by budget_omega)
  have hq' : RuleBudget.Allows levels (max n m + 1) := by have := D.bound; budget_omega
  exact Ctx.JEqB.recChildren_typing_of_hypotheses hH hq' D.context
    (Ctx.JEqB.cumul hq (Nat.le_max_left n m) (totalShape_formation D.toFormationData))
    (fun l hl => Ctx.JEqB.cumul hq (Nat.le_max_left n m) (positions_formation_of_hypotheses hH D.toFormationData l hl))
    (inductionMotive_formation_of_hypotheses hH D hm hC) (inductionStep_typing_of_hypotheses hH D hm hC hs) hl hf

/-- Actual recursive child application beta has no recursive-lambda redex. -/
theorem inductionChildren_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C s l f p : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hs : Γ.JEqB levels H (S.indexedStepType n C) s s)
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hp : Γ.JEqB levels H (S.positions.lst l) p p) :
    Γ.JEqB levels H ((S.inductionMotive n C).lst (.app f p))
      (.app (Tm.recChildren S.totalShape S.positions (S.inductionMotive n C) (S.inductionStep n C s) l f) p)
      (.wrec S.totalShape S.positions (S.inductionMotive n C) (S.inductionStep n C s) (.app f p)) := by
  have hq : RuleBudget.Allows levels (max n m) := RuleBudget.Allows.max (by have := D.bound; budget_omega) (by budget_omega)
  have hq' : RuleBudget.Allows levels (max n m + 1) := by have := D.bound; budget_omega
  exact Ctx.JEqB.recChildren_beta_of_hypotheses hH hq' D.context
    (Ctx.JEqB.cumul hq (Nat.le_max_left n m) (totalShape_formation D.toFormationData))
    (fun l hl => Ctx.JEqB.cumul hq (Nat.le_max_left n m) (positions_formation_of_hypotheses hH D.toFormationData l hl))
    (inductionMotive_formation_of_hypotheses hH D hm hC) (inductionStep_typing_of_hypotheses hH D hm hC hs) hl hf hp

/-- Actual W recursion and all four synthesized step applications reduce to the original source step. -/
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
      (S.sourceStepValue s l f c R) := by
  intro R
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hq : RuleBudget.Allows levels (max n m) := RuleBudget.Allows.max hn (by budget_omega)
  have hR := inductionChildren_typing_of_hypotheses hH D hm hC hs hl hf
  have hraw : Γ.JEqB levels H ((S.inductionMotive n C).lst (.sup S.totalShape S.positions l f))
      (.wrec S.totalShape S.positions (S.inductionMotive n C) (S.inductionStep n C s)
        (.sup S.totalShape S.positions l f)) (S.coherentStep n s l f R) :=
    (Ctx.JEqB.beta_wrec hn hq (totalShape_formation D.toFormationData) (positions_formation_of_hypotheses hH D.toFormationData)
      (inductionMotive_formation_of_hypotheses hH D hm hC) (inductionStep_typing_of_hypotheses hH D hm hC hs) hl hf).trans
      (inductionStep_beta_of_hypotheses hH D hm hC hs hl hf hR)
  have ht : Γ.JEqB levels H S.raw (.sup S.totalShape S.positions l f) (.sup S.totalShape S.positions l f) :=
    .sup hn (totalShape_formation D.toFormationData) (positions_formation_of_hypotheses hH D.toFormationData) hl hf
  have hcoh := coherence_formation_of_hypotheses hH D ht
  have happ : Γ.JEqB levels H
      (.app (.app C (S.root (.sup S.totalShape S.positions l f)))
        (S.canonical (.sup S.totalShape S.positions l f) c))
      (.app (.wrec S.totalShape S.positions (S.inductionMotive n C) (S.inductionStep n C s)
        (.sup S.totalShape S.positions l f)) c) (.app (S.coherentStep n s l f R) c) := by
    simpa only [Tm.lst, Tm.closed_wk0_lst, root_lst, canonical_lst, lastCases_zero, Tm.castLE_refl] using
      Ctx.JEqB.app hq (Ctx.JEqB.cumul hq (Nat.le_max_left n m) hcoh)
        (fun c hc => Ctx.JEqB.cumul hq (Nat.le_max_right n m) (canonicalMotive_codomain_of_hypotheses hH D hm hC ht c hc))
        (by simpa only [inductionMotive_lst] using hraw) hc
  exact happ.trans (coherentStep_beta_of_hypotheses hH D hm hC hs hl hf hc hR)


theorem inductionChildren_typing (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C s l f : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hs : Γ.JEqB levels ∅ (S.indexedStepType n C) s s)
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f) :
    Γ.JEqB levels ∅ (.pi (S.positions.lst l)
      ((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0))))
      (Tm.recChildren S.totalShape S.positions (S.inductionMotive n C) (S.inductionStep n C s) l f)
      (Tm.recChildren S.totalShape S.positions (S.inductionMotive n C) (S.inductionStep n C s) l f) :=
  inductionChildren_typing_of_hypotheses (StructuralTheory.empty levels) D hm hC hs hl hf

theorem inductionChildren_beta (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C s l f p : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hs : Γ.JEqB levels ∅ (S.indexedStepType n C) s s)
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hp : Γ.JEqB levels ∅ (S.positions.lst l) p p) :
    Γ.JEqB levels ∅ ((S.inductionMotive n C).lst (.app f p))
      (.app (Tm.recChildren S.totalShape S.positions (S.inductionMotive n C) (S.inductionStep n C s) l f) p)
      (.wrec S.totalShape S.positions (S.inductionMotive n C) (S.inductionStep n C s) (.app f p)) :=
  inductionChildren_beta_of_hypotheses (StructuralTheory.empty levels) D hm hC hs hl hf hp

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
  rawInduction_source_beta_of_hypotheses (StructuralTheory.empty levels) D hm hC hs hl hf hc

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
