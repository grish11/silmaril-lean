module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Induction.RawStep.Defs
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.DependentStep

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

variable {H : Set Jdg} {S : Description} {levels : RuleBudget} {n m : ℕ} {Γ : Ctx}

private theorem sourcePosition_open {k : ℕ} (S : Description) (l : Tm (k + 1)) (x : String) :
    (S.position.bsubst (Fin.cases (.snd l) (fun _ => .fst l))).open x =
    S.position.bsubst (Fin.cases (.snd (l.open x)) (fun _ => .fst (l.open x))) := by
  rw [Tm.open_bsubst]
  congr 1
  funext j
  cases j using Fin.cases <;> simp only [Fin.cases_zero, Fin.cases_succ, Tm.open]

private theorem sourcePosition_lst {k : ℕ} (S : Description) (l : Tm (k + 1)) (v : Tm 0) :
    (S.position.bsubst (Fin.cases (.snd l) (fun _ => .fst l))).lst v =
    S.position.bsubst (Fin.cases (.snd (l.lst v)) (fun _ => .fst (l.lst v))) := by
  rw [Tm.lst_bsubst]
  congr 1
  funext j
  cases j using Fin.cases <;> simp only [Fin.cases_zero, Fin.cases_succ, Tm.lst]

private theorem lastCases_first {α : Sort _} {k : ℕ} (a : α) (f : Fin (k + 1) → α) :
    Fin.lastCases a f (0 : Fin (k + 2)) = f 0 := Fin.lastCases_castSucc 0

private theorem lastCases_zero {α : Sort _} (a : α) (f : Fin 0 → α) :
    Fin.lastCases a f (0 : Fin 1) = a := Fin.lastCases_last

private theorem wk0_open {k : ℕ} (t : Tm (k + 1)) (x : String) :
    t.wk0.open x = (t.open x).wk0 := Tm.open_wkn t x 0 (Nat.zero_le k)

private theorem wk0_lst {k : ℕ} (t : Tm (k + 1)) (v : Tm 0) :
    t.wk0.lst v = (t.lst v).wk0 := Tm.lst_wkn t v 0 (Nat.zero_le k)

theorem reifyChildren_open {k : ℕ} (S : Description) (l f c : Tm (k + 1)) (x : String) :
    (S.reifyChildren l f c).open x = S.reifyChildren (l.open x) (f.open x) (c.open x) := by
  simp only [Description.reifyChildren, Tm.open, sourcePosition_open,
    wk0_open, lastCases_first]

theorem reifyChildren_lst {k : ℕ} (S : Description) (l f c : Tm (k + 1)) (v : Tm 0) :
    (S.reifyChildren l f c).lst v = S.reifyChildren (l.lst v) (f.lst v) (c.lst v) := by
  simp only [Description.reifyChildren, Tm.lst, sourcePosition_lst,
    wk0_lst, lastCases_first]

theorem reifyHypotheses_open {k : ℕ} (S : Description) (l c r : Tm (k + 1)) (x : String) :
    (S.reifyHypotheses l c r).open x = S.reifyHypotheses (l.open x) (c.open x) (r.open x) := by
  simp only [Description.reifyHypotheses, Tm.open, sourcePosition_open,
    wk0_open, lastCases_first]

theorem reifyHypotheses_lst {k : ℕ} (S : Description) (l c r : Tm (k + 1)) (v : Tm 0) :
    (S.reifyHypotheses l c r).lst v = S.reifyHypotheses (l.lst v) (c.lst v) (r.lst v) := by
  simp only [Description.reifyHypotheses, Tm.lst, sourcePosition_lst,
    wk0_lst, lastCases_first]

theorem sourceStepValue_open {k : ℕ} (S : Description) (s l f c r : Tm (k + 1)) (x : String) :
    (S.sourceStepValue s l f c r).open x =
      S.sourceStepValue (s.open x) (l.open x) (f.open x) (c.open x) (r.open x) := by
  simp only [Description.sourceStepValue, Tm.open, reifyChildren_open, reifyHypotheses_open]

theorem sourceStepValue_lst {k : ℕ} (S : Description) (s l f c r : Tm (k + 1)) (v : Tm 0) :
    (S.sourceStepValue s l f c r).lst v =
      S.sourceStepValue (s.lst v) (l.lst v) (f.lst v) (c.lst v) (r.lst v) := by
  simp only [Description.sourceStepValue, Tm.lst, reifyChildren_lst, reifyHypotheses_lst]

theorem coherentStep_open {k : ℕ} (S : Description) (n : ℕ) (s l f r : Tm (k + 1)) (x : String) :
    (S.coherentStep n s l f r).open x =
      S.coherentStep n (s.open x) (l.open x) (f.open x) (r.open x) := by
  simp only [Description.coherentStep, Tm.open, coherence_open, Tm.closed_castLE_open,
    Tm.open_castLE S.positions (Nat.succ_le_succ (Nat.zero_le k)), sourceStepValue_open,
    wk0_open, lastCases_first]

theorem coherentStep_lst {k : ℕ} (S : Description) (n : ℕ) (s l f r : Tm (k + 1)) (v : Tm 0) :
    (S.coherentStep n s l f r).lst v =
      S.coherentStep n (s.lst v) (l.lst v) (f.lst v) (r.lst v) := by
  simp only [Description.coherentStep, Tm.lst, coherence_lst, Tm.closed_castLE_lst,
    Tm.lst_castLE S.positions (Nat.succ_le_succ (Nat.zero_le k)), sourceStepValue_lst,
    wk0_lst, lastCases_first]

private theorem coherentStep_body_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C s l f r : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hs : Γ.JEqB levels H (S.indexedStepType n C) s s)
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hr : Γ.JEqB levels H (.pi (S.positions.lst l)
      ((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0)))) r r) :
    ∀ c ∉ Γ.dv, (Γ.cons c (S.coherence n (.sup S.totalShape S.positions l f))).JEqB levels H
      ((.app (.app C.wk0 (S.root (Tm.sup S.totalShape S.positions l f).wk0))
        (S.canonical (Tm.sup S.totalShape S.positions l f).wk0 (.bv 0)) : Tm 1).open c)
      ((S.sourceStepValue s.wk0 l.wk0 f.wk0 (.bv 0) r.wk0).open c)
      ((S.sourceStepValue s.wk0 l.wk0 f.wk0 (.bv 0) r.wk0).open c) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have ht : Γ.JEqB levels H S.raw (.sup S.totalShape S.positions l f) (.sup S.totalShape S.positions l f) :=
    .sup hn (totalShape_formation D.toFormationData) (positions_formation_of_hypotheses hH D.toFormationData) hl hf
  have hcoh := coherence_formation_of_hypotheses hH D ht
  intro c hc
  have hctx : (Γ.cons c (S.coherence n (.sup S.totalShape S.positions l f))).JEqB levels H .unit .star .star :=
    .cons_ok hn D.context hc hcoh
  have dc := D.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hc _) hctx
  have hC' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hc hn hcoh hC
  have hs' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hc hn hcoh hs
  have hl' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hc hn hcoh hl
  have hf' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hc hn hcoh hf
  have hr' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hc hn hcoh hr
  have hcv : (Γ.cons c (S.coherence n (.sup S.totalShape S.positions l f))).JEqB levels H
      (S.coherence n (.sup S.totalShape S.positions l f)) (.fv c) (.fv c) := .var hctx (.here Γ c _)
  simpa only [Tm.open, Tm.closed_wk0_open, root_open, canonical_open, lastCases_zero,
    sourceStepValue_open, reifyChildren_open, reifyHypotheses_open, Description.sourceStepValue] using indexedStep_reified_apply_of_hypotheses hH dc hm hC' hs' hl' hf' hcv hr'

/-- The actual source-step body abstracts the original coherence witness in the canonical raw motive. -/
theorem coherentStep_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C s l f r : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hs : Γ.JEqB levels H (S.indexedStepType n C) s s)
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hr : Γ.JEqB levels H (.pi (S.positions.lst l)
      ((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0)))) r r) :
    Γ.JEqB levels H ((S.inductionMotive n C).lst (.sup S.totalShape S.positions l f))
      (S.coherentStep n s l f r) (S.coherentStep n s l f r) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hq : RuleBudget.Allows levels (max n m) := RuleBudget.Allows.max hn (by budget_omega)
  have ht : Γ.JEqB levels H S.raw (.sup S.totalShape S.positions l f) (.sup S.totalShape S.positions l f) :=
    .sup hn (totalShape_formation D.toFormationData) (positions_formation_of_hypotheses hH D.toFormationData) hl hf
  have hcoh := coherence_formation_of_hypotheses hH D ht
  have hbody := coherentStep_body_of_hypotheses hH D hm hC hs hl hf hr
  simpa only [inductionMotive_lst, Description.coherentStep, Tm.castLE_refl] using
    Ctx.JEqB.abs hq (Ctx.JEqB.cumul hq (Nat.le_max_left n m) hcoh)
      (fun c hc => Ctx.JEqB.cumul hq (Nat.le_max_right n m) (canonicalMotive_codomain_of_hypotheses hH D hm hC ht c hc)) hbody

private theorem lastCases_one {α : Sort _} {k : ℕ} (a : α) (f : Fin (k + 2) → α) :
    Fin.lastCases a f (1 : Fin (k + 3)) = f 1 := Fin.lastCases_castSucc 1

private theorem lastCases_top_one {α : Sort _} (a : α) (f : Fin 1 → α) :
    Fin.lastCases a f (1 : Fin 2) = a := Fin.lastCases_last

private theorem lastCases_top_two {α : Sort _} (a : α) (f : Fin 2 → α) :
    Fin.lastCases a f (2 : Fin 3) = a := Fin.lastCases_last

theorem inductionStep_body_open (S : Description) (n : ℕ) (s : Tm 0) (l f r : String) :
    (((S.coherentStep n (s.castLE (Nat.zero_le 3)) (.bv 2) (.bv 1) (.bv 0)).open l).open f).open r =
      S.coherentStep n s (.fv l) (.fv f) (.fv r) := by
  simp only [coherentStep_open, Tm.closed_castLE_open, Tm.castLE_refl, Tm.open,
    lastCases_top_two, lastCases_top_one, lastCases_one, lastCases_first, lastCases_zero]

/-- Applying the abstracted coherence witness beta-reduces to the actual original source-step application. -/
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
      (.app (S.coherentStep n s l f r) c) (S.sourceStepValue s l f c r) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hq : RuleBudget.Allows levels (max n m) := RuleBudget.Allows.max hn (by budget_omega)
  have ht : Γ.JEqB levels H S.raw (.sup S.totalShape S.positions l f) (.sup S.totalShape S.positions l f) :=
    .sup hn (totalShape_formation D.toFormationData) (positions_formation_of_hypotheses hH D.toFormationData) hl hf
  have hcoh := coherence_formation_of_hypotheses hH D ht
  simpa only [Description.coherentStep, Tm.castLE_refl, Tm.lst, Tm.closed_wk0_lst,
    root_lst, canonical_lst, sourceStepValue_lst, reifyChildren_lst, reifyHypotheses_lst,
    Description.sourceStepValue, lastCases_zero] using
    Ctx.JEqB.beta_app hq (Ctx.JEqB.cumul hq (Nat.le_max_left n m) hcoh)
      (fun c hc => Ctx.JEqB.cumul hq (Nat.le_max_right n m) (canonicalMotive_codomain_of_hypotheses hH D hm hC ht c hc))
      (coherentStep_body_of_hypotheses hH D hm hC hs hl hf hr) hc

private theorem lst_fv {k : ℕ} (B : Tm (k + 1)) (x : String) : B.lst (.fv x) = B.open x := by
  rw [Tm.lst_eq_bsubst, Tm.open_eq_bsubst]
  simp only [Tm.castLE]

private theorem inductionStep_body_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C s : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hs : Γ.JEqB levels H (S.indexedStepType n C) s s) :
    ∀ l ∉ Γ.dv, ∀ f ∉ insert l Γ.dv, ∀ r ∉ insert f (insert l Γ.dv),
      (((Γ.cons l S.totalShape).cons f (.arr (S.positions.open l) S.raw)).cons r
        (.pi (S.positions.open l) ((S.inductionMotive n C).bsubst (fun _ => .app (Tm.fv f).wk0 (.bv 0))))).JEqB levels H
        ((S.inductionMotive n C).lst (.sup S.totalShape S.positions (.fv l) (.fv f)))
        ((((S.coherentStep n (s.castLE (Nat.zero_le 3)) (.bv 2) (.bv 1) (.bv 0)).open l).open f).open r)
        ((((S.coherentStep n (s.castLE (Nat.zero_le 3)) (.bv 2) (.bv 1) (.bv 0)).open l).open f).open r) := by
  intro l hl f hf r hr
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hq : RuleBudget.Allows levels (max n m) := RuleBudget.Allows.max hn (by budget_omega)
  have hq' : RuleBudget.Allows levels (max n m + 1) := by have := D.bound; budget_omega
  have hA : Γ.JEqB levels H (.univ n) S.totalShape S.totalShape := totalShape_formation D.toFormationData
  have hctx1 : (Γ.cons l S.totalShape).JEqB levels H .unit .star .star := .cons_ok hn D.context hl hA
  have d1 : IndexedFormationData S levels n (Γ.cons l S.totalShape) H := D.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hl S.totalShape) hctx1
  have hC1 : (Γ.cons l S.totalShape).JEqB levels H (S.motiveType n m) C C := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hl hn hA hC
  have hs1 : (Γ.cons l S.totalShape).JEqB levels H (S.indexedStepType n C) s s := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hl hn hA hs
  have hl1 : (Γ.cons l S.totalShape).JEqB levels H S.totalShape (.fv l) (.fv l) := .var hctx1 (.here Γ l _)
  have hP : (Γ.cons l S.totalShape).JEqB levels H (.univ n) (S.positions.open l) (S.positions.open l) :=
    positions_formation_of_hypotheses hH D.toFormationData l hl
  have hF : (Γ.cons l S.totalShape).JEqB levels H (.univ n)
      (.arr (S.positions.open l) S.raw) (.arr (S.positions.open l) S.raw) := Ctx.JEqB.arrow_formation_of_hypotheses hH.weakening hn hctx1 hP (raw_formation_of_hypotheses hH d1.toFormationData)
  have hfresh : f ∉ (Γ.cons l S.totalShape).dv := by simpa only [Ctx.dv] using hf
  have hctx2 : ((Γ.cons l S.totalShape).cons f (.arr (S.positions.open l) S.raw)).JEqB levels H .unit .star .star :=
    .cons_ok hn hctx1 hfresh hF
  have d2 : IndexedFormationData S levels n
      ((Γ.cons l S.totalShape).cons f (.arr (S.positions.open l) S.raw)) H := d1.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hfresh _) hctx2
  have hC2 := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening hctx1 hfresh hn hF hC1
  have hs2 := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening hctx1 hfresh hn hF hs1
  have hl2 := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening hctx1 hfresh hn hF hl1
  have hf2 : ((Γ.cons l S.totalShape).cons f (.arr (S.positions.open l) S.raw)).JEqB levels H
      (.arr (S.positions.open l) S.raw) (.fv f) (.fv f) := .var hctx2 (.here _ f _)
  have hP2 := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening hctx1 hfresh hn hF hP
  have hIH := Ctx.JEqB.dependentIH_formation_of_hypotheses hH hq' hctx2
    (Ctx.JEqB.cumul hq (Nat.le_max_left n m) (raw_formation_of_hypotheses hH d2.toFormationData))
    (Ctx.JEqB.cumul hq (Nat.le_max_left n m) hP2) hf2 (inductionMotive_formation_of_hypotheses hH d2 hm hC2)
  have hrFresh : r ∉ ((Γ.cons l S.totalShape).cons f (.arr (S.positions.open l) S.raw)).dv := by
    simpa only [Ctx.dv] using hr
  have hctx3 : (((Γ.cons l S.totalShape).cons f (.arr (S.positions.open l) S.raw)).cons r
      (.pi (S.positions.open l) ((S.inductionMotive n C).bsubst (fun _ => .app (Tm.fv f).wk0 (.bv 0))))).JEqB levels H
      .unit .star .star := .cons_ok hq hctx2 hrFresh hIH
  have d3 := d2.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hrFresh _) hctx3
  have hC3 := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening hctx2 hrFresh hq hIH hC2
  have hs3 := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening hctx2 hrFresh hq hIH hs2
  have hl3 := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening hctx2 hrFresh hq hIH hl2
  have hf3 := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening hctx2 hrFresh hq hIH hf2
  have hr3 : (((Γ.cons l S.totalShape).cons f (.arr (S.positions.open l) S.raw)).cons r
      (.pi (S.positions.open l) ((S.inductionMotive n C).bsubst (fun _ => .app (Tm.fv f).wk0 (.bv 0))))).JEqB levels H
      (.pi (S.positions.lst (.fv l)) ((S.inductionMotive n C).bsubst (fun _ => .app (Tm.fv f).wk0 (.bv 0))))
      (.fv r) (.fv r) := by
    simpa only [lst_fv] using Ctx.JEqB.var hctx3 (Ctx.Lookup.here _ r _)
  simpa only [inductionStep_body_open] using coherentStep_typing_of_hypotheses hH d3 hm hC3 hs3 hl3
    (by simpa only [lst_fv] using hf3) hr3

/-- Synthesize the actual ordinary W step from the supplied original indexed dependent step term. -/
theorem inductionStep_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C s : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hs : Γ.JEqB levels H (S.indexedStepType n C) s s) :
    Γ.JEqB levels H (Tm.wStepType S.totalShape S.positions (S.inductionMotive n C))
      (S.inductionStep n C s) (S.inductionStep n C s) := by
  have hq : RuleBudget.Allows levels (max n m) := RuleBudget.Allows.max (by have := D.bound; budget_omega) (by budget_omega)
  have hq' : RuleBudget.Allows levels (max n m + 1) := by have := D.bound; budget_omega
  simpa only [Description.inductionStep, Description.raw] using Ctx.JEqB.dependentStep_typing_of_hypotheses hH hq' D.context
    (Ctx.JEqB.cumul hq (Nat.le_max_left n m) (totalShape_formation D.toFormationData))
    (fun l hl => Ctx.JEqB.cumul hq (Nat.le_max_left n m) (positions_formation_of_hypotheses hH D.toFormationData l hl))
    (inductionMotive_formation_of_hypotheses hH D hm hC) (inductionStep_body_typing_of_hypotheses hH D hm hC hs)

/-- Generic dependent elimination from the exact original indexed-W encoding and actual source step. -/
theorem indexedInduction_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C s i t : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hs : Γ.JEqB levels H (S.indexedStepType n C) s s)
    (hi : Γ.JEqB levels H S.index i i) (ht : Γ.JEqB levels H (S.fibre n i) t t) :
    Γ.JEqB levels H (.app (.app C i) t)
      (S.indexedInduction n C s t) (S.indexedInduction n C s t) :=
  rawInduction_typing_of_hypotheses hH D hm hC (inductionStep_typing_of_hypotheses hH D hm hC hs) hi ht

private theorem inductionStep_body_lst (S : Description) (n : ℕ) (s l f r : Tm 0) :
    (((S.coherentStep n (s.castLE (Nat.zero_le 3)) (.bv 2) (.bv 1) (.bv 0)).lst l).lst f).lst r =
      S.coherentStep n s l f r := by
  simp only [coherentStep_lst, Tm.closed_castLE_lst, Tm.castLE_refl, Tm.lst,
    lastCases_top_two, lastCases_top_one, lastCases_one, lastCases_first, lastCases_zero]

/-- All three ordinary W-step applications beta-reduce to the actual coherence abstraction. -/
theorem inductionStep_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C s l f r : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hs : Γ.JEqB levels H (S.indexedStepType n C) s s)
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hr : Γ.JEqB levels H (.pi (S.positions.lst l)
      ((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0)))) r r) :
    Γ.JEqB levels H ((S.inductionMotive n C).lst (.sup S.totalShape S.positions l f))
      (.app (.app (.app (S.inductionStep n C s) l) f) r) (S.coherentStep n s l f r) := by
  have hq : RuleBudget.Allows levels (max n m) := RuleBudget.Allows.max (by have := D.bound; budget_omega) (by budget_omega)
  have hq' : RuleBudget.Allows levels (max n m + 1) := by have := D.bound; budget_omega
  simpa only [Description.inductionStep, Description.raw, inductionStep_body_lst] using
    Ctx.JEqB.dependentStep_beta_of_hypotheses hH hq' D.context
      (Ctx.JEqB.cumul hq (Nat.le_max_left n m) (totalShape_formation D.toFormationData))
      (fun l hl => Ctx.JEqB.cumul hq (Nat.le_max_left n m) (positions_formation_of_hypotheses hH D.toFormationData l hl))
      (inductionMotive_formation_of_hypotheses hH D hm hC) (inductionStep_body_typing_of_hypotheses hH D hm hC hs) hl hf hr


theorem coherentStep_typing (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C s l f r : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hs : Γ.JEqB levels ∅ (S.indexedStepType n C) s s)
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hr : Γ.JEqB levels ∅ (.pi (S.positions.lst l)
      ((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0)))) r r) :
    Γ.JEqB levels ∅ ((S.inductionMotive n C).lst (.sup S.totalShape S.positions l f))
      (S.coherentStep n s l f r) (S.coherentStep n s l f r) :=
  coherentStep_typing_of_hypotheses (StructuralTheory.empty levels) D hm hC hs hl hf hr

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
  coherentStep_beta_of_hypotheses (StructuralTheory.empty levels) D hm hC hs hl hf hc hr

theorem inductionStep_typing (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C s : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hs : Γ.JEqB levels ∅ (S.indexedStepType n C) s s) :
    Γ.JEqB levels ∅ (Tm.wStepType S.totalShape S.positions (S.inductionMotive n C))
      (S.inductionStep n C s) (S.inductionStep n C s) :=
  inductionStep_typing_of_hypotheses (StructuralTheory.empty levels) D hm hC hs

theorem indexedInduction_typing (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C s i t : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hs : Γ.JEqB levels ∅ (S.indexedStepType n C) s s)
    (hi : Γ.JEqB levels ∅ S.index i i) (ht : Γ.JEqB levels ∅ (S.fibre n i) t t) :
    Γ.JEqB levels ∅ (.app (.app C i) t)
      (S.indexedInduction n C s t) (S.indexedInduction n C s t) :=
  indexedInduction_typing_of_hypotheses (StructuralTheory.empty levels) D hm hC hs hi ht

theorem inductionStep_beta (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C s l f r : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hs : Γ.JEqB levels ∅ (S.indexedStepType n C) s s)
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hr : Γ.JEqB levels ∅ (.pi (S.positions.lst l)
      ((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0)))) r r) :
    Γ.JEqB levels ∅ ((S.inductionMotive n C).lst (.sup S.totalShape S.positions l f))
      (.app (.app (.app (S.inductionStep n C s) l) f) r) (S.coherentStep n s l f r) :=
  inductionStep_beta_of_hypotheses (StructuralTheory.empty levels) D hm hC hs hl hf hr

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
