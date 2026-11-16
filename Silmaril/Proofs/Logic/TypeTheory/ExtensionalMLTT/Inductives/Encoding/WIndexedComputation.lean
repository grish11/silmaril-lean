module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Induction.Computation.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Induction.Computation.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

variable {H : Set Jdg} {S : Description} {levels : RuleBudget} {n m : ℕ} {Γ : Ctx}

/-- Tagged source labels compute to their actual original index and shape arguments. -/
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
        (S.reifyHypotheses (.pair i a) c r)) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hl : Γ.JEqB levels H S.totalShape (.pair i a) (.pair i a) := .pair hn D.index D.shape hi ha
  have hiEq : Γ.JEqB levels H S.index (.fst (.pair i a)) i := .beta_fst hn D.index D.shape hi ha
  have haEq : Γ.JEqB levels H (S.shape.lst (.fst (.pair i a))) (.snd (.pair i a)) a :=
    .conv hn (shapeAt_congr_of_hypotheses hH D.toFormationData hiEq.symm) (Ctx.JEqB.beta_snd hn D.index D.shape hi ha)
  have happ := indexedStep_apply_congr_of_hypotheses hH D hm hC hs hiEq haEq
    (reifyChildren_source_typing_of_hypotheses hH D hl hf hc) (reifyHypotheses_source_typing_of_hypotheses hH D hm hC hl hf hc hr)
  exact .conv (by budget_omega) (motive_reifiedNode_eq_of_hypotheses hH D hm hC hl hf hc) happ

theorem reifySourceChildren_recovery_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i a g : Tm 0}
    (hi : Γ.JEqB levels H S.index i i)
    (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hg : Γ.JEqB levels H (.pi (S.positionAt i a) (S.childFibres n (.pair i a))) g g) :
    let P := S.positionAt i a
    let L : Tm 0 := .pair i a
    let F : Tm 0 := .abs P (.fst (.app g.wk0 (.bv 0)))
    let c : Tm 0 := .abs P (.snd (.app g.wk0 (.bv 0)))
    Γ.JEqB levels H (.pi P (S.childFibres n L)) (S.reifyChildren L F c) g := by
  intro P L F c
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hA := positionAt_formation_of_hypotheses hH D.toFormationData hi ha
  have hl : Γ.JEqB levels H S.totalShape L L :=
    .pair hn D.index D.shape hi ha
  have hP : Γ.JEqB levels H (.univ n) P (S.positions.lst L) :=
    (positions_tagged_beta_of_hypotheses hH D.toFormationData hi ha).symm
  have hF := eraseChildren_typing_of_hypotheses hH D hl hA hP hg
  have hpos : Γ.JEqB levels H (.univ n) (S.positions.lst L) (S.positions.lst L) := hP.symm.trans hP
  have hFpos : Γ.JEqB levels H (.arr (S.positions.lst L) S.raw) F F := by
    have ht := Ctx.JEqB.pi hn hP (Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn D.context hA (raw_formation_of_hypotheses hH D.toFormationData))
    exact .conv hn ht hF
  have hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions L F)) c c := by
    have h := node_coherence_beta_of_hypotheses hH D hi ha hg
    exact h.symm.trans h
  have hleft := reifyChildren_typing_of_hypotheses hH D hl hFpos hc
  have hleftP : Γ.JEqB levels H (.pi P (S.childFibres n L))
      (S.reifyChildren L F c) (S.reifyChildren L F c) :=
    .conv hn (.pi hn hP.symm (childFibres_formation_of_hypotheses hH D hl hpos hpos)) hleft
  apply Ctx.JEqB.pi_ext (L := Γ.dv) hn hA (childFibres_formation_of_hypotheses hH D hl hA hP) hleftP hg
  intro p hp
  have hctx : (Γ.cons p P).JEqB levels H .unit .star .star := .cons_ok hn D.context hp hA
  have dp := D.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hp P) hctx
  have hl' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hA hl
  have hA' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hA hA
  have hP' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hA hP
  have hg' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hA hg
  have hF' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hA hFpos
  have hc' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hA hc
  have hpA : (Γ.cons p P).JEqB levels H P (.fv p) (.fv p) := .var hctx (.here ..)
  have hpP : (Γ.cons p P).JEqB levels H (S.positions.lst L) (.fv p) (.fv p) := .conv hn hP' hpA
  have hnext := childIndexAt_typing_of_hypotheses hH dp hl' hpP
  have hr := childValue_typing_of_hypotheses hH dp hl' hA' hP' hg' hpA
  have hlchild := childValue_typing_of_hypotheses hH dp hl'
    (Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hA hpos)
    (Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hA hpos)
    (Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hA hleft) hpP
  have hfst := reifyChildren_fst_beta_of_hypotheses hH dp hl' hF' hc' hpP
  have hfstg := eraseChildren_beta_of_hypotheses hH dp hl' hA' hP' hg' hpA
  have hsnd := reifyChildren_snd_beta_of_hypotheses hH dp hl' hF' hc' hpP
  have hsndg := witnessChildren_beta_of_hypotheses hH dp hl' hA' hP' hg' hpA
  have htail := fibreTail_congr_of_hypotheses hH dp hnext hfst.symm
  have hsecond := Ctx.JEqB.conv hn htail (hsnd.trans hsndg)
  have heq := Ctx.JEqB.sigma_ext hn (raw_formation_of_hypotheses hH dp.toFormationData)
    (fibreTail_formation_of_hypotheses hH dp hnext) hlchild hr (hfst.trans hfstg) (by simpa only [fibreTail_lst] using hsecond)
  simpa only [childFibres_open, Description.fibre] using heq

private theorem erasedSource_data_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i a g : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hg : Γ.JEqB levels H (.pi (S.positionAt i a) (S.childFibres n (.pair i a))) g g) :
    let F : Tm 0 := .abs (S.positionAt i a) (.fst (.app g.wk0 (.bv 0)))
    let c : Tm 0 := .abs (S.positionAt i a) (.snd (.app g.wk0 (.bv 0)))
    Γ.JEqB levels H (.arr (S.positions.lst (.pair i a)) S.raw) F F ∧
    Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions (.pair i a) F)) c c := by
  intro F c
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hl : Γ.JEqB levels H S.totalShape (.pair i a) (.pair i a) := .pair hn D.index D.shape hi ha
  have hP := positionAt_formation_of_hypotheses hH D.toFormationData hi ha
  have hAP := (positions_tagged_beta_of_hypotheses hH D.toFormationData hi ha).symm
  have hF := eraseChildren_typing_of_hypotheses hH D hl hP hAP hg
  have hArrow : Γ.JEqB levels H (.univ n)
      (.arr (S.positionAt i a) S.raw) (.arr (S.positions.lst (.pair i a)) S.raw) :=
    .pi hn hAP (Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn D.context hP (raw_formation_of_hypotheses hH D.toFormationData))
  have hc := node_coherence_beta_of_hypotheses hH D hi ha hg
  exact ⟨Ctx.JEqB.conv hn hArrow hF, hc.symm.trans hc⟩

private theorem sourceNode_motive_eq_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C i a g : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hg : Γ.JEqB levels H (.pi (S.positionAt i a) (S.childFibres n (.pair i a))) g g) :
    let F : Tm 0 := .abs (S.positionAt i a) (.fst (.app g.wk0 (.bv 0)))
    let c : Tm 0 := .abs (S.positionAt i a) (.snd (.app g.wk0 (.bv 0)))
    Γ.JEqB levels H (.univ m) (.app (.app C i) (S.node i a g))
      (.app (.app C (S.root (.sup S.totalShape S.positions (.pair i a) F)))
        (S.canonical (.sup S.totalShape S.positions (.pair i a) F) c)) := by
  intro F c
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hnode := node_typing_of_hypotheses hH D hi ha hg
  have hraw := node_fst_beta_of_hypotheses hH D hi ha hg
  have hcoh := node_coherence_beta_of_hypotheses hH D hi ha hg
  have harg := Ctx.JEqB.conv hn (coherence_congr_of_hypotheses hH D hraw.symm) hcoh
  have hcanonical := canonical_congr_of_hypotheses hH D hraw harg
  have hmotive := motive_congr_of_hypotheses hH D hm hC (root_congr_of_hypotheses hH D.toFormationData hraw) hcanonical
  exact (motive_reconstruction_of_hypotheses hH D hm hC hi hnode).trans hmotive

/-- Original indexed-node recursion computes through its actual raw and coherence projections. -/
theorem indexedInduction_node_reified_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C s i a g : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hs : Γ.JEqB levels H (S.indexedStepType n C) s s)
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hg : Γ.JEqB levels H (.pi (S.positionAt i a) (S.childFibres n (.pair i a))) g g) :
    let F : Tm 0 := .abs (S.positionAt i a) (.fst (.app g.wk0 (.bv 0)))
    let c : Tm 0 := .abs (S.positionAt i a) (.snd (.app g.wk0 (.bv 0)))
    let R := Tm.recChildren S.totalShape S.positions (S.inductionMotive n C) (S.inductionStep n C s) (.pair i a) F
    Γ.JEqB levels H (.app (.app C i) (S.node i a g))
      (S.indexedInduction n C s (S.node i a g)) (S.sourceStepValue s (.pair i a) F c R) := by
  intro F c R
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hq : RuleBudget.Allows levels (max n m) := RuleBudget.Allows.max hn (by budget_omega)
  have hl : Γ.JEqB levels H S.totalShape (.pair i a) (.pair i a) := .pair hn D.index D.shape hi ha
  obtain ⟨hF, hc⟩ := erasedSource_data_of_hypotheses hH D hi ha hg
  have hnode := node_typing_of_hypotheses hH D hi ha hg
  have hraw : Γ.JEqB levels H S.raw (.fst (S.node i a g)) (.sup S.totalShape S.positions (.pair i a) F) :=
    node_fst_beta_of_hypotheses hH D hi ha hg
  have hcoh : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions (.pair i a) F))
      (.snd (.snd (S.node i a g))) c := node_coherence_beta_of_hypotheses hH D hi ha hg
  have harg := Ctx.JEqB.conv hn (coherence_congr_of_hypotheses hH D hraw.symm) hcoh
  have hrec := Ctx.JEqB.wrec hn hq (totalShape_formation D.toFormationData) (positions_formation_of_hypotheses hH D.toFormationData)
    (inductionMotive_formation_of_hypotheses hH D hm hC) (inductionStep_typing_of_hypotheses hH D hm hC hs) hraw
  have happ := canonicalMotive_apply_congr_of_hypotheses hH D hm hC hi hnode hrec harg
  have htransport := sourceNode_motive_eq_of_hypotheses hH D hm hC hi ha hg
  have hbeta := Ctx.JEqB.conv (by budget_omega) htransport.symm (rawInduction_source_beta_of_hypotheses hH D hm hC hs hl hF hc)
  exact happ.trans hbeta

private theorem lastCases_zero {α : Sort _} (a : α) (f : Fin 0 → α) :
    Fin.lastCases a f (0 : Fin 1) = a := Fin.lastCases_last

private theorem wkn_one_open (B : Tm 1) (p : String) : (B.wkn 1).open p = B := by
  rw [Tm.wkn_past B 1 (Nat.le_refl 1)]
  simpa only [Tm.castLE_refl] using Tm.open_castLE B (Nat.le_refl 1) p

private theorem wkn_one_lst (B : Tm 1) (p : Tm 0) : (B.wkn 1).lst p = B := by
  rw [Tm.wkn_past B 1 (Nat.le_refl 1)]
  simpa only [Tm.castLE_refl] using Tm.lst_castLE B (Nat.le_refl 1) p

theorem indexedHypothesisBody_open (S : Description) (n : ℕ) (C s g : Tm 0) (p : String) :
    (S.indexedHypothesisBody n C s g).open p = S.indexedInduction n C s (.app g (.fv p)) := by
  simp only [Description.indexedHypothesisBody, Description.indexedInduction, Tm.open,
    Tm.closed_wk0_open, wkn_one_open, lastCases_zero]

theorem indexedHypothesisBody_lst (S : Description) (n : ℕ) (C s g p : Tm 0) :
    (S.indexedHypothesisBody n C s g).lst p = S.indexedInduction n C s (.app g p) := by
  simp only [Description.indexedHypothesisBody, Description.indexedInduction, Tm.lst,
    Tm.closed_wk0_lst, wkn_one_lst, lastCases_zero, Tm.castLE_refl]

private theorem indexedHypotheses_data_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C s i a g : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hs : Γ.JEqB levels H (S.indexedStepType n C) s s)
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hg : Γ.JEqB levels H (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g) :
    ∀ p ∉ Γ.dv, (Γ.cons p (S.positionAt i a)).JEqB levels H (.univ m)
      ((.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0)) : Tm 1).open p)
      ((.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0)) : Tm 1).open p) ∧
    (Γ.cons p (S.positionAt i a)).JEqB levels H
      ((.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0)) : Tm 1).open p)
      ((S.indexedHypothesisBody n C s g).open p) ((S.indexedHypothesisBody n C s g).open p) := by
  intro p hp
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hP := positionAt_formation_of_hypotheses hH D.toFormationData hi ha
  have hctx : (Γ.cons p (S.positionAt i a)).JEqB levels H .unit .star .star := .cons_ok hn D.context hp hP
  have dp := D.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hp _) hctx
  have hC' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hC
  have hs' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hs
  have hi' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hi
  have ha' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP ha
  have hg' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hg
  have hp' : (Γ.cons p (S.positionAt i a)).JEqB levels H (S.positionAt i a) (.fv p) (.fv p) :=
    .var hctx (.here ..)
  have hnext := nextDirect_typing_of_hypotheses hH dp hi' ha' hp'
  have hchild := sourceChild_value_of_hypotheses hH dp hi' ha' hg' hp'
  have hcall := indexedInduction_typing_of_hypotheses hH dp hm hC' hs' hnext hchild
  exact ⟨sourceIH_codomain_of_hypotheses hH D hm hC hi ha hg p hp, by
    simpa only [Tm.open, Tm.closed_wk0_open, sourceNext_open, lastCases_zero, indexedHypothesisBody_open] using hcall⟩

/-- The normalized source IH function is typed using actual recursive calls on full original children. -/
theorem indexedHypotheses_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C s i a g : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hs : Γ.JEqB levels H (S.indexedStepType n C) s s)
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hg : Γ.JEqB levels H (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g) :
    Γ.JEqB levels H (.pi (S.positionAt i a)
      (.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0))))
      (S.indexedHypotheses n C s i a g) (S.indexedHypotheses n C s i a g) := by
  have hq : RuleBudget.Allows levels (max n m) := RuleBudget.Allows.max (by have := D.bound; budget_omega) (by budget_omega)
  have hdata := indexedHypotheses_data_of_hypotheses hH D hm hC hs hi ha hg
  exact .abs hq (Ctx.JEqB.cumul hq (Nat.le_max_left n m) (positionAt_formation_of_hypotheses hH D.toFormationData hi ha))
    (fun p hp => Ctx.JEqB.cumul hq (Nat.le_max_right n m) (hdata p hp).1) (fun p hp => (hdata p hp).2)

/-- The normalized source IH function beta-reduces directly to original indexed elimination of a child. -/
theorem indexedHypotheses_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C s i a g p : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hs : Γ.JEqB levels H (S.indexedStepType n C) s s)
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hg : Γ.JEqB levels H (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g)
    (hp : Γ.JEqB levels H (S.positionAt i a) p p) :
    Γ.JEqB levels H
      (.app (.app C (S.next.bsubst (Fin.cases p (Fin.cases a (fun _ => i))))) (.app g p))
      (.app (S.indexedHypotheses n C s i a g) p) (S.indexedInduction n C s (.app g p)) := by
  have hq : RuleBudget.Allows levels (max n m) := RuleBudget.Allows.max (by have := D.bound; budget_omega) (by budget_omega)
  have hdata := indexedHypotheses_data_of_hypotheses hH D hm hC hs hi ha hg
  simpa only [Description.indexedHypotheses, Tm.lst, Tm.closed_wk0_lst, triple_lst_eq_bsubst,
    indexedHypothesisBody_lst, lastCases_zero, Tm.castLE_refl] using
    Ctx.JEqB.beta_app hq (Ctx.JEqB.cumul hq (Nat.le_max_left n m) (positionAt_formation_of_hypotheses hH D.toFormationData hi ha))
      (fun p hp => Ctx.JEqB.cumul hq (Nat.le_max_right n m) (hdata p hp).1) (fun p hp => (hdata p hp).2) hp

private theorem sourceIH_recoveryType_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C i a G g : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hGg : Γ.JEqB levels H (.pi (S.positionAt i a) (S.childFibres n (.pair i a))) G g) :
    Γ.JEqB levels H (.univ (max n m))
      (.pi (S.positions.lst (.pair i a))
        (.app (.app C.wk0 (S.childIndexAt (Tm.pair i a).wk0 (.bv 0))) (.app G.wk0 (.bv 0))))
      (.pi (S.positionAt i a) (.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0)))) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hq : RuleBudget.Allows levels (max n m) := RuleBudget.Allows.max hn (by budget_omega)
  have hl : Γ.JEqB levels H S.totalShape (.pair i a) (.pair i a) := .pair hn D.index D.shape hi ha
  have hpos : Γ.JEqB levels H (.univ n)
      (S.positions.lst (.pair i a)) (S.positions.lst (.pair i a)) := positions_instance_formation_of_hypotheses hH D.toFormationData hl
  apply Ctx.JEqB.pi (L := Γ.dv) hq (Ctx.JEqB.cumul hq (Nat.le_max_left n m) (positions_tagged_beta_of_hypotheses hH D.toFormationData hi ha))
  intro p hp
  have hctx : (Γ.cons p (S.positions.lst (.pair i a))).JEqB levels H .unit .star .star := .cons_ok hn D.context hp hpos
  have dp : IndexedFormationData S levels n (Γ.cons p (S.positions.lst (.pair i a))) H := D.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hp _) hctx
  have hC' : (Γ.cons p (S.positions.lst (.pair i a))).JEqB levels H (S.motiveType n m) C C := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hpos hC
  have hi' : (Γ.cons p (S.positions.lst (.pair i a))).JEqB levels H S.index i i := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hpos hi
  have ha' : (Γ.cons p (S.positions.lst (.pair i a))).JEqB levels H (S.shape.lst i) a a := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hpos ha
  have hl' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hpos hl
  have hGg' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hpos hGg
  have hP := positionAt_formation_of_hypotheses hH dp.toFormationData hi' ha'
  have hAP := (positions_tagged_beta_of_hypotheses hH dp.toFormationData hi' ha').symm
  have hpComp : (Γ.cons p (S.positions.lst (.pair i a))).JEqB levels H (S.positions.lst (.pair i a)) (.fv p) (.fv p) :=
    .var hctx (.here ..)
  have hpP := Ctx.JEqB.conv hn hAP.symm hpComp
  have hchildEq : (Γ.cons p (S.positions.lst (.pair i a))).JEqB levels H
      (S.fibre n (S.childIndexAt (.pair i a) (.fv p))) (.app G (.fv p)) (.app g (.fv p)) := by
    simpa only [childFibres_lst] using Ctx.JEqB.app hn hP (childFibres_formation_of_hypotheses hH dp hl' hP hAP) hGg' hpP
  have hnextEq := childIndexAt_tagged_beta_of_hypotheses hH dp hi' ha' hpP
  have htype := motive_congr_of_hypotheses hH dp hm hC' hnextEq hchildEq
  simpa only [Tm.open, Tm.closed_wk0_open, childIndexAt_open, sourceNext_open, lastCases_zero] using
    Ctx.JEqB.cumul hq (Nat.le_max_right n m) htype

/-- A reified recursive IH computes directly to indexed elimination of the original full child. -/
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
      (.app (S.reifyHypotheses (.pair i a) c R) p) (S.indexedInduction n C s (.app g p)) := by
  intro F c R
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hq : RuleBudget.Allows levels (max n m) := RuleBudget.Allows.max hn (by budget_omega)
  have hl : Γ.JEqB levels H S.totalShape (.pair i a) (.pair i a) := .pair hn D.index D.shape hi ha
  have hP := positionAt_formation_of_hypotheses hH D.toFormationData hi ha
  have hAP := (positions_tagged_beta_of_hypotheses hH D.toFormationData hi ha).symm
  obtain ⟨hF, hc⟩ := erasedSource_data_of_hypotheses hH D hi ha hg
  have hpComp := Ctx.JEqB.conv hn hAP hp
  have hpos := positions_instance_formation_of_hypotheses hH D.toFormationData hl
  have hfp : Γ.JEqB levels H S.raw (.app F p) (.app F p) :=
    Ctx.JEqB.arrow_application_of_hypotheses hH.weakening hn D.context hpos (raw_formation_of_hypotheses hH D.toFormationData) hF hpComp
  have herase := eraseChildren_beta_of_hypotheses hH D hl hP hAP hg hp
  have hwitness := witnessChildren_beta_of_hypotheses hH D hl hP hAP hg hp
  have hE : Γ.JEqB levels H (.univ n)
      (.id S.index (S.root (.app F p)) (S.childIndexAt (.pair i a) p))
      (.id S.index (S.root (.app F p)) (S.childIndexAt (.pair i a) p)) :=
    .id hn D.index (root_typing_of_hypotheses hH D.toFormationData hfp) (childIndexAt_typing_of_hypotheses hH D hl hpComp)
  have hcoh := coherence_formation_of_hypotheses hH D hfp
  have harg : Γ.JEqB levels H (S.coherence n (.app F p)) (.snd (.app c p)) (.snd (.snd (.app g p))) := by
    simpa only [Tm.closed_wk0_lst] using Ctx.JEqB.snd hn hE
      (Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn D.context hE hcoh) hwitness
  have hR := inductionChildren_typing_of_hypotheses hH D hm hC hs hl hF
  have hrbeta := inductionChildren_beta_of_hypotheses hH D hm hC hs hl hF hpComp
  have hrmove := Ctx.JEqB.wrec hn hq (totalShape_formation D.toFormationData) (positions_formation_of_hypotheses hH D.toFormationData)
    (inductionMotive_formation_of_hypotheses hH D hm hC) (inductionStep_typing_of_hypotheses hH D hm hC hs) herase
  have hr := Ctx.JEqB.conv hq (inductionMotive_congr_of_hypotheses hH D hm hC herase) (hrbeta.trans hrmove)
  have harg' := Ctx.JEqB.conv hn (coherence_congr_of_hypotheses hH D herase) harg
  have hgDirect := Ctx.JEqB.conv hn (childFibres_tagged_beta_of_hypotheses hH D hi ha) hg
  have hnext := nextDirect_typing_of_hypotheses hH D hi ha hp
  have hgp := sourceChild_value_of_hypotheses hH D hi ha hgDirect hp
  have hnormal := canonicalMotive_apply_congr_of_hypotheses hH D hm hC hnext hgp hr.symm harg'.symm
  have hsource := reifyHypotheses_beta_of_hypotheses hH D hm hC hl hF hc hR hpComp
  have hchildEq : Γ.JEqB levels H (S.fibre n (S.childIndexAt (.pair i a) p))
      (.app (S.reifyChildren (.pair i a) F c) p) (.app g p) := by
    simpa only [childFibres_lst] using Ctx.JEqB.app hn hP (childFibres_formation_of_hypotheses hH D hl hP hAP)
      (reifySourceChildren_recovery_of_hypotheses hH D hi ha hg) hp
  have htransport := motive_congr_of_hypotheses hH D hm hC (childIndexAt_tagged_beta_of_hypotheses hH D hi ha hp) hchildEq
  exact (Ctx.JEqB.conv (by budget_omega) htransport hsource).trans hnormal.symm

/-- The actual reified dependent IH function equals the normalized original indexed recursive-call function. -/
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
      (S.reifyHypotheses (.pair i a) c R) (S.indexedHypotheses n C s i a g) := by
  intro F c R
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hq : RuleBudget.Allows levels (max n m) := RuleBudget.Allows.max hn (by budget_omega)
  have hl : Γ.JEqB levels H S.totalShape (.pair i a) (.pair i a) := .pair hn D.index D.shape hi ha
  have hP := positionAt_formation_of_hypotheses hH D.toFormationData hi ha
  obtain ⟨hF, hc⟩ := erasedSource_data_of_hypotheses hH D hi ha hg
  have hR := inductionChildren_typing_of_hypotheses hH D hm hC hs hl hF
  have hactual := reifyHypotheses_typing_of_hypotheses hH D hm hC hl hF hc hR
  have htype := sourceIH_recoveryType_of_hypotheses hH D hm hC hi ha (reifySourceChildren_recovery_of_hypotheses hH D hi ha hg)
  have hleft := Ctx.JEqB.conv hq htype hactual
  have hgDirect := Ctx.JEqB.conv hn (childFibres_tagged_beta_of_hypotheses hH D hi ha) hg
  have hright := indexedHypotheses_typing_of_hypotheses hH D hm hC hs hi ha hgDirect
  apply Ctx.JEqB.pi_ext (L := Γ.dv) hq (Ctx.JEqB.cumul hq (Nat.le_max_left n m) hP)
    (fun p hp => Ctx.JEqB.cumul hq (Nat.le_max_right n m) (sourceIH_codomain_of_hypotheses hH D hm hC hi ha hgDirect p hp)) hleft hright
  intro p hp
  have hctx : (Γ.cons p (S.positionAt i a)).JEqB levels H .unit .star .star := .cons_ok hn D.context hp hP
  have dp := D.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hp _) hctx
  have hC' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hC
  have hs' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hs
  have hi' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hi
  have ha' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP ha
  have hg' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hg
  have hgDirect' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hgDirect
  have hp' : (Γ.cons p (S.positionAt i a)).JEqB levels H (S.positionAt i a) (.fv p) (.fv p) := .var hctx (.here ..)
  have hsource := reifySourceHypothesis_beta_of_hypotheses hH dp hm hC' hs' hi' ha' hg' hp'
  have hnormal := indexedHypotheses_beta_of_hypotheses hH dp hm hC' hs' hi' ha' hgDirect' hp'
  simpa only [Tm.open, Tm.closed_wk0_open, sourceNext_open, lastCases_zero] using hsource.trans hnormal.symm

/-- Normalized original indexed constructor computation, with the original children and actual indexed recursive IHs. -/
theorem indexedInduction_node_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C s i a g : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hs : Γ.JEqB levels H (S.indexedStepType n C) s s)
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hg : Γ.JEqB levels H (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g) :
    Γ.JEqB levels H (.app (.app C i) (S.node i a g))
      (S.indexedInduction n C s (S.node i a g))
      (.app (.app (.app (.app s i) a) g) (S.indexedHypotheses n C s i a g)) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hgOriginal := Ctx.JEqB.conv hn (childFibres_tagged_beta_of_hypotheses hH D hi ha).symm hg
  have hl : Γ.JEqB levels H S.totalShape (.pair i a) (.pair i a) := .pair hn D.index D.shape hi ha
  obtain ⟨hF, hc⟩ := erasedSource_data_of_hypotheses hH D hi ha hgOriginal
  have hR := inductionChildren_typing_of_hypotheses hH D hm hC hs hl hF
  have hnode := indexedInduction_node_reified_beta_of_hypotheses hH D hm hC hs hi ha hgOriginal
  have hlabelRaw := sourceStepValue_tagged_beta_of_hypotheses hH D hm hC hs hi ha hF hc hR
  have hlabel := Ctx.JEqB.conv (by budget_omega) (sourceNode_motive_eq_of_hypotheses hH D hm hC hi ha hgOriginal).symm hlabelRaw
  have hchildren := Ctx.JEqB.conv hn (childFibres_tagged_beta_of_hypotheses hH D hi ha)
    (reifySourceChildren_recovery_of_hypotheses hH D hi ha hgOriginal).symm
  have hIH := (reifySourceHypotheses_recovery_of_hypotheses hH D hm hC hs hi ha hgOriginal).symm
  have hsource := indexedStep_apply_congr_of_hypotheses hH D hm hC hs hi ha hchildren hIH
  exact hnode.trans (hlabel.trans hsource.symm)


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
  sourceStepValue_tagged_beta_of_hypotheses (StructuralTheory.empty levels) D hm hC hs hi ha hf hc hr

theorem reifySourceChildren_recovery (D : IndexedFormationData S levels n Γ) {i a g : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i)
    (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hg : Γ.JEqB levels ∅ (.pi (S.positionAt i a) (S.childFibres n (.pair i a))) g g) :
    let P := S.positionAt i a
    let L : Tm 0 := .pair i a
    let F : Tm 0 := .abs P (.fst (.app g.wk0 (.bv 0)))
    let c : Tm 0 := .abs P (.snd (.app g.wk0 (.bv 0)))
    Γ.JEqB levels ∅ (.pi P (S.childFibres n L)) (S.reifyChildren L F c) g :=
  reifySourceChildren_recovery_of_hypotheses (StructuralTheory.empty levels) D hi ha hg

theorem indexedHypotheses_typing (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C s i a g : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hs : Γ.JEqB levels ∅ (S.indexedStepType n C) s s)
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hg : Γ.JEqB levels ∅ (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g) :
    Γ.JEqB levels ∅ (.pi (S.positionAt i a)
      (.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0))))
      (S.indexedHypotheses n C s i a g) (S.indexedHypotheses n C s i a g) :=
  indexedHypotheses_typing_of_hypotheses (StructuralTheory.empty levels) D hm hC hs hi ha hg

theorem indexedHypotheses_beta (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C s i a g p : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hs : Γ.JEqB levels ∅ (S.indexedStepType n C) s s)
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hg : Γ.JEqB levels ∅ (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g)
    (hp : Γ.JEqB levels ∅ (S.positionAt i a) p p) :
    Γ.JEqB levels ∅
      (.app (.app C (S.next.bsubst (Fin.cases p (Fin.cases a (fun _ => i))))) (.app g p))
      (.app (S.indexedHypotheses n C s i a g) p) (S.indexedInduction n C s (.app g p)) :=
  indexedHypotheses_beta_of_hypotheses (StructuralTheory.empty levels) D hm hC hs hi ha hg hp

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
  reifySourceHypothesis_beta_of_hypotheses (StructuralTheory.empty levels) D hm hC hs hi ha hg hp

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
  reifySourceHypotheses_recovery_of_hypotheses (StructuralTheory.empty levels) D hm hC hs hi ha hg

theorem indexedInduction_node_beta (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C s i a g : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hs : Γ.JEqB levels ∅ (S.indexedStepType n C) s s)
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hg : Γ.JEqB levels ∅ (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g) :
    Γ.JEqB levels ∅ (.app (.app C i) (S.node i a g))
      (S.indexedInduction n C s (S.node i a g))
      (.app (.app (.app (.app s i) a) g) (S.indexedHypotheses n C s i a g)) :=
  indexedInduction_node_beta_of_hypotheses (StructuralTheory.empty levels) D hm hC hs hi ha hg

theorem indexedInduction_node_reified_beta (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C s i a g : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hs : Γ.JEqB levels ∅ (S.indexedStepType n C) s s)
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hg : Γ.JEqB levels ∅ (.pi (S.positionAt i a) (S.childFibres n (.pair i a))) g g) :
    let F : Tm 0 := .abs (S.positionAt i a) (.fst (.app g.wk0 (.bv 0)))
    let c : Tm 0 := .abs (S.positionAt i a) (.snd (.app g.wk0 (.bv 0)))
    let R := Tm.recChildren S.totalShape S.positions (S.inductionMotive n C) (S.inductionStep n C s) (.pair i a) F
    Γ.JEqB levels ∅ (.app (.app C i) (S.node i a g))
      (S.indexedInduction n C s (S.node i a g)) (S.sourceStepValue s (.pair i a) F c R) :=
  indexedInduction_node_reified_beta_of_hypotheses (StructuralTheory.empty levels) D hm hC hs hi ha hg

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
