module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Fibres

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

variable {H : Set Jdg} {S : Description} {levels : RuleBudget} {n : ℕ} {Γ : Ctx}

private theorem lastCases_zero {α : Sort _} (a : α) (f : Fin 0 → α) :
    Fin.lastCases a f (0 : Fin 1) = a := Fin.lastCases_last

private theorem lastCases_one {α : Sort _} (a : α) (f : Fin 1 → α) :
    Fin.lastCases a f (1 : Fin 2) = a := Fin.lastCases_last

theorem root_congr_of_hypotheses (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) {t u : Tm 0}
    (ht : Γ.JEqB levels H S.raw t u) :
    Γ.JEqB levels H S.index (S.root t) (S.root u) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hlabel : ∀ x ∉ Γ.dv, (Γ.cons x S.totalShape).JEqB levels H S.index
      ((.fst (.bv 0) : Tm 1).open x) ((.fst (.bv 0) : Tm 1).open x) := by
    intro x hx
    have hctx : (Γ.cons x S.totalShape).JEqB levels H .unit .star .star :=
      .cons_ok hn D.context hx (totalShape_formation D)
    have hd := D.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hx S.totalShape) hctx
    have hl : (Γ.cons x S.totalShape).JEqB levels H S.totalShape (.fv x) (.fv x) :=
      .var hctx (.here Γ x S.totalShape)
    simpa only [Tm.open, lastCases_zero] using Ctx.JEqB.fst hn hd.index hd.shape hl
  have hC := Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn D.context (raw_formation_of_hypotheses hH D) D.index
  simpa only [root_eq_head, Tm.head, Tm.closed_wk0_lst] using Ctx.JEqB.wrec hn hn
    (totalShape_formation D) (positions_formation_of_hypotheses hH D) hC
    (Ctx.JEqB.headStep_typing_of_hypotheses hH.weakening hn D.context (totalShape_formation D) D.index
      (positions_formation_of_hypotheses hH D) hlabel) ht

theorem coherence_congr_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {t u : Tm 0}
    (ht : Γ.JEqB levels H S.raw t u) :
    Γ.JEqB levels H (.univ n) (S.coherence n t) (S.coherence n u) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hC : ∀ x ∉ Γ.dv, (Γ.cons x S.raw).JEqB levels H (.univ (n + 1))
      ((.univ n : Tm 1).open x) ((.univ n : Tm 1).open x) := by
    intro x hx
    simpa only [Tm.open] using Ctx.JEqB.univ D.bound
      (.cons_ok hn D.context hx (raw_formation_of_hypotheses hH D.toFormationData))
  simpa only [Description.coherence, Tm.castLE_refl, Tm.lst] using Ctx.JEqB.wrec hn D.bound
    (totalShape_formation D.toFormationData) (positions_formation_of_hypotheses hH D.toFormationData) hC
    (coherenceStep_typing_of_hypotheses hH D) ht

/-- Actual formation of the dependent tail used by both fibre projections. -/
theorem fibreTail_formation_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) :
    ∀ x ∉ Γ.dv, (Γ.cons x S.raw).JEqB levels H (.univ n)
      ((.sigma (.id S.index.wk0 (S.root (.bv 0)) i.wk0)
        (S.coherence n (.bv 1)) : Tm 1).open x)
      ((.sigma (.id S.index.wk0 (S.root (.bv 0)) i.wk0)
        (S.coherence n (.bv 1)) : Tm 1).open x) := by
  intro x hx
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hctx : (Γ.cons x S.raw).JEqB levels H .unit .star .star :=
    .cons_ok hn D.context hx (raw_formation_of_hypotheses hH D.toFormationData)
  have dx := D.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hx S.raw) hctx
  have ht : (Γ.cons x S.raw).JEqB levels H S.raw (.fv x) (.fv x) :=
    .var hctx (.here Γ x S.raw)
  have hi' := D.context.weaken_cons_of_hypotheses hH.weakening hx hn (raw_formation_of_hypotheses hH D.toFormationData) hi
  have hE : (Γ.cons x S.raw).JEqB levels H (.univ n)
      (.id S.index (S.root (.fv x)) i) (.id S.index (S.root (.fv x)) i) :=
    .id hn dx.index (root_typing_of_hypotheses hH dx.toFormationData ht) hi'
  simp only [Tm.open, Tm.closed_wk0_open, root_open, coherence_open, lastCases_zero, lastCases_one]
  apply Ctx.JEqB.sigma (L := (Γ.cons x S.raw).dv) hn hE
  intro e he
  have hctxE : ((Γ.cons x S.raw).cons e (.id S.index (S.root (.fv x)) i)).JEqB
      levels H .unit .star .star := .cons_ok hn hctx he hE
  have de := dx.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons he (.id S.index (S.root (.fv x)) i)) hctxE
  have htE := hctx.weaken_cons_of_hypotheses hH.weakening he hn hE ht
  simpa only [coherence_open, Tm.open] using coherence_formation_of_hypotheses hH de htE

theorem childFibres_open (S : Description) (n : ℕ) (l : Tm 0) (p : String) :
    (S.childFibres n l).open p = S.fibre n (S.childIndexAt l (.fv p)) := by
  simp only [Description.childFibres, fibreAt_open, childIndexAt_open,
    Tm.closed_wk0_open, Tm.open, lastCases_zero, fibreAt_closed]

theorem childFibres_lst (S : Description) (n : ℕ) (l p : Tm 0) :
    (S.childFibres n l).lst p = S.fibre n (S.childIndexAt l p) := by
  simp only [Description.childFibres, fibreAt_lst, childIndexAt_lst,
    Tm.closed_wk0_lst, Tm.lst, lastCases_zero, Tm.castLE_refl, fibreAt_closed]

theorem childFibres_formation_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l A : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l) (hA : Γ.JEqB levels H (.univ n) A A)
    (hP : Γ.JEqB levels H (.univ n) A (S.positions.lst l)) :
    ∀ p ∉ Γ.dv, (Γ.cons p A).JEqB levels H (.univ n)
      ((S.childFibres n l).open p) ((S.childFibres n l).open p) := by
  intro p hp
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hctx : (Γ.cons p A).JEqB levels H .unit .star .star := .cons_ok hn D.context hp hA
  have dp := D.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hp A) hctx
  have hl' := D.context.weaken_cons_of_hypotheses hH.weakening hp hn hA hl
  have hp' : (Γ.cons p A).JEqB levels H (S.positions.lst l) (.fv p) (.fv p) :=
    .conv hn (D.context.weaken_cons_of_hypotheses hH.weakening hp hn hA hP) (.var hctx (.here Γ p A))
  simpa only [childFibres_open] using fibre_formation_of_hypotheses hH dp (childIndexAt_typing_of_hypotheses hH dp hl' hp')

theorem childValue_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l A f p : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l) (hA : Γ.JEqB levels H (.univ n) A A)
    (hP : Γ.JEqB levels H (.univ n) A (S.positions.lst l))
    (hf : Γ.JEqB levels H (.pi A (S.childFibres n l)) f f)
    (hp : Γ.JEqB levels H A p p) :
    Γ.JEqB levels H (S.fibre n (S.childIndexAt l p)) (.app f p) (.app f p) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  simpa only [childFibres_lst] using Ctx.JEqB.app hn hA (childFibres_formation_of_hypotheses hH D hl hA hP) hf hp

theorem fibre_fst_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i t : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ht : Γ.JEqB levels H (S.fibre n i) t t) :
    Γ.JEqB levels H S.raw (.fst t) (.fst t) :=
  .fst (by have := D.bound; budget_omega) (raw_formation_of_hypotheses hH D.toFormationData) (fibreTail_formation_of_hypotheses hH D hi) ht

theorem fibre_snd_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i t : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ht : Γ.JEqB levels H (S.fibre n i) t t) :
    Γ.JEqB levels H
      (.sigma (.id S.index (S.root (.fst t)) i) (S.coherence n (.fst t)).wk0)
      (.snd t) (.snd t) := by
  simpa only [fibreTail_lst] using Ctx.JEqB.snd (by have := D.bound; budget_omega)
    (raw_formation_of_hypotheses hH D.toFormationData) (fibreTail_formation_of_hypotheses hH D hi) ht

private theorem erasure_body_typing (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l A f : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l) (hA : Γ.JEqB levels H (.univ n) A A)
    (hP : Γ.JEqB levels H (.univ n) A (S.positions.lst l))
    (hf : Γ.JEqB levels H (.pi A (S.childFibres n l)) f f) :
    ∀ p ∉ Γ.dv, (Γ.cons p A).JEqB levels H S.raw
      ((.fst (.app f.wk0 (.bv 0)) : Tm 1).open p)
      ((.fst (.app f.wk0 (.bv 0)) : Tm 1).open p) := by
  intro p hp
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hctx : (Γ.cons p A).JEqB levels H .unit .star .star := .cons_ok hn D.context hp hA
  have dp := D.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hp A) hctx
  have hl' := D.context.weaken_cons_of_hypotheses hH.weakening hp hn hA hl
  have hA' := D.context.weaken_cons_of_hypotheses hH.weakening hp hn hA hA
  have hP' := D.context.weaken_cons_of_hypotheses hH.weakening hp hn hA hP
  have hf' := D.context.weaken_cons_of_hypotheses hH.weakening hp hn hA hf
  have hpA : (Γ.cons p A).JEqB levels H A (.fv p) (.fv p) := .var hctx (.here Γ p A)
  have hpP : (Γ.cons p A).JEqB levels H (S.positions.lst l) (.fv p) (.fv p) := .conv hn hP' hpA
  have hnext := childIndexAt_typing_of_hypotheses hH dp hl' hpP
  have hchild := childValue_typing_of_hypotheses hH dp hl' hA' hP' hf' hpA
  simpa only [Tm.open, Tm.closed_wk0_open, lastCases_zero] using fibre_fst_typing_of_hypotheses hH dp hnext hchild

theorem eraseChildren_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l A f : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l) (hA : Γ.JEqB levels H (.univ n) A A)
    (hP : Γ.JEqB levels H (.univ n) A (S.positions.lst l))
    (hf : Γ.JEqB levels H (.pi A (S.childFibres n l)) f f) :
    Γ.JEqB levels H (.arr A S.raw)
      (.abs A (.fst (.app f.wk0 (.bv 0)))) (.abs A (.fst (.app f.wk0 (.bv 0)))) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  apply Ctx.JEqB.abs hn hA (Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn D.context hA (raw_formation_of_hypotheses hH D.toFormationData))
  simpa only [Tm.closed_wk0_open] using erasure_body_typing hH D hl hA hP hf

theorem eraseChildren_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l A f p : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l) (hA : Γ.JEqB levels H (.univ n) A A)
    (hP : Γ.JEqB levels H (.univ n) A (S.positions.lst l))
    (hf : Γ.JEqB levels H (.pi A (S.childFibres n l)) f f)
    (hp : Γ.JEqB levels H A p p) :
    Γ.JEqB levels H S.raw
      (.app (.abs A (.fst (.app f.wk0 (.bv 0)))) p) (.fst (.app f p)) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hb : ∀ x ∉ Γ.dv, (Γ.cons x A).JEqB levels H (S.raw.wk0.open x)
      ((.fst (.app f.wk0 (.bv 0)) : Tm 1).open x)
      ((.fst (.app f.wk0 (.bv 0)) : Tm 1).open x) := by
    simpa only [Tm.closed_wk0_open] using erasure_body_typing hH D hl hA hP hf
  simpa only [Tm.lst, Tm.closed_wk0_lst, lastCases_zero, Tm.castLE_refl] using Ctx.JEqB.beta_app hn hA
    (Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn D.context hA (raw_formation_of_hypotheses hH D.toFormationData)) hb hp

private theorem witnessChildren_data (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l A f : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l) (hA : Γ.JEqB levels H (.univ n) A A)
    (hP : Γ.JEqB levels H (.univ n) A (S.positions.lst l))
    (hf : Γ.JEqB levels H (.pi A (S.childFibres n l)) f f) :
    let F : Tm 0 := .abs A (.fst (.app f.wk0 (.bv 0)))
    let C : Tm 1 := .sigma
      (.id S.index.wk0 (S.root (.app F.wk0 (.bv 0))) (S.childIndexAt l.wk0 (.bv 0)))
      (S.coherence n (.app F.wk0 (.bv 0))).wk0
    ∀ p ∉ Γ.dv, (Γ.cons p A).JEqB levels H (.univ n) (C.open p) (C.open p) ∧
      (Γ.cons p A).JEqB levels H (C.open p)
        ((.snd (.app f.wk0 (.bv 0)) : Tm 1).open p)
        ((.snd (.app f.wk0 (.bv 0)) : Tm 1).open p) := by
  intro F C p hp
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hctx : (Γ.cons p A).JEqB levels H .unit .star .star := .cons_ok hn D.context hp hA
  have dp := D.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hp A) hctx
  have hl' := D.context.weaken_cons_of_hypotheses hH.weakening hp hn hA hl
  have hA' := D.context.weaken_cons_of_hypotheses hH.weakening hp hn hA hA
  have hP' := D.context.weaken_cons_of_hypotheses hH.weakening hp hn hA hP
  have hf' := D.context.weaken_cons_of_hypotheses hH.weakening hp hn hA hf
  have hpA : (Γ.cons p A).JEqB levels H A (.fv p) (.fv p) := .var hctx (.here Γ p A)
  have hpP : (Γ.cons p A).JEqB levels H (S.positions.lst l) (.fv p) (.fv p) := .conv hn hP' hpA
  have hnext := childIndexAt_typing_of_hypotheses hH dp hl' hpP
  have hchild := childValue_typing_of_hypotheses hH dp hl' hA' hP' hf' hpA
  have hbeta : (Γ.cons p A).JEqB levels H S.raw
      (.app F (.fv p)) (.fst (.app f (.fv p))) := eraseChildren_beta_of_hypotheses hH dp hl' hA' hP' hf' hpA
  have hIdEq : (Γ.cons p A).JEqB levels H (.univ n)
      (.id S.index (S.root (.fst (.app f (.fv p)))) (S.childIndexAt l (.fv p)))
      (.id S.index (S.root (.app F (.fv p))) (S.childIndexAt l (.fv p))) :=
    .id hn dp.index (root_congr_of_hypotheses hH dp.toFormationData hbeta).symm hnext
  have hcoh : (Γ.cons p A).JEqB levels H (.univ n)
      (S.coherence n (.fst (.app f (.fv p)))) (S.coherence n (.app F (.fv p))) :=
    (coherence_congr_of_hypotheses hH dp hbeta).symm
  have hSigma : (Γ.cons p A).JEqB levels H (.univ n)
      (.sigma (.id S.index (S.root (.fst (.app f (.fv p)))) (S.childIndexAt l (.fv p)))
        (S.coherence n (.fst (.app f (.fv p)))).wk0)
      (.sigma (.id S.index (S.root (.app F (.fv p))) (S.childIndexAt l (.fv p)))
        (S.coherence n (.app F (.fv p))).wk0) := by
    apply Ctx.JEqB.sigma (L := (Γ.cons p A).dv) hn hIdEq
    intro e he
    simpa only [Tm.closed_wk0_open] using hctx.weaken_cons_of_hypotheses hH.weakening he hn (hIdEq.trans hIdEq.symm) hcoh
  have hwitness := Ctx.JEqB.conv hn hSigma (fibre_snd_typing_of_hypotheses hH dp hnext hchild)
  constructor
  · simpa only [C, normalizedLayer_open] using hSigma.symm.trans hSigma
  · simpa only [C, normalizedLayer_open, Tm.open, Tm.closed_wk0_open, lastCases_zero] using hwitness

theorem witnessChildren_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l A f : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l) (hA : Γ.JEqB levels H (.univ n) A A)
    (hP : Γ.JEqB levels H (.univ n) A (S.positions.lst l))
    (hf : Γ.JEqB levels H (.pi A (S.childFibres n l)) f f) :
    let F : Tm 0 := .abs A (.fst (.app f.wk0 (.bv 0)))
    Γ.JEqB levels H
      (.pi A (.sigma
        (.id S.index.wk0 (S.root (.app F.wk0 (.bv 0))) (S.childIndexAt l.wk0 (.bv 0)))
        (S.coherence n (.app F.wk0 (.bv 0))).wk0))
      (.abs A (.snd (.app f.wk0 (.bv 0)))) (.abs A (.snd (.app f.wk0 (.bv 0)))) := by
  intro F
  exact .abs (by have := D.bound; budget_omega) hA
    (fun p hp => (witnessChildren_data hH D hl hA hP hf p hp).1)
    (fun p hp => (witnessChildren_data hH D hl hA hP hf p hp).2)

/-- Actual beta law for the original node's coherence-child abstraction. -/
theorem witnessChildren_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l A f p : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l) (hA : Γ.JEqB levels H (.univ n) A A)
    (hP : Γ.JEqB levels H (.univ n) A (S.positions.lst l))
    (hf : Γ.JEqB levels H (.pi A (S.childFibres n l)) f f)
    (hp : Γ.JEqB levels H A p p) :
    let F : Tm 0 := .abs A (.fst (.app f.wk0 (.bv 0)))
    Γ.JEqB levels H
      (.sigma (.id S.index (S.root (.app F p)) (S.childIndexAt l p))
        (S.coherence n (.app F p)).wk0)
      (.app (.abs A (.snd (.app f.wk0 (.bv 0)))) p) (.snd (.app f p)) := by
  intro F
  have hwk (t : Tm 1) : t.wk0.lst p = (t.lst p).wk0 :=
    Tm.lst_wkn t p 0 (Nat.zero_le 0)
  have h := Ctx.JEqB.beta_app (by have := D.bound; budget_omega) hA
    (fun p hp => (witnessChildren_data hH D hl hA hP hf p hp).1)
    (fun p hp => (witnessChildren_data hH D hl hA hP hf p hp).2) hp
  simpa only [Tm.lst, Tm.closed_wk0_lst, root_lst, childIndexAt_lst, coherence_lst,
    hwk, lastCases_zero, Tm.castLE_refl] using h

private def nodeRaw (S : Description) (i a f : Tm 0) : Tm 0 :=
  .sup S.totalShape S.positions (.pair i a)
    (.abs (S.positionAt i a) (.fst (.app f.wk0 (.bv 0))))

private def nodeWitness (S : Description) (i a f : Tm 0) : Tm 0 :=
  .abs (S.positionAt i a) (.snd (.app f.wk0 (.bv 0)))

private theorem node_data (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i a f : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hf : Γ.JEqB levels H (.pi (S.positionAt i a) (S.childFibres n (.pair i a))) f f) :
    Γ.JEqB levels H S.raw (nodeRaw S i a f) (nodeRaw S i a f) ∧
    Γ.JEqB levels H
      ((.sigma (.id S.index.wk0 (S.root (.bv 0)) i.wk0)
        (S.coherence n (.bv 1)) : Tm 1).lst (nodeRaw S i a f))
      (.pair (.refl i) (nodeWitness S i a f)) (.pair (.refl i) (nodeWitness S i a f)) ∧
    Γ.JEqB levels H (S.coherence n (nodeRaw S i a f)) (nodeWitness S i a f) (nodeWitness S i a f) ∧
    Γ.JEqB levels H (.id S.index (S.root (nodeRaw S i a f)) i) (.refl i) (.refl i) := by
  let A := S.positionAt i a
  let l : Tm 0 := .pair i a
  let F : Tm 0 := .abs A (.fst (.app f.wk0 (.bv 0)))
  let G : Tm 0 := .abs A (.snd (.app f.wk0 (.bv 0)))
  let w : Tm 0 := .sup S.totalShape S.positions l F
  let C : Tm 1 := .sigma
    (.id S.index.wk0 (S.root (.app F.wk0 (.bv 0))) (S.childIndexAt l.wk0 (.bv 0)))
    (S.coherence n (.app F.wk0 (.bv 0))).wk0
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hA : Γ.JEqB levels H (.univ n) A A := positionAt_formation_of_hypotheses hH D.toFormationData hi ha
  have hl : Γ.JEqB levels H S.totalShape l l := .pair hn D.index D.shape hi ha
  have hAP : Γ.JEqB levels H (.univ n) A (S.positions.lst l) :=
    (positions_tagged_beta_of_hypotheses hH D.toFormationData hi ha).symm
  have hF_A : Γ.JEqB levels H (.arr A S.raw) F F := eraseChildren_typing_of_hypotheses hH D hl hA hAP hf
  have hArrow : Γ.JEqB levels H (.univ n) (.arr A S.raw) (.arr (S.positions.lst l) S.raw) :=
    .pi hn hAP (Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn D.context hA (raw_formation_of_hypotheses hH D.toFormationData))
  have hF : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) F F := .conv hn hArrow hF_A
  have hw : Γ.JEqB levels H S.raw w w :=
    .sup hn (totalShape_formation D.toFormationData) (positions_formation_of_hypotheses hH D.toFormationData) hl hF
  have hroot : Γ.JEqB levels H S.index (S.root w) i :=
    root_tagged_sup_beta_of_hypotheses hH D.toFormationData hi ha hF
  have hG_A : Γ.JEqB levels H (.pi A C) G G := witnessChildren_typing_of_hypotheses hH D hl hA hAP hf
  have hPi : Γ.JEqB levels H (.univ n) (.pi A C) (.pi (S.positions.lst l) C) :=
    .pi hn hAP (fun p hp => (witnessChildren_data hH D hl hA hAP hf p hp).1)
  have hG_P : Γ.JEqB levels H (.pi (S.positions.lst l) C) G G := .conv hn hPi hG_A
  have hcoherence : Γ.JEqB levels H (.univ n) (S.coherence n w) (.pi (S.positions.lst l) C) :=
    coherence_sup_beta_of_hypotheses hH D hl hF
  have hG : Γ.JEqB levels H (S.coherence n w) G G := .conv hn hcoherence.symm hG_P
  have hId : Γ.JEqB levels H (.univ n) (.id S.index i i) (.id S.index (S.root w) i) :=
    .id hn D.index hroot.symm hi
  have hRefl : Γ.JEqB levels H (.id S.index (S.root w) i) (.refl i) (.refl i) :=
    .conv hn hId (.refl hi)
  have hEq : Γ.JEqB levels H (.univ n)
      (.id S.index (S.root w) i) (.id S.index (S.root w) i) := hId.symm.trans hId
  have hInner : Γ.JEqB levels H
      (.sigma (.id S.index (S.root w) i) (S.coherence n w).wk0)
      (.pair (.refl i) G) (.pair (.refl i) G) :=
    .pair hn hEq (Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn D.context hEq (coherence_formation_of_hypotheses hH D hw)) hRefl
      (by simpa only [Tm.closed_wk0_lst] using hG)
  have hTail : Γ.JEqB levels H
      ((.sigma (.id S.index.wk0 (S.root (.bv 0)) i.wk0)
        (S.coherence n (.bv 1)) : Tm 1).lst w)
      (.pair (.refl i) G) (.pair (.refl i) G) := by
    simpa only [fibreTail_lst] using hInner
  exact ⟨hw, hTail, hG, hRefl⟩

/-- The original indexed constructor inhabits the original fibre at its source index. -/
theorem node_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i a f : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hf : Γ.JEqB levels H (.pi (S.positionAt i a) (S.childFibres n (.pair i a))) f f) :
    Γ.JEqB levels H (S.fibre n i) (S.node i a f) (S.node i a f) :=
  .pair (by have := D.bound; budget_omega) (raw_formation_of_hypotheses hH D.toFormationData) (fibreTail_formation_of_hypotheses hH D hi)
    (node_data hH D hi ha hf).1 (node_data hH D hi ha hf).2.1

/-- Actual first projection beta for the exact original constructor. -/
theorem node_fst_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i a f : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hf : Γ.JEqB levels H (.pi (S.positionAt i a) (S.childFibres n (.pair i a))) f f) :
    Γ.JEqB levels H S.raw (.fst (S.node i a f))
      (.sup S.totalShape S.positions (.pair i a)
        (.abs (S.positionAt i a) (.fst (.app f.wk0 (.bv 0))))) :=
  .beta_fst (by have := D.bound; budget_omega) (raw_formation_of_hypotheses hH D.toFormationData) (fibreTail_formation_of_hypotheses hH D hi)
    (node_data hH D hi ha hf).1 (node_data hH D hi ha hf).2.1

/-- Actual second projection beta retains the original root equation and coherence function. -/
theorem node_snd_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i a f : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hf : Γ.JEqB levels H (.pi (S.positionAt i a) (S.childFibres n (.pair i a))) f f) :
    Γ.JEqB levels H
      ((.sigma (.id S.index.wk0 (S.root (.bv 0)) i.wk0) (S.coherence n (.bv 1)) : Tm 1).lst
        (.sup S.totalShape S.positions (.pair i a)
          (.abs (S.positionAt i a) (.fst (.app f.wk0 (.bv 0))))))
      (.snd (S.node i a f))
      (.pair (.refl i) (.abs (S.positionAt i a) (.snd (.app f.wk0 (.bv 0))))) :=
  .beta_snd (by have := D.bound; budget_omega) (raw_formation_of_hypotheses hH D.toFormationData) (fibreTail_formation_of_hypotheses hH D hi)
    (node_data hH D hi ha hf).1 (node_data hH D hi ha hf).2.1

/-- The actual coherence projection of the original node is its original witness lambda. -/
theorem node_coherence_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i a f : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hf : Γ.JEqB levels H (.pi (S.positionAt i a) (S.childFibres n (.pair i a))) f f) :
    Γ.JEqB levels H
      (S.coherence n (.sup S.totalShape S.positions (.pair i a)
        (.abs (S.positionAt i a) (.fst (.app f.wk0 (.bv 0))))))
      (.snd (.snd (S.node i a f))) (.abs (S.positionAt i a) (.snd (.app f.wk0 (.bv 0)))) := by
  let w := nodeRaw S i a f
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hw : Γ.JEqB levels H S.raw w w := (node_data hH D hi ha hf).1
  have hE : Γ.JEqB levels H (.univ n)
      (.id S.index (S.root w) i) (.id S.index (S.root w) i) :=
    .id hn D.index (root_typing_of_hypotheses hH D.toFormationData hw) hi
  have hcoh := coherence_formation_of_hypotheses hH D hw
  have htail : Γ.JEqB levels H
      (.sigma (.id S.index (S.root w) i) (S.coherence n w).wk0)
      (.snd (S.node i a f)) (.pair (.refl i) (nodeWitness S i a f)) := by
    simpa only [w, nodeRaw, nodeWitness, fibreTail_lst] using node_snd_beta_of_hypotheses hH D hi ha hf
  have hproj : Γ.JEqB levels H (S.coherence n w)
      (.snd (.snd (S.node i a f))) (.snd (.pair (.refl i) (nodeWitness S i a f))) := by
    simpa only [Tm.closed_wk0_lst] using Ctx.JEqB.snd hn hE
      (Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn D.context hE hcoh) htail
  have hG : Γ.JEqB levels H (S.coherence n w) (nodeWitness S i a f) (nodeWitness S i a f) :=
    (node_data hH D hi ha hf).2.2.1
  have hRefl : Γ.JEqB levels H (.id S.index (S.root w) i) (.refl i) (.refl i) :=
    (node_data hH D hi ha hf).2.2.2
  have hbeta : Γ.JEqB levels H (S.coherence n w)
      (.snd (.pair (.refl i) (nodeWitness S i a f))) (nodeWitness S i a f) := by
    simpa only [Tm.closed_wk0_lst] using Ctx.JEqB.beta_snd hn hE
      (Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn D.context hE hcoh) hRefl
      (by simpa only [Tm.closed_wk0_lst] using hG)
  simpa only [w, nodeRaw, nodeWitness] using hproj.trans hbeta


theorem root_congr (D : FormationData S levels n Γ) {t u : Tm 0}
    (ht : Γ.JEqB levels ∅ S.raw t u) :
    Γ.JEqB levels ∅ S.index (S.root t) (S.root u) :=
  root_congr_of_hypotheses (StructuralTheory.empty levels) D ht

theorem coherence_congr (D : IndexedFormationData S levels n Γ) {t u : Tm 0}
    (ht : Γ.JEqB levels ∅ S.raw t u) :
    Γ.JEqB levels ∅ (.univ n) (S.coherence n t) (S.coherence n u) :=
  coherence_congr_of_hypotheses (StructuralTheory.empty levels) D ht

theorem fibreTail_formation (D : IndexedFormationData S levels n Γ) {i : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) :
    ∀ x ∉ Γ.dv, (Γ.cons x S.raw).JEqB levels ∅ (.univ n)
      ((.sigma (.id S.index.wk0 (S.root (.bv 0)) i.wk0)
        (S.coherence n (.bv 1)) : Tm 1).open x)
      ((.sigma (.id S.index.wk0 (S.root (.bv 0)) i.wk0)
        (S.coherence n (.bv 1)) : Tm 1).open x) :=
  fibreTail_formation_of_hypotheses (StructuralTheory.empty levels) D hi

theorem childFibres_formation (D : IndexedFormationData S levels n Γ) {l A : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l) (hA : Γ.JEqB levels ∅ (.univ n) A A)
    (hP : Γ.JEqB levels ∅ (.univ n) A (S.positions.lst l)) :
    ∀ p ∉ Γ.dv, (Γ.cons p A).JEqB levels ∅ (.univ n)
      ((S.childFibres n l).open p) ((S.childFibres n l).open p) :=
  childFibres_formation_of_hypotheses (StructuralTheory.empty levels) D hl hA hP

theorem childValue_typing (D : IndexedFormationData S levels n Γ) {l A f p : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l) (hA : Γ.JEqB levels ∅ (.univ n) A A)
    (hP : Γ.JEqB levels ∅ (.univ n) A (S.positions.lst l))
    (hf : Γ.JEqB levels ∅ (.pi A (S.childFibres n l)) f f)
    (hp : Γ.JEqB levels ∅ A p p) :
    Γ.JEqB levels ∅ (S.fibre n (S.childIndexAt l p)) (.app f p) (.app f p) :=
  childValue_typing_of_hypotheses (StructuralTheory.empty levels) D hl hA hP hf hp

theorem fibre_fst_typing (D : IndexedFormationData S levels n Γ) {i t : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ht : Γ.JEqB levels ∅ (S.fibre n i) t t) :
    Γ.JEqB levels ∅ S.raw (.fst t) (.fst t) :=
  fibre_fst_typing_of_hypotheses (StructuralTheory.empty levels) D hi ht

theorem fibre_snd_typing (D : IndexedFormationData S levels n Γ) {i t : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ht : Γ.JEqB levels ∅ (S.fibre n i) t t) :
    Γ.JEqB levels ∅
      (.sigma (.id S.index (S.root (.fst t)) i) (S.coherence n (.fst t)).wk0)
      (.snd t) (.snd t) :=
  fibre_snd_typing_of_hypotheses (StructuralTheory.empty levels) D hi ht

theorem eraseChildren_typing (D : IndexedFormationData S levels n Γ) {l A f : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l) (hA : Γ.JEqB levels ∅ (.univ n) A A)
    (hP : Γ.JEqB levels ∅ (.univ n) A (S.positions.lst l))
    (hf : Γ.JEqB levels ∅ (.pi A (S.childFibres n l)) f f) :
    Γ.JEqB levels ∅ (.arr A S.raw)
      (.abs A (.fst (.app f.wk0 (.bv 0)))) (.abs A (.fst (.app f.wk0 (.bv 0)))) :=
  eraseChildren_typing_of_hypotheses (StructuralTheory.empty levels) D hl hA hP hf

theorem eraseChildren_beta (D : IndexedFormationData S levels n Γ) {l A f p : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l) (hA : Γ.JEqB levels ∅ (.univ n) A A)
    (hP : Γ.JEqB levels ∅ (.univ n) A (S.positions.lst l))
    (hf : Γ.JEqB levels ∅ (.pi A (S.childFibres n l)) f f)
    (hp : Γ.JEqB levels ∅ A p p) :
    Γ.JEqB levels ∅ S.raw
      (.app (.abs A (.fst (.app f.wk0 (.bv 0)))) p) (.fst (.app f p)) :=
  eraseChildren_beta_of_hypotheses (StructuralTheory.empty levels) D hl hA hP hf hp

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
  witnessChildren_typing_of_hypotheses (StructuralTheory.empty levels) D hl hA hP hf

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
  witnessChildren_beta_of_hypotheses (StructuralTheory.empty levels) D hl hA hP hf hp

theorem node_typing (D : IndexedFormationData S levels n Γ) {i a f : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hf : Γ.JEqB levels ∅ (.pi (S.positionAt i a) (S.childFibres n (.pair i a))) f f) :
    Γ.JEqB levels ∅ (S.fibre n i) (S.node i a f) (S.node i a f) :=
  node_typing_of_hypotheses (StructuralTheory.empty levels) D hi ha hf

theorem node_fst_beta (D : IndexedFormationData S levels n Γ) {i a f : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hf : Γ.JEqB levels ∅ (.pi (S.positionAt i a) (S.childFibres n (.pair i a))) f f) :
    Γ.JEqB levels ∅ S.raw (.fst (S.node i a f))
      (.sup S.totalShape S.positions (.pair i a)
        (.abs (S.positionAt i a) (.fst (.app f.wk0 (.bv 0))))) :=
  node_fst_beta_of_hypotheses (StructuralTheory.empty levels) D hi ha hf

theorem node_snd_beta (D : IndexedFormationData S levels n Γ) {i a f : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hf : Γ.JEqB levels ∅ (.pi (S.positionAt i a) (S.childFibres n (.pair i a))) f f) :
    Γ.JEqB levels ∅
      ((.sigma (.id S.index.wk0 (S.root (.bv 0)) i.wk0) (S.coherence n (.bv 1)) : Tm 1).lst
        (.sup S.totalShape S.positions (.pair i a)
          (.abs (S.positionAt i a) (.fst (.app f.wk0 (.bv 0))))))
      (.snd (S.node i a f))
      (.pair (.refl i) (.abs (S.positionAt i a) (.snd (.app f.wk0 (.bv 0))))) :=
  node_snd_beta_of_hypotheses (StructuralTheory.empty levels) D hi ha hf

theorem node_coherence_beta (D : IndexedFormationData S levels n Γ) {i a f : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hf : Γ.JEqB levels ∅ (.pi (S.positionAt i a) (S.childFibres n (.pair i a))) f f) :
    Γ.JEqB levels ∅
      (S.coherence n (.sup S.totalShape S.positions (.pair i a)
        (.abs (S.positionAt i a) (.fst (.app f.wk0 (.bv 0))))))
      (.snd (.snd (S.node i a f))) (.abs (S.positionAt i a) (.snd (.app f.wk0 (.bv 0)))) :=
  node_coherence_beta_of_hypotheses (StructuralTheory.empty levels) D hi ha hf

/-- Empty children for the existing nullary source; no new family is introduced. -/
def nullaryChildren : Tm 0 :=
  .abs (nullaryDescription.positionAt .star .star)
    (.absurd (nullaryDescription.childFibres 0 (.pair .star .star)) (.bv 0))

theorem nullaryChildren_typing : Ctx.JEqB 2 ∅ .nil
    (.pi (nullaryDescription.positionAt .star .star)
      (nullaryDescription.childFibres 0 (.pair .star .star))) nullaryChildren nullaryChildren := by
  let D := nullaryIndexedFormationData
  have hi : Ctx.JEqB 2 ∅ .nil nullaryDescription.index .star .star := .nil_ok
  have ha : Ctx.JEqB 2 ∅ .nil (nullaryDescription.shape.lst .star) .star .star := by
    simpa only [nullaryDescription, Tm.lst] using (Ctx.JEqB.nil_ok (levels := 2) (H := ∅))
  have hA := positionAt_formation D.toFormationData hi ha
  have hl : Ctx.JEqB 2 ∅ .nil nullaryDescription.totalShape (.pair .star .star) (.pair .star .star) :=
    .pair (by decide) D.index D.shape hi ha
  have hP := (positions_tagged_beta D.toFormationData hi ha).symm
  have hC := childFibres_formation D hl hA hP
  apply Ctx.JEqB.abs (n := 0) (by decide) hA hC
  intro p hp
  have hctx : (Ctx.nil.cons p (nullaryDescription.positionAt .star .star)).JEqB 2 ∅ .unit .star .star :=
    .cons_ok (n := 0) (by decide) .nil_ok hp hA
  have hp' : (Ctx.nil.cons p (nullaryDescription.positionAt .star .star)).JEqB 2 ∅ .empty (.fv p) (.fv p) := by
    simpa only [nullaryDescription, Description.positionAt, Tm.bsubst] using
      Ctx.JEqB.var hctx (.here .nil p (nullaryDescription.positionAt .star .star))
  simpa only [Tm.open, lastCases_zero] using Ctx.JEqB.absurd (by decide) (hC p hp) hp'

/-- The exact original indexed constructor yields a closed inhabitant of its original fibre. -/
theorem nullary_node_typing : Ctx.JEqB 2 ∅ .nil (nullaryDescription.fibre 0 .star)
    (nullaryDescription.node .star .star nullaryChildren)
    (nullaryDescription.node .star .star nullaryChildren) :=
  node_typing nullaryIndexedFormationData .nil_ok
    (by simpa only [nullaryDescription, Tm.lst] using (Ctx.JEqB.nil_ok (levels := 2) (H := ∅)))
    nullaryChildren_typing

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
