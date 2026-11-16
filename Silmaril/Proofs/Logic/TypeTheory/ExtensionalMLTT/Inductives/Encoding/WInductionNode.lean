module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Induction.Children.Thms

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

variable {H : Set Jdg} {S : Description} {levels : RuleBudget} {n : ℕ} {Γ : Ctx}

private theorem cast_one_eq_wk0 (I : Tm 0) : I.castLE (Nat.zero_le 1) = I.wk0 :=
  (Tm.wkn_past I 0 (Nat.le_refl 0)).symm

/-- The original three-binder next body, with its position declaration retained. -/
theorem next_retaining_position (N : Tm 3) (i a : Tm 0) :
    (N.lst i).lst a = N.bsubst (Fin.cases (.bv 0) (Fin.cases a.wk0 (fun _ => i.wk0))) := by
  rw [Tm.lst_eq_bsubst, Tm.bsubst_lst]
  simp only [cast_one_eq_wk0]
  congr 1
  funext j
  fin_cases j
  · change Fin.lastCases i.wk0 (Fin.lastCases a.wk0 Tm.bv) (Fin.castSucc (Fin.castSucc (0 : Fin 1))) = (Tm.bv (0 : Fin 1))
    rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc]
  · change Fin.lastCases i.wk0 (Fin.lastCases a.wk0 Tm.bv) (Fin.castSucc (Fin.last 1)) = a.wk0
    rw [Fin.lastCases_castSucc, Fin.lastCases_last]
  · change Fin.lastCases i.wk0 (Fin.lastCases a.wk0 Tm.bv) (Fin.last 2) = i.wk0
    exact Fin.lastCases_last

theorem canonical_congr_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {t u c d : Tm 0}
    (htu : Γ.JEqB levels H S.raw t u) (hcd : Γ.JEqB levels H (S.coherence n t) c d) :
    Γ.JEqB levels H (S.fibre n (S.root t)) (S.canonical t c) (S.canonical u d) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have ht := htu.trans htu.symm
  have hr := root_typing_of_hypotheses hH D.toFormationData ht
  have hroot := root_congr_of_hypotheses hH D.toFormationData htu
  have hE : Γ.JEqB levels H (.univ n)
      (.id S.index (S.root t) (S.root t)) (.id S.index (S.root t) (S.root t)) :=
    .id hn D.index hr hr
  have hcoh := coherence_formation_of_hypotheses hH D ht
  have htail : Γ.JEqB levels H
      ((.sigma (.id S.index.wk0 (S.root (.bv 0)) (S.root t).wk0)
        (S.coherence n (.bv 1)) : Tm 1).lst t)
      (.pair (.refl (S.root t)) c) (.pair (.refl (S.root u)) d) := by
    rw [fibreTail_lst]
    exact .pair hn hE (Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn D.context hE hcoh) (.refl hroot)
      (by simpa only [Tm.closed_wk0_lst] using hcd)
  exact .pair hn (raw_formation_of_hypotheses hH D.toFormationData) (fibreTail_formation_of_hypotheses hH D hr) htu htail

/-- The original child family is exactly the source next body with position retained. -/
theorem childFibres_as_source (S : Description) (n : ℕ) (l : Tm 0) :
    S.childFibres n l = S.fibreAt n ((S.next.lst (.fst l)).lst (.snd l)) := by
  unfold Description.childFibres
  rw [next_retaining_position]
  rfl

/-- The actual reified children inhabit the direct original input type of the original node. -/
theorem reifiedNode_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f c : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    Γ.JEqB levels H (S.fibre n (.fst l))
      (S.node (.fst l) (.snd l) (S.reifyChildren l f c))
      (S.node (.fst l) (.snd l) (S.reifyChildren l f c)) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hi := Ctx.JEqB.fst hn D.index D.shape hl
  have ha := Ctx.JEqB.snd hn D.index D.shape hl
  have hg : Γ.JEqB levels H
      (.pi (S.positionAt (.fst l) (.snd l)) (S.fibreAt n ((S.next.lst (.fst l)).lst (.snd l))))
      (S.reifyChildren l f c) (S.reifyChildren l f c) := by
    simpa only [positions_lst, childFibres_as_source] using reifyChildren_typing_of_hypotheses hH D hl hf hc
  exact node_typing_direct_of_hypotheses hH D hi ha hg

/-- Erasing an actual reconstructed child computes to the original raw child. -/
theorem reifyChildren_fst_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f c p : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hp : Γ.JEqB levels H (S.positions.lst l) p p) :
    Γ.JEqB levels H S.raw (.fst (.app (S.reifyChildren l f c) p)) (.app f p) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hP := positions_instance_formation_of_hypotheses hH D.toFormationData hl
  have hnext := childIndexAt_typing_of_hypotheses hH D hl hp
  have hchild : Γ.JEqB levels H S.raw (.app f p) (.app f p) :=
    Ctx.JEqB.arrow_application_of_hypotheses hH.weakening hn D.context hP (raw_formation_of_hypotheses hH D.toFormationData) hf hp
  have hcp : Γ.JEqB levels H
      ((.sigma (.id S.index.wk0 (S.root (.bv 0)) (S.childIndexAt l p).wk0)
        (S.coherence n (.bv 1)) : Tm 1).lst (.app f p)) (.app c p) (.app c p) := by
    simpa only [fibreTail_lst] using coherentChild_witness_typing_of_hypotheses hH D hl hf hc hp
  have hfst := Ctx.JEqB.fst hn (raw_formation_of_hypotheses hH D.toFormationData) (fibreTail_formation_of_hypotheses hH D hnext)
    (reifyChildren_beta_of_hypotheses hH D hl hf hc hp)
  exact hfst.trans (Ctx.JEqB.beta_fst hn (raw_formation_of_hypotheses hH D.toFormationData)
    (fibreTail_formation_of_hypotheses hH D hnext) hchild hcp)

/-- The actual erasure function of reconstructed children is the original raw child function. -/
theorem eraseReifiedChildren_eq_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f c : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    Γ.JEqB levels H (.arr (S.positions.lst l) S.raw)
      (.abs (S.positions.lst l) (.fst (.app (S.reifyChildren l f c).wk0 (.bv 0)))) f := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hP := positions_instance_formation_of_hypotheses hH D.toFormationData hl
  have hg := reifyChildren_typing_of_hypotheses hH D hl hf hc
  apply Ctx.JEqB.pi_ext hn hP
    (Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn D.context hP (raw_formation_of_hypotheses hH D.toFormationData))
    (eraseChildren_typing_of_hypotheses hH D hl hP hP hg) hf
  intro p hp
  have hctx : (Γ.cons p (S.positions.lst l)).JEqB levels H .unit .star .star :=
    .cons_ok hn D.context hp hP
  have dp := D.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hp (S.positions.lst l)) hctx
  have hl' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hl
  have hf' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hf
  have hc' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hc
  have hg' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hg
  have hP' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hP
  have hpos : (Γ.cons p (S.positions.lst l)).JEqB levels H (S.positions.lst l) (.fv p) (.fv p) :=
    .var hctx (.here Γ p (S.positions.lst l))
  simpa only [Tm.closed_wk0_open] using
    (eraseChildren_beta_of_hypotheses hH dp hl' hP' hP' hg' hpos).trans (reifyChildren_fst_beta_of_hypotheses hH dp hl' hf' hc' hpos)

/-- Reconstructing and erasing a source node returns the original ordinary W node. -/
theorem reifiedNode_raw_eq_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f c : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    Γ.JEqB levels H S.raw
      (.sup S.totalShape S.positions (.pair (.fst l) (.snd l))
        (.abs (S.positionAt (.fst l) (.snd l)) (.fst (.app (S.reifyChildren l f c).wk0 (.bv 0)))))
      (.sup S.totalShape S.positions l f) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hi := Ctx.JEqB.fst hn D.index D.shape hl
  have ha := Ctx.JEqB.snd hn D.index D.shape hl
  have hposEq : Γ.JEqB levels H (.univ n)
      (S.positions.lst (.pair (.fst l) (.snd l))) (S.positions.lst l) := by
    simpa only [positions_lst] using positions_tagged_beta_of_hypotheses hH D.toFormationData hi ha
  have hpos := hposEq.trans hposEq.symm
  have hArrow : Γ.JEqB levels H (.univ n)
      (.arr (S.positions.lst (.pair (.fst l) (.snd l))) S.raw) (.arr (S.positions.lst l) S.raw) :=
    .pi hn hposEq (Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn D.context hpos (raw_formation_of_hypotheses hH D.toFormationData))
  have hchildren := Ctx.JEqB.conv hn hArrow.symm (eraseReifiedChildren_eq_of_hypotheses hH D hl hf hc)
  have hlabel := (Ctx.JEqB.sigma_eta hn D.index D.shape hl).symm
  simpa only [positions_lst, Description.raw] using Ctx.JEqB.sup hn (totalShape_formation D.toFormationData)
    (positions_formation_of_hypotheses hH D.toFormationData) hlabel hchildren

theorem fibreTail_congr_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i t u : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (htu : Γ.JEqB levels H S.raw t u) :
    Γ.JEqB levels H (.univ n)
      (.sigma (.id S.index (S.root t) i) (S.coherence n t).wk0)
      (.sigma (.id S.index (S.root u) i) (S.coherence n u).wk0) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have ht := htu.trans htu.symm
  have hr := root_typing_of_hypotheses hH D.toFormationData ht
  have hroot := root_congr_of_hypotheses hH D.toFormationData htu
  have hE := Ctx.JEqB.id hn D.index hroot hi
  have hEform := Ctx.JEqB.id hn D.index hr hi
  apply Ctx.JEqB.sigma hn hE
  intro x hx
  have h := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hx hn hEform (coherence_congr_of_hypotheses hH D htu)
  simpa only [Tm.closed_wk0_open] using h

/-- Recovering a reconstructed child's witness computes to the original coherence application. -/
theorem reifyChildren_snd_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f c p : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hp : Γ.JEqB levels H (S.positions.lst l) p p) :
    Γ.JEqB levels H
      (.sigma (.id S.index (S.root (.app f p)) (S.childIndexAt l p)) (S.coherence n (.app f p)).wk0)
      (.snd (.app (S.reifyChildren l f c) p)) (.app c p) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hP := positions_instance_formation_of_hypotheses hH D.toFormationData hl
  have hnext := childIndexAt_typing_of_hypotheses hH D hl hp
  have hchild : Γ.JEqB levels H S.raw (.app f p) (.app f p) :=
    Ctx.JEqB.arrow_application_of_hypotheses hH.weakening hn D.context hP (raw_formation_of_hypotheses hH D.toFormationData) hf hp
  have hcp : Γ.JEqB levels H
      ((.sigma (.id S.index.wk0 (S.root (.bv 0)) (S.childIndexAt l p).wk0)
        (S.coherence n (.bv 1)) : Tm 1).lst (.app f p)) (.app c p) (.app c p) := by
    simpa only [fibreTail_lst] using coherentChild_witness_typing_of_hypotheses hH D hl hf hc hp
  have hproject := reifyChildren_fst_beta_of_hypotheses hH D hl hf hc hp
  have hsnd : Γ.JEqB levels H
      (.sigma (.id S.index (S.root (.fst (.app (S.reifyChildren l f c) p))) (S.childIndexAt l p))
        (S.coherence n (.fst (.app (S.reifyChildren l f c) p))).wk0)
      (.snd (.app (S.reifyChildren l f c) p)) (.snd (.pair (.app f p) (.app c p))) := by
    simpa only [fibreTail_lst] using Ctx.JEqB.snd hn (raw_formation_of_hypotheses hH D.toFormationData)
      (fibreTail_formation_of_hypotheses hH D hnext) (reifyChildren_beta_of_hypotheses hH D hl hf hc hp)
  have hnormalized := Ctx.JEqB.conv hn (fibreTail_congr_of_hypotheses hH D hnext hproject) hsnd
  have hbeta : Γ.JEqB levels H
      (.sigma (.id S.index (S.root (.app f p)) (S.childIndexAt l p)) (S.coherence n (.app f p)).wk0)
      (.snd (.pair (.app f p) (.app c p))) (.app c p) := by
    simpa only [fibreTail_lst] using Ctx.JEqB.beta_snd hn (raw_formation_of_hypotheses hH D.toFormationData)
      (fibreTail_formation_of_hypotheses hH D hnext) hchild hcp
  exact hnormalized.trans hbeta

private theorem lastCases_zero {α : Sort _} (a : α) (f : Fin 0 → α) :
    Fin.lastCases a f (0 : Fin 1) = a := Fin.lastCases_last

private theorem lst_fv (B : Tm 1) (x : String) : B.lst (.fv x) = B.open x := by
  rw [Tm.lst_eq_bsubst, Tm.open_eq_bsubst]
  simp only [Tm.castLE]

private theorem witnessReifiedChildren_body_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f c : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    let B : Tm 1 := .sigma
      (.id S.index.wk0 (S.root (.app f.wk0 (.bv 0))) (S.childIndexAt l.wk0 (.bv 0)))
      (S.coherence n (.app f.wk0 (.bv 0))).wk0
    ∀ p ∉ Γ.dv, (Γ.cons p (S.positions.lst l)).JEqB levels H (B.open p)
      ((.snd (.app (S.reifyChildren l f c).wk0 (.bv 0)) : Tm 1).open p) (.app c (.fv p)) := by
  intro B p hp
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hP := positions_instance_formation_of_hypotheses hH D.toFormationData hl
  have hctx : (Γ.cons p (S.positions.lst l)).JEqB levels H .unit .star .star :=
    .cons_ok hn D.context hp hP
  have dp := D.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hp (S.positions.lst l)) hctx
  have hl' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hl
  have hf' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hf
  have hc' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hc
  have hpos : (Γ.cons p (S.positions.lst l)).JEqB levels H (S.positions.lst l) (.fv p) (.fv p) :=
    .var hctx (.here Γ p (S.positions.lst l))
  simpa only [B, normalizedLayer_open, Tm.open, Tm.closed_wk0_open, lastCases_zero] using
    reifyChildren_snd_beta_of_hypotheses hH dp hl' hf' hc' hpos

private theorem witnessReifiedChildren_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f c p : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hp : Γ.JEqB levels H (S.positions.lst l) p p) :
    Γ.JEqB levels H
      ((.sigma (.id S.index.wk0 (S.root (.app f.wk0 (.bv 0))) (S.childIndexAt l.wk0 (.bv 0)))
        (S.coherence n (.app f.wk0 (.bv 0))).wk0 : Tm 1).lst p)
      (.app (.abs (S.positions.lst l) (.snd (.app (S.reifyChildren l f c).wk0 (.bv 0)))) p)
      (.snd (.app (S.reifyChildren l f c) p)) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hP := positions_instance_formation_of_hypotheses hH D.toFormationData hl
  have hbody := witnessReifiedChildren_body_of_hypotheses hH D hl hf hc
  have hb : ((.snd (.app (S.reifyChildren l f c).wk0 (.bv 0)) : Tm 1).lst p) =
      .snd (.app (S.reifyChildren l f c) p) := by
    simp only [Tm.lst, Tm.closed_wk0_lst, lastCases_zero, Tm.castLE_refl]
  simpa only [hb] using Ctx.JEqB.beta_app hn hP (coherenceWitness_formation_of_hypotheses hH D hl hf)
    (fun q hq => (hbody q hq).trans (hbody q hq).symm) hp

/-- The coherence function reconstructed by the original source node is the original coherence witness. -/
theorem witnessReifiedChildren_eq_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f c : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f))
      (.abs (S.positionAt (.fst l) (.snd l)) (.snd (.app (S.reifyChildren l f c).wk0 (.bv 0)))) c := by
  let B : Tm 1 := .sigma
    (.id S.index.wk0 (S.root (.app f.wk0 (.bv 0))) (S.childIndexAt l.wk0 (.bv 0)))
    (S.coherence n (.app f.wk0 (.bv 0))).wk0
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hP := positions_instance_formation_of_hypotheses hH D.toFormationData hl
  have hB := coherenceWitness_formation_of_hypotheses hH D hl hf
  have hbody := witnessReifiedChildren_body_of_hypotheses hH D hl hf hc
  have hG : Γ.JEqB levels H (.pi (S.positions.lst l) B)
      (.abs (S.positions.lst l) (.snd (.app (S.reifyChildren l f c).wk0 (.bv 0))))
      (.abs (S.positions.lst l) (.snd (.app (S.reifyChildren l f c).wk0 (.bv 0)))) :=
    .abs hn hP hB (fun p hp => (hbody p hp).trans (hbody p hp).symm)
  have hcf : Γ.JEqB levels H (.pi (S.positions.lst l) B) c c :=
    .conv hn (coherence_sup_beta_of_hypotheses hH D hl hf) hc
  have hEq : Γ.JEqB levels H (.pi (S.positions.lst l) B)
      (.abs (S.positions.lst l) (.snd (.app (S.reifyChildren l f c).wk0 (.bv 0)))) c := by
    apply Ctx.JEqB.pi_ext hn hP hB hG hcf
    intro p hp
    have hctx : (Γ.cons p (S.positions.lst l)).JEqB levels H .unit .star .star :=
      .cons_ok hn D.context hp hP
    have dp := D.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hp (S.positions.lst l)) hctx
    have hl' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hl
    have hf' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hf
    have hc' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hc
    have hpos : (Γ.cons p (S.positions.lst l)).JEqB levels H (S.positions.lst l) (.fv p) (.fv p) :=
      .var hctx (.here Γ p (S.positions.lst l))
    have hbeta : (Γ.cons p (S.positions.lst l)).JEqB levels H
        (.sigma (.id S.index (S.root (.app f (.fv p))) (S.childIndexAt l (.fv p)))
          (S.coherence n (.app f (.fv p))).wk0)
        (.app (.abs (S.positions.lst l) (.snd (.app (S.reifyChildren l f c).wk0 (.bv 0)))) (.fv p))
        (.snd (.app (S.reifyChildren l f c) (.fv p))) := by
      simpa only [lst_fv, normalizedLayer_open] using witnessReifiedChildren_beta_of_hypotheses hH dp hl' hf' hc' hpos
    simpa only [B, normalizedLayer_open] using hbeta.trans (reifyChildren_snd_beta_of_hypotheses hH dp hl' hf' hc' hpos)
  have hresult := Ctx.JEqB.conv hn (coherence_sup_beta_of_hypotheses hH D hl hf).symm hEq
  simpa only [positions_lst] using hresult

private theorem reifiedChildren_tagged_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f c : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    Γ.JEqB levels H (.pi (S.positionAt (.fst l) (.snd l))
      (S.childFibres n (.pair (.fst l) (.snd l))))
      (S.reifyChildren l f c) (S.reifyChildren l f c) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hi := Ctx.JEqB.fst hn D.index D.shape hl
  have ha := Ctx.JEqB.snd hn D.index D.shape hl
  have hg : Γ.JEqB levels H
      (.pi (S.positionAt (.fst l) (.snd l)) (S.fibreAt n ((S.next.lst (.fst l)).lst (.snd l))))
      (S.reifyChildren l f c) (S.reifyChildren l f c) := by
    simpa only [positions_lst, childFibres_as_source] using reifyChildren_typing_of_hypotheses hH D hl hf hc
  exact .conv hn (childFibres_tagged_beta_of_hypotheses hH D hi ha).symm hg

/-- The exact original source node reconstructs the original raw node and coherence witness. -/
theorem reifiedNode_eq_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f c : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    Γ.JEqB levels H (S.fibre n (.fst l))
      (S.node (.fst l) (.snd l) (S.reifyChildren l f c))
      (S.canonical (.sup S.totalShape S.positions l f) c) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hi := Ctx.JEqB.fst hn D.index D.shape hl
  have ha := Ctx.JEqB.snd hn D.index D.shape hl
  have hg := reifiedChildren_tagged_typing_of_hypotheses hH D hl hf hc
  have hnode := reifiedNode_typing_of_hypotheses hH D hl hf hc
  have hrawNode := reifiedNode_raw_eq_of_hypotheses hH D hl hf hc
  have hraw := (node_fst_beta_of_hypotheses hH D hi ha hg).trans hrawNode
  have hcohProjection := Ctx.JEqB.conv hn (coherence_congr_of_hypotheses hH D hrawNode)
    (node_coherence_beta_of_hypotheses hH D hi ha hg)
  have hcohAtOriginal := hcohProjection.trans (witnessReifiedChildren_eq_of_hypotheses hH D hl hf hc)
  have hcoh := Ctx.JEqB.conv hn (coherence_congr_of_hypotheses hH D hraw).symm hcohAtOriginal
  have hcanonical := canonical_congr_of_hypotheses hH D hraw hcoh
  have hindex := fibre_index_eq_of_hypotheses hH D hi hnode
  have hcanonical' := Ctx.JEqB.conv hn (fibre_congr_of_hypotheses hH D hindex) hcanonical
  exact (fibre_reconstruction_of_hypotheses hH D hi hnode).trans hcanonical'

/-- The source step's original node result converts to the constructed raw induction motive. -/
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
  motive_congr_of_hypotheses hH D hm hC (root_sup_beta_of_hypotheses hH D.toFormationData hl hf).symm (reifiedNode_eq_of_hypotheses hH D hl hf hc)


theorem canonical_congr (D : IndexedFormationData S levels n Γ) {t u c d : Tm 0}
    (htu : Γ.JEqB levels ∅ S.raw t u) (hcd : Γ.JEqB levels ∅ (S.coherence n t) c d) :
    Γ.JEqB levels ∅ (S.fibre n (S.root t)) (S.canonical t c) (S.canonical u d) :=
  canonical_congr_of_hypotheses (StructuralTheory.empty levels) D htu hcd

theorem reifiedNode_typing (D : IndexedFormationData S levels n Γ) {l f c : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    Γ.JEqB levels ∅ (S.fibre n (.fst l))
      (S.node (.fst l) (.snd l) (S.reifyChildren l f c))
      (S.node (.fst l) (.snd l) (S.reifyChildren l f c)) :=
  reifiedNode_typing_of_hypotheses (StructuralTheory.empty levels) D hl hf hc

theorem reifyChildren_fst_beta (D : IndexedFormationData S levels n Γ) {l f c p : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hp : Γ.JEqB levels ∅ (S.positions.lst l) p p) :
    Γ.JEqB levels ∅ S.raw (.fst (.app (S.reifyChildren l f c) p)) (.app f p) :=
  reifyChildren_fst_beta_of_hypotheses (StructuralTheory.empty levels) D hl hf hc hp

theorem eraseReifiedChildren_eq (D : IndexedFormationData S levels n Γ) {l f c : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw)
      (.abs (S.positions.lst l) (.fst (.app (S.reifyChildren l f c).wk0 (.bv 0)))) f :=
  eraseReifiedChildren_eq_of_hypotheses (StructuralTheory.empty levels) D hl hf hc

theorem reifiedNode_raw_eq (D : IndexedFormationData S levels n Γ) {l f c : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    Γ.JEqB levels ∅ S.raw
      (.sup S.totalShape S.positions (.pair (.fst l) (.snd l))
        (.abs (S.positionAt (.fst l) (.snd l)) (.fst (.app (S.reifyChildren l f c).wk0 (.bv 0)))))
      (.sup S.totalShape S.positions l f) :=
  reifiedNode_raw_eq_of_hypotheses (StructuralTheory.empty levels) D hl hf hc

theorem fibreTail_congr (D : IndexedFormationData S levels n Γ) {i t u : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (htu : Γ.JEqB levels ∅ S.raw t u) :
    Γ.JEqB levels ∅ (.univ n)
      (.sigma (.id S.index (S.root t) i) (S.coherence n t).wk0)
      (.sigma (.id S.index (S.root u) i) (S.coherence n u).wk0) :=
  fibreTail_congr_of_hypotheses (StructuralTheory.empty levels) D hi htu

theorem reifyChildren_snd_beta (D : IndexedFormationData S levels n Γ) {l f c p : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hp : Γ.JEqB levels ∅ (S.positions.lst l) p p) :
    Γ.JEqB levels ∅
      (.sigma (.id S.index (S.root (.app f p)) (S.childIndexAt l p)) (S.coherence n (.app f p)).wk0)
      (.snd (.app (S.reifyChildren l f c) p)) (.app c p) :=
  reifyChildren_snd_beta_of_hypotheses (StructuralTheory.empty levels) D hl hf hc hp

theorem witnessReifiedChildren_eq (D : IndexedFormationData S levels n Γ) {l f c : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f))
      (.abs (S.positionAt (.fst l) (.snd l)) (.snd (.app (S.reifyChildren l f c).wk0 (.bv 0)))) c :=
  witnessReifiedChildren_eq_of_hypotheses (StructuralTheory.empty levels) D hl hf hc

theorem reifiedNode_eq (D : IndexedFormationData S levels n Γ) {l f c : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    Γ.JEqB levels ∅ (S.fibre n (.fst l))
      (S.node (.fst l) (.snd l) (S.reifyChildren l f c))
      (S.canonical (.sup S.totalShape S.positions l f) c) :=
  reifiedNode_eq_of_hypotheses (StructuralTheory.empty levels) D hl hf hc

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
  motive_reifiedNode_eq_of_hypotheses (StructuralTheory.empty levels) D hm hC hl hf hc

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
