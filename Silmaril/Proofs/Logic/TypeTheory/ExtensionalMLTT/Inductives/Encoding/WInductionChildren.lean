module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Induction.Children.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

variable {H : Set Jdg} {S : Description} {levels : RuleBudget} {n : ℕ} {Γ : Ctx}

private theorem lastCases_zero {α : Sort _} (a : α) (f : Fin 0 → α) :
    Fin.lastCases a f (0 : Fin 1) = a := Fin.lastCases_last

/-- Formation at an actual original label, from its cofinite source formation. -/
theorem positions_instance_formation_of_hypotheses (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) {l : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l) :
    Γ.JEqB levels H (.univ n) (S.positions.lst l) (S.positions.lst l) := by
  simpa only [Tm.lst] using Ctx.JEqB.instantiate_of_hypotheses hH.weakening (fun x => hH.substitution x _) (B := .univ n) D.context hl
    (by simpa only [Tm.open] using positions_formation_of_hypotheses hH D)

private def coherenceLayer (S : Description) (n : ℕ) (l f : Tm 0) : Tm 1 :=
  .sigma (.id S.index.wk0 (S.root (.app f.wk0 (.bv 0))) (S.childIndexAt l.wk0 (.bv 0)))
    (S.coherence n (.app f.wk0 (.bv 0))).wk0

private theorem coherenceLayer_open (S : Description) (n : ℕ) (l f : Tm 0) (p : String) :
    (coherenceLayer S n l f).open p =
    .sigma (.id S.index (S.root (.app f (.fv p))) (S.childIndexAt l (.fv p)))
      (S.coherence n (.app f (.fv p))).wk0 := normalizedLayer_open S n l f p

private theorem coherenceLayer_lst (S : Description) (n : ℕ) (l f p : Tm 0) :
    (coherenceLayer S n l f).lst p =
    .sigma (.id S.index (S.root (.app f p)) (S.childIndexAt l p))
      (S.coherence n (.app f p)).wk0 := by
  have hw : ((S.coherence n (.app f.wk0 (.bv 0)) : Tm 1).wk0).lst p =
      ((S.coherence n (.app f.wk0 (.bv 0)) : Tm 1).lst p).wk0 :=
    Tm.lst_wkn _ p 0 (Nat.zero_le 0)
  simp only [coherenceLayer, Tm.lst, Tm.closed_wk0_lst, root_lst, childIndexAt_lst,
    hw, coherence_lst, lastCases_zero, Tm.castLE_refl]

private theorem coherenceLayer_formation_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f) :
    ∀ p ∉ Γ.dv, (Γ.cons p (S.positions.lst l)).JEqB levels H (.univ n)
      ((coherenceLayer S n l f).open p) ((coherenceLayer S n l f).open p) := by
  intro p hp
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hP : Γ.JEqB levels H (.univ n) (S.positions.lst l) (S.positions.lst l) :=
    positions_instance_formation_of_hypotheses hH D.toFormationData hl
  have hctx : (Γ.cons p (S.positions.lst l)).JEqB levels H .unit .star .star :=
    .cons_ok hn D.context hp hP
  have dp := D.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hp (S.positions.lst l)) hctx
  have hl' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hl
  have hf' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hf
  have hP' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hP
  have hp' : (Γ.cons p (S.positions.lst l)).JEqB levels H (S.positions.lst l) (.fv p) (.fv p) :=
    .var hctx (.here Γ p (S.positions.lst l))
  have hchild : (Γ.cons p (S.positions.lst l)).JEqB levels H S.raw (.app f (.fv p)) (.app f (.fv p)) :=
    Ctx.JEqB.arrow_application_of_hypotheses hH.weakening hn hctx hP' (raw_formation_of_hypotheses hH dp.toFormationData) hf' hp'
  have hnext : (Γ.cons p (S.positions.lst l)).JEqB levels H S.index
      (S.childIndexAt l (.fv p)) (S.childIndexAt l (.fv p)) := childIndexAt_typing_of_hypotheses hH dp hl' hp'
  have hE : (Γ.cons p (S.positions.lst l)).JEqB levels H (.univ n)
      (.id S.index (S.root (.app f (.fv p))) (S.childIndexAt l (.fv p)))
      (.id S.index (S.root (.app f (.fv p))) (S.childIndexAt l (.fv p))) :=
    .id hn dp.index (root_typing_of_hypotheses hH dp.toFormationData hchild) hnext
  have hcoh := coherence_formation_of_hypotheses hH dp hchild
  simpa only [coherenceLayer_open] using Ctx.JEqB.sigma hn hE
    (Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn hctx hE hcoh)

theorem coherenceWitness_formation_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f) :
    ∀ p ∉ Γ.dv, (Γ.cons p (S.positions.lst l)).JEqB levels H (.univ n)
      ((.sigma (.id S.index.wk0 (S.root (.app f.wk0 (.bv 0))) (S.childIndexAt l.wk0 (.bv 0)))
        (S.coherence n (.app f.wk0 (.bv 0))).wk0 : Tm 1).open p) ((.sigma (.id S.index.wk0 (S.root (.app f.wk0 (.bv 0))) (S.childIndexAt l.wk0 (.bv 0)))
        (S.coherence n (.app f.wk0 (.bv 0))).wk0 : Tm 1).open p) :=
  coherenceLayer_formation_of_hypotheses hH D hl hf

/-- The original coherence application carries exactly the child's edge proof and coherence. -/
theorem coherentChild_witness_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f c p : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hp : Γ.JEqB levels H (S.positions.lst l) p p) :
    Γ.JEqB levels H
      (.sigma (.id S.index (S.root (.app f p)) (S.childIndexAt l p)) (S.coherence n (.app f p)).wk0)
      (.app c p) (.app c p) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hP := positions_instance_formation_of_hypotheses hH D.toFormationData hl
  have hcf : Γ.JEqB levels H (.pi (S.positions.lst l) (coherenceLayer S n l f)) c c :=
    .conv hn (coherence_sup_beta_of_hypotheses hH D hl hf) hc
  simpa only [coherenceLayer_lst] using
    Ctx.JEqB.app hn hP (coherenceLayer_formation_of_hypotheses hH D hl hf) hcf hp

/-- Original node coherence reconstructs a full child in its requested original fibre. -/
theorem coherentChild_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f c p : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hp : Γ.JEqB levels H (S.positions.lst l) p p) :
    Γ.JEqB levels H (S.fibre n (S.childIndexAt l p))
      (.pair (.app f p) (.app c p)) (.pair (.app f p) (.app c p)) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hP : Γ.JEqB levels H (.univ n) (S.positions.lst l) (S.positions.lst l) :=
    positions_instance_formation_of_hypotheses hH D.toFormationData hl
  have hchild : Γ.JEqB levels H S.raw (.app f p) (.app f p) :=
    Ctx.JEqB.arrow_application_of_hypotheses hH.weakening hn D.context hP (raw_formation_of_hypotheses hH D.toFormationData) hf hp
  have hnext := childIndexAt_typing_of_hypotheses hH D hl hp
  have hcp : Γ.JEqB levels H
      ((.sigma (.id S.index.wk0 (S.root (.bv 0)) (S.childIndexAt l p).wk0)
        (S.coherence n (.bv 1)) : Tm 1).lst (.app f p))
      (.app c p) (.app c p) := by
    simpa only [fibreTail_lst] using coherentChild_witness_typing_of_hypotheses hH D hl hf hc hp
  exact .pair hn (raw_formation_of_hypotheses hH D.toFormationData) (fibreTail_formation_of_hypotheses hH D hnext) hchild hcp

private theorem reifyChildren_body_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f c : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    ∀ p ∉ Γ.dv, (Γ.cons p (S.positions.lst l)).JEqB levels H ((S.childFibres n l).open p)
      ((.pair (.app f.wk0 (.bv 0)) (.app c.wk0 (.bv 0)) : Tm 1).open p)
      ((.pair (.app f.wk0 (.bv 0)) (.app c.wk0 (.bv 0)) : Tm 1).open p) := by
  intro p hp
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hP : Γ.JEqB levels H (.univ n) (S.positions.lst l) (S.positions.lst l) :=
    positions_instance_formation_of_hypotheses hH D.toFormationData hl
  have hctx : (Γ.cons p (S.positions.lst l)).JEqB levels H .unit .star .star :=
    .cons_ok hn D.context hp hP
  have dp := D.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hp (S.positions.lst l)) hctx
  have hl' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hl
  have hf' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hf
  have hc' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hc
  have hp' : (Γ.cons p (S.positions.lst l)).JEqB levels H (S.positions.lst l) (.fv p) (.fv p) :=
    .var hctx (.here Γ p (S.positions.lst l))
  simpa only [childFibres_open, Tm.open, Tm.closed_wk0_open, lastCases_zero] using
    coherentChild_typing_of_hypotheses hH dp hl' hf' hc' hp'

/-- Reconstructed children are an actual object function into the original child fibres. -/
theorem reifyChildren_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f c : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    Γ.JEqB levels H (.pi (S.positions.lst l) (S.childFibres n l))
      (S.reifyChildren l f c) (S.reifyChildren l f c) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hP : Γ.JEqB levels H (.univ n) (S.positions.lst l) (S.positions.lst l) :=
    positions_instance_formation_of_hypotheses hH D.toFormationData hl
  have hterm : Γ.JEqB levels H (.pi (S.positions.lst l) (S.childFibres n l))
      (.abs (S.positions.lst l) (.pair (.app f.wk0 (.bv 0)) (.app c.wk0 (.bv 0))))
      (.abs (S.positions.lst l) (.pair (.app f.wk0 (.bv 0)) (.app c.wk0 (.bv 0)))) :=
    .abs hn hP (childFibres_formation_of_hypotheses hH D hl hP hP) (reifyChildren_body_typing_of_hypotheses hH D hl hf hc)
  simpa only [Description.reifyChildren, positions_lst, Description.positionAt] using hterm

/-- Actual beta computes reconstructed children to their raw tree and original coherence pair. -/
theorem reifyChildren_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f c p : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hp : Γ.JEqB levels H (S.positions.lst l) p p) :
    Γ.JEqB levels H (S.fibre n (S.childIndexAt l p))
      (.app (S.reifyChildren l f c) p) (.pair (.app f p) (.app c p)) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hP : Γ.JEqB levels H (.univ n) (S.positions.lst l) (S.positions.lst l) :=
    positions_instance_formation_of_hypotheses hH D.toFormationData hl
  simpa only [Description.reifyChildren, positions_lst, Description.positionAt, childFibres_lst,
    Tm.lst, Tm.closed_wk0_lst, lastCases_zero, Tm.castLE_refl] using
    Ctx.JEqB.beta_app hn hP (childFibres_formation_of_hypotheses hH D hl hP hP)
      (reifyChildren_body_typing_of_hypotheses hH D hl hf hc) hp

private theorem lst_fv (B : Tm 1) (x : String) : B.lst (.fv x) = B.open x := by
  rw [Tm.lst_eq_bsubst, Tm.open_eq_bsubst]
  simp only [Tm.castLE]

private theorem childMotive_lst (M : Tm 1) (f p : Tm 0) :
    (M.bsubst (fun _ => .app f.wk0 (.bv 0))).lst p = M.lst (.app f p) := by
  rw [Tm.lst_bsubst]
  simp only [Tm.lst, Tm.closed_wk0_lst, lastCases_zero, Tm.castLE_refl]
  rw [Tm.lst_eq_bsubst]
  congr 1
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  simp only [hj, lastCases_zero, Tm.castLE_refl]

private theorem childMotive_open (M : Tm 1) (f : Tm 0) (p : String) :
    (M.bsubst (fun _ => .app f.wk0 (.bv 0))).open p = M.lst (.app f (.fv p)) := by
  rw [← lst_fv (M.bsubst (fun _ => .app f.wk0 (.bv 0))) p, childMotive_lst]

private theorem childMotive_formation_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {m : ℕ}
    (hm : RuleBudget.Allows levels (m + 1)) {C l f : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f) :
    ∀ p ∉ Γ.dv, (Γ.cons p (S.positions.lst l)).JEqB levels H (.univ (max n m))
      (((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0))).open p)
      (((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0))).open p) := by
  intro p hp
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hP := positions_instance_formation_of_hypotheses hH D.toFormationData hl
  have hctx : (Γ.cons p (S.positions.lst l)).JEqB levels H .unit .star .star :=
    .cons_ok hn D.context hp hP
  have dp := D.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hp (S.positions.lst l)) hctx
  have hC' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hC
  have hf' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hf
  have hP' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hP
  have hpos : (Γ.cons p (S.positions.lst l)).JEqB levels H (S.positions.lst l) (.fv p) (.fv p) :=
    .var hctx (.here Γ p (S.positions.lst l))
  have hchild : (Γ.cons p (S.positions.lst l)).JEqB levels H S.raw (.app f (.fv p)) (.app f (.fv p)) :=
    Ctx.JEqB.arrow_application_of_hypotheses hH.weakening hn hctx hP' (raw_formation_of_hypotheses hH dp.toFormationData) hf' hpos
  simpa only [childMotive_open, Tm.lst] using Ctx.JEqB.instantiate_of_hypotheses hH.weakening (fun x => hH.substitution x _) (B := .univ (max n m))
    hctx hchild (by simpa only [Tm.open] using inductionMotive_formation_of_hypotheses hH dp hm hC')

/-- A raw recursive hypothesis applies to the reconstructed full original child value. -/
theorem coherentHypothesis_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {m : ℕ}
    (hm : RuleBudget.Allows levels (m + 1)) {C l f c r p : Tm 0}
    (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hr : Γ.JEqB levels H (.pi (S.positions.lst l)
      ((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0)))) r r)
    (hp : Γ.JEqB levels H (S.positions.lst l) p p) :
    Γ.JEqB levels H
      (.app (.app C (S.childIndexAt l p)) (.pair (.app f p) (.app c p)))
      (.app (.app r p) (.snd (.app c p)))
      (.app (.app r p) (.snd (.app c p))) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hq : RuleBudget.Allows levels (max n m) := RuleBudget.Allows.max hn (by budget_omega)
  have hP := positions_instance_formation_of_hypotheses hH D.toFormationData hl
  have hchild : Γ.JEqB levels H S.raw (.app f p) (.app f p) :=
    Ctx.JEqB.arrow_application_of_hypotheses hH.weakening hn D.context hP (raw_formation_of_hypotheses hH D.toFormationData) hf hp
  have hnext := childIndexAt_typing_of_hypotheses hH D hl hp
  have hcp : Γ.JEqB levels H
      ((.sigma (.id S.index.wk0 (S.root (.bv 0)) (S.childIndexAt l p).wk0)
        (S.coherence n (.bv 1)) : Tm 1).lst (.app f p)) (.app c p) (.app c p) := by
    simpa only [fibreTail_lst] using coherentChild_witness_typing_of_hypotheses hH D hl hf hc hp
  have hproject : Γ.JEqB levels H S.raw (.app f p) (.fst (.pair (.app f p) (.app c p))) :=
    (Ctx.JEqB.beta_fst hn (raw_formation_of_hypotheses hH D.toFormationData) (fibreTail_formation_of_hypotheses hH D hnext) hchild hcp).symm
  have hrp : Γ.JEqB levels H ((S.inductionMotive n C).lst (.app f p)) (.app r p) (.app r p) := by
    simpa only [childMotive_lst] using Ctx.JEqB.app hq
      (Ctx.JEqB.cumul hq (Nat.le_max_left n m) hP) (childMotive_formation_of_hypotheses hH D hm hC hl hf) hr hp
  have hrp' := Ctx.JEqB.conv hq (inductionMotive_congr_of_hypotheses hH D hm hC hproject) hrp
  have hroot := root_typing_of_hypotheses hH D.toFormationData hchild
  have hE : Γ.JEqB levels H (.univ n)
      (.id S.index (S.root (.app f p)) (S.childIndexAt l p))
      (.id S.index (S.root (.app f p)) (S.childIndexAt l p)) := .id hn D.index hroot hnext
  have hcoh := coherence_formation_of_hypotheses hH D hchild
  have htailBeta : Γ.JEqB levels H
      (.sigma (.id S.index (S.root (.app f p)) (S.childIndexAt l p)) (S.coherence n (.app f p)).wk0)
      (.snd (.pair (.app f p) (.app c p))) (.app c p) := by
    simpa only [fibreTail_lst] using Ctx.JEqB.beta_snd hn (raw_formation_of_hypotheses hH D.toFormationData)
      (fibreTail_formation_of_hypotheses hH D hnext) hchild hcp
  have hargRaw : Γ.JEqB levels H (S.coherence n (.app f p))
      (.snd (.snd (.pair (.app f p) (.app c p)))) (.snd (.app c p)) := by
    simpa only [Tm.closed_wk0_lst] using Ctx.JEqB.snd hn hE
      (Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn D.context hE hcoh) htailBeta
  have harg := Ctx.JEqB.conv hn (coherence_congr_of_hypotheses hH D hproject) hargRaw
  have happ := canonicalMotive_apply_congr_of_hypotheses hH D hm hC hnext
    (coherentChild_typing_of_hypotheses hH D hl hf hc hp) hrp' harg
  exact happ.symm.trans happ

private theorem reifyHypotheses_data_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {m : ℕ}
    (hm : RuleBudget.Allows levels (m + 1)) {C l f c r : Tm 0}
    (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hr : Γ.JEqB levels H (.pi (S.positions.lst l)
      ((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0)))) r r) :
    let B : Tm 1 := .app (.app C.wk0 (S.childIndexAt l.wk0 (.bv 0)))
      (.app (S.reifyChildren l f c).wk0 (.bv 0))
    let b : Tm 1 := .app (.app r.wk0 (.bv 0)) (.snd (.app c.wk0 (.bv 0)))
    ∀ p ∉ Γ.dv, (Γ.cons p (S.positions.lst l)).JEqB levels H (.univ (max n m)) (B.open p) (B.open p) ∧
      (Γ.cons p (S.positions.lst l)).JEqB levels H (B.open p) (b.open p) (b.open p) := by
  intro B b p hp
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hq : RuleBudget.Allows levels (max n m) := RuleBudget.Allows.max hn (by budget_omega)
  have hP := positions_instance_formation_of_hypotheses hH D.toFormationData hl
  have hctx : (Γ.cons p (S.positions.lst l)).JEqB levels H .unit .star .star :=
    .cons_ok hn D.context hp hP
  have dp := D.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hp (S.positions.lst l)) hctx
  have hC' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hC
  have hl' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hl
  have hf' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hf
  have hc' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hc
  have hr' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hr
  have hP' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hP
  have hpos : (Γ.cons p (S.positions.lst l)).JEqB levels H (S.positions.lst l) (.fv p) (.fv p) :=
    .var hctx (.here Γ p (S.positions.lst l))
  have hnext := childIndexAt_typing_of_hypotheses hH dp hl' hpos
  have hg := reifyChildren_typing_of_hypotheses hH dp hl' hf' hc'
  have hgp := childValue_typing_of_hypotheses hH dp hl' hP' hP' hg hpos
  have hType := motive_congr_of_hypotheses hH dp hm hC' hnext hgp
  have hbeta := reifyChildren_beta_of_hypotheses hH dp hl' hf' hc' hpos
  have hconvert := motive_congr_of_hypotheses hH dp hm hC' hnext hbeta
  have hactual := Ctx.JEqB.conv (by budget_omega) hconvert.symm
    (coherentHypothesis_typing_of_hypotheses hH dp hm hC' hl' hf' hc' hr' hpos)
  constructor
  · simpa only [B, Tm.open, Tm.closed_wk0_open, childIndexAt_open, lastCases_zero] using
      Ctx.JEqB.cumul hq (Nat.le_max_right n m) hType
  · simpa only [B, b, Tm.open, Tm.closed_wk0_open, childIndexAt_open, lastCases_zero] using hactual

/-- The original child functions and actual recursive hypotheses supply full dependent source IHs. -/
theorem reifyHypotheses_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {m : ℕ}
    (hm : RuleBudget.Allows levels (m + 1)) {C l f c r : Tm 0}
    (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hr : Γ.JEqB levels H (.pi (S.positions.lst l)
      ((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0)))) r r) :
    Γ.JEqB levels H (.pi (S.positions.lst l)
      (.app (.app C.wk0 (S.childIndexAt l.wk0 (.bv 0))) (.app (S.reifyChildren l f c).wk0 (.bv 0))))
      (S.reifyHypotheses l c r) (S.reifyHypotheses l c r) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hq : RuleBudget.Allows levels (max n m) := RuleBudget.Allows.max hn (by budget_omega)
  have hP := positions_instance_formation_of_hypotheses hH D.toFormationData hl
  have hdata := reifyHypotheses_data_of_hypotheses hH D hm hC hl hf hc hr
  have hterm := Ctx.JEqB.abs hq (Ctx.JEqB.cumul hq (Nat.le_max_left n m) hP)
    (fun p hp => (hdata p hp).1) (fun p hp => (hdata p hp).2)
  simpa only [Description.reifyHypotheses, positions_lst, Description.positionAt] using hterm

/-- Actual source IH application has no residual recursive lambda or projection of a reconstructed pair. -/
theorem reifyHypotheses_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {m : ℕ}
    (hm : RuleBudget.Allows levels (m + 1)) {C l f c r p : Tm 0}
    (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hr : Γ.JEqB levels H (.pi (S.positions.lst l)
      ((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0)))) r r)
    (hp : Γ.JEqB levels H (S.positions.lst l) p p) :
    Γ.JEqB levels H (.app (.app C (S.childIndexAt l p)) (.app (S.reifyChildren l f c) p))
      (.app (S.reifyHypotheses l c r) p) (.app (.app r p) (.snd (.app c p))) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hq : RuleBudget.Allows levels (max n m) := RuleBudget.Allows.max hn (by budget_omega)
  have hP := positions_instance_formation_of_hypotheses hH D.toFormationData hl
  have hdata := reifyHypotheses_data_of_hypotheses hH D hm hC hl hf hc hr
  simpa only [Description.reifyHypotheses, positions_lst, Description.positionAt, Tm.lst,
    Tm.closed_wk0_lst, childIndexAt_lst, lastCases_zero, Tm.castLE_refl] using
    Ctx.JEqB.beta_app hq (Ctx.JEqB.cumul hq (Nat.le_max_left n m) hP)
      (fun p hp => (hdata p hp).1) (fun p hp => (hdata p hp).2) hp


theorem positions_instance_formation (D : FormationData S levels n Γ) {l : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l) :
    Γ.JEqB levels ∅ (.univ n) (S.positions.lst l) (S.positions.lst l) :=
  positions_instance_formation_of_hypotheses (StructuralTheory.empty levels) D hl

theorem coherentChild_witness_typing (D : IndexedFormationData S levels n Γ) {l f c p : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hp : Γ.JEqB levels ∅ (S.positions.lst l) p p) :
    Γ.JEqB levels ∅
      (.sigma (.id S.index (S.root (.app f p)) (S.childIndexAt l p)) (S.coherence n (.app f p)).wk0)
      (.app c p) (.app c p) :=
  coherentChild_witness_typing_of_hypotheses (StructuralTheory.empty levels) D hl hf hc hp

theorem coherentChild_typing (D : IndexedFormationData S levels n Γ) {l f c p : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hp : Γ.JEqB levels ∅ (S.positions.lst l) p p) :
    Γ.JEqB levels ∅ (S.fibre n (S.childIndexAt l p))
      (.pair (.app f p) (.app c p)) (.pair (.app f p) (.app c p)) :=
  coherentChild_typing_of_hypotheses (StructuralTheory.empty levels) D hl hf hc hp

theorem reifyChildren_typing (D : IndexedFormationData S levels n Γ) {l f c : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    Γ.JEqB levels ∅ (.pi (S.positions.lst l) (S.childFibres n l))
      (S.reifyChildren l f c) (S.reifyChildren l f c) :=
  reifyChildren_typing_of_hypotheses (StructuralTheory.empty levels) D hl hf hc

theorem reifyChildren_beta (D : IndexedFormationData S levels n Γ) {l f c p : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hp : Γ.JEqB levels ∅ (S.positions.lst l) p p) :
    Γ.JEqB levels ∅ (S.fibre n (S.childIndexAt l p))
      (.app (S.reifyChildren l f c) p) (.pair (.app f p) (.app c p)) :=
  reifyChildren_beta_of_hypotheses (StructuralTheory.empty levels) D hl hf hc hp

theorem coherentHypothesis_typing (D : IndexedFormationData S levels n Γ) {m : ℕ}
    (hm : RuleBudget.Allows levels (m + 1)) {C l f c r p : Tm 0}
    (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hr : Γ.JEqB levels ∅ (.pi (S.positions.lst l)
      ((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0)))) r r)
    (hp : Γ.JEqB levels ∅ (S.positions.lst l) p p) :
    Γ.JEqB levels ∅
      (.app (.app C (S.childIndexAt l p)) (.pair (.app f p) (.app c p)))
      (.app (.app r p) (.snd (.app c p)))
      (.app (.app r p) (.snd (.app c p))) :=
  coherentHypothesis_typing_of_hypotheses (StructuralTheory.empty levels) D hm hC hl hf hc hr hp

theorem reifyHypotheses_typing (D : IndexedFormationData S levels n Γ) {m : ℕ}
    (hm : RuleBudget.Allows levels (m + 1)) {C l f c r : Tm 0}
    (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hr : Γ.JEqB levels ∅ (.pi (S.positions.lst l)
      ((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0)))) r r) :
    Γ.JEqB levels ∅ (.pi (S.positions.lst l)
      (.app (.app C.wk0 (S.childIndexAt l.wk0 (.bv 0))) (.app (S.reifyChildren l f c).wk0 (.bv 0))))
      (S.reifyHypotheses l c r) (S.reifyHypotheses l c r) :=
  reifyHypotheses_typing_of_hypotheses (StructuralTheory.empty levels) D hm hC hl hf hc hr

theorem reifyHypotheses_beta (D : IndexedFormationData S levels n Γ) {m : ℕ}
    (hm : RuleBudget.Allows levels (m + 1)) {C l f c r p : Tm 0}
    (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hr : Γ.JEqB levels ∅ (.pi (S.positions.lst l)
      ((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0)))) r r)
    (hp : Γ.JEqB levels ∅ (S.positions.lst l) p p) :
    Γ.JEqB levels ∅ (.app (.app C (S.childIndexAt l p)) (.app (S.reifyChildren l f c) p))
      (.app (S.reifyHypotheses l c r) p) (.app (.app r p) (.snd (.app c p))) :=
  reifyHypotheses_beta_of_hypotheses (StructuralTheory.empty levels) D hm hC hl hf hc hr hp

theorem coherenceWitness_formation (D : IndexedFormationData S levels n Γ) {l f : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f) :
    ∀ p ∉ Γ.dv, (Γ.cons p (S.positions.lst l)).JEqB levels ∅ (.univ n)
      ((.sigma (.id S.index.wk0 (S.root (.app f.wk0 (.bv 0))) (S.childIndexAt l.wk0 (.bv 0)))
        (S.coherence n (.app f.wk0 (.bv 0))).wk0 : Tm 1).open p) ((.sigma (.id S.index.wk0 (S.root (.app f.wk0 (.bv 0))) (S.childIndexAt l.wk0 (.bv 0)))
        (S.coherence n (.app f.wk0 (.bv 0))).wk0 : Tm 1).open p) :=
  coherenceWitness_formation_of_hypotheses (StructuralTheory.empty levels) D hl hf

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
