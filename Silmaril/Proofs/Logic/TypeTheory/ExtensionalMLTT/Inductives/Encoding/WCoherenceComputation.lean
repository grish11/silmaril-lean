module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Computation.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.ConstantStepComputation

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

variable {H : Set Jdg} {S : Description} {levels : RuleBudget} {n : ℕ} {Γ : Ctx}

theorem root_lst {k : ℕ} (S : Description) (t : Tm (k + 1)) (a : Tm 0) :
    (S.root t).lst a = S.root (t.lst a) := by
  simp only [Description.root, Tm.lst, Tm.closed_castLE_lst]
  rw [Tm.lst_castLE S.positions (by budget_omega)]

theorem coherence_lst {k : ℕ} (S : Description) (n : ℕ) (t : Tm (k + 1)) (a : Tm 0) :
    (S.coherence n t).lst a = S.coherence n (t.lst a) := by
  simp only [Description.coherence, Tm.lst, Tm.closed_castLE_lst]
  rw [Tm.lst_castLE S.positions (by budget_omega)]

theorem childIndexAt_lst {k : ℕ} (S : Description) (l p : Tm (k + 1)) (a : Tm 0) :
    (S.childIndexAt l p).lst a = S.childIndexAt (l.lst a) (p.lst a) := by
  simp only [Description.childIndexAt, Tm.lst_bsubst]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun _ => ?_) j) i <;>
    simp only [Fin.cases_zero, Fin.cases_succ, Tm.lst]

theorem coherenceBody_lst (S : Description) (l f r : Tm 0) :
    ((S.coherenceBody.lst l).lst f).lst r =
      .pi (S.positions.lst l)
        (.sigma (.id S.index.wk0
          (S.root (.app f.wk0 (.bv 0)))
          (S.childIndexAt l.wk0 (.bv 0)))
          (.app (r.castLE (by decide)) (.bv 1))) := by
  have h2 : (((Tm.bv (2 : Fin 4)).lst l).lst f).lst r =
      (f.castLE (by decide) : Tm 1) := by
    simp only [Tm.lst, show (2 : Fin 4) = Fin.castSucc (Fin.last 2) from rfl,
      Fin.lastCases_castSucc, Fin.lastCases_last, Tm.closed_castLE_lst]
  have h3 : (((Tm.bv (3 : Fin 4)).lst l).lst f).lst r =
      (l.castLE (by decide) : Tm 1) := by
    simp only [Tm.lst, show (3 : Fin 4) = Fin.last 3 from rfl, Fin.lastCases_last, Tm.closed_castLE_lst]
  have h0 : (((Tm.bv (0 : Fin 4)).lst l).lst f).lst r =
      (.bv 0 : Tm 1) := by
    simp only [Tm.lst,
      show (0 : Fin 4) = Fin.castSucc (Fin.castSucc (Fin.castSucc (0 : Fin 1))) from rfl,
      Fin.lastCases_castSucc]
  have hih : (((Tm.bv (2 : Fin 5)).lst l).lst f).lst r =
      (r.castLE (by decide) : Tm 2) := by
    simp only [Tm.lst,
      show (2 : Fin 5) = Fin.castSucc (Fin.castSucc (Fin.last 2)) from rfl,
      Fin.lastCases_castSucc, Fin.lastCases_last]
  have hp : (((Tm.bv (1 : Fin 5)).lst l).lst f).lst r =
      (.bv 1 : Tm 2) := by
    simp only [Tm.lst,
      show (1 : Fin 5) = Fin.castSucc (Fin.castSucc (Fin.castSucc (1 : Fin 2))) from rfl,
      Fin.lastCases_castSucc]
  simp only [Description.coherenceBody, Tm.lst, root_lst, childIndexAt_lst,
    Tm.closed_castLE_lst, Tm.lst_bsubst]
  congr 1
  · conv_rhs => rw [Tm.lst_eq_bsubst]
    congr 1
    funext i
    fin_cases i
    simp only [show (2 : Fin 3) = Fin.last 2 from rfl,
      Fin.lastCases_last, Tm.closed_castLE_lst, Tm.castLE_refl]
    exact (Fin.lastCases_last (n := 0) (motive := fun _ => Tm 0) (last := l) (cast := Tm.bv)).symm
  · simp only [Tm.lst] at h2 h3 h0 hih hp
    rw [h2, h3, h0, hih, hp]
    have hi : S.index.castLE (by decide : 0 ≤ 1) = S.index.wk0 :=
      (Tm.wkn_past S.index 0 (by decide)).symm
    rw [hi]
    rw [← Tm.wkn_past f 0 (by decide), ← Tm.wkn_past l 0 (by decide)]
    rfl


/-- Original coherence computes through all three step applications. -/
theorem coherence_sup_beta_iterated_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f) :
    let R := Tm.recChildren S.totalShape S.positions (.univ n) (S.coherenceStep n) l f
    Γ.JEqB levels H (.univ n) (S.coherence n (.sup S.totalShape S.positions l f))
      (((S.coherenceBody.lst l).lst f).lst R) := by
  intro R
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hA : Γ.JEqB levels H (.univ n) S.totalShape S.totalShape := totalShape_formation D.toFormationData
  have hA' := Ctx.JEqB.cumul D.bound (Nat.le_succ n) hA
  have hP' : ∀ x ∉ Γ.dv, (Γ.cons x S.totalShape).JEqB levels H (.univ (n + 1))
      (S.positions.open x) (S.positions.open x) :=
    fun x hx => .cumul D.bound (Nat.le_succ n) (positions_formation_of_hypotheses hH D.toFormationData x hx)
  have hR : Γ.JEqB levels H (.arr (S.positions.lst l) (.univ n)) R R := by
    simpa only [Tm.wk0, Tm.wkn] using Ctx.JEqB.recChildren_constant_typing_of_hypotheses hH D.bound D.context
      hA' (.univ D.bound D.context) hP' (coherenceStep_typing_of_hypotheses hH D) hl hf
  have hC : ∀ x ∉ Γ.dv, (Γ.cons x S.raw).JEqB levels H (.univ (n + 1))
      ((.univ n : Tm 1).open x) ((.univ n : Tm 1).open x) := by
    intro x hx
    simpa only [Tm.open] using Ctx.JEqB.univ D.bound
      (.cons_ok hn D.context hx (raw_formation_of_hypotheses hH D.toFormationData))
  have hrec : Γ.JEqB levels H (.univ n)
      (S.coherence n (.sup S.totalShape S.positions l f))
      (.app (.app (.app (S.coherenceStep n) l) f) R) := by
    simpa only [Description.coherence, Tm.castLE_refl, Tm.lst] using
      Ctx.JEqB.beta_wrec hn D.bound hA (positions_formation_of_hypotheses hH D.toFormationData) hC
        (coherenceStep_typing_of_hypotheses hH D) hl hf
  have hstep : Γ.JEqB levels H (.univ n)
      (.app (.app (.app (S.coherenceStep n) l) f) R)
      (((S.coherenceBody.lst l).lst f).lst R) := by
    simpa only [coherenceStep_eq_constantStep, Description.raw, Tm.castLE] using
      Ctx.JEqB.constantStep_beta_of_hypotheses hH D.bound D.context hA' (.univ D.bound D.context) hP'
        (coherenceBody_typing_of_hypotheses hH D) hl hf hR
  exact hrec.trans hstep

/-- The original coherence layer with explicit recursive W calls. -/
theorem coherence_sup_beta_recursive_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f) :
    let R := Tm.recChildren S.totalShape S.positions (.univ n) (S.coherenceStep n) l f
    Γ.JEqB levels H (.univ n) (S.coherence n (.sup S.totalShape S.positions l f))
      (.pi (S.positions.lst l)
        (.sigma (.id S.index.wk0 (S.root (.app f.wk0 (.bv 0))) (S.childIndexAt l.wk0 (.bv 0)))
          (.app (R.castLE (by decide)) (.bv 1)))) := by
  simpa only [coherenceBody_lst] using coherence_sup_beta_iterated_of_hypotheses hH D hl hf

private theorem recursiveLayer_open (S : Description) (l f r : Tm 0) (p : String) :
    (.sigma (.id S.index.wk0 (S.root (.app f.wk0 (.bv 0)))
      (S.childIndexAt l.wk0 (.bv 0)))
      (.app (r.castLE (by decide)) (.bv 1)) : Tm 1).open p =
    .sigma (.id S.index (S.root (.app f (.fv p))) (S.childIndexAt l (.fv p)))
      ((.app r (.fv p) : Tm 0).wk0) := by
  simp only [Tm.open, Tm.closed_wk0_open, root_open, childIndexAt_open,
    Tm.closed_castLE_open]
  change Tm.sigma (.id S.index (S.root (.app f (.fv p))) (S.childIndexAt l (.fv p)))
    (.app (r.castLE (by decide)) (Fin.lastCases (.fv p) Tm.bv (Fin.last 1))) = _
  rw [Fin.lastCases_last]
  congr 1
  simp only [Tm.wk0, Tm.wkn]
  rw [Tm.wkn_past r 0 (by decide)]


private theorem lastCases_zero {α : Sort _} (a : α) (f : Fin 0 → α) :
    Fin.lastCases a f (0 : Fin 1) = a := Fin.lastCases_last

private theorem open_wk0 (t : Tm 1) (x : String) : t.wk0.open x = (t.open x).wk0 :=
  Tm.open_wkn t x 0 (Nat.zero_le _)

theorem normalizedLayer_open (S : Description) (n : ℕ) (l f : Tm 0) (p : String) :
    ((.sigma
      (.id S.index.wk0 (S.root (.app f.wk0 (.bv 0))) (S.childIndexAt l.wk0 (.bv 0)))
      (S.coherence n (.app f.wk0 (.bv 0))).wk0 : Tm 1).open p) =
    .sigma (.id S.index (S.root (.app f (.fv p))) (S.childIndexAt l (.fv p)))
      (S.coherence n (.app f (.fv p))).wk0 := by
  simp only [Tm.open, root_open, childIndexAt_open, Tm.closed_wk0_open,
    open_wk0, coherence_open, lastCases_zero]

/-- Every edge of an original node computes to its original child coherence type. -/
theorem coherence_sup_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f) :
    Γ.JEqB levels H (.univ n) (S.coherence n (.sup S.totalShape S.positions l f))
      (.pi (S.positions.lst l)
        (.sigma (.id S.index.wk0 (S.root (.app f.wk0 (.bv 0))) (S.childIndexAt l.wk0 (.bv 0)))
          (S.coherence n (.app f.wk0 (.bv 0))).wk0)) := by
  let R := Tm.recChildren S.totalShape S.positions (.univ n) (S.coherenceStep n) l f
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hP : Γ.JEqB levels H (.univ n) (S.positions.lst l) (S.positions.lst l) :=
    (compiledPositions_beta_of_hypotheses hH D.toFormationData hl).symm.trans
      (compiledPositions_beta_of_hypotheses hH D.toFormationData hl)
  have hbase : Γ.JEqB levels H (.univ n) (S.coherence n (.sup S.totalShape S.positions l f))
      (.pi (S.positions.lst l)
        (.sigma (.id S.index.wk0 (S.root (.app f.wk0 (.bv 0))) (S.childIndexAt l.wk0 (.bv 0)))
          (.app (R.castLE (by decide)) (.bv 1)))) := coherence_sup_beta_recursive_of_hypotheses hH D hl hf
  apply hbase.trans
  apply Ctx.JEqB.pi (L := Γ.dv) hn hP
  intro p hp
  have hctx : (Γ.cons p (S.positions.lst l)).JEqB levels H .unit .star .star :=
    .cons_ok hn D.context hp hP
  have dp := D.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hp (S.positions.lst l)) hctx
  have hl' := D.context.weaken_cons_of_hypotheses hH.weakening hp hn hP hl
  have hf' := D.context.weaken_cons_of_hypotheses hH.weakening hp hn hP hf
  have hp' : (Γ.cons p (S.positions.lst l)).JEqB levels H (S.positions.lst l) (.fv p) (.fv p) :=
    .var hctx (.here Γ p (S.positions.lst l))
  have hchild : (Γ.cons p (S.positions.lst l)).JEqB levels H S.raw
      (.app f (.fv p)) (.app f (.fv p)) :=
    Ctx.JEqB.arrow_application_of_hypotheses hH.weakening hn hctx (D.context.weaken_cons_of_hypotheses hH.weakening hp hn hP hP)
      (raw_formation_of_hypotheses hH dp.toFormationData) hf' hp'
  have hE : (Γ.cons p (S.positions.lst l)).JEqB levels H (.univ n)
      (.id S.index (S.root (.app f (.fv p))) (S.childIndexAt l (.fv p)))
      (.id S.index (S.root (.app f (.fv p))) (S.childIndexAt l (.fv p))) :=
    .id hn dp.index (root_typing_of_hypotheses hH dp.toFormationData hchild) (childIndexAt_typing_of_hypotheses hH dp hl' hp')
  have hrecursive : (Γ.cons p (S.positions.lst l)).JEqB levels H (.univ n)
      (.app R (.fv p)) (S.coherence n (.app f (.fv p))) := by
    simpa only [Description.coherence, Tm.castLE_refl, Tm.wk0, Tm.wkn] using
      Ctx.JEqB.recChildren_constant_beta_of_hypotheses hH dp.bound dp.context
        (Ctx.JEqB.cumul dp.bound (Nat.le_succ n) (totalShape_formation dp.toFormationData))
        (.univ dp.bound dp.context)
        (fun x hx => Ctx.JEqB.cumul dp.bound (Nat.le_succ n) (positions_formation_of_hypotheses hH dp.toFormationData x hx))
        (coherenceStep_typing_of_hypotheses hH dp) hl' hf' hp'
  have hSigma : (Γ.cons p (S.positions.lst l)).JEqB levels H (.univ n)
      (.sigma (.id S.index (S.root (.app f (.fv p))) (S.childIndexAt l (.fv p)))
        (Tm.app R (.fv p)).wk0)
      (.sigma (.id S.index (S.root (.app f (.fv p))) (S.childIndexAt l (.fv p)))
        (S.coherence n (.app f (.fv p))).wk0) := by
    apply Ctx.JEqB.sigma (L := (Γ.cons p (S.positions.lst l)).dv) hn hE
    intro e he
    simpa only [Tm.closed_wk0_open] using hctx.weaken_cons_of_hypotheses hH.weakening he hn hE hrecursive
  simpa only [recursiveLayer_open, normalizedLayer_open] using hSigma


theorem coherence_sup_beta_iterated (D : IndexedFormationData S levels n Γ) {l f : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f) :
    let R := Tm.recChildren S.totalShape S.positions (.univ n) (S.coherenceStep n) l f
    Γ.JEqB levels ∅ (.univ n) (S.coherence n (.sup S.totalShape S.positions l f))
      (((S.coherenceBody.lst l).lst f).lst R) :=
  coherence_sup_beta_iterated_of_hypotheses (StructuralTheory.empty levels) D hl hf

theorem coherence_sup_beta_recursive (D : IndexedFormationData S levels n Γ) {l f : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f) :
    let R := Tm.recChildren S.totalShape S.positions (.univ n) (S.coherenceStep n) l f
    Γ.JEqB levels ∅ (.univ n) (S.coherence n (.sup S.totalShape S.positions l f))
      (.pi (S.positions.lst l)
        (.sigma (.id S.index.wk0 (S.root (.app f.wk0 (.bv 0))) (S.childIndexAt l.wk0 (.bv 0)))
          (.app (R.castLE (by decide)) (.bv 1)))) :=
  coherence_sup_beta_recursive_of_hypotheses (StructuralTheory.empty levels) D hl hf

theorem coherence_sup_beta (D : IndexedFormationData S levels n Γ) {l f : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f) :
    Γ.JEqB levels ∅ (.univ n) (S.coherence n (.sup S.totalShape S.positions l f))
      (.pi (S.positions.lst l)
        (.sigma (.id S.index.wk0 (S.root (.app f.wk0 (.bv 0))) (S.childIndexAt l.wk0 (.bv 0)))
          (S.coherence n (.app f.wk0 (.bv 0))).wk0)) :=
  coherence_sup_beta_of_hypotheses (StructuralTheory.empty levels) D hl hf

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
