module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Direct
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.ConstantStep

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

variable {S : Description} {levels : RuleBudget} {n : ℕ} {Γ : Ctx}

theorem root_open {k : ℕ} (S : Description) (t : Tm (k + 1)) (x : String) :
    (S.root t).open x = S.root (t.open x) := by
  simp only [Description.root, Tm.open, Tm.closed_castLE_open]
  rw [Tm.open_castLE S.positions (by budget_omega)]

theorem coherence_open {k : ℕ} (S : Description) (n : ℕ) (t : Tm (k + 1)) (x : String) :
    (S.coherence n t).open x = S.coherence n (t.open x) := by
  simp only [Description.coherence, Tm.open, Tm.closed_castLE_open]
  rw [Tm.open_castLE S.positions (by budget_omega)]

theorem childIndexAt_open {k : ℕ} (S : Description) (l p : Tm (k + 1)) (x : String) :
    (S.childIndexAt l p).open x = S.childIndexAt (l.open x) (p.open x) := by
  simp only [Description.childIndexAt, Tm.open_bsubst]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun _ => ?_) j) i <;> simp only [Fin.cases_zero, Fin.cases_succ, Tm.open]

theorem coherenceBody_open (S : Description) (label children ih : String) :
    ((S.coherenceBody.open label).open children).open ih =
      .pi (S.positions.lst (.fv label))
        (.sigma (.id S.index.wk0
          (S.root (.app (.fv children) (.bv 0)))
          (S.childIndexAt (.fv label) (.bv 0)))
          (.app (.fv ih) (.bv 1))) := by
  have h2 : (((Tm.bv (2 : Fin 4)).open label).open children).open ih =
      (.fv children : Tm 1) := by
    simp only [Tm.open, show (2 : Fin 4) = Fin.castSucc (Fin.last 2) from rfl,
      Fin.lastCases_castSucc, Fin.lastCases_last]
  have h3 : (((Tm.bv (3 : Fin 4)).open label).open children).open ih =
      (.fv label : Tm 1) := by
    simp only [Tm.open, show (3 : Fin 4) = Fin.last 3 from rfl, Fin.lastCases_last]
  have h0 : (((Tm.bv (0 : Fin 4)).open label).open children).open ih =
      (.bv 0 : Tm 1) := by
    simp only [Tm.open,
      show (0 : Fin 4) = Fin.castSucc (Fin.castSucc (Fin.castSucc (0 : Fin 1))) from rfl,
      Fin.lastCases_castSucc]
  have hih : (((Tm.bv (2 : Fin 5)).open label).open children).open ih =
      (.fv ih : Tm 2) := by
    simp only [Tm.open,
      show (2 : Fin 5) = Fin.castSucc (Fin.castSucc (Fin.last 2)) from rfl,
      Fin.lastCases_castSucc, Fin.lastCases_last]
  have hp : (((Tm.bv (1 : Fin 5)).open label).open children).open ih =
      (.bv 1 : Tm 2) := by
    simp only [Tm.open,
      show (1 : Fin 5) = Fin.castSucc (Fin.castSucc (Fin.castSucc (1 : Fin 2))) from rfl,
      Fin.lastCases_castSucc]
  simp only [Description.coherenceBody, Tm.open, root_open, childIndexAt_open,
    Tm.closed_castLE_open, Tm.open_bsubst]
  congr 1
  · rw [Tm.lst_eq_bsubst]
    congr 1
    funext i
    fin_cases i
    simp only [show (2 : Fin 3) = Fin.last 2 from rfl,
      Fin.lastCases_last, Tm.open, Tm.castLE]
    exact (Fin.lastCases_last (n := 0) (motive := fun _ => Tm 0) (last := .fv label) (cast := Tm.bv)).symm
  · simp only [Tm.open] at h2 h3 h0 hih hp
    rw [h2, h3, h0, hih, hp]
    have hi : S.index.castLE (by decide : 0 ≤ 1) = S.index.wk0 :=
      (Tm.wkn_past S.index 0 (by decide)).symm
    rw [hi]

/-- Preserve the original next premise, including its full dependent telescope. -/
def indexedWeakenData_of_hypotheses {H K : Set Jdg} {Δ : Ctx} (D : IndexedFormationData S levels n Γ H)
    (hh : HypothesisTransport levels H K)
    (e : Γ.LookupLE Δ) (hΔ : Δ.JEqB levels K .unit .star .star) :
    IndexedFormationData S levels n Δ K where
  toFormationData := D.toFormationData.weaken_of_hypotheses hh e hΔ
  next x hx y hy p hp := by
    have hxS : x ∉ D.names := fun h => hx (Finset.mem_union_left _ h)
    have hxΔ : x ∉ Δ.dv := fun h => hx (Finset.mem_union_right _ h)
    have hyx : y ≠ x := fun h => hy (h ▸ Finset.mem_insert_self x (D.names ∪ Δ.dv))
    have hyΔ : y ∉ Δ.dv := fun h => hy (Finset.mem_insert_of_mem (Finset.mem_union_right _ h))
    have hyS : y ∉ insert x D.names := by
      simpa only [Finset.mem_insert, not_or] using And.intro hyx
        (show y ∉ D.names from fun h => hy (Finset.mem_insert_of_mem (Finset.mem_union_left _ h)))
    have hpx : p ≠ x := by
      intro h
      exact hp (Finset.mem_insert_of_mem (h ▸ Finset.mem_insert_self x (D.names ∪ Δ.dv)))
    have hpy : p ≠ y := fun h => hp (h ▸ Finset.mem_insert_self y (insert x (D.names ∪ Δ.dv)))
    have hpΔ : p ∉ Δ.dv := fun h => hp
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_right _ h)))
    have hpS : p ∉ insert y (insert x D.names) := by
      simpa only [Finset.mem_insert, not_or, and_assoc] using
        And.intro hpy (And.intro hpx (show p ∉ D.names from fun h => hp
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _ h)))))
    have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
    have hctx : (Δ.cons x S.index).JEqB levels K .unit .star .star :=
      .cons_ok hn hΔ hxΔ (D.index.weaken_of_hypotheses hh e hΔ)
    have hshape : (Δ.cons x S.index).JEqB levels K (.univ n)
        (S.shape.open x) (S.shape.open x) := (D.shape x hxS).weaken_of_hypotheses hh (e.cons x S.index) hctx
    have hctx' : ((Δ.cons x S.index).cons y (S.shape.open x)).JEqB levels K .unit .star .star :=
      .cons_ok hn hctx
        (by simpa only [Ctx.dv, Finset.mem_insert, not_or] using And.intro hyx hyΔ) hshape
    have hpositions : ((Δ.cons x S.index).cons y (S.shape.open x)).JEqB levels K (.univ n)
        ((S.position.open x).open y) ((S.position.open x).open y) :=
      (D.position x hxS y hyS).weaken_of_hypotheses hh
        (Ctx.LookupLE.cons (Ctx.LookupLE.cons e x S.index) y (S.shape.open x)) hctx'
    have hctx'' : (((Δ.cons x S.index).cons y (S.shape.open x)).cons p
        ((S.position.open x).open y)).JEqB levels K .unit .star .star :=
      .cons_ok hn hctx'
        (by simpa only [Ctx.dv, Finset.mem_insert, not_or, and_assoc] using
          And.intro hpy (And.intro hpx hpΔ)) hpositions
    exact (D.next x hxS y hyS p hpS).weaken_of_hypotheses hh
      (Ctx.LookupLE.cons
        (Ctx.LookupLE.cons (Ctx.LookupLE.cons e x S.index) y (S.shape.open x))
        p ((S.position.open x).open y)) hctx''

private theorem positionsAt_formation_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) {l : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l) :
    Γ.JEqB levels H (.univ n) (S.positions.lst l) (S.positions.lst l) :=
  (compiledPositions_beta_of_hypotheses hH D hl).symm.trans (compiledPositions_beta_of_hypotheses hH D hl)

/-- Both components of one edge's coherence sigma are actual small types. -/
theorem edgeCoherence_formation_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f r p : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hr : Γ.JEqB levels H (.arr (S.positions.lst l) (.univ n)) r r)
    (hp : Γ.JEqB levels H (S.positions.lst l) p p) :
    Γ.JEqB levels H (.univ n)
      (.sigma (.id S.index (S.root (.app f p)) (S.childIndexAt l p))
        (Tm.app r p).wk0)
      (.sigma (.id S.index (S.root (.app f p)) (S.childIndexAt l p))
        (Tm.app r p).wk0) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hP : Γ.JEqB levels H (.univ n) (S.positions.lst l) (S.positions.lst l) :=
    positionsAt_formation_of_hypotheses hH D.toFormationData hl
  have hchild : Γ.JEqB levels H S.raw (.app f p) (.app f p) :=
    Ctx.JEqB.arrow_application_of_hypotheses hH.weakening hn D.context hP (raw_formation_of_hypotheses hH D.toFormationData) hf hp
  have hroot : Γ.JEqB levels H S.index (S.root (.app f p)) (S.root (.app f p)) :=
    root_typing_of_hypotheses hH D.toFormationData hchild
  have hnext : Γ.JEqB levels H S.index (S.childIndexAt l p) (S.childIndexAt l p) :=
    childIndexAt_typing_of_hypotheses hH D hl hp
  have hEq : Γ.JEqB levels H (.univ n)
      (.id S.index (S.root (.app f p)) (S.childIndexAt l p))
      (.id S.index (S.root (.app f p)) (S.childIndexAt l p)) :=
    .id hn D.index hroot hnext
  have hIH : Γ.JEqB levels H (.univ n) (.app r p) (.app r p) :=
    Ctx.JEqB.arrow_application_of_hypotheses hH.weakening D.bound D.context
      (.cumul D.bound (Nat.le_succ n) hP) (.univ D.bound D.context) hr hp
  exact .sigma hn hEq (Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn D.context hEq hIH)

private def coherenceLayer (S : Description) (l f r : Tm 0) : Tm 0 :=
  .pi (S.positions.lst l)
    (.sigma
      (.id S.index.wk0 (S.root (.app f.wk0 (.bv 0))) (S.childIndexAt l.wk0 (.bv 0)))
      (.app (r.castLE (by decide)) (.bv 1)))

private theorem coherenceLayer_open (S : Description) (l f r : Tm 0) (p : String) :
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

/-- The whole pointwise layer, with original root/next operations on every child. -/
private theorem coherenceLayer_formation_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f r : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hr : Γ.JEqB levels H (.arr (S.positions.lst l) (.univ n)) r r) :
    Γ.JEqB levels H (.univ n) (coherenceLayer S l f r) (coherenceLayer S l f r) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hP : Γ.JEqB levels H (.univ n) (S.positions.lst l) (S.positions.lst l) :=
    positionsAt_formation_of_hypotheses hH D.toFormationData hl
  apply Ctx.JEqB.pi (L := Γ.dv) hn hP
  intro p hp
  have hctx : (Γ.cons p (S.positions.lst l)).JEqB levels H .unit .star .star :=
    .cons_ok hn D.context hp hP
  have hd := indexedWeakenData_of_hypotheses D hH.weakening (Ctx.LookupLE.fresh_cons hp (S.positions.lst l)) hctx
  have hl' := D.context.weaken_cons_of_hypotheses hH.weakening hp hn hP hl
  have hf' := D.context.weaken_cons_of_hypotheses hH.weakening hp hn hP hf
  have hr' := D.context.weaken_cons_of_hypotheses hH.weakening hp hn hP hr
  have hp' : (Γ.cons p (S.positions.lst l)).JEqB levels H (S.positions.lst l) (.fv p) (.fv p) :=
    .var hctx (.here Γ p (S.positions.lst l))
  simpa only [coherenceLayer_open] using edgeCoherence_formation_of_hypotheses hH hd hl' hf' hr' hp'

private theorem lst_fv (B : Tm 1) (x : String) : B.lst (.fv x) = B.open x := by
  rw [Tm.lst_eq_bsubst, Tm.open_eq_bsubst]
  simp only [Tm.castLE]

theorem coherenceBody_typing_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) :
    ∀ x ∉ Γ.dv, ∀ f ∉ insert x Γ.dv, ∀ r ∉ insert f (insert x Γ.dv),
      (((Γ.cons x S.totalShape).cons f (.arr (S.positions.open x) S.raw)).cons r
        (.arr (S.positions.open x) (.univ n))).JEqB levels H (.univ n)
        (((S.coherenceBody.open x).open f).open r)
        (((S.coherenceBody.open x).open f).open r) := by
  intro x hx f hf r hr
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hA : Γ.JEqB levels H (.univ n) S.totalShape S.totalShape := totalShape_formation D.toFormationData
  have hctxL : (Γ.cons x S.totalShape).JEqB levels H .unit .star .star :=
    .cons_ok hn D.context hx hA
  have dL := indexedWeakenData_of_hypotheses D hH.weakening (Ctx.LookupLE.fresh_cons hx S.totalShape) hctxL
  have hP : (Γ.cons x S.totalShape).JEqB levels H (.univ n)
      (S.positions.open x) (S.positions.open x) := positions_formation_of_hypotheses hH D.toFormationData x hx
  have hF : (Γ.cons x S.totalShape).JEqB levels H (.univ n)
      (.arr (S.positions.open x) S.raw) (.arr (S.positions.open x) S.raw) :=
    Ctx.JEqB.arrow_formation_of_hypotheses hH.weakening hn hctxL hP (raw_formation_of_hypotheses hH dL.toFormationData)
  have hR : (Γ.cons x S.totalShape).JEqB levels H (.univ (n + 1))
      (.arr (S.positions.open x) (.univ n)) (.arr (S.positions.open x) (.univ n)) :=
    Ctx.JEqB.arrow_formation_of_hypotheses hH.weakening D.bound hctxL (.cumul D.bound (Nat.le_succ n) hP)
      (.univ D.bound hctxL)
  have hfCtx : f ∉ (Γ.cons x S.totalShape).dv := by simpa only [Ctx.dv] using hf
  have hctxF : ((Γ.cons x S.totalShape).cons f (.arr (S.positions.open x) S.raw)).JEqB
      levels H .unit .star .star := .cons_ok hn hctxL hfCtx hF
  have dF := indexedWeakenData_of_hypotheses dL hH.weakening
    (Ctx.LookupLE.fresh_cons hfCtx (.arr (S.positions.open x) S.raw)) hctxF
  have hRF : ((Γ.cons x S.totalShape).cons f (.arr (S.positions.open x) S.raw)).JEqB
      levels H (.univ (n + 1))
      (.arr (S.positions.open x) (.univ n)) (.arr (S.positions.open x) (.univ n)) :=
    hctxL.weaken_cons_of_hypotheses hH.weakening hfCtx hn hF hR
  have hrCtx : r ∉ ((Γ.cons x S.totalShape).cons f (.arr (S.positions.open x) S.raw)).dv := by
    simpa only [Ctx.dv] using hr
  have hctxR : (((Γ.cons x S.totalShape).cons f (.arr (S.positions.open x) S.raw)).cons r
      (.arr (S.positions.open x) (.univ n))).JEqB levels H .unit .star .star :=
    .cons_ok D.bound hctxF hrCtx hRF
  have dR := indexedWeakenData_of_hypotheses dF hH.weakening
    (Ctx.LookupLE.fresh_cons hrCtx (.arr (S.positions.open x) (.univ n))) hctxR
  have hl : (Γ.cons x S.totalShape).JEqB levels H S.totalShape (.fv x) (.fv x) :=
    .var hctxL (.here Γ x S.totalShape)
  have hlF := hctxL.weaken_cons_of_hypotheses hH.weakening hfCtx hn hF hl
  have hlR := hctxF.weaken_cons_of_hypotheses hH.weakening hrCtx D.bound hRF hlF
  have hfF : ((Γ.cons x S.totalShape).cons f (.arr (S.positions.open x) S.raw)).JEqB
      levels H (.arr (S.positions.open x) S.raw) (.fv f) (.fv f) :=
    .var hctxF (.here _ f (.arr (S.positions.open x) S.raw))
  have hfR := hctxF.weaken_cons_of_hypotheses hH.weakening hrCtx D.bound hRF hfF
  have hrR : (((Γ.cons x S.totalShape).cons f (.arr (S.positions.open x) S.raw)).cons r
      (.arr (S.positions.open x) (.univ n))).JEqB levels H
      (.arr (S.positions.open x) (.univ n)) (.fv r) (.fv r) :=
    .var hctxR (.here _ r (.arr (S.positions.open x) (.univ n)))
  have hresult := coherenceLayer_formation_of_hypotheses hH dR hlR
    (by simpa only [lst_fv] using hfR) (by simpa only [lst_fv] using hrR)
  simpa only [coherenceBody_open, coherenceLayer, Tm.wk0, Tm.wkn, Tm.castLE] using hresult

private theorem single_shift (B : Tm 1) :
    B.bsubst (fun _ => .bv (1 : Fin 2)) = B.wk0 := by
  rw [Tm.wk0, Tm.wkn_eq_bsubst]
  congr 1
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

theorem coherenceStep_eq_constantStep (S : Description) (n : ℕ) :
    S.coherenceStep n =
      .abs S.totalShape (.abs (.arr S.positions (S.raw.castLE (by decide)))
        (.abs ((Tm.arr S.positions (.univ n)).wk0) S.coherenceBody)) := by
  simp [Description.coherenceStep, Description.childrenType, Tm.arr, Tm.wk0,
    Tm.wkn_eq_bsubst, Tm.bsubst, single_shift]

theorem coherenceStep_typing_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) :
    Γ.JEqB levels H (Tm.wStepType S.totalShape S.positions (.univ n))
      (S.coherenceStep n) (S.coherenceStep n) := by
  have hA : Γ.JEqB levels H (.univ n) S.totalShape S.totalShape := totalShape_formation D.toFormationData
  have hbody := coherenceBody_typing_of_hypotheses hH D
  have hstep := Ctx.JEqB.constantStep_typing_of_hypotheses hH.weakening (I := .univ n) D.bound D.context
    (Ctx.JEqB.cumul D.bound (Nat.le_succ n) hA) (.univ D.bound D.context)
    (fun x hx => Ctx.JEqB.cumul D.bound (Nat.le_succ n) (positions_formation_of_hypotheses hH D.toFormationData x hx))
    hbody
  simpa only [coherenceStep_eq_constantStep, Description.raw, Tm.wk0, Tm.wkn, Tm.castLE] using hstep

theorem coherence_formation_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {t : Tm 0}
    (ht : Γ.JEqB levels H S.raw t t) :
    Γ.JEqB levels H (.univ n) (S.coherence n t) (S.coherence n t) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hC : ∀ x ∉ Γ.dv, (Γ.cons x S.raw).JEqB levels H (.univ (n + 1))
      ((.univ n : Tm 1).open x) ((.univ n : Tm 1).open x) := by
    intro x hx
    simpa only [Tm.open] using Ctx.JEqB.univ D.bound
      (.cons_ok hn D.context hx (raw_formation_of_hypotheses hH D.toFormationData))
  simpa only [Description.coherence, Tm.castLE_refl, Tm.lst] using Ctx.JEqB.wrec hn D.bound
    (totalShape_formation D.toFormationData) (positions_formation_of_hypotheses hH D.toFormationData) hC
    (coherenceStep_typing_of_hypotheses hH D) ht

private theorem lastCases_zero {α : Sort _} (a : α) (f : Fin 0 → α) :
    Fin.lastCases a f (0 : Fin 1) = a := Fin.lastCases_last

private theorem lastCases_one {α : Sort _} (a : α) (f : Fin 1 → α) :
    Fin.lastCases a f (1 : Fin 2) = a := Fin.lastCases_last

/-- The original sigma fibre is a small type at every actual source index. -/
theorem fibre_formation_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) :
    Γ.JEqB levels H (.univ n) (S.fibre n i) (S.fibre n i) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  apply Ctx.JEqB.sigma (L := Γ.dv) hn (raw_formation_of_hypotheses hH D.toFormationData)
  intro x hx
  have hctx : (Γ.cons x S.raw).JEqB levels H .unit .star .star :=
    .cons_ok hn D.context hx (raw_formation_of_hypotheses hH D.toFormationData)
  have dx := indexedWeakenData_of_hypotheses D hH.weakening (Ctx.LookupLE.fresh_cons hx S.raw) hctx
  have ht : (Γ.cons x S.raw).JEqB levels H S.raw (.fv x) (.fv x) :=
    .var hctx (.here Γ x S.raw)
  have hi' : (Γ.cons x S.raw).JEqB levels H S.index i i :=
    D.context.weaken_cons_of_hypotheses hH.weakening hx hn (raw_formation_of_hypotheses hH D.toFormationData) hi
  have hroot := root_typing_of_hypotheses hH dx.toFormationData ht
  have hE : (Γ.cons x S.raw).JEqB levels H (.univ n)
      (.id S.index (S.root (.fv x)) i) (.id S.index (S.root (.fv x)) i) :=
    .id hn dx.index hroot hi'
  simp only [Tm.open, Tm.closed_wk0_open, root_open, coherence_open, lastCases_zero,
    lastCases_one]
  apply Ctx.JEqB.sigma (L := (Γ.cons x S.raw).dv) hn hE
  intro e he
  have hctxE : ((Γ.cons x S.raw).cons e (.id S.index (S.root (.fv x)) i)).JEqB
      levels H .unit .star .star := .cons_ok hn hctx he hE
  have de := indexedWeakenData_of_hypotheses dx hH.weakening
    (Ctx.LookupLE.fresh_cons he (.id S.index (S.root (.fv x)) i)) hctxE
  have htE := hctx.weaken_cons_of_hypotheses hH.weakening he hn hE ht
  simpa only [coherence_open, Tm.open] using coherence_formation_of_hypotheses hH de htE

def indexedWeakenData {Δ : Ctx} (D : IndexedFormationData S levels n Γ)
    (e : Γ.LookupLE Δ) (hΔ : Δ.JEqB levels ∅ .unit .star .star) :
    IndexedFormationData S levels n Δ :=
  indexedWeakenData_of_hypotheses D (HypothesisTransport.empty levels ∅) e hΔ

theorem edgeCoherence_formation (D : IndexedFormationData S levels n Γ) {l f r p : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hr : Γ.JEqB levels ∅ (.arr (S.positions.lst l) (.univ n)) r r)
    (hp : Γ.JEqB levels ∅ (S.positions.lst l) p p) :
    Γ.JEqB levels ∅ (.univ n)
      (.sigma (.id S.index (S.root (.app f p)) (S.childIndexAt l p))
        (Tm.app r p).wk0)
      (.sigma (.id S.index (S.root (.app f p)) (S.childIndexAt l p))
        (Tm.app r p).wk0) :=
  edgeCoherence_formation_of_hypotheses (StructuralTheory.empty levels) D hl hf hr hp

theorem coherenceBody_typing (D : IndexedFormationData S levels n Γ) :
    ∀ x ∉ Γ.dv, ∀ f ∉ insert x Γ.dv, ∀ r ∉ insert f (insert x Γ.dv),
      (((Γ.cons x S.totalShape).cons f (.arr (S.positions.open x) S.raw)).cons r
        (.arr (S.positions.open x) (.univ n))).JEqB levels ∅ (.univ n)
        (((S.coherenceBody.open x).open f).open r)
        (((S.coherenceBody.open x).open f).open r) :=
  coherenceBody_typing_of_hypotheses (StructuralTheory.empty levels) D

theorem coherenceStep_typing (D : IndexedFormationData S levels n Γ) :
    Γ.JEqB levels ∅ (Tm.wStepType S.totalShape S.positions (.univ n))
      (S.coherenceStep n) (S.coherenceStep n) :=
  coherenceStep_typing_of_hypotheses (StructuralTheory.empty levels) D

theorem coherence_formation (D : IndexedFormationData S levels n Γ) {t : Tm 0}
    (ht : Γ.JEqB levels ∅ S.raw t t) :
    Γ.JEqB levels ∅ (.univ n) (S.coherence n t) (S.coherence n t) :=
  coherence_formation_of_hypotheses (StructuralTheory.empty levels) D ht

theorem fibre_formation (D : IndexedFormationData S levels n Γ) {i : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) :
    Γ.JEqB levels ∅ (.univ n) (S.fibre n i) (S.fibre n i) :=
  fibre_formation_of_hypotheses (StructuralTheory.empty levels) D hi

/-- Reuse the existing nullary source as satisfiable indexed formation data. -/
def nullaryIndexedFormationData : IndexedFormationData nullaryDescription 2 0 .nil where
  toFormationData := nullaryFormationData
  next x hx y hy p hp := by
    have hyx : y ≠ x := fun h => hy (Finset.mem_insert.mpr (Or.inl h))
    have hctxX : (Ctx.nil.cons x .unit).JEqB 2 ∅ .unit .star .star :=
      .cons_ok (n := 0) (by decide) .nil_ok (by simp [Ctx.dv]) (.unit (by decide) .nil_ok)
    have hctxY : ((Ctx.nil.cons x .unit).cons y .unit).JEqB 2 ∅ .unit .star .star :=
      .cons_ok (n := 0) (by decide) hctxX
        (by simpa only [Ctx.dv, Finset.mem_insert, Finset.notMem_empty, or_false] using hyx)
        (.unit (by decide) hctxX)
    have hpCtx : p ∉ ((Ctx.nil.cons x .unit).cons y .unit).dv := by
      simpa [Ctx.dv, nullaryFormationData] using hp
    have hctxP : (((Ctx.nil.cons x .unit).cons y .unit).cons p .empty).JEqB 2 ∅ .unit .star .star :=
      .cons_ok (n := 0) (by decide) hctxY hpCtx (.empty (by decide) hctxY)
    simpa only [nullaryDescription, Tm.open] using hctxP

def nullaryRawLeaf : Tm 0 :=
  .sup nullaryDescription.totalShape nullaryDescription.positions (.pair .star .star)
    (.abs .empty (.absurd (nullaryDescription.raw.castLE (by decide)) (.bv 0)))

/-- The original raw carrier used by root and coherence actually has a closed term. -/
theorem nullaryRawLeaf_typing : Ctx.JEqB 2 ∅ .nil nullaryDescription.raw
    nullaryRawLeaf nullaryRawLeaf := by
  let D := nullaryIndexedFormationData
  have hraw : Ctx.JEqB 2 ∅ .nil (.univ 0) nullaryDescription.raw nullaryDescription.raw :=
    raw_formation D.toFormationData
  have hlabel : Ctx.JEqB 2 ∅ .nil nullaryDescription.totalShape (.pair .star .star) (.pair .star .star) :=
    .pair (n := 0) (by decide) D.index D.shape .nil_ok
      (by simpa only [nullaryDescription, Tm.lst] using (Ctx.JEqB.nil_ok (levels := 2) (H := ∅)))
  have hfun : Ctx.JEqB 2 ∅ .nil (.arr .empty nullaryDescription.raw)
      (.abs .empty (.absurd (nullaryDescription.raw.castLE (by decide)) (.bv 0)))
      (.abs .empty (.absurd (nullaryDescription.raw.castLE (by decide)) (.bv 0))) := by
    apply Ctx.JEqB.abs (L := ∅) (n := 0) (by decide) (.empty (by decide) .nil_ok)
      (Ctx.JEqB.constant_family (by decide) .nil_ok (.empty (by decide) .nil_ok) hraw)
    intro p hp
    have hctx : (Ctx.nil.cons p .empty).JEqB 2 ∅ .unit .star .star :=
      .cons_ok (n := 0) (by decide) .nil_ok (by simp [Ctx.dv]) (.empty (by decide) .nil_ok)
    have hp' : (Ctx.nil.cons p .empty).JEqB 2 ∅ .empty (.fv p) (.fv p) :=
      .var hctx (.here .nil p .empty)
    simpa only [Tm.open, Tm.closed_castLE_open, Tm.castLE_refl, Tm.closed_wk0_open,
      lastCases_zero] using Ctx.JEqB.absurd (by decide) (hraw.weaken (Ctx.LookupLE.fresh_cons (by simp [Ctx.dv]) .empty) hctx) hp'
  exact Ctx.JEqB.sup (by decide) (totalShape_formation D.toFormationData)
    (positions_formation D.toFormationData) hlabel
    (by simpa only [Description.positions, nullaryDescription, Tm.bsubst, Tm.lst,
      Description.raw] using hfun)

theorem nullary_root_typing : Ctx.JEqB 2 ∅ .nil .unit
    (nullaryDescription.root nullaryRawLeaf) (nullaryDescription.root nullaryRawLeaf) :=
  root_typing nullaryIndexedFormationData.toFormationData nullaryRawLeaf_typing

theorem nullary_coherence_formation : Ctx.JEqB 2 ∅ .nil (.univ 0)
    (nullaryDescription.coherence 0 nullaryRawLeaf) (nullaryDescription.coherence 0 nullaryRawLeaf) :=
  coherence_formation nullaryIndexedFormationData nullaryRawLeaf_typing

theorem nullary_fibre_formation : Ctx.JEqB 2 ∅ .nil (.univ 0)
    (nullaryDescription.fibre 0 .star) (nullaryDescription.fibre 0 .star) :=
  fibre_formation nullaryIndexedFormationData .nil_ok

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
