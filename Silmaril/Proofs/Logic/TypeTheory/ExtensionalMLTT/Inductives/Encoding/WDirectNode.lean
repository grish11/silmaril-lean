module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Node
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Next

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

variable {H : Set Jdg} {S : Description} {levels : RuleBudget} {n : ℕ} {Γ : Ctx}

private theorem lastCases_zero {α : Sort _} (a : α) (f : Fin 0 → α) :
    Fin.lastCases a f (0 : Fin 1) = a := Fin.lastCases_last

private theorem lastCases_one {α : Sort _} (a : α) (f : Fin 1 → α) :
    Fin.lastCases a f (1 : Fin 2) = a := Fin.lastCases_last

/-- The original indexed fibre respects actual equality of its requested index. -/
theorem fibre_congr_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i j : Tm 0}
    (hij : Γ.JEqB levels H S.index i j) :
    Γ.JEqB levels H (.univ n) (S.fibre n i) (S.fibre n j) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  apply Ctx.JEqB.sigma (L := Γ.dv) hn (raw_formation_of_hypotheses hH D.toFormationData)
  intro x hx
  have hctx : (Γ.cons x S.raw).JEqB levels H .unit .star .star :=
    .cons_ok hn D.context hx (raw_formation_of_hypotheses hH D.toFormationData)
  have dx := D.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hx S.raw) hctx
  have ht : (Γ.cons x S.raw).JEqB levels H S.raw (.fv x) (.fv x) :=
    .var hctx (.here Γ x S.raw)
  have hij' := D.context.weaken_cons_of_hypotheses hH.weakening hx hn (raw_formation_of_hypotheses hH D.toFormationData) hij
  have hE : (Γ.cons x S.raw).JEqB levels H (.univ n)
      (.id S.index (S.root (.fv x)) i) (.id S.index (S.root (.fv x)) j) :=
    .id hn dx.index (root_typing_of_hypotheses hH dx.toFormationData ht) hij'
  simp only [Tm.open, Tm.closed_wk0_open, root_open, coherence_open, lastCases_zero, lastCases_one]
  apply Ctx.JEqB.sigma (L := (Γ.cons x S.raw).dv) hn hE
  intro e he
  have hEi := hE.trans hE.symm
  have hcoh := coherence_formation_of_hypotheses hH dx ht
  simpa only [Tm.open, coherence_open] using hctx.weaken_cons_of_hypotheses hH.weakening he hn hEi hcoh

private theorem lst_fv (B : Tm 1) (x : String) : B.lst (.fv x) = B.open x := by
  rw [Tm.lst_eq_bsubst, Tm.open_eq_bsubst]
  simp only [Tm.castLE]

/-- Child inputs are exactly the original next body after its index and shape arguments. -/
theorem childFibres_tagged_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i a : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a) :
    Γ.JEqB levels H (.univ n)
      (.pi (S.positionAt i a) (S.childFibres n (.pair i a)))
      (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hpositions := positionAt_formation_of_hypotheses hH D.toFormationData hi ha
  apply Ctx.JEqB.pi (L := Γ.dv) hn hpositions
  intro p hp
  have hctx : (Γ.cons p (S.positionAt i a)).JEqB levels H .unit .star .star :=
    .cons_ok hn D.context hp hpositions
  have dp := D.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hp (S.positionAt i a)) hctx
  have hi' := D.context.weaken_cons_of_hypotheses hH.weakening hp hn hpositions hi
  have ha' := D.context.weaken_cons_of_hypotheses hH.weakening hp hn hpositions ha
  have hpos : (Γ.cons p (S.positionAt i a)).JEqB levels H (S.positionAt i a) (.fv p) (.fv p) :=
    .var hctx (.here Γ p (S.positionAt i a))
  have hnext : (Γ.cons p (S.positionAt i a)).JEqB levels H S.index
      (S.childIndexAt (.pair i a) (.fv p)) (((S.next.lst i).lst a).open p) := by
    simpa only [← triple_lst_eq_bsubst, lst_fv] using childIndexAt_tagged_beta_of_hypotheses hH dp hi' ha' hpos
  simpa only [childFibres_open, fibreAt_open, fibreAt_closed] using fibre_congr_of_hypotheses hH dp hnext

/-- The original constructor accepts full children at the direct original source next index. -/
theorem node_typing_direct_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i a f : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hf : Γ.JEqB levels H (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) f f) :
    Γ.JEqB levels H (S.fibre n i) (S.node i a f) (S.node i a f) :=
  node_typing_of_hypotheses hH D hi ha (.conv (by have := D.bound; budget_omega) (childFibres_tagged_beta_of_hypotheses hH D hi ha).symm hf)

theorem fibre_congr (D : IndexedFormationData S levels n Γ) {i j : Tm 0}
    (hij : Γ.JEqB levels ∅ S.index i j) :
    Γ.JEqB levels ∅ (.univ n) (S.fibre n i) (S.fibre n j) :=
  fibre_congr_of_hypotheses (StructuralTheory.empty levels) D hij

theorem childFibres_tagged_beta (D : IndexedFormationData S levels n Γ) {i a : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a) :
    Γ.JEqB levels ∅ (.univ n)
      (.pi (S.positionAt i a) (S.childFibres n (.pair i a)))
      (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) :=
  childFibres_tagged_beta_of_hypotheses (StructuralTheory.empty levels) D hi ha

theorem node_typing_direct (D : IndexedFormationData S levels n Γ) {i a f : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hf : Γ.JEqB levels ∅ (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) f f) :
    Γ.JEqB levels ∅ (S.fibre n i) (S.node i a f) (S.node i a f) :=
  node_typing_direct_of_hypotheses (StructuralTheory.empty levels) D hi ha hf

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
