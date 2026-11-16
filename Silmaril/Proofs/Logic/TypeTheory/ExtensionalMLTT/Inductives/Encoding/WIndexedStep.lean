module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Induction.Node.Thms

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

variable {H : Set Jdg} {S : Description} {levels : RuleBudget} {n m : ℕ} {Γ : Ctx}

private theorem positionSource_open {k : ℕ} (S : Description) (i a : Tm (k + 1)) (x : String) :
    (S.position.bsubst (Fin.cases a (fun _ => i))).open x =
    S.position.bsubst (Fin.cases (a.open x) (fun _ => i.open x)) := by
  rw [Tm.open_bsubst]
  congr 1
  funext j
  fin_cases j <;> rfl

private theorem positionSource_lst {k : ℕ} (S : Description) (i a : Tm (k + 1)) (v : Tm 0) :
    (S.position.bsubst (Fin.cases a (fun _ => i))).lst v =
    S.position.bsubst (Fin.cases (a.lst v) (fun _ => i.lst v)) := by
  rw [Tm.lst_bsubst]
  congr 1
  funext j
  fin_cases j <;> rfl

private theorem lastCases_first {α : Sort _} {k : ℕ} (a : α) (f : Fin (k + 1) → α) :
    Fin.lastCases a f (0 : Fin (k + 2)) = f 0 := Fin.lastCases_castSucc 0

theorem nodeAt_open {k : ℕ} (S : Description) (i a f : Tm (k + 1)) (x : String) :
    (S.nodeAt i a f).open x = S.nodeAt (i.open x) (a.open x) (f.open x) := by
  have hw : f.wk0.open x = (f.open x).wk0 := Tm.open_wkn f x 0 (Nat.zero_le k)
  simp only [Description.nodeAt, Tm.open, Tm.closed_castLE_open,
    Tm.open_castLE S.positions (Nat.succ_le_succ (Nat.zero_le k)), positionSource_open,
    hw, lastCases_first]

theorem nodeAt_lst {k : ℕ} (S : Description) (i a f : Tm (k + 1)) (v : Tm 0) :
    (S.nodeAt i a f).lst v = S.nodeAt (i.lst v) (a.lst v) (f.lst v) := by
  have hw : f.wk0.lst v = (f.lst v).wk0 := Tm.lst_wkn f v 0 (Nat.zero_le k)
  simp only [Description.nodeAt, Tm.lst, Tm.closed_castLE_lst,
    Tm.lst_castLE S.positions (Nat.succ_le_succ (Nat.zero_le k)), positionSource_lst,
    hw, lastCases_first]

private theorem lastCases_zero {α : Sort _} (a : α) (f : Fin 0 → α) :
    Fin.lastCases a f (0 : Fin 1) = a := Fin.lastCases_last

private theorem lst_fv {k : ℕ} (B : Tm (k + 1)) (x : String) : B.lst (.fv x) = B.open x := by
  rw [Tm.lst_eq_bsubst, Tm.open_eq_bsubst]
  simp only [Tm.castLE]

theorem nextBody_open (S : Description) (i a : Tm 0) (p : String) :
    ((S.next.lst i).lst a).open p = S.next.bsubst (Fin.cases (.fv p) (Fin.cases a (fun _ => i))) := by
  rw [← lst_fv ((S.next.lst i).lst a) p, triple_lst_eq_bsubst]

/-- Instantiating the original dependent shape preserves actual equality of source indices. -/
theorem shapeAt_congr_of_hypotheses (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) {i j : Tm 0}
    (hij : Γ.JEqB levels H S.index i j) :
    Γ.JEqB levels H (.univ n) (S.shape.lst i) (S.shape.lst j) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hU : ∀ x ∉ Γ.dv, (Γ.cons x S.index).JEqB levels H (.univ (n + 1))
      ((.univ n : Tm 1).open x) ((.univ n : Tm 1).open x) := by
    intro x hx
    simpa only [Tm.open] using Ctx.JEqB.univ D.bound (Ctx.JEqB.cons_ok hn D.context hx D.index)
  have happ : Γ.JEqB levels H (.univ n)
      (.app (.abs S.index S.shape) i) (.app (.abs S.index S.shape) j) := by
    simpa only [Tm.lst] using Ctx.JEqB.app D.bound
      (Ctx.JEqB.cumul D.bound (Nat.le_succ n) D.index) hU
      (Ctx.JEqB.abstract_type D.bound D.context D.index D.shape) hij
  exact (Ctx.JEqB.type_beta D.bound D.context D.index D.shape (hij.trans hij.symm)).symm.trans
    (happ.trans (Ctx.JEqB.type_beta D.bound D.context D.index D.shape (hij.symm.trans hij)))

/-- Original next typing forms every full source child fibre under its position declaration. -/
theorem sourceChildren_codomain_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i a : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a) :
    ∀ p ∉ Γ.dv, (Γ.cons p (S.positionAt i a)).JEqB levels H (.univ n)
      ((S.fibreAt n ((S.next.lst i).lst a)).open p)
      ((S.fibreAt n ((S.next.lst i).lst a)).open p) := by
  intro p hp
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hP := positionAt_formation_of_hypotheses hH D.toFormationData hi ha
  have hctx : (Γ.cons p (S.positionAt i a)).JEqB levels H .unit .star .star :=
    .cons_ok hn D.context hp hP
  have dp := D.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hp (S.positionAt i a)) hctx
  have hi' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hi
  have ha' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP ha
  have hpos : (Γ.cons p (S.positionAt i a)).JEqB levels H (S.positionAt i a) (.fv p) (.fv p) :=
    .var hctx (.here Γ p (S.positionAt i a))
  have hnext := nextDirect_typing_of_hypotheses hH dp hi' ha' hpos
  simpa only [fibreAt_open, fibreAt_closed, nextBody_open] using fibre_formation_of_hypotheses hH dp hnext

theorem sourceChildren_formation_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i a : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a) :
    Γ.JEqB levels H (.univ n)
      (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a)))
      (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) :=
  .pi (by have := D.bound; budget_omega) (positionAt_formation_of_hypotheses hH D.toFormationData hi ha)
    (sourceChildren_codomain_of_hypotheses hH D hi ha)

/-- Applying actual source children yields a value in the exact original next fibre. -/
theorem sourceChild_value_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i a g p : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hg : Γ.JEqB levels H (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g)
    (hp : Γ.JEqB levels H (S.positionAt i a) p p) :
    Γ.JEqB levels H (S.fibre n (S.next.bsubst (Fin.cases p (Fin.cases a (fun _ => i)))))
      (.app g p) (.app g p) := by
  simpa only [fibreAt_lst, fibreAt_closed, triple_lst_eq_bsubst] using
    Ctx.JEqB.app (by have := D.bound; budget_omega) (positionAt_formation_of_hypotheses hH D.toFormationData hi ha)
      (sourceChildren_codomain_of_hypotheses hH D hi ha) hg hp

/-- Actual source children form the dependent motive requested by each source IH. -/
theorem sourceIH_codomain_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C i a g : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hg : Γ.JEqB levels H (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g) :
    ∀ p ∉ Γ.dv, (Γ.cons p (S.positionAt i a)).JEqB levels H (.univ m)
      ((.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0)) : Tm 1).open p)
      ((.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0)) : Tm 1).open p) := by
  intro p hp
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hP := positionAt_formation_of_hypotheses hH D.toFormationData hi ha
  have hctx : (Γ.cons p (S.positionAt i a)).JEqB levels H .unit .star .star :=
    .cons_ok hn D.context hp hP
  have dp := D.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hp (S.positionAt i a)) hctx
  have hC' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hC
  have hi' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hi
  have ha' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP ha
  have hg' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hp hn hP hg
  have hpos : (Γ.cons p (S.positionAt i a)).JEqB levels H (S.positionAt i a) (.fv p) (.fv p) :=
    .var hctx (.here Γ p (S.positionAt i a))
  have hnext := nextDirect_typing_of_hypotheses hH dp hi' ha' hpos
  have hchild := sourceChild_value_of_hypotheses hH dp hi' ha' hg' hpos
  simpa only [Tm.open, Tm.closed_wk0_open, nextBody_open, lastCases_zero] using
    motive_congr_of_hypotheses hH dp hm hC' hnext hchild

theorem sourceIH_formation_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C i a g : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hg : Γ.JEqB levels H (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g) :
    Γ.JEqB levels H (.univ (max n m))
      (.pi (S.positionAt i a) (.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0))))
      (.pi (S.positionAt i a) (.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0)))) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hq : RuleBudget.Allows levels (max n m) := RuleBudget.Allows.max hn (by budget_omega)
  exact .pi hq (Ctx.JEqB.cumul hq (Nat.le_max_left n m) (positionAt_formation_of_hypotheses hH D.toFormationData hi ha))
    (fun p hp => Ctx.JEqB.cumul hq (Nat.le_max_right n m) (sourceIH_codomain_of_hypotheses hH D hm hC hi ha hg p hp))

private def stepBody (S : Description) (n : ℕ) (C : Tm 0) : Tm 2 :=
  .pi (.pi S.position (S.fibreAt n S.next))
    (.pi (.pi S.position.wk0
      (.app (.app (C.castLE (Nat.zero_le 4)) (S.next.wkn 1)) (.app (.bv 1) (.bv 0))))
      (.app (.app (C.castLE (Nat.zero_le 4)) (.bv 3)) (S.nodeAt (.bv 3) (.bv 2) (.bv 1))))

private def stepTail (S : Description) (n : ℕ) (C i a : Tm 0) : Tm 0 :=
  .pi (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a)))
    (.pi (.pi (S.positionAt i a).wk0
      (.app (.app (C.castLE (Nat.zero_le 2)) (((S.next.lst i).lst a).wkn 1)) (.app (.bv 1) (.bv 0))))
      (.app (.app (C.castLE (Nat.zero_le 2)) (i.castLE (Nat.zero_le 2)))
        (S.nodeAt (i.castLE (Nat.zero_le 2)) (a.castLE (Nat.zero_le 2)) (.bv 1))))

private theorem lastCases_one {α : Sort _} {k : ℕ} (a : α) (f : Fin (k + 2) → α) :
    Fin.lastCases a f (1 : Fin (k + 3)) = f 1 := Fin.lastCases_castSucc 1

private theorem lastCases_two {α : Sort _} {k : ℕ} (a : α) (f : Fin (k + 3) → α) :
    Fin.lastCases a f (2 : Fin (k + 4)) = f 2 := Fin.lastCases_castSucc 2

private theorem lastCases_top_one {α : Sort _} (a : α) (f : Fin 1 → α) :
    Fin.lastCases a f (1 : Fin 2) = a := Fin.lastCases_last

private theorem lastCases_top_two {α : Sort _} (a : α) (f : Fin 2 → α) :
    Fin.lastCases a f (2 : Fin 3) = a := Fin.lastCases_last

private theorem lastCases_top_three {α : Sort _} (a : α) (f : Fin 3 → α) :
    Fin.lastCases a f (3 : Fin 4) = a := Fin.lastCases_last

private theorem stepBody_lst (S : Description) (n : ℕ) (C i a : Tm 0) :
    ((stepBody S n C).lst i).lst a = stepTail S n C i a := by
  simp only [stepBody, stepTail, Tm.lst, Tm.wk0, fibreAt_lst, Tm.closed_castLE_lst,
    Tm.lst_wkn S.position i 0 (by budget_omega), Tm.lst_wkn (S.position.lst i) a 0 (by budget_omega),
    Tm.lst_wkn S.next i 1 (by budget_omega), Tm.lst_wkn (S.next.lst i) a 1 (by budget_omega),
    nodeAt_lst, double_lst_eq_bsubst, Description.positionAt, lastCases_first,
    lastCases_one, lastCases_two, lastCases_top_two, lastCases_top_three]

private def sourceIH (S : Description) (_n : ℕ) (C i a g : Tm 0) : Tm 0 :=
  .pi (S.positionAt i a)
    (.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0)))

private def stepOutput (S : Description) (C i a g : Tm 0) : Tm 1 :=
  .app (.app (C.castLE (Nat.zero_le 1)) (i.castLE (Nat.zero_le 1)))
    (S.nodeAt (i.castLE (Nat.zero_le 1)) (a.castLE (Nat.zero_le 1)) (g.castLE (Nat.zero_le 1)))

private def stepAfterChildren (S : Description) (n : ℕ) (C i a g : Tm 0) : Tm 0 :=
  .pi (sourceIH S n C i a g) (stepOutput S C i a g)

private def stepTailBody (S : Description) (C i a : Tm 0) : Tm 1 :=
  .pi (.pi (S.positionAt i a).wk0
      (.app (.app (C.castLE (Nat.zero_le 2)) (((S.next.lst i).lst a).wkn 1)) (.app (.bv 1) (.bv 0))))
    (.app (.app (C.castLE (Nat.zero_le 2)) (i.castLE (Nat.zero_le 2)))
      (S.nodeAt (i.castLE (Nat.zero_le 2)) (a.castLE (Nat.zero_le 2)) (.bv 1)))

private theorem cast_one_eq_wk0 (t : Tm 0) : t.castLE (Nat.zero_le 1) = t.wk0 :=
  (Tm.wkn_past t 0 (Nat.zero_le 0)).symm

private theorem stepTailBody_open (S : Description) (C i a : Tm 0) (g : String) :
    (stepTailBody S C i a).open g = stepAfterChildren S n C i a (.fv g) := by
  have hn := Tm.open_castLE ((S.next.lst i).lst a) (Nat.le_refl 1) g
  simp only [Tm.castLE_refl] at hn
  simp only [stepTailBody, stepAfterChildren, sourceIH, stepOutput, Tm.open,
    Tm.closed_wk0_open, Tm.closed_castLE_open,
    Tm.wkn_past ((S.next.lst i).lst a) 1 (Nat.le_refl 1), hn,
    nodeAt_open, lastCases_first, lastCases_top_one, cast_one_eq_wk0]
  rfl

private theorem stepTailBody_lst (S : Description) (C i a g : Tm 0) :
    (stepTailBody S C i a).lst g = stepAfterChildren S n C i a g := by
  have hn := Tm.lst_castLE ((S.next.lst i).lst a) (Nat.le_refl 1) g
  simp only [Tm.castLE_refl] at hn
  simp only [stepTailBody, stepAfterChildren, sourceIH, stepOutput, Tm.lst,
    Tm.closed_wk0_lst, Tm.closed_castLE_lst,
    Tm.wkn_past ((S.next.lst i).lst a) 1 (Nat.le_refl 1), hn,
    nodeAt_lst, lastCases_first, lastCases_top_one, cast_one_eq_wk0]

private theorem stepOutput_open (S : Description) (C i a g : Tm 0) (h : String) :
    (stepOutput S C i a g).open h = .app (.app C i) (S.node i a g) := by
  simp only [stepOutput, Tm.open, Tm.closed_castLE_open, Tm.castLE_refl, nodeAt_open, nodeAt_closed]

private theorem stepOutput_lst (S : Description) (C i a g h : Tm 0) :
    (stepOutput S C i a g).lst h = .app (.app C i) (S.node i a g) := by
  simp only [stepOutput, Tm.lst, Tm.closed_castLE_lst, Tm.castLE_refl, nodeAt_lst, nodeAt_closed]

private theorem stepOutput_codomain_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C i a g : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hg : Γ.JEqB levels H (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g) :
    ∀ h ∉ Γ.dv, (Γ.cons h (sourceIH S n C i a g)).JEqB levels H (.univ m)
      ((stepOutput S C i a g).open h) ((stepOutput S C i a g).open h) := by
  intro h hh
  have hq : RuleBudget.Allows levels (max n m) := RuleBudget.Allows.max (by have := D.bound; budget_omega) (by budget_omega)
  have hIH := sourceIH_formation_of_hypotheses hH D hm hC hi ha hg
  have hnode := node_typing_direct_of_hypotheses hH D hi ha hg
  have hout := motive_congr_of_hypotheses hH D hm hC hi hnode
  simpa only [stepOutput_open, sourceIH] using Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hh hq hIH hout

private theorem stepAfterChildren_formation_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C i a g : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hg : Γ.JEqB levels H (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g) :
    Γ.JEqB levels H (.univ (max n m)) (stepAfterChildren S n C i a g) (stepAfterChildren S n C i a g) := by
  have hq : RuleBudget.Allows levels (max n m) := RuleBudget.Allows.max (by have := D.bound; budget_omega) (by budget_omega)
  exact .pi hq (sourceIH_formation_of_hypotheses hH D hm hC hi ha hg)
    (fun h hh => Ctx.JEqB.cumul hq (Nat.le_max_right n m) (stepOutput_codomain_of_hypotheses hH D hm hC hi ha hg h hh))

private theorem stepTail_codomain_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C i a : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a) :
    ∀ g ∉ Γ.dv, (Γ.cons g (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a)))).JEqB levels H
      (.univ (max n m)) ((stepTailBody S C i a).open g) ((stepTailBody S C i a).open g) := by
  intro g hg
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hG := sourceChildren_formation_of_hypotheses hH D hi ha
  have hctx : (Γ.cons g (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a)))).JEqB levels H
      .unit .star .star := .cons_ok hn D.context hg hG
  have dp := D.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hg _) hctx
  have hC' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hg hn hG hC
  have hi' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hg hn hG hi
  have ha' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hg hn hG ha
  have hgv : (Γ.cons g (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a)))).JEqB levels H
      (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) (.fv g) (.fv g) :=
    .var hctx (.here Γ g _)
  simpa only [stepTailBody_open (n := n)] using stepAfterChildren_formation_of_hypotheses hH dp hm hC' hi' ha' hgv

private theorem stepTail_formation_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C i a : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a) :
    Γ.JEqB levels H (.univ (max n m)) (stepTail S n C i a) (stepTail S n C i a) := by
  have hq : RuleBudget.Allows levels (max n m) := RuleBudget.Allows.max (by have := D.bound; budget_omega) (by budget_omega)
  exact .pi hq (Ctx.JEqB.cumul hq (Nat.le_max_left n m) (sourceChildren_formation_of_hypotheses hH D hi ha))
    (stepTail_codomain_of_hypotheses hH D hm hC hi ha)

private theorem sourceShape_codomain_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C i : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hi : Γ.JEqB levels H S.index i i) :
    ∀ a ∉ Γ.dv, (Γ.cons a (S.shape.lst i)).JEqB levels H (.univ (max n m))
      (((stepBody S n C).lst i).open a) (((stepBody S n C).lst i).open a) := by
  intro a ha
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hA := shapeAt_formation_of_hypotheses hH D.toFormationData hi
  have hctx : (Γ.cons a (S.shape.lst i)).JEqB levels H .unit .star .star :=
    .cons_ok hn D.context ha hA
  have dp := D.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons ha _) hctx
  have hC' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context ha hn hA hC
  have hi' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context ha hn hA hi
  have hav : (Γ.cons a (S.shape.lst i)).JEqB levels H (S.shape.lst i) (.fv a) (.fv a) :=
    .var hctx (.here Γ a _)
  simpa only [← lst_fv, stepBody_lst] using stepTail_formation_of_hypotheses hH dp hm hC' hi' hav

private theorem sourceShape_formation_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C i : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hi : Γ.JEqB levels H S.index i i) :
    Γ.JEqB levels H (.univ (max n m))
      ((.pi S.shape (stepBody S n C) : Tm 1).lst i)
      ((.pi S.shape (stepBody S n C) : Tm 1).lst i) := by
  have hq : RuleBudget.Allows levels (max n m) := RuleBudget.Allows.max (by have := D.bound; budget_omega) (by budget_omega)
  simpa only [Tm.lst] using Ctx.JEqB.pi hq
    (Ctx.JEqB.cumul hq (Nat.le_max_left n m) (shapeAt_formation_of_hypotheses hH D.toFormationData hi))
    (sourceShape_codomain_of_hypotheses hH D hm hC hi)

private theorem sourceIndex_codomain_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C) :
    ∀ i ∉ Γ.dv, (Γ.cons i S.index).JEqB levels H (.univ (max n m))
      ((.pi S.shape (stepBody S n C) : Tm 1).open i)
      ((.pi S.shape (stepBody S n C) : Tm 1).open i) := by
  intro i hi
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hctx : (Γ.cons i S.index).JEqB levels H .unit .star .star :=
    .cons_ok hn D.context hi D.index
  have dp := D.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hi S.index) hctx
  have hC' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hi hn D.index hC
  have hiv : (Γ.cons i S.index).JEqB levels H S.index (.fv i) (.fv i) := .var hctx (.here Γ i S.index)
  simpa only [← lst_fv] using sourceShape_formation_of_hypotheses hH dp hm hC' hiv

/-- The original method tail is formed from the actual description and motive. -/
theorem indexedStepBody_formation_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C) :
    ∀ i ∉ Γ.dv, (Γ.cons i S.index).JEqB levels H (.univ (max n m))
      ((S.indexedStepBody n C).open i) ((S.indexedStepBody n C).open i) :=
  sourceIndex_codomain_of_hypotheses hH D hm hC

/-- The full original indexed step telescope is formed from the source description and motive. -/
theorem indexedStepType_formation_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C) :
    Γ.JEqB levels H (.univ (max n m)) (S.indexedStepType n C) (S.indexedStepType n C) := by
  have hq : RuleBudget.Allows levels (max n m) := RuleBudget.Allows.max (by have := D.bound; budget_omega) (by budget_omega)
  exact .pi hq (Ctx.JEqB.cumul hq (Nat.le_max_left n m) D.index) (sourceIndex_codomain_of_hypotheses hH D hm hC)

private def stepValueBody (S : Description) (n : ℕ) (C : Tm 0) (b : Tm 4) : Tm 2 :=
  .abs (.pi S.position (S.fibreAt n S.next))
    (.abs (.pi S.position.wk0
      (.app (.app (C.castLE (Nat.zero_le 4)) (S.next.wkn 1)) (.app (.bv 1) (.bv 0)))) b)

private def stepValueTail (S : Description) (n : ℕ) (C i a : Tm 0) (b : Tm 2) : Tm 0 :=
  .abs (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a)))
    (.abs (.pi (S.positionAt i a).wk0
      (.app (.app (C.castLE (Nat.zero_le 2)) (((S.next.lst i).lst a).wkn 1)) (.app (.bv 1) (.bv 0)))) b)

private theorem stepValueBody_lst (S : Description) (n : ℕ) (C i a : Tm 0) (b : Tm 4) :
    ((stepValueBody S n C b).lst i).lst a = stepValueTail S n C i a ((b.lst i).lst a) := by
  simp only [stepValueBody, stepValueTail, Tm.lst, Tm.wk0, fibreAt_lst, Tm.closed_castLE_lst,
    Tm.lst_wkn S.position i 0 (by budget_omega), Tm.lst_wkn (S.position.lst i) a 0 (by budget_omega),
    Tm.lst_wkn S.next i 1 (by budget_omega), Tm.lst_wkn (S.next.lst i) a 1 (by budget_omega),
    double_lst_eq_bsubst, Description.positionAt, lastCases_first, lastCases_one]

private theorem stepValueTail_open (S : Description) (n : ℕ) (C i a : Tm 0) (b : Tm 2) (g : String) :
    ((.abs (.pi (S.positionAt i a).wk0
      (.app (.app (C.castLE (Nat.zero_le 2)) (((S.next.lst i).lst a).wkn 1)) (.app (.bv 1) (.bv 0)))) b : Tm 1).open g) =
      .abs (sourceIH S n C i a (.fv g)) (b.open g) := by
  have hn := Tm.open_castLE ((S.next.lst i).lst a) (Nat.le_refl 1) g
  simp only [Tm.castLE_refl] at hn
  simp only [sourceIH, Tm.open, Tm.closed_wk0_open, Tm.closed_castLE_open,
    Tm.wkn_past ((S.next.lst i).lst a) 1 (Nat.le_refl 1), hn,
    lastCases_first, lastCases_top_one, cast_one_eq_wk0]
  rfl

/-- Source-step introduction from an ordinary scoped body under its four source declarations. -/
theorem indexedStep_abstraction_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C : Tm 0} {b : Tm 4} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hb : ∀ i ∉ Γ.dv, ∀ a ∉ (Γ.cons i S.index).dv,
      ∀ g ∉ ((Γ.cons i S.index).cons a (S.shape.open i)).dv,
      ∀ h ∉ (((Γ.cons i S.index).cons a (S.shape.open i)).cons g
        (.pi (S.positionAt (.fv i) (.fv a)) (S.fibreAt n ((S.next.lst (.fv i)).lst (.fv a))))).dv,
      ((((Γ.cons i S.index).cons a (S.shape.open i)).cons g
        (.pi (S.positionAt (.fv i) (.fv a)) (S.fibreAt n ((S.next.lst (.fv i)).lst (.fv a))))).cons h
          (.pi (S.positionAt (.fv i) (.fv a))
            (.app (.app C.wk0 ((S.next.lst (.fv i)).lst (.fv a))) (.app (Tm.fv g).wk0 (.bv 0))))).JEqB levels H
        (.app (.app C (.fv i)) (S.node (.fv i) (.fv a) (.fv g)))
        ((((b.open i).open a).open g).open h) ((((b.open i).open a).open g).open h)) :
    Γ.JEqB levels H (S.indexedStepType n C)
      (S.indexedStepAbstraction n C b) (S.indexedStepAbstraction n C b) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hq : RuleBudget.Allows levels (max n m) := RuleBudget.Allows.max hn (by budget_omega)
  apply Ctx.JEqB.abs hq (Ctx.JEqB.cumul hq (Nat.le_max_left n m) D.index)
    (sourceIndex_codomain_of_hypotheses hH D hm hC)
  intro i hi
  have hctxI : (Γ.cons i S.index).JEqB levels H .unit .star .star := .cons_ok hn D.context hi D.index
  have di : IndexedFormationData S levels n (Γ.cons i S.index) H := D.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hi _) hctxI
  have hCi : (Γ.cons i S.index).JEqB levels H (S.motiveType n m) C C := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hi hn D.index hC
  have hiv : (Γ.cons i S.index).JEqB levels H S.index (.fv i) (.fv i) := .var hctxI (.here ..)
  have hA : (Γ.cons i S.index).JEqB levels H (.univ n) (S.shape.lst (.fv i)) (S.shape.lst (.fv i)) := shapeAt_formation_of_hypotheses hH di.toFormationData hiv
  change (Γ.cons i S.index).JEqB levels H
    ((.pi S.shape (stepBody S n C) : Tm 1).open i)
    ((.abs S.shape (stepValueBody S n C b) : Tm 1).open i)
    ((.abs S.shape (stepValueBody S n C b) : Tm 1).open i)
  rw [← lst_fv, ← lst_fv]
  simp only [Tm.lst]
  apply Ctx.JEqB.abs hq (Ctx.JEqB.cumul hq (Nat.le_max_left n m) hA)
    (sourceShape_codomain_of_hypotheses hH di hm hCi hiv)
  intro a ha
  have hctxA : ((Γ.cons i S.index).cons a (S.shape.lst (.fv i))).JEqB levels H .unit .star .star :=
    .cons_ok hn hctxI ha hA
  have da : IndexedFormationData S levels n ((Γ.cons i S.index).cons a (S.shape.lst (.fv i))) H := di.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons ha _) hctxA
  have hCa : ((Γ.cons i S.index).cons a (S.shape.lst (.fv i))).JEqB levels H (S.motiveType n m) C C := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening hctxI ha hn hA hCi
  have hia : ((Γ.cons i S.index).cons a (S.shape.lst (.fv i))).JEqB levels H S.index (.fv i) (.fv i) := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening hctxI ha hn hA hiv
  have hav : ((Γ.cons i S.index).cons a (S.shape.lst (.fv i))).JEqB levels H
    (S.shape.lst (.fv i)) (.fv a) (.fv a) := .var hctxA (.here ..)
  rw [← lst_fv, ← lst_fv, stepBody_lst, stepValueBody_lst]
  have hG : ((Γ.cons i S.index).cons a (S.shape.lst (.fv i))).JEqB levels H (.univ n)
    (.pi (S.positionAt (.fv i) (.fv a)) (S.fibreAt n ((S.next.lst (.fv i)).lst (.fv a))))
    (.pi (S.positionAt (.fv i) (.fv a)) (S.fibreAt n ((S.next.lst (.fv i)).lst (.fv a)))) := sourceChildren_formation_of_hypotheses hH da hia hav
  apply Ctx.JEqB.abs hq (Ctx.JEqB.cumul hq (Nat.le_max_left n m) hG) (stepTail_codomain_of_hypotheses hH da hm hCa hia hav)
  intro g hg
  rw [stepTailBody_open (n := n), stepValueTail_open S n]
  have hctxG : (((Γ.cons i S.index).cons a (S.shape.lst (.fv i))).cons g
    (.pi (S.positionAt (.fv i) (.fv a)) (S.fibreAt n ((S.next.lst (.fv i)).lst (.fv a))))).JEqB levels H .unit .star .star := Ctx.JEqB.cons_ok hn hctxA hg hG
  have dg : IndexedFormationData S levels n (((Γ.cons i S.index).cons a (S.shape.lst (.fv i))).cons g
    (.pi (S.positionAt (.fv i) (.fv a)) (S.fibreAt n ((S.next.lst (.fv i)).lst (.fv a))))) H := da.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hg _) hctxG
  have hCg := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening hctxA hg hn hG hCa
  have hig := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening hctxA hg hn hG hia
  have hag := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening hctxA hg hn hG hav
  have hgv := Ctx.JEqB.var hctxG (Ctx.Lookup.here _ g _)
  apply Ctx.JEqB.abs hq (sourceIH_formation_of_hypotheses hH dg hm hCg hig hag hgv)
    (fun h hh => Ctx.JEqB.cumul hq (Nat.le_max_right n m) (stepOutput_codomain_of_hypotheses hH dg hm hCg hig hag hgv h hh))
  intro h hh
  simpa only [← lst_fv, stepOutput_lst, sourceIH] using
    hb i hi a (by simpa only [← lst_fv] using ha) g (by simpa only [← lst_fv] using hg) h
      (by simpa only [← lst_fv, sourceIH] using hh)

/-- Four actual applications of the supplied source step, retaining the original child fibres and dependent IHs. -/
theorem indexedStep_apply_congr_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C s i i' a a' g g' h h' : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hs : Γ.JEqB levels H (S.indexedStepType n C) s s)
    (hi : Γ.JEqB levels H S.index i i') (ha : Γ.JEqB levels H (S.shape.lst i) a a')
    (hg : Γ.JEqB levels H (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g')
    (hh : Γ.JEqB levels H (.pi (S.positionAt i a)
      (.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0)))) h h') :
    Γ.JEqB levels H (.app (.app C i) (S.node i a g))
      (.app (.app (.app (.app s i) a) g) h) (.app (.app (.app (.app s i') a') g') h') := by
  have hi0 : Γ.JEqB levels H S.index i i := hi.trans hi.symm
  have ha0 : Γ.JEqB levels H (S.shape.lst i) a a := ha.trans ha.symm
  have hg0 : Γ.JEqB levels H (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g := hg.trans hg.symm
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hq : RuleBudget.Allows levels (max n m) := RuleBudget.Allows.max hn (by budget_omega)
  have h1 := Ctx.JEqB.app hq (Ctx.JEqB.cumul hq (Nat.le_max_left n m) D.index)
    (sourceIndex_codomain_of_hypotheses hH D hm hC) hs hi
  have h2 := Ctx.JEqB.app hq
    (Ctx.JEqB.cumul hq (Nat.le_max_left n m) (shapeAt_formation_of_hypotheses hH D.toFormationData hi0))
    (sourceShape_codomain_of_hypotheses hH D hm hC hi0) (by simpa only [Tm.lst] using h1) ha
  have h2' : Γ.JEqB levels H (stepTail S n C i a) (.app (.app s i) a) (.app (.app s i') a') := by
    simpa only [Tm.lst, stepBody_lst] using h2
  have h3 := Ctx.JEqB.app hq
    (Ctx.JEqB.cumul hq (Nat.le_max_left n m) (sourceChildren_formation_of_hypotheses hH D hi0 ha0))
    (stepTail_codomain_of_hypotheses hH D hm hC hi0 ha0) h2' hg
  have h3' : Γ.JEqB levels H (stepAfterChildren S n C i a g)
      (.app (.app (.app s i) a) g) (.app (.app (.app s i') a') g') := by
    simpa only [stepTailBody_lst (n := n)] using h3
  simpa only [stepOutput_lst] using Ctx.JEqB.app hq (sourceIH_formation_of_hypotheses hH D hm hC hi0 ha0 hg0)
    (fun z hz => Ctx.JEqB.cumul hq (Nat.le_max_right n m) (stepOutput_codomain_of_hypotheses hH D hm hC hi0 ha0 hg0 z hz))
    h3' hh

theorem indexedStep_apply_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C s i a g h : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hs : Γ.JEqB levels H (S.indexedStepType n C) s s)
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hg : Γ.JEqB levels H (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g)
    (hh : Γ.JEqB levels H (.pi (S.positionAt i a)
      (.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0)))) h h) :
    Γ.JEqB levels H (.app (.app C i) (S.node i a g))
      (.app (.app (.app (.app s i) a) g) h) (.app (.app (.app (.app s i) a) g) h) :=
  indexedStep_apply_congr_of_hypotheses hH D hm hC hs hi ha hg hh

/-- Reified original children inhabit exactly the child argument of the source step. -/
theorem reifyChildren_source_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l f c : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    Γ.JEqB levels H (.pi (S.positionAt (.fst l) (.snd l))
      (S.fibreAt n ((S.next.lst (.fst l)).lst (.snd l))))
      (S.reifyChildren l f c) (S.reifyChildren l f c) := by
  simpa only [positions_lst, childFibres_as_source] using reifyChildren_typing_of_hypotheses hH D hl hf hc

/-- Reified IHs inhabit exactly the dependent motive argument of the source step. -/
theorem reifyHypotheses_source_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C l f c r : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels H (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hr : Γ.JEqB levels H (.pi (S.positions.lst l)
      ((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0)))) r r) :
    Γ.JEqB levels H (.pi (S.positionAt (.fst l) (.snd l))
      (.app (.app C.wk0 ((S.next.lst (.fst l)).lst (.snd l)))
        (.app (S.reifyChildren l f c).wk0 (.bv 0))))
      (S.reifyHypotheses l c r) (S.reifyHypotheses l c r) := by
  have hnext : S.childIndexAt l.wk0 (.bv 0) = (S.next.lst (.fst l)).lst (.snd l) := by
    rw [next_retaining_position]
    rfl
  simpa only [positions_lst, hnext] using reifyHypotheses_typing_of_hypotheses hH D hm hC hl hf hc hr

/-- The actual source step computes in the canonical ordinary-W motive from full reified data. -/
theorem indexedStep_reified_apply_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
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
      (.app (.app (.app (.app s (.fst l)) (.snd l)) (S.reifyChildren l f c)) (S.reifyHypotheses l c r))
      (.app (.app (.app (.app s (.fst l)) (.snd l)) (S.reifyChildren l f c)) (S.reifyHypotheses l c r)) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hi := Ctx.JEqB.fst hn D.index D.shape hl
  have ha := Ctx.JEqB.snd hn D.index D.shape hl
  have hstep := indexedStep_apply_of_hypotheses hH D hm hC hs hi ha (reifyChildren_source_typing_of_hypotheses hH D hl hf hc)
    (reifyHypotheses_source_typing_of_hypotheses hH D hm hC hl hf hc hr)
  exact .conv (by budget_omega) (motive_reifiedNode_eq_of_hypotheses hH D hm hC hl hf hc) hstep


theorem shapeAt_congr (D : FormationData S levels n Γ) {i j : Tm 0}
    (hij : Γ.JEqB levels ∅ S.index i j) :
    Γ.JEqB levels ∅ (.univ n) (S.shape.lst i) (S.shape.lst j) :=
  shapeAt_congr_of_hypotheses (StructuralTheory.empty levels) D hij

theorem sourceChildren_formation (D : IndexedFormationData S levels n Γ) {i a : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a) :
    Γ.JEqB levels ∅ (.univ n)
      (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a)))
      (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) :=
  sourceChildren_formation_of_hypotheses (StructuralTheory.empty levels) D hi ha

theorem sourceIH_formation (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C i a g : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hg : Γ.JEqB levels ∅ (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g) :
    Γ.JEqB levels ∅ (.univ (max n m))
      (.pi (S.positionAt i a) (.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0))))
      (.pi (S.positionAt i a) (.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0)))) :=
  sourceIH_formation_of_hypotheses (StructuralTheory.empty levels) D hm hC hi ha hg

/-- Formation of the full dependent method tail at each actual source index. -/

theorem indexedStepBody_formation (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C) :
    ∀ i ∉ Γ.dv, (Γ.cons i S.index).JEqB levels ∅ (.univ (max n m))
      ((S.indexedStepBody n C).open i) ((S.indexedStepBody n C).open i) :=
  indexedStepBody_formation_of_hypotheses (StructuralTheory.empty levels) D hm hC

theorem indexedStepType_formation (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C) :
    Γ.JEqB levels ∅ (.univ (max n m)) (S.indexedStepType n C) (S.indexedStepType n C) :=
  indexedStepType_formation_of_hypotheses (StructuralTheory.empty levels) D hm hC

/-- Source-step introduction from an ordinary scoped body under its four source declarations. -/

theorem indexedStep_abstraction (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C : Tm 0} {b : Tm 4} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hb : ∀ i ∉ Γ.dv, ∀ a ∉ (Γ.cons i S.index).dv,
      ∀ g ∉ ((Γ.cons i S.index).cons a (S.shape.open i)).dv,
      ∀ h ∉ (((Γ.cons i S.index).cons a (S.shape.open i)).cons g
        (.pi (S.positionAt (.fv i) (.fv a)) (S.fibreAt n ((S.next.lst (.fv i)).lst (.fv a))))).dv,
      ((((Γ.cons i S.index).cons a (S.shape.open i)).cons g
        (.pi (S.positionAt (.fv i) (.fv a)) (S.fibreAt n ((S.next.lst (.fv i)).lst (.fv a))))).cons h
          (.pi (S.positionAt (.fv i) (.fv a))
            (.app (.app C.wk0 ((S.next.lst (.fv i)).lst (.fv a))) (.app (Tm.fv g).wk0 (.bv 0))))).JEqB levels ∅
        (.app (.app C (.fv i)) (S.node (.fv i) (.fv a) (.fv g)))
        ((((b.open i).open a).open g).open h) ((((b.open i).open a).open g).open h)) :
    Γ.JEqB levels ∅ (S.indexedStepType n C)
      (S.indexedStepAbstraction n C b) (S.indexedStepAbstraction n C b) :=
  indexedStep_abstraction_of_hypotheses (StructuralTheory.empty levels) D hm hC hb

theorem indexedStep_apply_congr (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C s i i' a a' g g' h h' : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hs : Γ.JEqB levels ∅ (S.indexedStepType n C) s s)
    (hi : Γ.JEqB levels ∅ S.index i i') (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a')
    (hg : Γ.JEqB levels ∅ (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g')
    (hh : Γ.JEqB levels ∅ (.pi (S.positionAt i a)
      (.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0)))) h h') :
    Γ.JEqB levels ∅ (.app (.app C i) (S.node i a g))
      (.app (.app (.app (.app s i) a) g) h) (.app (.app (.app (.app s i') a') g') h') :=
  indexedStep_apply_congr_of_hypotheses (StructuralTheory.empty levels) D hm hC hs hi ha hg hh

theorem indexedStep_apply (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C s i a g h : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hs : Γ.JEqB levels ∅ (S.indexedStepType n C) s s)
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hg : Γ.JEqB levels ∅ (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g)
    (hh : Γ.JEqB levels ∅ (.pi (S.positionAt i a)
      (.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0)))) h h) :
    Γ.JEqB levels ∅ (.app (.app C i) (S.node i a g))
      (.app (.app (.app (.app s i) a) g) h) (.app (.app (.app (.app s i) a) g) h) :=
  indexedStep_apply_of_hypotheses (StructuralTheory.empty levels) D hm hC hs hi ha hg hh

theorem reifyChildren_source_typing (D : IndexedFormationData S levels n Γ) {l f c : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c) :
    Γ.JEqB levels ∅ (.pi (S.positionAt (.fst l) (.snd l))
      (S.fibreAt n ((S.next.lst (.fst l)).lst (.snd l))))
      (S.reifyChildren l f c) (S.reifyChildren l f c) :=
  reifyChildren_source_typing_of_hypotheses (StructuralTheory.empty levels) D hl hf hc

theorem reifyHypotheses_source_typing (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C l f c r : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f)
    (hc : Γ.JEqB levels ∅ (S.coherence n (.sup S.totalShape S.positions l f)) c c)
    (hr : Γ.JEqB levels ∅ (.pi (S.positions.lst l)
      ((S.inductionMotive n C).bsubst (fun _ => .app f.wk0 (.bv 0)))) r r) :
    Γ.JEqB levels ∅ (.pi (S.positionAt (.fst l) (.snd l))
      (.app (.app C.wk0 ((S.next.lst (.fst l)).lst (.snd l)))
        (.app (S.reifyChildren l f c).wk0 (.bv 0))))
      (S.reifyHypotheses l c r) (S.reifyHypotheses l c r) :=
  reifyHypotheses_source_typing_of_hypotheses (StructuralTheory.empty levels) D hm hC hl hf hc hr

theorem indexedStep_reified_apply (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
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
      (.app (.app (.app (.app s (.fst l)) (.snd l)) (S.reifyChildren l f c)) (S.reifyHypotheses l c r))
      (.app (.app (.app (.app s (.fst l)) (.snd l)) (S.reifyChildren l f c)) (S.reifyHypotheses l c r)) :=
  indexedStep_reified_apply_of_hypotheses (StructuralTheory.empty levels) D hm hC hs hl hf hc hr

theorem sourceChildren_codomain (D : IndexedFormationData S levels n Γ) {i a : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a) :
    ∀ p ∉ Γ.dv, (Γ.cons p (S.positionAt i a)).JEqB levels ∅ (.univ n)
      ((S.fibreAt n ((S.next.lst i).lst a)).open p)
      ((S.fibreAt n ((S.next.lst i).lst a)).open p) :=
  sourceChildren_codomain_of_hypotheses (StructuralTheory.empty levels) D hi ha

theorem sourceChild_value (D : IndexedFormationData S levels n Γ) {i a g p : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hg : Γ.JEqB levels ∅ (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g)
    (hp : Γ.JEqB levels ∅ (S.positionAt i a) p p) :
    Γ.JEqB levels ∅ (S.fibre n (S.next.bsubst (Fin.cases p (Fin.cases a (fun _ => i)))))
      (.app g p) (.app g p) :=
  sourceChild_value_of_hypotheses (StructuralTheory.empty levels) D hi ha hg hp

theorem sourceIH_codomain (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C i a g : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hg : Γ.JEqB levels ∅ (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) g g) :
    ∀ p ∉ Γ.dv, (Γ.cons p (S.positionAt i a)).JEqB levels ∅ (.univ m)
      ((.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0)) : Tm 1).open p)
      ((.app (.app C.wk0 ((S.next.lst i).lst a)) (.app g.wk0 (.bv 0)) : Tm 1).open p) :=
  sourceIH_codomain_of_hypotheses (StructuralTheory.empty levels) D hm hC hi ha hg

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
