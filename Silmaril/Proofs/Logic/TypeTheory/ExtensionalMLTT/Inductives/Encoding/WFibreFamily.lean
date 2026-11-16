module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Fibres.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

variable {H : Set Jdg}

theorem fibreAt_closed (S : Description) (n : ℕ) (i : Tm 0) :
    S.fibreAt n i = S.fibre n i := by
  simp only [Description.fibreAt, Description.fibre, Tm.castLE_refl]
  have hI : S.index.wk0 = S.index.castLE (Nat.zero_le 1) := Tm.wkn_past S.index 0 (Nat.le_refl 0)
  rw [hI]

theorem fibreAt_open {k : ℕ} (S : Description) (n : ℕ) (i : Tm (k + 1)) (x : String) :
    (S.fibreAt n i).open x = S.fibreAt n (i.open x) := by
  simp only [Description.fibreAt, Tm.open, Tm.closed_castLE_open, root_open, coherence_open,
    Tm.wk0, Tm.open_wkn i x 0 (Nat.zero_le _),
    show (0 : Fin (k + 2)) = Fin.castSucc (0 : Fin (k + 1)) from rfl,
    show (1 : Fin (k + 3)) = Fin.castSucc (1 : Fin (k + 2)) from rfl,
    Fin.lastCases_castSucc]

theorem fibreAt_lst {k : ℕ} (S : Description) (n : ℕ) (i : Tm (k + 1)) (a : Tm 0) :
    (S.fibreAt n i).lst a = S.fibreAt n (i.lst a) := by
  simp only [Description.fibreAt, Tm.lst, Tm.closed_castLE_lst, root_lst, coherence_lst,
    Tm.wk0, Tm.lst_wkn i a 0 (Nat.zero_le _),
    show (0 : Fin (k + 2)) = Fin.castSucc (0 : Fin (k + 1)) from rfl,
    show (1 : Fin (k + 3)) = Fin.castSucc (1 : Fin (k + 2)) from rfl,
    Fin.lastCases_castSucc]

theorem fibreAt_formation_of_hypotheses {S : Description} {levels : RuleBudget} {n : ℕ} {Γ : Ctx}
    (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) :
    Γ.JEqB levels H (.univ n) (S.fibreAt n i) (S.fibreAt n i) := by
  simpa only [fibreAt_closed] using fibre_formation_of_hypotheses hH D hi

theorem coherence_wk0 (S : Description) (n : ℕ) (t : Tm 0) :
    (S.coherence n t).wk0 = S.coherence n t.wk0 := by
  simp only [Description.coherence, Tm.wk0]
  rw [Tm.wkn]
  simp only [Tm.wkn_past S.positions 1 (Nat.le_refl 1),
    Tm.wkn_past S.totalShape 0 (Nat.le_refl 0),
    Tm.wkn_past (S.coherenceStep n) 0 (Nat.le_refl 0), Tm.wkn, Tm.castLE_refl]

private theorem lastCases_zero {α : Sort _} (a : α) (f : Fin 0 → α) :
    Fin.lastCases a f (0 : Fin 1) = a := Fin.lastCases_last

private theorem lastCases_one {α : Sort _} (a : α) (f : Fin 1 → α) :
    Fin.lastCases a f (1 : Fin 2) = a := Fin.lastCases_last

theorem fibreTail_lst (S : Description) (n : ℕ) (i t : Tm 0) :
    ((.sigma (.id S.index.wk0 (S.root (.bv 0)) i.wk0)
      (S.coherence n (.bv 1)) : Tm 1).lst t) =
    .sigma (.id S.index (S.root t) i) (S.coherence n t).wk0 := by
  simp only [Tm.lst, root_lst, coherence_lst, Tm.closed_wk0_lst,
    lastCases_zero, lastCases_one, Tm.castLE_refl, coherence_wk0]
  have ht : t.castLE (Nat.zero_le 1) = t.wk0 := (Tm.wkn_past t 0 (Nat.le_refl 0)).symm
  rw [ht, ← coherence_wk0]

theorem positions_tagged_beta_of_hypotheses {S : Description} {levels : RuleBudget} {n : ℕ} {Γ : Ctx}
    (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) {i a : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a) :
    Γ.JEqB levels H (.univ n) (S.positions.lst (.pair i a)) (S.positionAt i a) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hlabel : Γ.JEqB levels H S.totalShape (.pair i a) (.pair i a) :=
    .pair hn D.index D.shape hi ha
  have hcodomain : ∀ x ∉ D.names, (Γ.cons x S.index).JEqB levels H (.univ (n + 1))
      ((.pi S.shape (.univ n) : Tm 1).open x) ((.pi S.shape (.univ n) : Tm 1).open x) := by
    intro x hx
    have hctx := Ctx.JEqB.cons_ok hn D.context (fun h => hx (D.declared h)) D.index
    simpa only [Tm.open] using Ctx.JEqB.type_family_formation D.bound hctx (D.shape x hx)
  have hfirst : Γ.JEqB levels H (.pi (S.shape.lst i) (.univ n))
      (.app S.positionFamily i) (.app S.positionFamily (.fst (.pair i a))) := by
    simpa only [Tm.lst] using Ctx.JEqB.app D.bound
      (.cumul D.bound (Nat.le_succ n) D.index) hcodomain (positionFamily_typing D)
      (Ctx.JEqB.beta_fst hn D.index D.shape hi ha).symm
  have hshape := shapeAt_formation_of_hypotheses hH D hi
  have huniv : ∀ x ∉ Γ.dv, (Γ.cons x (S.shape.lst i)).JEqB levels H (.univ (n + 1))
      ((.univ n : Tm 1).open x) ((.univ n : Tm 1).open x) := by
    intro x hx
    simpa only [Tm.open] using Ctx.JEqB.univ D.bound (Ctx.JEqB.cons_ok hn D.context hx hshape)
  have happ : Γ.JEqB levels H (.univ n)
      (.app (.app S.positionFamily i) a)
      (.app (.app S.positionFamily (.fst (.pair i a))) (.snd (.pair i a))) := by
    simpa only [Tm.lst] using Ctx.JEqB.app D.bound
      (.cumul D.bound (Nat.le_succ n) hshape) huniv hfirst
      (Ctx.JEqB.beta_snd hn D.index D.shape hi ha).symm
  have hleft := positionFamily_beta_direct_of_hypotheses hH D
    (Ctx.JEqB.fst hn D.index D.shape hlabel) (Ctx.JEqB.snd hn D.index D.shape hlabel)
  rw [positions_lst]
  exact (hleft.symm.trans happ.symm).trans (positionFamily_beta_direct_of_hypotheses hH D hi ha)



theorem fibreAt_formation {S : Description} {levels : RuleBudget} {n : ℕ} {Γ : Ctx}
    (D : IndexedFormationData S levels n Γ) {i : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) :
    Γ.JEqB levels ∅ (.univ n) (S.fibreAt n i) (S.fibreAt n i) :=
  fibreAt_formation_of_hypotheses (StructuralTheory.empty levels) D hi

theorem positions_tagged_beta {S : Description} {levels : RuleBudget} {n : ℕ} {Γ : Ctx}
    (D : FormationData S levels n Γ) {i a : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a) :
    Γ.JEqB levels ∅ (.univ n) (S.positions.lst (.pair i a)) (S.positionAt i a) :=
  positions_tagged_beta_of_hypotheses (StructuralTheory.empty levels) D hi ha

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
