module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Fibres
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.Telescope

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

variable {H : Set Jdg} {S : Description} {levels : RuleBudget} {n : ℕ} {Γ : Ctx}

private theorem cast_one_eq_wk0 (I : Tm 0) : I.castLE (Nat.zero_le 1) = I.wk0 :=
  (Tm.wkn_past I 0 (Nat.le_refl 0)).symm

private theorem nextAfterIndex_data (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) :
    ∃ L : Finset String, ∀ y ∉ L,
      (Γ.cons y (S.shape.lst i)).JEqB levels H (.univ n)
        ((.pi (S.position.lst i) (S.index.castLE (by decide)) : Tm 1).open y)
        ((.pi (S.position.lst i) (S.index.castLE (by decide)) : Tm 1).open y) ∧
      (Γ.cons y (S.shape.lst i)).JEqB levels H
        ((.pi (S.position.lst i) (S.index.castLE (by decide)) : Tm 1).open y)
        ((.abs (S.position.lst i) (S.next.lst i) : Tm 1).open y)
        ((.abs (S.position.lst i) (S.next.lst i) : Tm 1).open y) := by
  obtain ⟨M, hM⟩ := position_after_index_of_hypotheses hH D.toFormationData hi
  obtain ⟨N, hN⟩ := Ctx.JEqB.instantiate_three_retaining_two_of_hypotheses hH
    (by have := D.bound; budget_omega) D.context D.shape D.position D.next hi
  refine ⟨M ∪ N ∪ Γ.dv, ?_⟩
  intro y hy
  have hyParts : y ∉ M ∧ y ∉ N ∧ y ∉ Γ.dv := by
    simpa only [Finset.mem_union, not_or, and_assoc] using hy
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hshape := shapeAt_formation_of_hypotheses hH D.toFormationData hi
  have hctx : (Γ.cons y (S.shape.lst i)).JEqB levels H .unit .star .star :=
    .cons_ok hn D.context hyParts.2.2 hshape
  have hI : (Γ.cons y (S.shape.lst i)).JEqB levels H (.univ n) S.index S.index :=
    D.context.weaken_cons_of_hypotheses hH.weakening hyParts.2.2 hn hshape D.index
  have hP := hM y hyParts.1
  have hcodomain := Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn hctx hP hI
  have hbody : ∀ p ∉ insert y (M ∪ N ∪ Γ.dv),
      ((Γ.cons y (S.shape.lst i)).cons p ((S.position.lst i).open y)).JEqB levels H
        (S.index.wk0.open p) (((S.next.lst i).open y).open p) (((S.next.lst i).open y).open p) := by
    intro p hp
    have hpN : p ∉ insert y N := by
      intro h
      rcases Finset.mem_insert.mp h with h | h
      · exact hp (Finset.mem_insert.mpr (Or.inl h))
      · exact hp (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
    simpa only [Tm.closed_wk0_open] using hN y hyParts.2.1 p hpN
  have hterm := Ctx.JEqB.abs (L := insert y (M ∪ N ∪ Γ.dv)) hn hP
    (fun p hp => hcodomain p (by
      intro h
      rcases Finset.mem_insert.mp h with h | h
      · exact hp (Finset.mem_insert.mpr (Or.inl h))
      · exact hp (Finset.mem_insert_of_mem (Finset.mem_union_right _ h)))) hbody
  simpa only [Tm.open, Tm.closed_castLE_open, cast_one_eq_wk0, Tm.arr] using
    And.intro (Ctx.JEqB.arrow_formation_of_hypotheses hH.weakening hn hctx hP hI) hterm

/-- Normalize all three actual applications of the original next family. -/
theorem nextFamily_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i a p : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hp : Γ.JEqB levels H ((S.position.lst i).lst a) p p) :
    Γ.JEqB levels H S.index (.app (.app (.app S.nextFamily i) a) p)
      (((S.next.lst i).lst a).lst p) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hfirst : Γ.JEqB levels H
      (.pi (S.shape.lst i) (.pi (S.position.lst i) (S.index.castLE (by decide))))
      (.app S.nextFamily i) (.abs (S.shape.lst i) (.abs (S.position.lst i) (S.next.lst i))) := by
    simpa only [Description.nextFamily, Tm.lst, Tm.closed_castLE_lst] using
      Ctx.JEqB.beta_app hn D.index (nextFamily_data_of_hypotheses D hH.weakening).1 (nextFamily_data_of_hypotheses D hH.weakening).2 hi
  have hshape := shapeAt_formation_of_hypotheses hH D.toFormationData hi
  obtain ⟨L, hL⟩ := nextAfterIndex_data hH D hi
  have hsecondApp : Γ.JEqB levels H
      (.pi ((S.position.lst i).lst a) (S.index.castLE (by decide)))
      (.app (.app S.nextFamily i) a)
      (.app (.abs (S.shape.lst i) (.abs (S.position.lst i) (S.next.lst i))) a) := by
    simpa only [Tm.lst, Tm.closed_castLE_lst] using
      Ctx.JEqB.app hn hshape (fun y hy => (hL y hy).1) hfirst ha
  have hsecondBeta : Γ.JEqB levels H
      (.pi ((S.position.lst i).lst a) (S.index.castLE (by decide)))
      (.app (.abs (S.shape.lst i) (.abs (S.position.lst i) (S.next.lst i))) a)
      (.abs ((S.position.lst i).lst a) ((S.next.lst i).lst a)) := by
    simpa only [Tm.lst, Tm.closed_castLE_lst] using
      Ctx.JEqB.beta_app hn hshape (fun y hy => (hL y hy).1) (fun y hy => (hL y hy).2) ha
  have hsecond : Γ.JEqB levels H (.arr ((S.position.lst i).lst a) S.index)
      (.app (.app S.nextFamily i) a)
      (.abs ((S.position.lst i).lst a) ((S.next.lst i).lst a)) := by
    simpa only [cast_one_eq_wk0, Tm.arr] using hsecondApp.trans hsecondBeta
  have hpositions := positionAt_formation_iterated_of_hypotheses hH D.toFormationData hi ha
  have hindexFamily := Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn D.context hpositions D.index
  have hthirdApp : Γ.JEqB levels H S.index
      (.app (.app (.app S.nextFamily i) a) p)
      (.app (.abs ((S.position.lst i).lst a) ((S.next.lst i).lst a)) p) := by
    simpa only [cast_one_eq_wk0, Tm.closed_wk0_lst] using
      Ctx.JEqB.app hn hpositions hindexFamily hsecond hp
  obtain ⟨M, hM⟩ := Ctx.JEqB.instantiate_three_retaining_one_of_hypotheses hH
    (by have := D.bound; budget_omega) D.context D.shape D.position D.next hi ha
  have hthirdBeta : Γ.JEqB levels H S.index
      (.app (.abs ((S.position.lst i).lst a) ((S.next.lst i).lst a)) p)
      (((S.next.lst i).lst a).lst p) := by
    simpa only [Tm.closed_wk0_lst] using Ctx.JEqB.beta_app (L := M ∪ Γ.dv) hn hpositions
      (fun x hx => hindexFamily x (fun h => hx (Finset.mem_union_right _ h)))
      (fun x hx => by
        simpa only [Tm.closed_wk0_open] using (hM x (fun h => hx (Finset.mem_union_left _ h)))) hp
  exact hthirdApp.trans hthirdBeta

/-- The computed next index is the exact simultaneous substitution of the source. -/
theorem nextFamily_beta_direct_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i a p : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hp : Γ.JEqB levels H (S.positionAt i a) p p) :
    Γ.JEqB levels H S.index (.app (.app (.app S.nextFamily i) a) p)
      (S.next.bsubst (Fin.cases p (Fin.cases a (fun _ => i)))) := by
  have heq : Γ.JEqB levels H (.univ n) ((S.position.lst i).lst a) (S.positionAt i a) :=
    (positionFamily_beta_of_hypotheses hH D.toFormationData hi ha).symm.trans
      (positionFamily_beta_direct_of_hypotheses hH D.toFormationData hi ha)
  have hp' : Γ.JEqB levels H ((S.position.lst i).lst a) p p :=
    .conv (by have := D.bound; budget_omega) heq.symm hp
  simpa only [triple_lst_eq_bsubst] using nextFamily_beta_of_hypotheses hH D hi ha hp'

/-- The compiled child index computes to the original source template. -/
theorem compiledChildIndex_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l p : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hp : Γ.JEqB levels H (S.positions.lst l) p p) :
    Γ.JEqB levels H S.index (S.compiledChildIndex l p) (S.childIndexAt l p) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hi := Ctx.JEqB.fst hn D.index D.shape hl
  have ha := Ctx.JEqB.snd hn D.index D.shape hl
  have hp' : Γ.JEqB levels H (S.positionAt (.fst l) (.snd l)) p p := by
    simpa only [positions_lst] using hp
  exact nextFamily_beta_direct_of_hypotheses hH D hi ha hp'

/-- Remove the two tag projections from the original child-index template. -/
theorem childIndexAt_tagged_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i a p : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hp : Γ.JEqB levels H (S.positionAt i a) p p) :
    Γ.JEqB levels H S.index (S.childIndexAt (.pair i a) p)
      (S.next.bsubst (Fin.cases p (Fin.cases a (fun _ => i)))) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hlabel : Γ.JEqB levels H S.totalShape (.pair i a) (.pair i a) :=
    .pair hn D.index D.shape hi ha
  have hfirst : Γ.JEqB levels H
      (.pi (S.shape.lst i) (.pi (S.position.lst i) (S.index.castLE (by decide))))
      (.app S.nextFamily i) (.app S.nextFamily (.fst (.pair i a))) := by
    simpa only [Description.nextFamilyType, Tm.lst, Tm.closed_castLE_lst] using
      Ctx.JEqB.app hn D.index (nextFamily_data_of_hypotheses D hH.weakening).1 (nextFamily_typing_of_hypotheses D hH.weakening)
        (Ctx.JEqB.beta_fst hn D.index D.shape hi ha).symm
  have hshape := shapeAt_formation_of_hypotheses hH D.toFormationData hi
  obtain ⟨L, hL⟩ := nextAfterIndex_data hH D hi
  have hsecond : Γ.JEqB levels H (.arr ((S.position.lst i).lst a) S.index)
      (.app (.app S.nextFamily i) a)
      (.app (.app S.nextFamily (.fst (.pair i a))) (.snd (.pair i a))) := by
    simpa only [Tm.lst, Tm.closed_castLE_lst, cast_one_eq_wk0, Tm.arr] using
      Ctx.JEqB.app hn hshape (fun y hy => (hL y hy).1) hfirst
        (Ctx.JEqB.beta_snd hn D.index D.shape hi ha).symm
  have hpositions := positionAt_formation_iterated_of_hypotheses hH D.toFormationData hi ha
  have hpositionEq : Γ.JEqB levels H (.univ n) (S.positionAt i a) ((S.position.lst i).lst a) :=
    (positionFamily_beta_direct_of_hypotheses hH D.toFormationData hi ha).symm.trans
      (positionFamily_beta_of_hypotheses hH D.toFormationData hi ha)
  have hp' := Ctx.JEqB.conv hn hpositionEq hp
  have happ : Γ.JEqB levels H S.index
      (.app (.app (.app S.nextFamily i) a) p) (S.compiledChildIndex (.pair i a) p) := by
    simpa only [Tm.closed_wk0_lst, Description.compiledChildIndex] using Ctx.JEqB.app hn hpositions
      (Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn D.context hpositions D.index) hsecond hp'
  have hpPair := Ctx.JEqB.conv hn (positions_tagged_beta_of_hypotheses hH D.toFormationData hi ha).symm hp
  exact ((compiledChildIndex_beta_of_hypotheses hH D hlabel hpPair).symm.trans happ.symm).trans
    (nextFamily_beta_direct_of_hypotheses hH D hi ha hp)


theorem nextFamily_beta (D : IndexedFormationData S levels n Γ) {i a p : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hp : Γ.JEqB levels ∅ ((S.position.lst i).lst a) p p) :
    Γ.JEqB levels ∅ S.index (.app (.app (.app S.nextFamily i) a) p)
      (((S.next.lst i).lst a).lst p) :=
  nextFamily_beta_of_hypotheses (StructuralTheory.empty levels) D hi ha hp

theorem nextFamily_beta_direct (D : IndexedFormationData S levels n Γ) {i a p : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hp : Γ.JEqB levels ∅ (S.positionAt i a) p p) :
    Γ.JEqB levels ∅ S.index (.app (.app (.app S.nextFamily i) a) p)
      (S.next.bsubst (Fin.cases p (Fin.cases a (fun _ => i)))) :=
  nextFamily_beta_direct_of_hypotheses (StructuralTheory.empty levels) D hi ha hp

theorem compiledChildIndex_beta (D : IndexedFormationData S levels n Γ) {l p : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hp : Γ.JEqB levels ∅ (S.positions.lst l) p p) :
    Γ.JEqB levels ∅ S.index (S.compiledChildIndex l p) (S.childIndexAt l p) :=
  compiledChildIndex_beta_of_hypotheses (StructuralTheory.empty levels) D hl hp

theorem childIndexAt_tagged_beta (D : IndexedFormationData S levels n Γ) {i a p : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hp : Γ.JEqB levels ∅ (S.positionAt i a) p p) :
    Γ.JEqB levels ∅ S.index (S.childIndexAt (.pair i a) p)
      (S.next.bsubst (Fin.cases p (Fin.cases a (fun _ => i)))) :=
  childIndexAt_tagged_beta_of_hypotheses (StructuralTheory.empty levels) D hi ha hp

/-- The generic computation has a nonconstant successor-index instance. -/
theorem successor_nextFamily_beta : Ctx.JEqB 2 ∅ .nil .nats
    (.app (.app (.app successorDescription.nextFamily .zero) .star) .star) (.succ .zero) := by
  have hi : Ctx.JEqB 2 ∅ .nil successorDescription.index .zero .zero := .zero .nil_ok
  have ha : Ctx.JEqB 2 ∅ .nil (successorDescription.shape.lst .zero) .star .star := by
    simpa only [successorDescription, Tm.lst] using (Ctx.JEqB.nil_ok (levels := 2) (H := ∅))
  have hp : Ctx.JEqB 2 ∅ .nil (successorDescription.positionAt .zero .star) .star .star := by
    simpa only [successorDescription, Description.positionAt, Tm.bsubst] using
      (Ctx.JEqB.nil_ok (levels := 2) (H := ∅))
  exact nextFamily_beta_direct successorIndexedFormationData hi ha hp

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
