module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Source
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.Telescope
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

variable {S : Description} {levels : RuleBudget} {n : ℕ} {Γ : Ctx}

/-- Substitute the original index through both remaining dependent declarations. -/
theorem next_after_index (D : IndexedFormationData S levels n Γ) {i : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) :
    ∃ L : Finset String, ∀ y ∉ L, ∀ p ∉ insert y L,
      ((Γ.cons y (S.shape.lst i)).cons p ((S.position.lst i).open y)).JEqB levels ∅ S.index
        (((S.next.lst i).open y).open p) (((S.next.lst i).open y).open p) := by
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
    (D.names ∪ Γ.typeFvs ∪ S.index.fvs ∪ S.shape.fvs ∪ S.position.fvs ∪ S.next.fvs ∪ i.fvs)
  simp only [Finset.mem_union, not_or, and_assoc] at hx
  rcases hx with ⟨hxD, hxΓ, hxI, hxS, hxP, hxN, hxi⟩
  refine ⟨insert x (D.names ∪ Γ.dv ∪ i.fvs), ?_⟩
  intro y hy p hp
  simp only [Finset.mem_insert, Finset.mem_union, not_or, and_assoc] at hy hp
  rcases hy with ⟨hyx, hyD, hyΓ, hyi⟩
  rcases hp with ⟨hpy, hpx, hpD, hpΓ, hpi⟩
  have hyS : y ∉ insert x D.names := by
    simpa only [Finset.mem_insert, not_or] using And.intro hyx hyD
  have hpS : p ∉ insert y (insert x D.names) := by
    simpa only [Finset.mem_insert, not_or] using And.intro hpy (And.intro hpx hpD)
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hs : (S.shape.open x).fsubst x i = S.shape.lst i :=
    Tm.fsubst_open_self x i S.shape hxS
  have hP : ((S.position.open x).open y).fsubst x i = (S.position.lst i).open y := by
    rw [Tm.fsubst_open x i _ hyx, Tm.fsubst_open_self x i S.position hxP]
  have hctx : (Γ.cons y ((S.shape.open x).fsubst x i)).JEqB levels ∅ .unit .star .star := by
    rw [hs]
    exact .cons_ok hn D.context hyΓ (shapeAt_formation D.toFormationData hi)
  have e : Ctx.SubstB levels x i (Γ.cons x S.index) Γ :=
    Ctx.SubstB.drop D.context hi hxΓ hxI
  have ey : Ctx.SubstB levels x i ((Γ.cons x S.index).cons y (S.shape.open x))
      (Γ.cons y ((S.shape.open x).fsubst x i)) :=
    Ctx.SubstB.cons e hyx hyΓ hctx
  have hpositions : (Γ.cons y ((S.shape.open x).fsubst x i)).JEqB levels ∅ (.univ n)
      (((S.position.open x).open y).fsubst x i) (((S.position.open x).open y).fsubst x i) := by
    simpa only [Tm.fsubst] using (D.position x hxD y hyS).substitute x i _ ey hctx
  have hpFresh : p ∉ (Γ.cons y ((S.shape.open x).fsubst x i)).dv := by
    simpa only [Ctx.dv, Finset.mem_insert, not_or] using And.intro hpy hpΓ
  have hctxp : ((Γ.cons y ((S.shape.open x).fsubst x i)).cons p
      (((S.position.open x).open y).fsubst x i)).JEqB levels ∅ .unit .star .star :=
    .cons_ok hn hctx hpFresh hpositions
  have ep : Ctx.SubstB levels x i
      (((Γ.cons x S.index).cons y (S.shape.open x)).cons p ((S.position.open x).open y))
      ((Γ.cons y ((S.shape.open x).fsubst x i)).cons p
        (((S.position.open x).open y).fsubst x i)) :=
    Ctx.SubstB.cons ey hpx hpFresh hctxp
  have hnext := (D.next x hxD y hyS p hpS).substitute x i _ ep hctxp
  simpa only [hs, hP, Tm.fsubst_fresh x i S.index hxI,
    Tm.fsubst_open x i _ hpx, Tm.fsubst_open x i _ hyx,
    Tm.fsubst_open_self x i S.next hxN] using hnext

/-- Then substitute the shape while retaining the final position declaration. -/
theorem next_after_shape (D : IndexedFormationData S levels n Γ) {i a : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a) :
    ∃ L : Finset String, ∀ p ∉ L, (Γ.cons p ((S.position.lst i).lst a)).JEqB levels ∅ S.index
      ((((S.next.lst i).lst a).open p)) ((((S.next.lst i).lst a).open p)) := by
  obtain ⟨L, hN⟩ := next_after_index D hi
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset
    (L ∪ Γ.typeFvs ∪ (S.shape.lst i).fvs ∪ S.index.fvs ∪
      (S.position.lst i).fvs ∪ (S.next.lst i).fvs ∪ a.fvs)
  simp only [Finset.mem_union, not_or, and_assoc] at hy
  rcases hy with ⟨hyL, hyΓ, hyS, hyI, hyP, hyN, hya⟩
  refine ⟨insert y (L ∪ Γ.dv ∪ a.fvs), ?_⟩
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_union, not_or, and_assoc] at hp
  rcases hp with ⟨hpy, hpL, hpΓ, hpa⟩
  have hpS : p ∉ insert y L := by
    simpa only [Finset.mem_insert, not_or] using And.intro hpy hpL
  have hP : ((S.position.lst i).open y).fsubst y a = (S.position.lst i).lst a :=
    Tm.fsubst_open_self y a (S.position.lst i) hyP
  have hpositions : Γ.JEqB levels ∅ (.univ n) ((S.position.lst i).lst a)
      ((S.position.lst i).lst a) := positionAt_formation_iterated D.toFormationData hi ha
  have hctx : (Γ.cons p (((S.position.lst i).open y).fsubst y a)).JEqB levels ∅ .unit .star .star := by
    rw [hP]
    exact .cons_ok (by have := D.bound; budget_omega) D.context hpΓ hpositions
  have e : Ctx.SubstB levels y a (Γ.cons y (S.shape.lst i)) Γ :=
    Ctx.SubstB.drop D.context ha hyΓ hyS
  have ep : Ctx.SubstB levels y a
      ((Γ.cons y (S.shape.lst i)).cons p ((S.position.lst i).open y))
      (Γ.cons p (((S.position.lst i).open y).fsubst y a)) :=
    Ctx.SubstB.cons e hpy hpΓ hctx
  have hnext := (hN y hyL p hpS).substitute y a _ ep hctx
  simpa only [hP, Tm.fsubst_fresh y a S.index hyI, Tm.fsubst_open y a _ hpy,
    Tm.fsubst_open_self y a (S.next.lst i) hyN] using hnext

/-- Three actual source arguments instantiate the original next term in its own theory. -/
theorem nextDirect_typing_iterated_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H)
    (D : IndexedFormationData S levels n Γ H) {i a p : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hp : Γ.JEqB levels H ((S.position.lst i).lst a) p p) :
    Γ.JEqB levels H S.index (((S.next.lst i).lst a).lst p) (((S.next.lst i).lst a).lst p) :=
  Ctx.JEqB.instantiate_three_of_hypotheses hH (by have := D.bound; budget_omega)
    D.context D.shape D.position D.next hi ha hp

theorem nextDirect_typing_iterated (D : IndexedFormationData S levels n Γ) {i a p : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hp : Γ.JEqB levels ∅ ((S.position.lst i).lst a) p p) :
    Γ.JEqB levels ∅ S.index (((S.next.lst i).lst a).lst p) (((S.next.lst i).lst a).lst p) := by
  obtain ⟨L, hN⟩ := next_after_shape D hi ha
  simpa only [Tm.closed_wk0_lst] using Ctx.JEqB.instantiate (B := S.index.wk0) D.context hp
    (by simpa only [Tm.closed_wk0_open] using hN)

theorem triple_lst_eq_bsubst (N : Tm 3) (i a p : Tm 0) :
    ((N.lst i).lst a).lst p = N.bsubst (Fin.cases p (Fin.cases a (fun _ => i))) := by
  rw [Tm.lst_eq_bsubst, Tm.bsubst_lst, Tm.bsubst_lst]
  simp only [Tm.castLE_refl]
  congr 1
  funext j
  fin_cases j
  · change Fin.lastCases i _ ((Fin.last 0).castSucc.castSucc) = p
    rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc, Fin.lastCases_last]
  · dsimp only
    change Fin.lastCases i _ (Fin.castSucc (Fin.last 1)) = a
    rw [Fin.lastCases_castSucc, Fin.lastCases_last]
  · dsimp only
    change Fin.lastCases i _ (Fin.last 2) = i
    exact Fin.lastCases_last

theorem nextDirect_typing_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H)
    (D : IndexedFormationData S levels n Γ H) {i a p : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hp : Γ.JEqB levels H (S.positionAt i a) p p) :
    Γ.JEqB levels H S.index
      (S.next.bsubst (Fin.cases p (Fin.cases a (fun _ => i))))
      (S.next.bsubst (Fin.cases p (Fin.cases a (fun _ => i)))) := by
  have hp' : Γ.JEqB levels H ((S.position.lst i).lst a) p p := by
    simpa only [Description.positionAt, double_lst_eq_bsubst] using hp
  simpa only [triple_lst_eq_bsubst] using nextDirect_typing_iterated_of_hypotheses hH D hi ha hp'

theorem nextDirect_typing (D : IndexedFormationData S levels n Γ) {i a p : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hp : Γ.JEqB levels ∅ (S.positionAt i a) p p) :
    Γ.JEqB levels ∅ S.index
      (S.next.bsubst (Fin.cases p (Fin.cases a (fun _ => i))))
      (S.next.bsubst (Fin.cases p (Fin.cases a (fun _ => i)))) := by
  have heq : Γ.JEqB levels ∅ (.univ n) ((S.position.lst i).lst a) (S.positionAt i a) :=
    (positionFamily_beta D.toFormationData hi ha).symm.trans
      (positionFamily_beta_direct D.toFormationData hi ha)
  have hp' : Γ.JEqB levels ∅ ((S.position.lst i).lst a) p p :=
    .conv (by have := D.bound; budget_omega) heq.symm hp
  simpa only [triple_lst_eq_bsubst] using nextDirect_typing_iterated D hi ha hp'

private theorem lastCases_zero {α : Sort _} (a : α) (f : Fin 0 → α) :
    Fin.lastCases a f (0 : Fin 1) = a := Fin.lastCases_last

theorem positions_lst (S : Description) (l : Tm 0) :
    S.positions.lst l = S.positionAt (.fst l) (.snd l) := by
  rw [Description.positions, Tm.lst_eq_bsubst, Tm.bsubst_comp, Description.positionAt]
  congr 1
  funext j
  refine Fin.cases ?_ (fun _ => ?_) j
  · change Tm.bsubst _ (.snd (.bv (0 : Fin 1))) = .snd l
    simp only [Tm.bsubst, lastCases_zero, Tm.castLE_refl]
  · change Tm.bsubst _ (.fst (.bv (0 : Fin 1))) = .fst l
    simp only [Tm.bsubst, lastCases_zero, Tm.castLE_refl]

theorem childIndexAt_typing_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H)
    (D : IndexedFormationData S levels n Γ H) {l p : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hp : Γ.JEqB levels H (S.positions.lst l) p p) :
    Γ.JEqB levels H S.index (S.childIndexAt l p) (S.childIndexAt l p) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hi : Γ.JEqB levels H S.index (.fst l) (.fst l) := .fst hn D.index D.shape hl
  have ha : Γ.JEqB levels H (S.shape.lst (.fst l)) (.snd l) (.snd l) :=
    .snd hn D.index D.shape hl
  have hp' : Γ.JEqB levels H (S.positionAt (.fst l) (.snd l)) p p := by
    simpa only [positions_lst] using hp
  exact nextDirect_typing_of_hypotheses hH D hi ha hp'

theorem childIndexAt_typing (D : IndexedFormationData S levels n Γ) {l p : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hp : Γ.JEqB levels ∅ (S.positions.lst l) p p) :
    Γ.JEqB levels ∅ S.index (S.childIndexAt l p) (S.childIndexAt l p) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hi : Γ.JEqB levels ∅ S.index (.fst l) (.fst l) := .fst hn D.index D.shape hl
  have ha : Γ.JEqB levels ∅ (S.shape.lst (.fst l)) (.snd l) (.snd l) :=
    .snd hn D.index D.shape hl
  have hp' : Γ.JEqB levels ∅ (S.positionAt (.fst l) (.snd l)) p p := by
    simpa only [positions_lst] using hp
  exact nextDirect_typing D hi ha hp'

private theorem lst_fv (B : Tm 1) (x : String) : B.lst (.fv x) = B.open x := by
  rw [Tm.lst_eq_bsubst, Tm.open_eq_bsubst]
  simp only [Tm.castLE]

theorem positions_formation_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) :
    ∀ x ∉ Γ.dv, (Γ.cons x S.totalShape).JEqB levels H (.univ n)
      (S.positions.open x) (S.positions.open x) := by
  intro x hx
  have hctx : (Γ.cons x S.totalShape).JEqB levels H .unit .star .star :=
    .cons_ok (by have := D.bound; budget_omega) D.context hx (totalShape_formation D)
  have hd := D.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hx S.totalShape) hctx
  have hl : (Γ.cons x S.totalShape).JEqB levels H S.totalShape (.fv x) (.fv x) :=
    .var hctx (.here Γ x S.totalShape)
  simpa only [lst_fv] using (compiledPositions_beta_of_hypotheses hH hd hl).symm.trans (compiledPositions_beta_of_hypotheses hH hd hl)

private theorem single_shift (B : Tm 1) :
    B.bsubst (fun _ => .bv (1 : Fin 2)) = B.wk0 := by
  rw [Tm.wk0, Tm.wkn_eq_bsubst]
  congr 1
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

private theorem cast_one_eq_wk0 (I : Tm 0) : I.castLE (Nat.zero_le 1) = I.wk0 :=
  (Tm.wkn_past I 0 (Nat.le_refl 0)).symm

theorem rootStep_eq_headStep (S : Description) :
    S.rootStep = Tm.headStep S.totalShape S.positions S.index (.fst (.bv 0)) := by
  simp [Description.rootStep, Description.childrenType, Description.raw, Tm.headStep,
    Tm.arr, Tm.wk0, Tm.wkn, single_shift]

theorem root_eq_head (S : Description) (t : Tm 0) :
    S.root t = Tm.head S.totalShape S.positions S.index (.fst (.bv 0)) t := by
  simp only [Description.root, Tm.head, rootStep_eq_headStep, Tm.castLE_refl, cast_one_eq_wk0]

theorem root_typing_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) {t : Tm 0}
    (ht : Γ.JEqB levels H S.raw t t) :
    Γ.JEqB levels H S.index (S.root t) (S.root t) := by
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
  simpa only [root_eq_head] using Ctx.JEqB.head_typing_of_hypotheses hH.weakening hn D.context
    (totalShape_formation D) D.index (positions_formation_of_hypotheses hH D) hlabel ht

theorem positions_formation (D : FormationData S levels n Γ) :
    ∀ x ∉ Γ.dv, (Γ.cons x S.totalShape).JEqB levels ∅ (.univ n)
      (S.positions.open x) (S.positions.open x) :=
  positions_formation_of_hypotheses (StructuralTheory.empty levels) D

theorem root_typing (D : FormationData S levels n Γ) {t : Tm 0}
    (ht : Γ.JEqB levels ∅ S.raw t t) :
    Γ.JEqB levels ∅ S.index (S.root t) (S.root t) :=
  root_typing_of_hypotheses (StructuralTheory.empty levels) D ht

/-- Direct source substitution has an actual nonconstant instance. -/
theorem successor_nextDirect_typing : Ctx.JEqB 2 ∅ .nil .nats (.succ .zero) (.succ .zero) := by
  have hi : Ctx.JEqB 2 ∅ .nil successorDescription.index .zero .zero := .zero .nil_ok
  have ha : Ctx.JEqB 2 ∅ .nil (successorDescription.shape.lst .zero) .star .star := by
    simpa only [successorDescription, Tm.lst] using (Ctx.JEqB.nil_ok (levels := 2) (H := ∅))
  have hp : Ctx.JEqB 2 ∅ .nil (successorDescription.positionAt .zero .star) .star .star := by
    simpa only [successorDescription, Description.positionAt, Tm.bsubst] using
      (Ctx.JEqB.nil_ok (levels := 2) (H := ∅))
  exact nextDirect_typing successorIndexedFormationData hi ha hp

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
