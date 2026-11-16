module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Source.Defs
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

variable {S : Description} {levels : RuleBudget} {n : ℕ} {Γ : Ctx}

theorem shapeAt_formation_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) {i : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) :
    Γ.JEqB levels H (.univ n) (S.shape.lst i) (S.shape.lst i) := by
  simpa only [Tm.lst] using Ctx.JEqB.instantiate_of_hypotheses (B := .univ n) hH.weakening (fun x => hH.substitution x _)
    D.context hi (by simpa only [Tm.open] using D.shape)

/-- Substitute the source index while retaining its dependent shape declaration. -/
theorem position_after_index_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) {i : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) :
    ∃ L : Finset String, ∀ y ∉ L, (Γ.cons y (S.shape.lst i)).JEqB levels H (.univ n)
      ((S.position.lst i).open y) ((S.position.lst i).open y) := by
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
    (D.names ∪ Γ.typeFvs ∪ S.index.fvs ∪ S.shape.fvs ∪ S.position.fvs ∪ S.next.fvs ∪ i.fvs)
  simp only [Finset.mem_union, not_or, and_assoc] at hx
  rcases hx with ⟨hxD, hxΓ, hxI, hxS, hxP, hxN, hxi⟩
  refine ⟨insert x (D.names ∪ Γ.dv ∪ i.fvs), ?_⟩
  intro y hy
  simp only [Finset.mem_insert, Finset.mem_union, not_or, and_assoc] at hy
  rcases hy with ⟨hyx, hyD, hyΓ, hyi⟩
  have hyS : y ∉ insert x D.names := by
    simpa only [Finset.mem_insert, not_or] using And.intro hyx hyD
  have hshape : Γ.JEqB levels H (.univ n) (S.shape.lst i) (S.shape.lst i) :=
    shapeAt_formation_of_hypotheses hH D hi
  have hs : (S.shape.open x).fsubst x i = S.shape.lst i := Tm.fsubst_open_self x i S.shape hxS
  have hctx : (Γ.cons y ((S.shape.open x).fsubst x i)).JEqB levels H .unit .star .star := by
    rw [hs]
    exact .cons_ok (by have := D.bound; budget_omega) D.context hyΓ hshape
  have e : Ctx.SubstB levels x i (Γ.cons x S.index) Γ H :=
    Ctx.SubstB.drop D.context hi hxΓ hxI
  have ey : Ctx.SubstB levels x i ((Γ.cons x S.index).cons y (S.shape.open x))
      (Γ.cons y ((S.shape.open x).fsubst x i)) H :=
    Ctx.SubstB.cons_of_hypotheses hH.weakening e hyx hyΓ hctx
  have hp := (D.position x hxD y hyS).substitute_of_hypotheses hH.weakening x i (hH.substitution x i) _ ey hctx
  simpa only [Tm.fsubst, hs, Tm.fsubst_open x i _ hyx,
    Tm.fsubst_open_self x i S.position hxP] using hp

theorem positionAt_formation_iterated_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) {i a : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a) :
    Γ.JEqB levels H (.univ n) ((S.position.lst i).lst a) ((S.position.lst i).lst a) := by
  obtain ⟨L, hP⟩ := position_after_index_of_hypotheses hH D hi
  simpa only [Tm.lst] using Ctx.JEqB.instantiate_of_hypotheses (B := .univ n) hH.weakening (fun x => hH.substitution x _)
    D.context ha (by simpa only [Tm.open] using hP)

/-- Actual object beta equality, using the original source position premises. -/
theorem positionFamily_beta_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) {i a : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a) :
    Γ.JEqB levels H (.univ n) (.app (.app S.positionFamily i) a)
      ((S.position.lst i).lst a) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hctx : ∀ x ∉ D.names, (Γ.cons x S.index).JEqB levels H .unit .star .star := by
    intro x hx
    exact .cons_ok hn D.context (fun h => hx (D.declared h)) D.index
  have hcodomain : ∀ x ∉ D.names, (Γ.cons x S.index).JEqB levels H (.univ (n + 1))
      ((.pi S.shape (.univ n) : Tm 1).open x) ((.pi S.shape (.univ n) : Tm 1).open x) := by
    intro x hx
    simpa only [Tm.open] using
      Ctx.JEqB.type_family_formation D.bound (hctx x hx) (D.shape x hx)
  have hbody : ∀ x ∉ D.names, (Γ.cons x S.index).JEqB levels H
      ((.pi S.shape (.univ n) : Tm 1).open x)
      ((.abs S.shape S.position : Tm 1).open x) ((.abs S.shape S.position : Tm 1).open x) := by
    intro x hx
    simpa only [Tm.open] using
      Ctx.JEqB.abstract_type D.bound (hctx x hx) (D.shape x hx) (D.position x hx)
  have houter : Γ.JEqB levels H (.pi (S.shape.lst i) (.univ n))
      (.app S.positionFamily i) (.abs (S.shape.lst i) (S.position.lst i)) := by
    simpa only [Description.positionFamily, Tm.lst] using
      Ctx.JEqB.beta_app D.bound (.cumul D.bound (Nat.le_succ n) D.index) hcodomain hbody hi
  have hshape : Γ.JEqB levels H (.univ n) (S.shape.lst i) (S.shape.lst i) :=
    shapeAt_formation_of_hypotheses hH D hi
  have huniv : ∀ y ∉ Γ.dv, (Γ.cons y (S.shape.lst i)).JEqB levels H (.univ (n + 1))
      ((.univ n : Tm 1).open y) ((.univ n : Tm 1).open y) := by
    intro y hy
    simpa only [Tm.open] using Ctx.JEqB.univ D.bound
      (Ctx.JEqB.cons_ok hn D.context hy hshape)
  have happ : Γ.JEqB levels H (.univ n) (.app (.app S.positionFamily i) a)
      (.app (.abs (S.shape.lst i) (S.position.lst i)) a) := by
    simpa only [Tm.lst] using Ctx.JEqB.app D.bound
      (.cumul D.bound (Nat.le_succ n) hshape) huniv houter ha
  obtain ⟨L, hP⟩ := position_after_index_of_hypotheses hH D hi
  exact happ.trans (Ctx.JEqB.type_beta D.bound D.context hshape hP ha)

theorem double_lst_eq_bsubst (C : Tm 2) (i a : Tm 0) :
    (C.lst i).lst a = C.bsubst (Fin.cases a (fun _ => i)) := by
  rw [Tm.lst_eq_bsubst, Tm.bsubst_lst]
  simp only [Tm.castLE_refl]
  congr 1
  funext j
  fin_cases j
  · change Fin.lastCases i _ (Fin.castSucc (Fin.last 0)) = a
    rw [Fin.lastCases_castSucc, Fin.lastCases_last]
  · dsimp only
    change Fin.lastCases i _ (Fin.last 1) = i
    exact Fin.lastCases_last

theorem positionAt_formation_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) {i a : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a) :
    Γ.JEqB levels H (.univ n) (S.positionAt i a) (S.positionAt i a) := by
  simpa only [Description.positionAt, double_lst_eq_bsubst] using positionAt_formation_iterated_of_hypotheses hH D hi ha

theorem positionFamily_beta_direct_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) {i a : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a) :
    Γ.JEqB levels H (.univ n) (.app (.app S.positionFamily i) a) (S.positionAt i a) := by
  simpa only [Description.positionAt, double_lst_eq_bsubst] using positionFamily_beta_of_hypotheses hH D hi ha

private theorem lastCases_zero {α : Sort _} (a : α) (f : Fin 0 → α) :
    Fin.lastCases a f (0 : Fin 1) = a := Fin.lastCases_last

private theorem positions_lst (S : Description) (l : Tm 0) :
    S.positions.lst l = S.positionAt (.fst l) (.snd l) := by
  rw [Description.positions, Tm.lst_eq_bsubst, Tm.bsubst_comp, Description.positionAt]
  congr 1
  funext j
  refine Fin.cases ?_ (fun _ => ?_) j
  · change Tm.bsubst _ (.snd (.bv (0 : Fin 1))) = .snd l
    simp only [Tm.bsubst, lastCases_zero, Tm.castLE_refl]
  · change Tm.bsubst _ (.fst (.bv (0 : Fin 1))) = .fst l
    simp only [Tm.bsubst, lastCases_zero, Tm.castLE_refl]

private theorem compiledPositions_lst (S : Description) (l : Tm 0) :
    S.compiledPositions.lst l = .app (.app S.positionFamily (.fst l)) (.snd l) := by
  rw [Tm.lst_eq_bsubst]
  simp only [Description.compiledPositions, Tm.bsubst, Tm.bsubst_closed_castLE,
    Tm.castLE_refl, lastCases_zero]

theorem compiledPositions_beta_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) {l : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l) :
    Γ.JEqB levels H (.univ n) (S.compiledPositions.lst l) (S.positions.lst l) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hi : Γ.JEqB levels H S.index (.fst l) (.fst l) := .fst hn D.index D.shape hl
  have ha : Γ.JEqB levels H (S.shape.lst (.fst l)) (.snd l) (.snd l) :=
    .snd hn D.index D.shape hl
  simpa only [compiledPositions_lst, positions_lst] using positionFamily_beta_direct_of_hypotheses hH D hi ha

private theorem lst_fv (B : Tm 1) (x : String) : B.lst (.fv x) = B.open x := by
  rw [Tm.lst_eq_bsubst, Tm.open_eq_bsubst]
  simp only [Tm.castLE]

theorem compiledRaw_beta_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) :
    Γ.JEqB levels H (.univ n) S.compiledRaw S.raw := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hlabels := totalShape_formation D
  have hB : ∀ x ∉ Γ.dv, (Γ.cons x S.totalShape).JEqB levels H (.univ n)
      (S.compiledPositions.open x) (S.positions.open x) := by
    intro x hx
    have hctx : (Γ.cons x S.totalShape).JEqB levels H .unit .star .star :=
      .cons_ok hn D.context hx hlabels
    have hd := D.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hx S.totalShape) hctx
    have hl : (Γ.cons x S.totalShape).JEqB levels H S.totalShape (.fv x) (.fv x) :=
      .var hctx (.here Γ x S.totalShape)
    simpa only [lst_fv] using compiledPositions_beta_of_hypotheses hH hd hl
  exact .wtype hn hlabels hB

theorem raw_formation_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) :
    Γ.JEqB levels H (.univ n) S.raw S.raw :=
  (compiledRaw_beta_of_hypotheses hH D).symm.trans (compiledRaw_beta_of_hypotheses hH D)

private theorem cast_one_eq_wk0 (I : Tm 0) : I.castLE (Nat.zero_le 1) = I.wk0 :=
  (Tm.wkn_past I 0 (Nat.le_refl 0)).symm

theorem nextFamily_data_of_hypotheses {H : Set Jdg} (D : IndexedFormationData S levels n Γ H)
    (hh : HypothesisTransport levels H H) :
    (∀ x ∉ D.names, (Γ.cons x S.index).JEqB levels H (.univ n)
      ((.pi S.shape (.pi S.position (S.index.castLE (by decide))) : Tm 1).open x)
      ((.pi S.shape (.pi S.position (S.index.castLE (by decide))) : Tm 1).open x)) ∧
    (∀ x ∉ D.names, (Γ.cons x S.index).JEqB levels H
      ((.pi S.shape (.pi S.position (S.index.castLE (by decide))) : Tm 1).open x)
      ((.abs S.shape (.abs S.position S.next) : Tm 1).open x)
      ((.abs S.shape (.abs S.position S.next) : Tm 1).open x)) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hctx : ∀ x ∉ D.names, (Γ.cons x S.index).JEqB levels H .unit .star .star := by
    intro x hx
    exact .cons_ok hn D.context (fun h => hx (D.declared h)) D.index
  have hlocal : ∀ x ∉ D.names, ∀ y ∉ insert x D.names,
      ((Γ.cons x S.index).cons y (S.shape.open x)).JEqB levels H (.univ n)
        (((.pi S.position (S.index.castLE (by decide)) : Tm 2).open x).open y)
        (((.pi S.position (S.index.castLE (by decide)) : Tm 2).open x).open y) ∧
      ((Γ.cons x S.index).cons y (S.shape.open x)).JEqB levels H
        (((.pi S.position (S.index.castLE (by decide)) : Tm 2).open x).open y)
        (((.abs S.position S.next : Tm 2).open x).open y)
        (((.abs S.position S.next : Tm 2).open x).open y) := by
    intro x hx y hy
    have hyΓ : y ∉ (Γ.cons x S.index).dv := by
      intro h
      rcases Finset.mem_insert.mp h with h | h
      · exact hy (Finset.mem_insert.mpr (Or.inl h))
      · exact hy (Finset.mem_insert_of_mem (D.declared h))
    have hxy : ((Γ.cons x S.index).cons y (S.shape.open x)).JEqB levels H .unit .star .star :=
      .cons_ok hn (hctx x hx) hyΓ (D.shape x hx)
    have hxΓ : x ∉ Γ.dv := fun h => hx (D.declared h)
    have hIx : (Γ.cons x S.index).JEqB levels H (.univ n) S.index S.index :=
      Ctx.JEqB.weaken_of_hypotheses hh D.index (Ctx.LookupLE.fresh_cons hxΓ S.index) (hctx x hx)
    have hI : ((Γ.cons x S.index).cons y (S.shape.open x)).JEqB levels H (.univ n) S.index S.index :=
      Ctx.JEqB.weaken_of_hypotheses hh hIx (Ctx.LookupLE.fresh_cons hyΓ (S.shape.open x)) hxy
    have hP : ((Γ.cons x S.index).cons y (S.shape.open x)).JEqB levels H (.univ n)
        ((S.position.open x).open y) ((S.position.open x).open y) := D.position x hx y hy
    have hcodomain : ∀ p ∉ ((Γ.cons x S.index).cons y (S.shape.open x)).dv,
        (((Γ.cons x S.index).cons y (S.shape.open x)).cons p ((S.position.open x).open y)).JEqB
          levels H (.univ n) (S.index.wk0.open p) (S.index.wk0.open p) := by
      intro p hp
      have hctxp : (((Γ.cons x S.index).cons y (S.shape.open x)).cons p
          ((S.position.open x).open y)).JEqB levels H .unit .star .star := .cons_ok hn hxy hp hP
      simpa only [Tm.closed_wk0_open] using
        Ctx.JEqB.weaken_of_hypotheses hh hI (Ctx.LookupLE.fresh_cons hp _) hctxp
    have hform : ((Γ.cons x S.index).cons y (S.shape.open x)).JEqB levels H (.univ n)
        (.arr ((S.position.open x).open y) S.index) (.arr ((S.position.open x).open y) S.index) :=
      .pi hn hP hcodomain
    have hnext : ∀ p ∉ insert y (insert x D.names),
        (((Γ.cons x S.index).cons y (S.shape.open x)).cons p ((S.position.open x).open y)).JEqB
          levels H (S.index.wk0.open p) (((S.next.open x).open y).open p)
          (((S.next.open x).open y).open p) := by
      intro p hp
      simpa only [Tm.closed_wk0_open] using D.next x hx y hy p hp
    have hterm := Ctx.JEqB.abs hn hP
      (fun p hp => hcodomain p (by
        intro h
        rcases Finset.mem_insert.mp h with h | h
        · exact hp (Finset.mem_insert.mpr (Or.inl h))
        · rcases Finset.mem_insert.mp h with h | h
          · exact hp (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl h)))
          · exact hp (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (D.declared h))))) hnext
    simpa only [Tm.open, Tm.closed_castLE_open, cast_one_eq_wk0, Tm.arr] using And.intro hform hterm
  have htype : ∀ x ∉ D.names, (Γ.cons x S.index).JEqB levels H (.univ n)
      ((.pi S.shape (.pi S.position (S.index.castLE (by decide))) : Tm 1).open x)
      ((.pi S.shape (.pi S.position (S.index.castLE (by decide))) : Tm 1).open x) := by
    intro x hx
    simpa only [Tm.open] using Ctx.JEqB.pi hn (D.shape x hx)
      (fun y hy => (hlocal x hx y hy).1)
  have hbody : ∀ x ∉ D.names, (Γ.cons x S.index).JEqB levels H
      ((.pi S.shape (.pi S.position (S.index.castLE (by decide))) : Tm 1).open x)
      ((.abs S.shape (.abs S.position S.next) : Tm 1).open x)
      ((.abs S.shape (.abs S.position S.next) : Tm 1).open x) := by
    intro x hx
    simpa only [Tm.open] using Ctx.JEqB.abs hn (D.shape x hx)
      (fun y hy => (hlocal x hx y hy).1) (fun y hy => (hlocal x hx y hy).2)
  exact ⟨htype, hbody⟩

theorem nextFamily_typing_of_hypotheses {H : Set Jdg} (D : IndexedFormationData S levels n Γ H)
    (hh : HypothesisTransport levels H H) :
    Γ.JEqB levels H S.nextFamilyType S.nextFamily S.nextFamily :=
  Ctx.JEqB.abs (by have := D.bound; budget_omega) D.index (nextFamily_data_of_hypotheses D hh).1 (nextFamily_data_of_hypotheses D hh).2

theorem nextFamily_data (D : IndexedFormationData S levels n Γ) :
    (∀ x ∉ D.names, (Γ.cons x S.index).JEqB levels ∅ (.univ n)
      ((.pi S.shape (.pi S.position (S.index.castLE (by decide))) : Tm 1).open x)
      ((.pi S.shape (.pi S.position (S.index.castLE (by decide))) : Tm 1).open x)) ∧
    (∀ x ∉ D.names, (Γ.cons x S.index).JEqB levels ∅
      ((.pi S.shape (.pi S.position (S.index.castLE (by decide))) : Tm 1).open x)
      ((.abs S.shape (.abs S.position S.next) : Tm 1).open x)
      ((.abs S.shape (.abs S.position S.next) : Tm 1).open x)) :=
  nextFamily_data_of_hypotheses D (HypothesisTransport.empty levels ∅)

theorem nextFamily_typing (D : IndexedFormationData S levels n Γ) :
    Γ.JEqB levels ∅ S.nextFamilyType S.nextFamily S.nextFamily :=
  nextFamily_typing_of_hypotheses D (HypothesisTransport.empty levels ∅)

private theorem closed_castLE_lst {k : ℕ} (I a : Tm 0) :
    (I.castLE (Nat.zero_le (k + 1))).lst a = I.castLE (Nat.zero_le k) := by
  rw [Tm.lst_eq_bsubst, Tm.bsubst_closed_castLE]

theorem nextValue_typing_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i a p : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hp : Γ.JEqB levels H (S.positionAt i a) p p) :
    Γ.JEqB levels H S.index (.app (.app (.app S.nextFamily i) a) p)
      (.app (.app (.app S.nextFamily i) a) p) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hfirst : Γ.JEqB levels H
      (.pi (S.shape.lst i) (.pi (S.position.lst i) (S.index.castLE (by decide))))
      (.app S.nextFamily i) (.app S.nextFamily i) := by
    simpa only [Description.nextFamilyType, Tm.lst, closed_castLE_lst] using
      Ctx.JEqB.app hn D.index (nextFamily_data_of_hypotheses D hH.weakening).1 (nextFamily_typing_of_hypotheses D hH.weakening) hi
  have hshape : Γ.JEqB levels H (.univ n) (S.shape.lst i) (S.shape.lst i) :=
    shapeAt_formation_of_hypotheses hH D.toFormationData hi
  obtain ⟨L, hP⟩ := position_after_index_of_hypotheses hH D.toFormationData hi
  have hsecondFamily : ∀ y ∉ L ∪ Γ.dv, (Γ.cons y (S.shape.lst i)).JEqB levels H (.univ n)
      ((.pi (S.position.lst i) (S.index.castLE (by decide)) : Tm 1).open y)
      ((.pi (S.position.lst i) (S.index.castLE (by decide)) : Tm 1).open y) := by
    intro y hy
    have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _ h)
    have hyΓ : y ∉ Γ.dv := fun h => hy (Finset.mem_union_right _ h)
    have hctx : (Γ.cons y (S.shape.lst i)).JEqB levels H .unit .star .star :=
      .cons_ok hn D.context hyΓ hshape
    have hI : (Γ.cons y (S.shape.lst i)).JEqB levels H (.univ n) S.index S.index :=
      Ctx.JEqB.weaken_of_hypotheses hH.weakening D.index (Ctx.LookupLE.fresh_cons hyΓ _) hctx
    simpa only [Tm.open, Tm.closed_castLE_open, cast_one_eq_wk0, Tm.arr] using
      Ctx.JEqB.arrow_formation_of_hypotheses hH.weakening hn hctx (hP y hyL) hI
  have hsecond : Γ.JEqB levels H (.arr (S.positionAt i a) S.index)
      (.app (.app S.nextFamily i) a) (.app (.app S.nextFamily i) a) := by
    simpa only [Tm.lst, closed_castLE_lst, double_lst_eq_bsubst, Description.positionAt,
      cast_one_eq_wk0, Tm.arr] using Ctx.JEqB.app hn hshape hsecondFamily hfirst ha
  have hpositions : Γ.JEqB levels H (.univ n) (S.positionAt i a) (S.positionAt i a) :=
    positionAt_formation_of_hypotheses hH D.toFormationData hi ha
  simpa only [Tm.closed_wk0_lst] using Ctx.JEqB.app hn hpositions
    (Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn D.context hpositions D.index) hsecond hp

/-- No compiled-child certificate: the input is the original three-binder source typing. -/
theorem compiledChildIndex_typing_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l p : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hp : Γ.JEqB levels H (S.compiledPositions.lst l) p p) :
    Γ.JEqB levels H S.index (S.compiledChildIndex l p) (S.compiledChildIndex l p) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hi : Γ.JEqB levels H S.index (.fst l) (.fst l) := .fst hn D.index D.shape hl
  have ha : Γ.JEqB levels H (S.shape.lst (.fst l)) (.snd l) (.snd l) :=
    .snd hn D.index D.shape hl
  have hp' : Γ.JEqB levels H (S.positionAt (.fst l) (.snd l)) p p := by
    simpa only [positions_lst] using Ctx.JEqB.conv hn (compiledPositions_beta_of_hypotheses hH D.toFormationData hl) hp
  exact nextValue_typing_of_hypotheses hH D hi ha hp'

theorem shapeAt_formation (D : FormationData S levels n Γ) {i : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) :
    Γ.JEqB levels ∅ (.univ n) (S.shape.lst i) (S.shape.lst i) :=
  shapeAt_formation_of_hypotheses (StructuralTheory.empty levels) D hi

theorem position_after_index (D : FormationData S levels n Γ) {i : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) :
    ∃ L : Finset String, ∀ y ∉ L, (Γ.cons y (S.shape.lst i)).JEqB levels ∅ (.univ n)
      ((S.position.lst i).open y) ((S.position.lst i).open y) :=
  position_after_index_of_hypotheses (StructuralTheory.empty levels) D hi

theorem positionAt_formation_iterated (D : FormationData S levels n Γ) {i a : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a) :
    Γ.JEqB levels ∅ (.univ n) ((S.position.lst i).lst a) ((S.position.lst i).lst a) :=
  positionAt_formation_iterated_of_hypotheses (StructuralTheory.empty levels) D hi ha

theorem positionFamily_beta (D : FormationData S levels n Γ) {i a : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a) :
    Γ.JEqB levels ∅ (.univ n) (.app (.app S.positionFamily i) a)
      ((S.position.lst i).lst a) :=
  positionFamily_beta_of_hypotheses (StructuralTheory.empty levels) D hi ha

theorem positionAt_formation (D : FormationData S levels n Γ) {i a : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a) :
    Γ.JEqB levels ∅ (.univ n) (S.positionAt i a) (S.positionAt i a) :=
  positionAt_formation_of_hypotheses (StructuralTheory.empty levels) D hi ha

theorem positionFamily_beta_direct (D : FormationData S levels n Γ) {i a : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a) :
    Γ.JEqB levels ∅ (.univ n) (.app (.app S.positionFamily i) a) (S.positionAt i a) :=
  positionFamily_beta_direct_of_hypotheses (StructuralTheory.empty levels) D hi ha

theorem compiledPositions_beta (D : FormationData S levels n Γ) {l : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l) :
    Γ.JEqB levels ∅ (.univ n) (S.compiledPositions.lst l) (S.positions.lst l) :=
  compiledPositions_beta_of_hypotheses (StructuralTheory.empty levels) D hl

theorem compiledRaw_beta (D : FormationData S levels n Γ) :
    Γ.JEqB levels ∅ (.univ n) S.compiledRaw S.raw :=
  compiledRaw_beta_of_hypotheses (StructuralTheory.empty levels) D

theorem raw_formation (D : FormationData S levels n Γ) :
    Γ.JEqB levels ∅ (.univ n) S.raw S.raw :=
  raw_formation_of_hypotheses (StructuralTheory.empty levels) D

theorem nextValue_typing (D : IndexedFormationData S levels n Γ) {i a p : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hp : Γ.JEqB levels ∅ (S.positionAt i a) p p) :
    Γ.JEqB levels ∅ S.index (.app (.app (.app S.nextFamily i) a) p)
      (.app (.app (.app S.nextFamily i) a) p) :=
  nextValue_typing_of_hypotheses (StructuralTheory.empty levels) D hi ha hp

theorem compiledChildIndex_typing (D : IndexedFormationData S levels n Γ) {l p : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hp : Γ.JEqB levels ∅ (S.compiledPositions.lst l) p p) :
    Γ.JEqB levels ∅ S.index (S.compiledChildIndex l p) (S.compiledChildIndex l p) :=
  compiledChildIndex_typing_of_hypotheses (StructuralTheory.empty levels) D hl hp

private theorem successor_index_context (x : String) :
    (Ctx.nil.cons x .nats).JEqB 2 ∅ .unit .star .star :=
  .cons_ok (n := 0) (by decide) .nil_ok (by simp [Ctx.dv]) (.nats (by decide) .nil_ok)

private theorem successor_shape_context (x y : String) (hy : y ∉ ({x} : Finset String)) :
    ((Ctx.nil.cons x .nats).cons y .unit).JEqB 2 ∅ .unit .star .star :=
  .cons_ok (n := 0) (by decide) (successor_index_context x)
    (by simpa [Ctx.dv] using hy) (.unit (by decide) (successor_index_context x))

private theorem lastCases_two {α : Sort _} (a : α) (f : Fin 2 → α) :
    Fin.lastCases a f (2 : Fin 3) = a := Fin.lastCases_last

/-- A source telescope with actual arguments and a nonconstant original next term. -/
def successorIndexedFormationData : IndexedFormationData successorDescription 2 0 .nil where
  bound := by decide
  names := ∅
  declared := by simp [Ctx.dv]
  context := .nil_ok
  index := .nats (by decide) .nil_ok
  shape x hx := by
    simpa only [successorDescription, Tm.open] using
      Ctx.JEqB.unit (n := 0) (by decide) (successor_index_context x)
  position x hx y hy := by
    simpa only [successorDescription, Tm.open] using
      Ctx.JEqB.unit (n := 0) (by decide) (successor_shape_context x y (by simpa using hy))
  next x hx y hy p hp := by
    have hyx : y ≠ x := by simpa using hy
    have hxy : ((Ctx.nil.cons x .nats).cons y .unit).JEqB 2 ∅ .unit .star .star :=
      successor_shape_context x y (by simpa using hy)
    have hpCtx : p ∉ ((Ctx.nil.cons x .nats).cons y .unit).dv := by
      simpa [Ctx.dv] using hp
    have hpX : p ≠ x := by
      intro h
      subst p
      exact hp (by simp)
    have hctx : (((Ctx.nil.cons x .nats).cons y .unit).cons p .unit).JEqB 2 ∅ .unit .star .star :=
      .cons_ok (n := 0) (by decide) hxy hpCtx (.unit (by decide) hxy)
    have hlookup : (((Ctx.nil.cons x .nats).cons y .unit).cons p .unit).Lookup x .nats :=
      .there _ _ _ _ _ (.there _ _ _ _ _ (.here .nil x .nats) hyx.symm) hpX.symm
    simpa only [successorDescription, Tm.open, lastCases_two] using
      Ctx.JEqB.succ (Ctx.JEqB.var hctx hlookup)

theorem successor_nextValue_typing : Ctx.JEqB 2 ∅ .nil .nats
    (.app (.app (.app successorDescription.nextFamily .zero) .star) .star)
    (.app (.app (.app successorDescription.nextFamily .zero) .star) .star) := by
  have hi : Ctx.JEqB 2 ∅ .nil successorDescription.index .zero .zero :=
    .zero .nil_ok
  have ha : Ctx.JEqB 2 ∅ .nil (successorDescription.shape.lst .zero) .star .star := by
    simpa only [successorDescription, Tm.lst] using (Ctx.JEqB.nil_ok (levels := 2) (H := ∅))
  have hp : Ctx.JEqB 2 ∅ .nil (successorDescription.positionAt .zero .star) .star .star := by
    simpa only [successorDescription, Description.positionAt, Tm.bsubst] using
      (Ctx.JEqB.nil_ok (levels := 2) (H := ∅))
  exact nextValue_typing successorIndexedFormationData hi ha hp

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
