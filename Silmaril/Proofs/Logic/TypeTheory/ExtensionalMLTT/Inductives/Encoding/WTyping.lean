module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Typing.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

variable {H : Set Jdg} {S : Description} {levels : RuleBudget} {n : ℕ} {Γ : Ctx}

private theorem index_context (D : FormationData S levels n Γ H) {x : String} (hx : x ∉ D.names) :
    (Γ.cons x S.index).JEqB levels H .unit .star .star :=
  .cons_ok (by have := D.bound; budget_omega) D.context (fun h => hx (D.declared h)) D.index

theorem totalShape_formation (D : FormationData S levels n Γ H) :
    Γ.JEqB levels H (.univ n) S.totalShape S.totalShape :=
  .sigma (L := D.names) (by have := D.bound; budget_omega) D.index D.shape

theorem positionFamily_typing (D : FormationData S levels n Γ H) :
    Γ.JEqB levels H (S.positionFamilyType n) S.positionFamily S.positionFamily := by
  have hi : Γ.JEqB levels H (.univ (n + 1)) S.index S.index :=
    .cumul D.bound (Nat.le_succ n) D.index
  have htype : ∀ x ∉ D.names, (Γ.cons x S.index).JEqB levels H (.univ (n + 1))
      ((.pi S.shape (.univ n) : Tm 1).open x) ((.pi S.shape (.univ n) : Tm 1).open x) := by
    intro x hx
    simpa only [Tm.open] using
      Ctx.JEqB.type_family_formation D.bound (index_context D hx) (D.shape x hx)
  have hbody : ∀ x ∉ D.names, (Γ.cons x S.index).JEqB levels H
      ((.pi S.shape (.univ n) : Tm 1).open x)
      ((.abs S.shape S.position : Tm 1).open x) ((.abs S.shape S.position : Tm 1).open x) := by
    intro x hx
    simpa only [Tm.open] using
      Ctx.JEqB.abstract_type D.bound (index_context D hx) (D.shape x hx) (D.position x hx)
  exact Ctx.JEqB.abs D.bound hi htype hbody

/-- Formation data can be carried into all extra telescope contexts by actual weakening. -/
def weakenData_of_hypotheses {K : Set Jdg} {Δ : Ctx} (D : FormationData S levels n Γ H)
    (hh : HypothesisTransport levels H K) (e : Γ.LookupLE Δ)
    (hΔ : Δ.JEqB levels K .unit .star .star) : FormationData S levels n Δ K where
  bound := D.bound
  names := D.names ∪ Δ.dv
  declared _ h := Finset.mem_union_right _ h
  context := hΔ
  index := Ctx.JEqB.weaken_of_hypotheses hh D.index e hΔ
  shape x hx := by
    have hxS : x ∉ D.names := fun h => hx (Finset.mem_union_left _ h)
    have hxΔ : x ∉ Δ.dv := fun h => hx (Finset.mem_union_right _ h)
    have hctx : (Δ.cons x S.index).JEqB levels K .unit .star .star :=
      .cons_ok (by have := D.bound; budget_omega) hΔ hxΔ (Ctx.JEqB.weaken_of_hypotheses hh D.index e hΔ)
    exact Ctx.JEqB.weaken_of_hypotheses hh (D.shape x hxS) (e.cons x S.index) hctx
  position x hx y hy := by
    have hxS : x ∉ D.names := fun h => hx (Finset.mem_union_left _ h)
    have hxΔ : x ∉ Δ.dv := fun h => hx (Finset.mem_union_right _ h)
    have hyx : y ≠ x := fun h => hy (h ▸ Finset.mem_insert_self x (D.names ∪ Δ.dv))
    have hyΔ : y ∉ Δ.dv := fun h => hy (Finset.mem_insert_of_mem (Finset.mem_union_right _ h))
    have hyS : y ∉ insert x D.names := by
      intro h
      rcases Finset.mem_insert.mp h with h | h
      · exact hyx h
      · exact hy (Finset.mem_insert_of_mem (Finset.mem_union_left _ h))
    have hctx : (Δ.cons x S.index).JEqB levels K .unit .star .star :=
      .cons_ok (by have := D.bound; budget_omega) hΔ hxΔ (Ctx.JEqB.weaken_of_hypotheses hh D.index e hΔ)
    have hshape : (Δ.cons x S.index).JEqB levels K (.univ n)
        (S.shape.open x) (S.shape.open x) :=
      Ctx.JEqB.weaken_of_hypotheses hh (D.shape x hxS) (e.cons x S.index) hctx
    have hctx' : ((Δ.cons x S.index).cons y (S.shape.open x)).JEqB levels K .unit .star .star :=
      .cons_ok (by have := D.bound; budget_omega) hctx (by simpa only [Ctx.dv, Finset.mem_insert, not_or] using And.intro hyx hyΔ) hshape
    exact Ctx.JEqB.weaken_of_hypotheses hh (D.position x hxS y hyS)
      (Ctx.LookupLE.cons (Ctx.LookupLE.cons e x S.index) y (S.shape.open x)) hctx'

theorem positionValue_formation (D : FormationData S levels n Γ H) {l : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l) :
    Γ.JEqB levels H (.univ n)
      (.app (.app S.positionFamily (.fst l)) (.snd l))
      (.app (.app S.positionFamily (.fst l)) (.snd l)) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hi : Γ.JEqB levels H S.index (.fst l) (.fst l) :=
    .fst (L := D.names) hn D.index D.shape hl
  have ha : Γ.JEqB levels H (S.shape.lst (.fst l)) (.snd l) (.snd l) :=
    .snd (L := D.names) hn D.index D.shape hl
  have hshape : Γ.JEqB levels H (.univ n) (S.shape.lst (.fst l)) (S.shape.lst (.fst l)) :=
    .instantiate_type D.bound D.context D.index D.shape hi
  have hfamily : Γ.JEqB levels H (S.positionFamilyType n) S.positionFamily S.positionFamily :=
    positionFamily_typing D
  have hcodomain : ∀ x ∉ D.names, (Γ.cons x S.index).JEqB levels H (.univ (n + 1))
      ((.pi S.shape (.univ n) : Tm 1).open x) ((.pi S.shape (.univ n) : Tm 1).open x) := by
    intro x hx
    simpa only [Tm.open] using
      Ctx.JEqB.type_family_formation D.bound (index_context D hx) (D.shape x hx)
  have hfirst : Γ.JEqB levels H (.pi (S.shape.lst (.fst l)) (.univ n))
      (.app S.positionFamily (.fst l)) (.app S.positionFamily (.fst l)) := by
    simpa only [Tm.lst] using Ctx.JEqB.app D.bound
      (Ctx.JEqB.cumul D.bound (Nat.le_succ n) D.index) hcodomain hfamily hi
  have huniverse : ∀ x ∉ Γ.dv, (Γ.cons x (S.shape.lst (.fst l))).JEqB levels H (.univ (n + 1))
      ((.univ n : Tm 1).open x) ((.univ n : Tm 1).open x) := by
    intro x hx
    simpa only [Tm.open] using Ctx.JEqB.univ D.bound (Ctx.JEqB.cons_ok hn D.context hx hshape)
  simpa only [Tm.lst] using Ctx.JEqB.app D.bound
    (Ctx.JEqB.cumul D.bound (Nat.le_succ n) hshape) huniverse hfirst ha

private theorem lastCases_zero {α : Sort _} (a : α) (f : Fin 0 → α) :
    Fin.lastCases a f (0 : Fin 1) = a := Fin.lastCases_last

theorem compiledPositions_formation_of_hypotheses (D : FormationData S levels n Γ H)
    (hh : HypothesisTransport levels H H) :
    ∀ x ∉ Γ.dv, (Γ.cons x S.totalShape).JEqB levels H (.univ n)
      (S.compiledPositions.open x) (S.compiledPositions.open x) := by
  intro x hx
  have htotal : Γ.JEqB levels H (.univ n) S.totalShape S.totalShape := totalShape_formation D
  have hctx : (Γ.cons x S.totalShape).JEqB levels H .unit .star .star :=
    .cons_ok (by have := D.bound; budget_omega) D.context hx htotal
  have hd := weakenData_of_hypotheses D hh (Ctx.LookupLE.fresh_cons hx S.totalShape) hctx
  have hl : (Γ.cons x S.totalShape).JEqB levels H S.totalShape (.fv x) (.fv x) :=
    .var hctx (.here Γ x S.totalShape)
  have hopen : S.compiledPositions.open x =
      .app (.app S.positionFamily (.fst (.fv x))) (.snd (.fv x)) := by
    simp only [Description.compiledPositions, Tm.open, lastCases_zero]
    rw [Tm.open_castLE S.positionFamily (Nat.le_refl 0), Tm.castLE_refl]
  rw [hopen]
  exact positionValue_formation hd hl

/-- A genuinely typed W carrier compiled from arbitrary indexed source families. -/
theorem compiledRaw_formation_of_hypotheses (D : FormationData S levels n Γ H)
    (hh : HypothesisTransport levels H H) :
    Γ.JEqB levels H (.univ n) S.compiledRaw S.compiledRaw :=
  .wtype (L := Γ.dv) (by have := D.bound; budget_omega) (totalShape_formation D)
    (compiledPositions_formation_of_hypotheses D hh)

theorem compiledNode_typing_of_hypotheses (D : FormationData S levels n Γ H)
    (hh : HypothesisTransport levels H H) {a f : Tm 0}
    (ha : Γ.JEqB levels H S.totalShape a a)
    (hf : Γ.JEqB levels H (.arr (S.compiledPositions.lst a) S.compiledRaw) f f) :
    Γ.JEqB levels H S.compiledRaw
      (.sup S.totalShape S.compiledPositions a f) (.sup S.totalShape S.compiledPositions a f) :=
  .sup (L := Γ.dv) (by have := D.bound; budget_omega) (totalShape_formation D)
    (compiledPositions_formation_of_hypotheses D hh) ha hf

/-- Preserve the existing closed-theory API. -/
def weakenData {Δ : Ctx} (D : FormationData S levels n Γ) (e : Γ.LookupLE Δ)
    (hΔ : Δ.JEqB levels ∅ .unit .star .star) : FormationData S levels n Δ :=
  weakenData_of_hypotheses D (HypothesisTransport.empty levels ∅) e hΔ

theorem compiledPositions_formation (D : FormationData S levels n Γ) :
    ∀ x ∉ Γ.dv, (Γ.cons x S.totalShape).JEqB levels ∅ (.univ n)
      (S.compiledPositions.open x) (S.compiledPositions.open x) :=
  compiledPositions_formation_of_hypotheses D (HypothesisTransport.empty levels ∅)

theorem compiledRaw_formation (D : FormationData S levels n Γ) :
    Γ.JEqB levels ∅ (.univ n) S.compiledRaw S.compiledRaw :=
  compiledRaw_formation_of_hypotheses D (HypothesisTransport.empty levels ∅)

theorem compiledNode_typing (D : FormationData S levels n Γ) {a f : Tm 0}
    (ha : Γ.JEqB levels ∅ S.totalShape a a)
    (hf : Γ.JEqB levels ∅ (.arr (S.compiledPositions.lst a) S.compiledRaw) f f) :
    Γ.JEqB levels ∅ S.compiledRaw
      (.sup S.totalShape S.compiledPositions a f) (.sup S.totalShape S.compiledPositions a f) :=
  compiledNode_typing_of_hypotheses D (HypothesisTransport.empty levels ∅) ha hf

theorem compiledRoot_typing_of_hypotheses (hh : HypothesisTransport levels H H) (D : FormationData S levels n Γ H) {t : Tm 0}
    (ht : Γ.JEqB levels H S.compiledRaw t t) :
    Γ.JEqB levels H S.index (S.compiledRoot t) (S.compiledRoot t) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hlabel : ∀ x ∉ Γ.dv, (Γ.cons x S.totalShape).JEqB levels H S.index
      ((.fst (.bv 0) : Tm 1).open x) ((.fst (.bv 0) : Tm 1).open x) := by
    intro x hx
    have hctx : (Γ.cons x S.totalShape).JEqB levels H .unit .star .star :=
      .cons_ok hn D.context hx (totalShape_formation D)
    have hd := weakenData_of_hypotheses D hh (Ctx.LookupLE.fresh_cons hx S.totalShape) hctx
    have hv : (Γ.cons x S.totalShape).JEqB levels H S.totalShape (.fv x) (.fv x) :=
      .var hctx (.here Γ x S.totalShape)
    simpa only [Tm.open, lastCases_zero] using
      Ctx.JEqB.fst hn hd.index hd.shape hv
  simpa only [Description.compiledRaw, Description.compiledRoot] using
    Ctx.JEqB.head_typing_of_hypotheses hh hn D.context (totalShape_formation D) D.index
      (compiledPositions_formation_of_hypotheses D hh) hlabel ht
theorem compiledRoot_typing (D : FormationData S levels n Γ) {t : Tm 0}
    (ht : Γ.JEqB levels ∅ S.compiledRaw t t) :
    Γ.JEqB levels ∅ S.index (S.compiledRoot t) (S.compiledRoot t) :=
  compiledRoot_typing_of_hypotheses (HypothesisTransport.empty levels ∅) D ht


/-- The generic source hypotheses are realized at the first usable beta budget. -/
def nullaryFormationData : FormationData nullaryDescription 2 0 .nil where
  bound := by decide
  names := ∅
  declared := by simp [Ctx.dv]
  context := .nil_ok
  index := .unit (by decide) .nil_ok
  shape x hx := by
    have hctx : (Ctx.nil.cons x .unit).JEqB 2 ∅ .unit .star .star :=
      .cons_ok (n := 0) (by decide) .nil_ok (by simp [Ctx.dv]) (.unit (by decide) .nil_ok)
    simpa only [nullaryDescription, Tm.open] using Ctx.JEqB.unit (n := 0) (by decide) hctx
  position x hx y hy := by
    have hctx : (Ctx.nil.cons x .unit).JEqB 2 ∅ .unit .star .star :=
      .cons_ok (n := 0) (by decide) .nil_ok (by simp [Ctx.dv]) (.unit (by decide) .nil_ok)
    have hctx' : ((Ctx.nil.cons x .unit).cons y .unit).JEqB 2 ∅ .unit .star .star :=
      .cons_ok (n := 0) (by decide) hctx (by simpa [Ctx.dv] using hy) (.unit (by decide) hctx)
    simpa only [nullaryDescription, Tm.open] using Ctx.JEqB.empty (n := 0) (by decide) hctx'

theorem nullary_raw_formation : Ctx.JEqB 2 ∅ .nil (.univ 0)
    nullaryDescription.compiledRaw nullaryDescription.compiledRaw :=
  compiledRaw_formation nullaryFormationData

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
