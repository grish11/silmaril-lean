module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Coherence
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.HeadComputation

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

variable {H : Set Jdg} {S : Description} {levels : RuleBudget} {n : ℕ} {Γ : Ctx}

private theorem lastCases_zero {α : Sort _} (a : α) (f : Fin 0 → α) :
    Fin.lastCases a f (0 : Fin 1) = a := Fin.lastCases_last

/-- The original root eliminator computes to the first projection of its actual label. -/
theorem root_sup_beta_of_hypotheses (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) {l f : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f) :
    Γ.JEqB levels H S.index (S.root (.sup S.totalShape S.positions l f)) (.fst l) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hlabel : ∀ x ∉ Γ.dv, (Γ.cons x S.totalShape).JEqB levels H S.index
      ((.fst (.bv 0) : Tm 1).open x) ((.fst (.bv 0) : Tm 1).open x) := by
    intro x hx
    have hctx : (Γ.cons x S.totalShape).JEqB levels H .unit .star .star :=
      .cons_ok hn D.context hx (totalShape_formation D)
    have hd := D.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hx S.totalShape) hctx
    have hlx : (Γ.cons x S.totalShape).JEqB levels H S.totalShape (.fv x) (.fv x) :=
      .var hctx (.here Γ x S.totalShape)
    simpa only [Tm.open, lastCases_zero] using Ctx.JEqB.fst hn hd.index hd.shape hlx
  simpa only [root_eq_head, Tm.lst, lastCases_zero, Tm.castLE_refl] using
    Ctx.JEqB.head_beta_of_hypotheses hH hn D.context (totalShape_formation D) D.index
      (positions_formation_of_hypotheses hH D) hlabel hl hf

/-- A tagged actual W node has exactly its declared result index. -/
theorem root_tagged_sup_beta_of_hypotheses (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) {i a f : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst (.pair i a)) S.raw) f f) :
    Γ.JEqB levels H S.index
      (S.root (.sup S.totalShape S.positions (.pair i a) f)) i := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hlabel : Γ.JEqB levels H S.totalShape (.pair i a) (.pair i a) :=
    .pair hn D.index D.shape hi ha
  exact (root_sup_beta_of_hypotheses hH D hlabel hf).trans (.beta_fst hn D.index D.shape hi ha)

theorem root_sup_beta (D : FormationData S levels n Γ) {l f : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f) :
    Γ.JEqB levels ∅ S.index (S.root (.sup S.totalShape S.positions l f)) (.fst l) :=
  root_sup_beta_of_hypotheses (StructuralTheory.empty levels) D hl hf

theorem root_tagged_sup_beta (D : FormationData S levels n Γ) {i a f : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst (.pair i a)) S.raw) f f) :
    Γ.JEqB levels ∅ S.index
      (S.root (.sup S.totalShape S.positions (.pair i a) f)) i :=
  root_tagged_sup_beta_of_hypotheses (StructuralTheory.empty levels) D hi ha hf

/-- A closed original raw leaf supplies an actual constructor-computation instance. -/
theorem nullary_root_beta : Ctx.JEqB 2 ∅ .nil .unit
    (nullaryDescription.root nullaryRawLeaf) .star := by
  let D := nullaryIndexedFormationData
  have hraw : Ctx.JEqB 2 ∅ .nil (.univ 0) nullaryDescription.raw nullaryDescription.raw :=
    raw_formation D.toFormationData
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
      lastCases_zero] using Ctx.JEqB.absurd (by decide)
        (hraw.weaken (Ctx.LookupLE.fresh_cons (by simp [Ctx.dv]) .empty) hctx) hp'
  exact root_tagged_sup_beta D.toFormationData .nil_ok
    (by simpa only [nullaryDescription, Tm.lst] using (Ctx.JEqB.nil_ok (levels := 2) (H := ∅)))
    (by simpa only [Description.positions, nullaryDescription, Tm.bsubst, Tm.lst] using hfun)

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
