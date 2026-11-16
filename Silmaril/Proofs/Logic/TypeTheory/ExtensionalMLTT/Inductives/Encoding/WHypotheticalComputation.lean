module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Computation.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.DependentTelescope

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.WHypotheticalComputation

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.HypotheticalExamples

private theorem unit_hyp {Γ : Ctx} : Γ.JEqB 2 (ContextClosure basis) (.univ 0) .unit .unit := by
  apply Ctx.JEqB.hyp
  refine ⟨.nil, hypothesis_present, ?_⟩
  intro y A h
  cases h

private theorem lastCases_zero {α : Sort _} (a : α) (f : Fin 0 → α) :
    Fin.lastCases a f (0 : Fin 1) = a := Fin.lastCases_last

private theorem lastCases_one {α : Sort _} (a : α) (f : Fin 1 → α) :
    Fin.lastCases a f (1 : Fin 2) = a := Fin.lastCases_last

private theorem lastCases_first {α : Sort _} (a : α) (f : Fin 1 → α) :
    Fin.lastCases a f (0 : Fin 2) = f 0 := Fin.lastCases_castSucc 0

private theorem typeContext (x : String) :
    (Ctx.nil.cons x (.univ 0)).JEqB 2 (ContextClosure basis) .unit .star .star :=
  .cons_ok (n := 1) (by decide) .nil_ok (by simp [Ctx.dv]) (.univ (by decide) .nil_ok)

private theorem elementContext (x y : String) (hy : y ≠ x) :
    ((Ctx.nil.cons x (.univ 0)).cons y (.fv x)).JEqB 2 (ContextClosure basis) .unit .star .star :=
  .cons_ok (n := 0) (by decide) (typeContext x) (by simpa [Ctx.dv] using hy)
    (.var (typeContext x) (.here ..))

/-- The result carrier depends on the first source argument; its Unit instantiation is an actual hypothesis leaf. -/
theorem dependent_identity_beta : Ctx.nil.JEqB 2 (ContextClosure basis) .unit
    (.app (.app (.abs (.univ 0) (.abs (.bv 0) (.bv 0))) .unit) .star) .star := by
  have hB : ∀ x ∉ (∅ : Finset String), (Ctx.nil.cons x (.univ 0)).JEqB 2 (ContextClosure basis)
      (.univ 1) ((.bv 0 : Tm 1).open x) ((.bv 0 : Tm 1).open x) := by
    intro x _
    simpa [Tm.open, lastCases_zero, lastCases_one, lastCases_first] using
      Ctx.JEqB.cumul (n := 1) (by decide) (by decide) (Ctx.JEqB.var (typeContext x) (.here ..))
  have hD : ∀ x ∉ (∅ : Finset String), ∀ y ∉ insert x (∅ : Finset String),
      ((Ctx.nil.cons x (.univ 0)).cons y ((.bv 0 : Tm 1).open x)).JEqB 2 (ContextClosure basis)
        (.univ 1) (((.bv 1 : Tm 2).open x).open y) (((.bv 1 : Tm 2).open x).open y) := by
    intro x _ y hy
    have hyx : y ≠ x := by simpa using hy
    have hx : ((Ctx.nil.cons x (.univ 0)).cons y (.fv x)).Lookup x (.univ 0) :=
      .there _ _ _ _ _ (.here ..) hyx.symm
    simpa [Tm.open, lastCases_zero, lastCases_one, lastCases_first] using
      Ctx.JEqB.cumul (n := 1) (by decide) (by decide) (Ctx.JEqB.var (elementContext x y hyx) hx)
  have hK : ∀ x ∉ (∅ : Finset String), ∀ y ∉ insert x (∅ : Finset String),
      ((Ctx.nil.cons x (.univ 0)).cons y ((.bv 0 : Tm 1).open x)).JEqB 2 (ContextClosure basis)
        (((.bv 1 : Tm 2).open x).open y) (((.bv 0 : Tm 2).open x).open y)
        (((.bv 0 : Tm 2).open x).open y) := by
    intro x _ y hy
    have hyx : y ≠ x := by simpa using hy
    simpa [Tm.open, lastCases_zero, lastCases_one, lastCases_first] using Ctx.JEqB.var (elementContext x y hyx) (.here ..)
  simpa [Tm.lst, Tm.castLE, lastCases_zero, lastCases_one, lastCases_first] using
    Ctx.JEqB.doubleAbstraction_beta_of_hypotheses (A := .univ 0) (B := .bv 0) (D := .bv 1)
      (K := .bv 0) (a := .unit) (b := .star) basis_structural (n := 1) (by decide) .nil_ok
      (.univ (by decide) .nil_ok) hB hD hK unit_hyp (by simpa [Tm.lst, Tm.castLE, lastCases_zero, lastCases_one, lastCases_first] using
        (Ctx.JEqB.nil_ok (levels := 2) (H := ContextClosure basis)))

/-- The original root computes on an actual W leaf formed from the hypothesis-bearing descriptor. -/
theorem nullary_root_beta : Ctx.nil.JEqB 2 (ContextClosure basis) .unit
    (nullaryDescription.root nullaryRawLeaf) .star := by
  let D := nullarySourceData.toFormationData
  have hraw : Ctx.nil.JEqB 2 (ContextClosure basis) (.univ 0)
      nullaryDescription.raw nullaryDescription.raw := raw_formation_of_hypotheses basis_structural D
  have hfun : Ctx.nil.JEqB 2 (ContextClosure basis) (.arr .empty nullaryDescription.raw)
      (.abs .empty (.absurd (nullaryDescription.raw.castLE (by decide)) (.bv 0)))
      (.abs .empty (.absurd (nullaryDescription.raw.castLE (by decide)) (.bv 0))) := by
    apply Ctx.JEqB.abs (L := ∅) (n := 0) (by decide) (.empty (by decide) .nil_ok)
      (Ctx.JEqB.constant_family_of_hypotheses basis_structural.weakening (by decide) .nil_ok
        (.empty (by decide) .nil_ok) hraw)
    intro p _
    have hctx : (Ctx.nil.cons p .empty).JEqB 2 (ContextClosure basis) .unit .star .star :=
      .cons_ok (n := 0) (by decide) .nil_ok (by simp [Ctx.dv]) (.empty (by decide) .nil_ok)
    have hp : (Ctx.nil.cons p .empty).JEqB 2 (ContextClosure basis) .empty (.fv p) (.fv p) :=
      .var hctx (.here ..)
    simpa [Tm.open, Tm.castLE_refl, Tm.closed_castLE_open, Tm.closed_wk0_open, lastCases_zero, lastCases_one, lastCases_first] using
      Ctx.JEqB.absurd (n := 0) (by decide)
        (hraw.weaken_of_hypotheses basis_structural.weakening
          (Ctx.LookupLE.fresh_cons (by simp [Ctx.dv]) .empty) hctx) hp
  exact root_tagged_sup_beta_of_hypotheses basis_structural D .nil_ok
    (by simpa only [nullaryDescription, Tm.lst] using
      (Ctx.JEqB.nil_ok (levels := 2) (H := ContextClosure basis)))
    (by simpa only [Description.positions, nullaryDescription, Tm.bsubst, Tm.lst] using hfun)

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.WHypotheticalComputation
