module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Source.Thms

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.HypotheticalExamples

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

theorem basis_closed : ClosedHypotheses basis := by
  intro j hj
  have heq : j = indexHypothesis := hj
  subst j
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The nonempty theory has actual structural leaf transport, not encoded result assumptions. -/
theorem basis_structural : StructuralTheory 2 (ContextClosure basis) :=
  StructuralTheory.contextClosure basis_closed

private theorem unit_hyp {Γ : Ctx} : Γ.JEqB 2 (ContextClosure basis) (.univ 0) .unit .unit := by
  apply Ctx.JEqB.hyp
  refine ⟨.nil, hypothesis_present, ?_⟩
  intro y A h
  cases h

private theorem lastCases_zero {α : Sort _} (a : α) (f : Fin 0 → α) :
    Fin.lastCases a f (0 : Fin 1) = a := Fin.lastCases_last

/-- Generic substitution runs through an actual hypothesis beneath a cofinite binder. -/
theorem pair_instantiated : Ctx.nil.JEqB 2 (ContextClosure basis)
    (.sigma .nats .unit) (.pair .zero .star) (.pair .zero .star) := by
  have hbody : ∀ y ∉ (∅ : Finset String), (Ctx.nil.cons y .nats).JEqB 2 (ContextClosure basis)
      ((.sigma .nats .unit : Tm 1).open y) ((.pair (.bv 0) .star : Tm 1).open y)
      ((.pair (.bv 0) .star : Tm 1).open y) := by
    intro y _
    have hΓ : (Ctx.nil.cons y .nats).JEqB 2 (ContextClosure basis) .unit .star .star :=
      .cons_ok (n := 0) (by decide) .nil_ok (by simp [Ctx.dv]) (.nats (by decide) .nil_ok)
    have hpair : (Ctx.nil.cons y .nats).JEqB 2 (ContextClosure basis)
        (.sigma .nats .unit) (.pair (.fv y) .star) (.pair (.fv y) .star) :=
      .pair (n := 0) (B := .unit) (L := ∅) (by decide) (.nats (by decide) hΓ)
        (fun _ _ => by simpa only [Tm.open] using unit_hyp) (.var hΓ (.here ..))
        (by simpa only [Tm.lst] using hΓ)
    simpa only [Tm.open, lastCases_zero] using hpair
  simpa only [Tm.lst, Tm.castLE, lastCases_zero] using Ctx.JEqB.instantiate_of_hypotheses
    (v := .zero) basis_structural.weakening (fun x => basis_structural.substitution x .zero)
    Ctx.JEqB.nil_ok (Ctx.JEqB.zero .nil_ok) hbody

private theorem lastCases_two {α : Sort _} (a : α) (f : Fin 2 → α) :
    Fin.lastCases a f (2 : Fin 3) = a := Fin.lastCases_last

/-- Original successor-index data, with actual theory leaves in shape and next-context formation. -/
def successorSourceData : IndexedFormationData successorDescription 2 0 .nil (ContextClosure basis) where
  toFormationData := {
    successorIndexedFormationData.toFormationData.monoTheory (Set.empty_subset _) with
    shape := fun _ _ => by simpa only [successorDescription, Tm.open] using unit_hyp }
  next x hx y hy p hp := by
    have hyx : y ≠ x := by
      intro heq
      subst y
      exact hy (Finset.mem_insert_self _ _)
    have hΓ : (Ctx.nil.cons x .nats).JEqB 2 (ContextClosure basis) .unit .star .star :=
      .cons_ok (n := 0) (by decide) .nil_ok (by simp [Ctx.dv]) (.nats (by decide) .nil_ok)
    have hyΓ : y ∉ (Ctx.nil.cons x .nats).dv := by simpa [Ctx.dv] using hyx
    have hxy : ((Ctx.nil.cons x .nats).cons y .unit).JEqB 2 (ContextClosure basis) .unit .star .star :=
      .cons_ok (n := 0) (by decide) hΓ hyΓ unit_hyp
    have hpX : p ≠ x := by
      intro heq
      subst p
      exact hp (by simp)
    have hpY : p ≠ y := by
      intro heq
      subst p
      exact hp (Finset.mem_insert_self _ _)
    have hpCtx : p ∉ ((Ctx.nil.cons x .nats).cons y .unit).dv := by
      simpa [Ctx.dv] using And.intro hpY hpX
    have hctx : (((Ctx.nil.cons x .nats).cons y .unit).cons p .unit).JEqB
        2 (ContextClosure basis) .unit .star .star :=
      .cons_ok (n := 0) (by decide) hxy hpCtx unit_hyp
    have hlookup : (((Ctx.nil.cons x .nats).cons y .unit).cons p .unit).Lookup x .nats :=
      .there _ _ _ _ _ (.there _ _ _ _ _ (.here .nil x .nats) hyx.symm) hpX.symm
    simpa only [successorDescription, Tm.open, lastCases_two] using
      Ctx.JEqB.succ (Ctx.JEqB.var hctx hlookup)

theorem successor_family_typing : Ctx.nil.JEqB 2 (ContextClosure basis)
    successorDescription.nextFamilyType successorDescription.nextFamily successorDescription.nextFamily :=
  nextFamily_typing_of_hypotheses successorSourceData basis_structural.weakening

/-- Actual original index, shape and position values drive the generic curried source term. -/
theorem successor_value_typing : Ctx.nil.JEqB 2 (ContextClosure basis) .nats
    (.app (.app (.app successorDescription.nextFamily .zero) .star) .star)
    (.app (.app (.app successorDescription.nextFamily .zero) .star) .star) := by
  have hi : Ctx.nil.JEqB 2 (ContextClosure basis) successorDescription.index .zero .zero := .zero .nil_ok
  have ha : Ctx.nil.JEqB 2 (ContextClosure basis) (successorDescription.shape.lst .zero) .star .star := by
    simpa only [successorDescription, Tm.lst] using (Ctx.JEqB.nil_ok (levels := 2) (H := ContextClosure basis))
  have hp : Ctx.nil.JEqB 2 (ContextClosure basis) (successorDescription.positionAt .zero .star) .star .star := by
    simpa only [successorDescription, Description.positionAt, Tm.bsubst] using
      (Ctx.JEqB.nil_ok (levels := 2) (H := ContextClosure basis))
  exact nextValue_typing_of_hypotheses basis_structural successorSourceData hi ha hp

/-- The actual label and position type yield compiled-child typing, without a child certificate. -/
theorem successor_compiledChild_typing : Ctx.nil.JEqB 2 (ContextClosure basis) .nats
    (successorDescription.compiledChildIndex (.pair .zero .star) .star)
    (successorDescription.compiledChildIndex (.pair .zero .star) .star) := by
  have hl : Ctx.nil.JEqB 2 (ContextClosure basis) successorDescription.totalShape
      (.pair .zero .star) (.pair .zero .star) := by
    simpa only [successorDescription, Description.totalShape] using pair_instantiated
  have hdirect : Ctx.nil.JEqB 2 (ContextClosure basis)
      (successorDescription.positions.lst (.pair .zero .star)) .star .star := by
    simpa only [successorDescription, Description.positions, Tm.bsubst, Tm.lst] using
      (Ctx.JEqB.nil_ok (levels := 2) (H := ContextClosure basis))
  have hp : Ctx.nil.JEqB 2 (ContextClosure basis)
      (successorDescription.compiledPositions.lst (.pair .zero .star)) .star .star :=
    .conv (n := 0) (by decide)
      (compiledPositions_beta_of_hypotheses basis_structural successorSourceData.toFormationData hl).symm hdirect
  exact compiledChildIndex_typing_of_hypotheses basis_structural successorSourceData hl hp

/-- Compiled and direct raw W carriers are object-equal in the same nonempty theory. -/
theorem successor_raw_beta : Ctx.nil.JEqB 2 (ContextClosure basis) (.univ 0)
    successorDescription.compiledRaw successorDescription.raw :=
  compiledRaw_beta_of_hypotheses basis_structural successorSourceData.toFormationData

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.HypotheticalExamples
