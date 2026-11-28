module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.TriplingComputedCallFeedback

/-! # Observation preservation for computed-call and unary forwarding returns -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.ComputedReturns

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls (Step)
open scoped Paper.BoundSimulation.Obstruction BoundSimulation.Obstruction.Observer.CanonicalUnit
open _root_.Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer
  (TermObservation SameWith evalReturnRegion evalTermWith extension_same unary_fusion_same)

universe u v w
variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

private theorem computedCall_same {obs : TermObservation (α := α) Φ}
    (evaluate : obs.evaluateCallOperand = true)
    {Γ L : List (Ty α)} {r s : Region Φ}
    (step : Paper.WithComputedCallReturns.Step Γ r s L) : SameWith obs Γ r s := by
  cases step with
  | @seq a p ha =>
    intro env he
    let call : Tm.HasType (instrSrc p :: Γ) (.op p (.var 0)) (instrTrg p) := .op (.var rfl)
    rw [evalReturnRegion (observation := obs) (.op ha) he, evalReturnRegion (observation := obs) (.let₁ ha call) he]
    simp only [evalTermWith, evaluate, ↓reduceIte]
    cases evalTermWith obs a env <;> rfl

theorem computedExtension_same {obs : TermObservation (α := α) Φ}
    (unmarked : obs.caseTerm = false) (evaluate : obs.evaluateCallOperand = true)
    {Γ L : List (Ty α)} {r s : Region Φ}
    (eq : Paper.Extension.Eqv (Step (τ := Ty α) (Φ := Φ) pe) Γ r s L) :
    SameWith obs Γ r s :=
  extension_same (fun step => step.elim
    (TriplingComputedCallFeedback.withTriplingSeed_same pe unmarked)
    (computedCall_same evaluate)) eq

/-- The current unary quotient preserves the observation when the term-let
scrutinee test is disabled. Primitive arguments are evaluated in order. -/
theorem unaryExtension_same {obs : TermObservation (α := α) Φ}
    (caseUnmarked : obs.caseTerm = false) (evaluate : obs.evaluateCallOperand = true)
    (binderUnmarked : obs.boundUnaryLet = false)
    {Γ L : List (Ty α)} {r s : Region Φ}
    (eq : Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.Eqv pe Γ r s L) :
    SameWith obs Γ r s :=
  extension_same (fun seed => seed.elim
    (fun e => e.elim (TriplingComputedCallFeedback.withTriplingSeed_same pe caseUnmarked) (computedCall_same evaluate))
    (unary_fusion_same binderUnmarked)) eq

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.ComputedReturns
