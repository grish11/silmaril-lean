module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.Defs

/-! # The exact returned-call root equation -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling

open Silmaril Silmaril.Isotope.LambdaSSA
open Paper.WithComputedCallReturns
open Paper.Extension.Singleton (ofRegion)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε]

/-- The existing root rule would sequence a computed primitive operand in
the actual guarded singleton quotient if it could be replayed there. -/
@[expose] def ComputedCallAgreement (pe : ε) : Prop :=
  ∀ {X : τ} {a : Tm Φ} (p : Φ) (ha : Tm.HasType [X] a (instrSrc p)),
    let root := WithComputedCallReturns.Step.seq p ha
    ofRegion (Step pe) root.valueBranches.1 = ofRegion (Step pe) root.valueBranches.2

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling
