module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.Defs

/-! # Exact typed sequencing in the extended quotient -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls

open CategoryTheory
open CfgEta.TypeCategory (returnRegion)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- Both quotient maps act on the same guarded representatives. -/
theorem projection_comp_fromWithTripling :
    Paper.Extension.Singleton.projection (WithTripling.Step (τ := τ) (Φ := Φ) pe) ⋙ fromWithTripling pe =
      Paper.Extension.Singleton.projection (Step pe) :=
  CategoryTheory.Quotient.lift_spec _ _ _

/-- The existing root sequences an arbitrary exactly typed operand at one exit. -/
theorem computedCall {Γ : VCtx τ} {a : Tm Φ} (p : Φ) (ha : Tm.HasType Γ a (instrSrc p)) :
    Eqv pe Γ (returnRegion (.op p a)) (returnRegion (.let₁ a (.op p (.var 0)))) [instrTrg p] :=
  let root := Paper.WithComputedCallReturns.Step.seq p ha
  .extra root.valueBranches.1.hasType root.valueBranches.2.hasType (.inr root)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls
