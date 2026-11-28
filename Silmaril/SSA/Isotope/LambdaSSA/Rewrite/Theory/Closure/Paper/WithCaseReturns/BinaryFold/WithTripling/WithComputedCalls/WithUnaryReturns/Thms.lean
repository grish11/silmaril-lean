module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Thms

/-! # Exact lifting of a unary producer into a single bind -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns

open CategoryTheory
open CfgEta.TypeCategory (returnRegion returnRegion_typed)
open Paper.RetainedLet (returnOnce returnOnce_typed)
open Paper.Extension.Singleton (ofRegion ofRegion_eq_iff)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

theorem projection_comp_fromWithComputedCalls :
    Paper.Extension.Singleton.projection (WithComputedCalls.Step (τ := τ) (Φ := Φ) pe) ⋙
      fromWithComputedCalls pe = Paper.Extension.Singleton.projection (Step pe) :=
  CategoryTheory.Quotient.lift_spec _ _ _

/-- Only the unary-let clause of lowering needs a rewrite. The existing
forwarding rule closes that clause under exact guarded label substitution. -/
theorem lowering {Γ : VCtx τ} {D : τ} {a : Tm Φ} (ha : Tm.HasType Γ a D) :
    Eqv pe Γ (returnRegion a) (returnOnce a) [D] :=
  Paper.UnaryReturn.returnRegion_eq_returnOnce Or.inr ha

/-- A returned term always agrees with the producer used by a literal bind. -/
theorem onceReturnAgreement {X D : τ} {a : Tm Φ} (ha : Tm.HasType [X] a D) :
    ofRegion (Step pe) (returnRegion_typed ha) = ofRegion (Step pe) (returnOnce_typed ha) :=
  (ofRegion_eq_iff (Step pe) _ _).2 (lowering pe ha)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns
