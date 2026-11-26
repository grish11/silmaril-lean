module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProductDestructureReturns.Example.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.CfgEta
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Generation.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.CaseReturns
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.ConstructorSoundness

/-! # An observation that marks a unary let under term product destructuring -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.RetainedLet (unpackBody unpackTerm unpackTerm_typed)
open Paper.WithProductDestructureReturns.Example
open Paper.WithPairReturns (ReturnFragmentWithCalls)
open CfgEta.TypeCategory (returnRegion)
open _root_.Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer
  (TermObservation SameWith extension_same unary_fusion_same evalReturnRegion sequence_pair evalTermWith)
open scoped Paper.BoundSimulation.Obstruction Observer.CanonicalUnit
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer (EnvTy Result)

universe u v w

variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)]

private def observation : TermObservation (α := α) Φ := { binaryLetBody := true }

private theorem computedStep_same {Γ L : List (Ty α)} {r s : Region Φ}
    (step : Paper.WithComputedCallReturns.Step Γ r s L) : SameWith observation Γ r s := by
  cases step with
  | @seq a p ha =>
    intro env he
    let inner : Tm.HasType (instrSrc p :: Γ) (.op p (.var 0)) (instrTrg p) := .op (.var rfl)
    rw [evalReturnRegion (.op ha) he, evalReturnRegion (.let₁ ha inner) he]
    simp only [evalTermWith]
    cases evalTermWith (observation (α := α)) a env <;> rfl

variable {ε : Type w} [HasEff Φ ε]

theorem computedCallSeed_same {obs : TermObservation (α := α) Φ}
    (caseUnmarked : obs.caseTerm = false) (pairUnmarked : obs.pairLet = false)
    (callSame : ∀ {Γ L r s}, Paper.WithComputedCallReturns.Step Γ r s L → SameWith obs Γ r s)
    {pe : ε} {Γ L : List (Ty α)} {r s : Region Φ}
    (step : Paper.WithComputedCallReturns.JoinedStep pe Γ r s L) : SameWith obs Γ r s := by
  rcases step with (((base | returned) | pair) | call)
  · exact projectionUnitSeed_same base
  · exact returned.elim unary_fusion_same (caseReturnSeed_same caseUnmarked)
  · cases pair with
    | seq ha hb => exact fun env _ => sequence_pair pairUnmarked _ _ env
  · exact callSame call

private theorem env_typed : EnvTy [product (U α) (U α)] (fun _ => .pair .unit .unit) := by
  intro i A hi
  cases i with
  | zero => cases Option.some.inj hi; exact .pair .unit .unit
  | succ i => simp [At] at hi

theorem product_destructure_return_fails (pe : ε) :
    ¬ Paper.Extension.Eqv (Paper.WithComputedCallReturns.JoinedStep pe) [product (U α) (U α)]
      (unpackBody (returnRegion (body : Tm Φ))) (returnRegion (unpackTerm body)) [product (U α) (U α)] := by
  intro h
  have same := extension_same (computedCallSeed_same rfl rfl (fun step => computedStep_same step)) h
  have seen := same (fun _ => .pair .unit .unit) env_typed
  rw [evalReturnRegion (unpackTerm_typed body_typed) env_typed] at seen
  change Result.jump 0 (.pair .unit .unit) = .fault at seen
  cases seen

private def marksDestructuring : Tm Φ → Bool
  | .let₂ _ (.let₁ _ _) => true
  | _ => false

private theorem previousRoot
    {pe : ε} {A D : Ty α} {t : Tm Φ} {ht : Tm.HasType [A] t D}
    (h : ReturnFragmentWithCalls pe true ht) : marksDestructuring t = false := by
  cases h with
  | destructure enables _ => cases enables
  | value ht => cases ht <;> rfl
  | _ => rfl

theorem witness_outside_previous_fragment (pe : ε) :
    ¬ ReturnFragmentWithCalls pe true (unpackTerm_typed (body_typed (α := α) (Φ := Φ))) := by
  intro h
  have bound := previousRoot h
  change true = false at bound
  cases bound

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing
