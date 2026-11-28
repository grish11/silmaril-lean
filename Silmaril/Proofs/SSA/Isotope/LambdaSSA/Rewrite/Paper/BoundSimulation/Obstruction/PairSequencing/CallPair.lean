module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.PairSequencing.CallPair.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.CaseReturns
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.ConstructorSoundness

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction.PairSequencing.RawBranch (Op)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction.PairSequencing.CallPair
  (U Packet paired sequenced)
open _root_.Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer
  (TermObservation SameWith extension_same unary_fusion_same constructorStep_same_of_guard
    evalReturnRegion evalTermWith selectsPair)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer (EnvTy Result)
open scoped Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer.CanonicalUnit

local notation "S" => Paper.WithComputedCallReturns.ConstructorJoin.Seed (τ := Ty Empty) (Φ := Op) false

/-- Keep call-operand evaluation intact and mark a pair whose left is an
operation and whose right begins with a unary let. -/
private def observation : TermObservation (α := Empty) Op where
  pairLet := true
  pairLetCall := some (fun _ => true)
  evaluateCallOperand := true
  callResult _ := some .unit
  callResult_typed _ _ _ h := Option.some.inj h ▸ .unit

private theorem constructor_not_call {Γ : VCtx (Ty Empty)} {a v : Tm Op} {A : Ty Empty}
    (h : Paper.UnaryReturn.Beta.Constructors.Normalizes Γ a v A) :
    selectsPair observation.pairLetCall a = false := by
  cases h with
  | value h => cases h <;> rfl
  | _ => rfl

private theorem call_same {Γ L : VCtx (Ty Empty)} {r s : Region Op}
    (step : Paper.WithComputedCallReturns.Step Γ r s L) : SameWith observation Γ r s := by
  cases step with
  | @seq a p ha =>
    intro env he
    let inner : Tm.HasType (instrSrc p :: Γ) (.op p (.var 0)) (instrTrg p) := .op (.var rfl)
    rw [evalReturnRegion (.op ha) he, evalReturnRegion (.let₁ ha inner) he]
    simp only [evalTermWith, observation, ↓reduceIte, Silmaril.Isotope.LambdaSSA.Semantics.extend]
    cases evalTermWith observation a env <;> rfl

private theorem step_same {Γ L : VCtx (Ty Empty)} {r s : Region Op}
    (h : S Γ r s L) : SameWith observation Γ r s := by
  rcases h with ((old | constructors) | call)
  · exact old.elim projectionUnitSeed_same
      (fun h => h.elim (unary_fusion_same rfl) (caseReturnSeed_same rfl))
  · exact constructorStep_same_of_guard (fun h _ => by
      rw [constructor_not_call h]
      simp only [Bool.and_false, Bool.false_and]) rfl constructors
  · exact call_same call

theorem call_pair_fails :
    ¬ Paper.WithComputedCallReturns.ConstructorJoin.Eqv false [U] paired sequenced [Packet] := by
  intro h
  have typed : EnvTy [U] (fun _ => .unit) := by
    intro i A hi
    cases i with
    | zero => cases Option.some.inj hi; exact .unit
    | succ i => simp [At] at hi
  have seen := extension_same step_same h (fun _ => .unit) typed
  change Result.fault = .jump 0 (.pair .unit .unit) at seen
  cases seen

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing
