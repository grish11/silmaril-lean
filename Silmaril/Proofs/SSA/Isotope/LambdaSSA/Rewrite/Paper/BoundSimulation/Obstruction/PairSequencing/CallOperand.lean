module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.PairSequencing.CallOperand.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.CaseReturns
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.ConstructorSoundness

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction.PairSequencing.RawBranch (Op)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction.PairSequencing.CallOperand
  (nestedReturn sequencedReturn)
open _root_.Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer
  (TermObservation SameWith extension_same unary_fusion_same constructorStep_same)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer (EnvTy Result)
open scoped Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer.CanonicalUnit

local notation "U" => (Ty.unit : Ty Empty)
local notation "Seed" => Paper.WithConstructorSequencing.Joined.Seed (τ := Ty Empty) (Φ := Op) false

/-- The observer accepts unit-returning primitives, but detects a syntactic
let still nested in the operand. Constructor assembly and case are unmarked. -/
private def callOperandObservation : TermObservation (α := Empty) Op where
  callResult _ := some .unit
  callResult_typed _ _ _ h := Option.some.inj h ▸ .unit

private theorem callOperandStep_same {Γ L : List (Ty Empty)} {r s : Region Op} (h : Seed Γ r s L) :
    SameWith callOperandObservation Γ r s :=
  h.elim
    (fun joined => joined.elim projectionUnitSeed_same
      (fun returns => returns.elim (unary_fusion_same rfl) (caseReturnSeed_same rfl)))
    (constructorStep_same rfl rfl)

theorem callOperand_fails :
    ¬ Paper.WithConstructorSequencing.Joined.Eqv false [U] nestedReturn sequencedReturn [U] := by
  intro h
  have typed : EnvTy [U] (fun _ => .unit) := by
    intro i A hi
    cases i with
    | zero => cases Option.some.inj hi; exact .unit
    | succ i => simp [At] at hi
  have observed := extension_same callOperandStep_same h (fun _ => .unit) typed
  change Result.fault = .jump 0 .unit at observed
  cases observed

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing
