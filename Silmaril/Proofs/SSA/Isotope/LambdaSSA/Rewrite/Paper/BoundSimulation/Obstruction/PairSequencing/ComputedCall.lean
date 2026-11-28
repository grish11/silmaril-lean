module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.Example.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.PairReturns

/-! # A typed observation of unary lets inside primitive arguments -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithComputedCallReturns.Example
open CfgEta.TypeCategory (returnRegion)
open _root_.Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer (TermObservation evalReturnRegion pair_join_same)
open scoped Paper.BoundSimulation.Obstruction Observer.CanonicalUnit
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer (EnvTy Result)

private def observation : TermObservation (α := Atom) Op where
  callResult _ := some .unit
  callResult_typed _ _ _ h := Option.some.inj h ▸ .base

private theorem env_typed : EnvTy [Payload] (fun _ => .unit) := by
  intro i A hi
  cases i with
  | zero => cases Option.some.inj hi; exact .base
  | succ i => simp [At] at hi

theorem computed_call_fails (pe : Bool) :
    ¬ Paper.Extension.Eqv (Paper.WithPairReturns.JoinedStep pe) [Payload]
      (returnRegion nested) (returnRegion sequenced) [Payload] := by
  intro h
  have eq := pair_join_same (observation := observation) rfl rfl rfl h (fun _ => .unit) env_typed
  rw [evalReturnRegion nested_typed env_typed, evalReturnRegion sequenced_typed env_typed] at eq
  change Result.fault = .jump 0 .unit at eq
  cases eq

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing
