module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.UnaryProducer.Example.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.ComputedReturns

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingUnaryProducer

open Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.UnaryProducer.Example (singleBind_typed singleBindArrow)
open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory
open Paper.WithComputedCallReturns.Example (Op Payload sequenced_typed)
open Paper.WithCaseReturns.BinaryFold.WithTripling.ComputedCallExample (keepInput_typed)
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.Example
  (Seed explicitArrow)
open Paper.Extension.Singleton (ofRegion)
open Paper.RetainedLet (returnOnce_typed)
open CfgEta.TypeCategory (returnRegion_typed)

open Paper.WithComputedCallReturns.Example (Atom)
open Paper.WithCaseReturns.BinaryFold.WithTripling.ComputedCallExample (explicitSequence_typed)
open Paper.Extension.Singleton (ofRegion_eq_iff)
open BoundSimulation.Obstruction.Observer (EnvTy Result)
open scoped Paper.BoundSimulation.Obstruction BoundSimulation.Obstruction.Observer.CanonicalUnit
open BoundSimulation.Obstruction.PairSequencing.Observer
  (TermObservation)
open BoundSimulation.Obstruction.PairSequencing.ComputedReturns (computedExtension_same)

private def observationForProducer : TermObservation (α := Atom) Op where
  boundUnaryLet := true
  evaluateCallOperand := true
  callResult _ := some .unit
  callResult_typed _ _ _ h := Option.some.inj h ▸ .base

private theorem env_typed : EnvTy [Payload] (fun _ => .unit) := by
  intro i A hi
  cases i with
  | zero => cases Option.some.inj hi; exact .base
  | succ i => simp [At] at hi

theorem retained_ne : explicitArrow ≠ singleBindArrow := by
  intro equal
  have rewrite := (ofRegion_eq_iff Seed explicitSequence_typed singleBind_typed).mp equal
  have seen := computedExtension_same false (obs := observationForProducer) rfl rfl rewrite
    (fun _ => .unit) env_typed
  change Result.jump 0 (.pair .unit .unit) = .fault at seen
  cases seen

theorem root_ne :
    ofRegion Seed (returnRegion_typed sequenced_typed) ≠ ofRegion Seed (returnOnce_typed sequenced_typed) := by
  intro equal
  have rewrite := (ofRegion_eq_iff Seed _ _).mp equal
  exact retained_ne ((ofRegion_eq_iff Seed explicitSequence_typed singleBind_typed).2
    (.lsubstPost rewrite (returnRegion_typed sequenced_typed) (returnOnce_typed sequenced_typed)
      (fun _ _ hi => (keepInput_typed hi).hasType)))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingUnaryProducer
