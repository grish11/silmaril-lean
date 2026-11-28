module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.ComputedCall.Example.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.TriplingComputedCallFeedback

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingComputedCallSeparation

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory
open Paper.WithCaseReturns.BinaryFold.WithTripling (ComputedCallAgreement Eqv)
open Paper.WithCaseReturns.BinaryFold.WithTripling.ComputedCallExample
open Paper.WithComputedCallReturns.Example (Atom Op Payload nested sequenced operand_typed
  nested_typed sequenced_typed)
open Paper.Extension.Singleton (ofRegion ofRegion_eq_iff)
open BoundSimulation.Obstruction.Observer (Env EnvTy)
open BoundSimulation.Obstruction.PairSequencing.Observer (TermObservation evalRegionWith)
open scoped Paper.BoundSimulation.Obstruction BoundSimulation.Obstruction.Observer.CanonicalUnit
open CfgEta.TypeCategory (returnRegion_typed)

private def observation : TermObservation (α := Atom) Op where
  callResult _ := some .unit
  callResult_typed _ _ _ h := Option.some.inj h ▸ .base

private theorem env_typed : EnvTy [Payload] (fun _ => .unit) := by
  intro i A hi
  cases i with
  | zero => cases Option.some.inj hi; exact .base
  | succ i => simp [At] at hi

theorem retained_ne : sourceArrow ≠ explicitArrow := by
  intro equal
  have rewrite : Eqv false [Payload] source explicitSequence [Result] :=
    (ofRegion_eq_iff Seed source_typed explicitSequence_typed).mp equal
  have eq := TriplingComputedCallFeedback.withTripling_same (observation := observation) false rfl
    rewrite (fun _ => .unit) env_typed
  change BoundSimulation.Obstruction.Observer.Result.fault = .jump 0 (.pair .unit .unit) at eq
  cases eq

theorem root_ne :
    ofRegion Seed (returnRegion_typed nested_typed) ≠
      ofRegion Seed (returnRegion_typed sequenced_typed) := by
  intro eq
  have rewrite := (ofRegion_eq_iff Seed (returnRegion_typed nested_typed)
    (returnRegion_typed sequenced_typed)).mp eq
  exact retained_ne ((ofRegion_eq_iff Seed source_typed explicitSequence_typed).mpr
    (.lsubstPost rewrite (returnRegion_typed nested_typed) (returnRegion_typed sequenced_typed)
      (fun _ _ hi => (keepInput_typed hi).hasType)))

theorem computedCallAgreement_fails :
    ¬ ComputedCallAgreement (τ := Ty Atom) (Φ := Op) false := by
  intro agreement
  unfold ComputedCallAgreement at agreement
  exact root_ne (agreement Op.consume operand_typed)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingComputedCallSeparation
