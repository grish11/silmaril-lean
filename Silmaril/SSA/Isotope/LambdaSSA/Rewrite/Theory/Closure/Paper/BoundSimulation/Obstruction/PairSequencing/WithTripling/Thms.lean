module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.ComputedCall.Example.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.TriplingComputedCallSeparation

/-! # The native separation in unchanged WithTripling -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.ComputedCallExample

open Paper.WithComputedCallReturns.Example (Atom Op nested_typed sequenced_typed)
open CfgEta.TypeCategory (returnRegion_typed)
open Paper.Extension.Singleton (ofRegion)

/-- The observer preserves the native relation and every WithTripling seed,
including both feedback folds. It distinguishes the original retained arrows. -/
theorem retained_ne : sourceArrow ≠ explicitArrow :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingComputedCallSeparation.retained_ne

/-- Equality of the two typed root returns would transport through the
retaining continuation. -/
theorem root_ne :
    ofRegion Seed (returnRegion_typed nested_typed) ≠
      ofRegion Seed (returnRegion_typed sequenced_typed) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingComputedCallSeparation.root_ne

/-- The exact returned-call equation fails before the retaining continuation
as well, since native equality would transport through that continuation. -/
theorem computedCallAgreement_fails :
    ¬ ComputedCallAgreement (τ := Ty Atom) (Φ := Op) false :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingComputedCallSeparation.computedCallAgreement_fails

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.ComputedCallExample
