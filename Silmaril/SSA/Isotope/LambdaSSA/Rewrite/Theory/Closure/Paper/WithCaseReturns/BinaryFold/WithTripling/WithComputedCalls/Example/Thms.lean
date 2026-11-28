module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.Example.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.ComputedCall.Example.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithComputedCalls.Example

/-! # Equality, generation, and effect order of the original retained witness -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.Example

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory
open Paper.WithComputedCallReturns.Example (Op nested_typed)
open Paper.WithComputedCallReturns.Example.ITree (PayloadValue)
open Paper.WithCaseReturns.BinaryFold.WithTripling.ComputedCallExample
  (expected)
open Paper.Extension.Singleton (ofRegion)
open Paper.Extension.Singleton.Generation (Generated)
open CfgEta.TypeCategory (returnRegion_typed)

open Paper.WithCaseReturns.BinaryFold.WithTripling
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

/-- The two written representatives agree by postcomposition of the added root. -/
theorem retained_eq : sourceArrow = explicitArrow :=
  TriplingWithComputedCalls.Example.retained_eq

/-- The projection equates the same arrows separated in WithTripling. -/
theorem projection_identifies_distinct :
    ComputedCallExample.sourceArrow ≠ ComputedCallExample.explicitArrow ∧
      (fromWithTripling false).map ComputedCallExample.sourceArrow =
        (fromWithTripling false).map ComputedCallExample.explicitArrow :=
  TriplingWithComputedCalls.Example.projection_identifies_distinct

/-- A further computed call exercises recursive generation of its operand. -/
theorem further_call_generated :
    Generated Seed (ofRegion Seed (returnRegion_typed (.op (f := Op.produce) nested_typed))) :=
  TriplingWithComputedCalls.Example.further_call_generated

/-- The retained input and reply are generated at the original result type. -/
theorem source_generated : Generated Seed sourceArrow :=
  TriplingWithComputedCalls.Example.source_generated

/-- The original source requests produce and then consume, using the first
reply as the second operand and retaining the original input in the result. -/
theorem source_visible (x : PayloadValue) : (treeInterpretation.map sourceArrow).of x = expected x :=
  TriplingWithComputedCalls.Example.source_visible x

/-- The explicit sequence has the same two requests and retained result. -/
theorem explicit_visible (x : PayloadValue) : (treeInterpretation.map explicitArrow).of x = expected x :=
  retained_eq ▸ source_visible x

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.Example
