module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Composition.Example.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Comparison.Equation.Example.Defs

/-! # The unequal-arm inequation after two typed entry permutations -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Composition.Equation.Example

open Composition.Example (first second paired sequentialResults)
open Pruned.Equation.Example (projectedVariant)
open SeaOfNodes.Loop.MLIR.CF (model evalOp)
open SeaOfNodes.MLIR.Lowering (encodeValues)

/-- Each pair records the numbered RVSDG and typed CF results at the shared
valuation. The base fixture uses three activations and sixteen CF visits. -/
def results : (Option Nat × Option Nat) × (Option Nat × Option Nat) :=
  (sequentialResults,
    (((graph second (graph first projectedVariant.lower)).run (Join.model model) 3 paired).map
      (fun values => (values.get .head).toNat),
    ((lowerWith projectedVariant (pull first (cfNames second))).run evalOp 16 (encodeValues paired)).map
      (fun env => (env.get .here).toNat)))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Composition.Equation.Example
