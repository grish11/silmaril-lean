module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MLIR.CF.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Comparison.Correctness

/-! # Typed CF and numbered RVSDG observations of the same checked loop -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Comparison

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op evalOp model)
open SeaOfNodes.MLIR.Lowering (encodeValues valueWidth)
open Silmaril.MLIR.Arith (Env Width)
open Diamond.Prune (HeaderProjection)
open Blocks (Bank)
open Blocks.Prune (Mask)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {mask : Mask regs}
variable (p : Program src entry) (projected : HeaderProjection (src p.header).body mask)
variable (result : KeptResult p (mask := mask)) (input : Bank (regs := regs) model)

/-- Count the source visits of the selected native path, then one CF
return visit. This also compares bounded exhaustion at those budgets. -/
theorem cf_at_activations (activations : Nat) :
    (Nested.MLIR.CF.lower p projected).run evalOp (sourceVisits p model activations input + 1) (encodeValues input) =
      ((lower p projected result).run (Join.model model) activations input).map
        (encodeValues (ins := [out])) :=
  Proofs.cf_at_activations p projected result input activations

/-- Each target witnesses the same finite returned environment with a
bound in its own budget. Both start at the same typed boundary bank. -/
theorem cf_returns_iff (output : Env [valueWidth out]) :
    (∃ visits, (Nested.MLIR.CF.lower p projected).run evalOp visits (encodeValues input) = some output) ↔
      ∃ activations, ((lower p projected result).run (Join.model model) activations input).map
        (encodeValues (ins := [out])) = some output :=
  Proofs.cf_returns_iff p projected result input output

/-- The targets agree on absence of returns at all finite budgets. -/
theorem cf_diverges_iff :
    (Nested.MLIR.CF.lower p projected).Diverges evalOp (encodeValues input) ↔
      ∀ activations, (lower p projected result).run (Join.model model) activations input = none :=
  Proofs.cf_diverges_iff p projected result input

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Comparison
