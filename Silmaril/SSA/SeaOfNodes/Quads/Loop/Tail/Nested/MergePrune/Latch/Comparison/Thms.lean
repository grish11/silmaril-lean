module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.Thms
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MLIR.CF.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Comparison.Thms

/-! # Compare the narrower numbered runner with the existing typed CF runner -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Comparison

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op evalOp model)
open SeaOfNodes.MLIR.Lowering (encodeValues valueWidth)
open Silmaril.MLIR.Arith (Env Width)
open Diamond.Prune (HeaderProjection)
open Nested.Numbered (KeptResult sourceVisits)
open Blocks (Bank)
open Blocks.Prune (Mask)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {carry merge : Mask regs}
variable (p : Program src entry) (projected : HeaderProjection (src p.header).body carry)
variable (checked : Checked p carry merge) (result : KeptResult p (mask := carry))
variable (input : Bank (regs := regs) model)

theorem cf_at_activations (fuel : Nat) :
    (Nested.MLIR.CF.lower p projected).run evalOp (sourceVisits p model fuel input + 1) (encodeValues input) =
      ((Numbered.lower p projected checked result).run (Join.model model) fuel input).map
        (encodeValues (ins := [out])) := by
  simpa only [Numbered.run_agrees] using
    Nested.Numbered.Comparison.cf_at_activations p projected result input fuel

/-- The existing CF emitter and the narrower numbered graph have their
own witnesses for the same finite return at this typed input. -/
theorem cf_returns_iff (output : Env [valueWidth out]) :
    (∃ visits, (Nested.MLIR.CF.lower p projected).run evalOp visits (encodeValues input) = some output) ↔
      ∃ activations, ((Numbered.lower p projected checked result).run (Join.model model) activations input).map
        (encodeValues (ins := [out])) = some output := by
  simpa only [Numbered.run_agrees] using
    Nested.Numbered.Comparison.cf_returns_iff p projected result input output

theorem cf_diverges_iff :
    (Nested.MLIR.CF.lower p projected).Diverges evalOp (encodeValues input) ↔
      ∀ activations, (Numbered.lower p projected checked result).run (Join.model model) activations input = none := by
  simpa only [Numbered.run_agrees] using
    Nested.Numbered.Comparison.cf_diverges_iff p projected result input

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Comparison
