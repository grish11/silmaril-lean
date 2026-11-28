module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.Thms
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Comparison.Thms

/-! # Independent finite-return witnesses across the two smaller emitters -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.Comparison

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op evalOp model)
open SeaOfNodes.MLIR.Lowering (encodeValues valueWidth)
open Silmaril.MLIR.Arith (Env Width)
open Diamond.Prune (HeaderProjection)
open Nested.Numbered (KeptResult sourceVisits)
open Blocks (Bank)
open Blocks.Prune (Mask)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {carry merge atLatch : Mask regs}
variable (p : Program src entry) (projected : HeaderProjection (src p.header).body carry)
variable (checked : Split.Checked p carry merge atLatch) (result : KeptResult p (mask := carry))
variable (input : Bank (regs := regs) model)

theorem cf_at_activations (fuel : Nat) :
    (lower p projected checked).run evalOp (sourceVisits p model fuel input + 1) (encodeValues input) =
      ((Latch.Numbered.lower p projected checked.whole result).run (Join.model model) fuel input).map
        (encodeValues (ins := [out])) := by
  rw [run_agrees]
  exact Latch.Comparison.cf_at_activations p projected checked.whole result input fuel

theorem cf_returns_iff (output : Env [valueWidth out]) :
    (∃ visits, (lower p projected checked).run evalOp visits (encodeValues input) = some output) ↔
      ∃ activations, ((Latch.Numbered.lower p projected checked.whole result).run (Join.model model)
        activations input).map (encodeValues (ins := [out])) = some output := by
  simpa only [run_agrees] using Latch.Comparison.cf_returns_iff p projected checked.whole result input output

theorem cf_diverges_iff :
    (lower p projected checked).Diverges evalOp (encodeValues input) ↔
      ∀ activations, (Latch.Numbered.lower p projected checked.whole result).run (Join.model model)
        activations input = none := by
  simpa only [Silmaril.MLIR.CF.Cfg.Diverges, run_agrees] using
    Latch.Comparison.cf_diverges_iff p projected checked.whole result input

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.Comparison
