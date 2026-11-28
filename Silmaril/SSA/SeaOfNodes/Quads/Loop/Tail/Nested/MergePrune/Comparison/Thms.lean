module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Numbered.Thms
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.MLIR.CF.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Comparison.Thms

/-! # Compare finite observations after projecting the common merge -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Comparison

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
variable (checked : Checked p merge) (result : KeptResult p (mask := carry))
variable (input : Bank (regs := regs) model)

/-- Both emitted targets see the same bounded observation at the selected
source visit count plus the CF return visit. -/
theorem cf_at_activations (fuel : Nat) :
    (MLIR.CF.lower p projected checked).run evalOp (sourceVisits p model fuel input + 1) (encodeValues input) =
      ((Numbered.lower p projected checked result).run (Join.model model) fuel input).map
        (encodeValues (ins := [out])) := by
  rw [MLIR.CF.run_agrees, Numbered.run_agrees]
  exact Nested.Numbered.Comparison.cf_at_activations p projected result input fuel

/-- Each graph has its own budget witness for the same encoded finite return. -/
theorem cf_returns_iff (output : Env [valueWidth out]) :
    (∃ visits, (MLIR.CF.lower p projected checked).run evalOp visits (encodeValues input) = some output) ↔
      ∃ activations, ((Numbered.lower p projected checked result).run (Join.model model) activations input).map
        (encodeValues (ins := [out])) = some output := by
  simpa only [MLIR.CF.run_agrees, Numbered.run_agrees] using
    Nested.Numbered.Comparison.cf_returns_iff p projected result input output

theorem cf_diverges_iff :
    (MLIR.CF.lower p projected checked).Diverges evalOp (encodeValues input) ↔
      ∀ activations, (Numbered.lower p projected checked result).run (Join.model model) activations input = none := by
  simpa only [Silmaril.MLIR.CF.Cfg.Diverges, MLIR.CF.run_agrees, Numbered.run_agrees] using
    Nested.Numbered.Comparison.cf_diverges_iff p projected result input

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Comparison
