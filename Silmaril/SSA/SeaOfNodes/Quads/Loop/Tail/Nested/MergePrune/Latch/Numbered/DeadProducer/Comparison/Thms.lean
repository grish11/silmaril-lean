module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.DeadProducer.Thms
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.DeadProducer.Thms

/-! # Compare the actual emitters using the same shortened latch -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.DeadProducer.Comparison

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR.Lowering (encodeValues valueWidth)
open Silmaril.MLIR.Arith (Width Env)
open Diamond.Prune (HeaderProjection)
open Nested.Numbered (KeptResult sourceVisits)
open Blocks (Bank)
open Blocks.Prune (Mask)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {carry merge atLatch : Mask regs}
variable (p : Program src entry) (projected : HeaderProjection (src p.header).body carry)
variable (checked : Split.Checked p carry merge atLatch)
variable (cut : Split.DeadProducer.Checked checked.latchTransfer)
variable (result : KeptResult p (mask := carry)) (input : Bank (regs := regs) model)

/-- CF counts the chosen source visits plus its return block, while the
numbered program counts θ activations. -/
theorem cf_at_activations (activations : Nat) :
    (MLIR.CF.DeadProducer.lower p projected checked cut).run evalOp
        (sourceVisits p model activations input + 1) (encodeValues input) =
      ((lower p projected checked cut result).run (Join.model model) activations input).map
        (encodeValues (ins := [out])) := by
  simpa only [run_agrees] using
    MLIR.CF.DeadProducer.cf_at_activations p projected checked cut input result activations

theorem cf_returns_iff (output : Env [valueWidth out]) :
    (∃ visits, (MLIR.CF.DeadProducer.lower p projected checked cut).run evalOp visits (encodeValues input) =
      some output) ↔ ∃ activations,
      ((lower p projected checked cut result).run (Join.model model) activations input).map
        (encodeValues (ins := [out])) = some output := by
  simpa only [run_agrees] using MLIR.CF.DeadProducer.numbered_returns_iff p projected checked cut input result output

theorem cf_noFiniteReturn_iff :
    (MLIR.CF.DeadProducer.lower p projected checked cut).Diverges evalOp (encodeValues input) ↔
      ∀ activations, (lower p projected checked cut result).run (Join.model model) activations input = none := by
  simpa only [run_agrees] using MLIR.CF.DeadProducer.numbered_diverges_iff p projected checked cut input result

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.DeadProducer.Comparison
