module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Split.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Split.Correctness

/-! # The separate block transfers realize the shared latch certificate -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Split

open SeaOfNodes.Diamond (Model ValueSort)
open Blocks (Bank)
open Blocks.Prune (Mask)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {carry merge atLatch : Mask regs}
variable {p : Program src entry} (checked : Checked p carry merge atLatch) (m : Model.{u, v, w} Op)

/-- The merge supplies exactly the latch's needed values in slot order. -/
theorem Checked.merge_agrees (old : Bank (regs := regs) m) :
    checked.mergeTransfer.eval m (merge.project old) = atLatch.project ((src p.join).body.eval m old) :=
  Proofs.merge_agrees p m checked old

/-- The latch returns the resolved guard, exit word and projected feedback
from the same final bank. -/
theorem Checked.latch_agrees (old : Bank (regs := regs) m) :
    checked.latchTransfer.eval m (atLatch.project old) = observe p carry ((src p.latch).body.eval m old) :=
  Proofs.latch_agrees p m checked old

/-- The checked cut composes to the original certificate for each incoming
column, without constructing a whole bank between the two blocks. -/
theorem Checked.split_agrees (old : Bank (regs := regs) m) (occurrence : Occurrence) :
    checked.latchTransfer.eval m (checked.mergeTransfer.eval m (incoming p merge m old occurrence)) =
      checked.whole.eval m (incoming p merge m old occurrence) :=
  Proofs.split_agrees p m checked (p.mergeBank m old occurrence)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Split
