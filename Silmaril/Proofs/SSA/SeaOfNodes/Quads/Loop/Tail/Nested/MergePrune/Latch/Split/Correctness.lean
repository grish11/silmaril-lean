module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Split.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.Thms
import Silmaril.SSA.SeaOfNodes.Quads.CFG.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Split.Proofs

open SeaOfNodes.Diamond (Model Ty Val ValueSort dataPorts)
open RVSDG (Locals Tuple Wires extend)
open Join (Block)
open Blocks (Bank)
open Blocks.Prune (Mask)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {carry merge atLatch : Mask regs}
variable (p : Program src entry) (m : Model.{u, v, w} Op)

private theorem transfer_eval {body : Block Op regs} {mask : Mask regs} {outputs : List (Ty Data)}
    {wires : Wires (dataPorts regs) (extend [] body.producers) outputs}
    (checked : Transfer body mask wires) (old : Bank (regs := regs) m) :
    checked.eval m (mask.project old) =
      wires.read old ((Diamond.Prune.headerTransferFor body).flow.eval m old PUnit.unit) := by
  unfold Transfer.eval
  rw [mask.projected_flow m old (past := []) PUnit.unit _ _ checked.flow_eq,
    mask.projected_wires m old _ _ _ checked.outgoing_eq]

private theorem block_eval (body : Block Op regs) (old : Bank (regs := regs) m) :
    let compiled := Diamond.Prune.headerTransferFor body
    compiled.outgoing.read old (compiled.flow.eval m old PUnit.unit) = body.eval m old :=
  (CFG.compileBlock_read (past := []) body m old PUnit.unit (initial regs)).trans
    (congrArg (Block.eval body m) (read_initial m old))

theorem merge_agrees (checked : Checked p carry merge atLatch) (old : Bank (regs := regs) m) :
    checked.mergeTransfer.eval m (merge.project old) = atLatch.project ((src p.join).body.eval m old) := by
  rw [transfer_eval m checked.mergeTransfer old]
  unfold mergeWires
  rw [atLatch.project_read m, block_eval]

theorem latch_agrees (checked : Checked p carry merge atLatch) (old : Bank (regs := regs) m) :
    checked.latchTransfer.eval m (atLatch.project old) = observe p carry ((src p.latch).body.eval m old) := by
  rw [transfer_eval m checked.latchTransfer old]
  let built := Diamond.Prune.headerTransferFor (src p.latch).body
  let locals := built.flow.eval m old PUnit.unit
  change Tuple.cons (SeaOfNodes.Diamond.read m (built.outgoing.get p.again) old locals)
    (.cons (SeaOfNodes.Diamond.read m (built.outgoing.get p.result) old locals)
      (Wires.read (carry.project built.outgoing) old locals)) = _
  rw [← read_get, ← read_get, carry.project_read m]
  have agrees : built.outgoing.read old locals = (src p.latch).body.eval m old := block_eval m _ old
  rw [agrees]
  rfl

theorem split_agrees (checked : Checked p carry merge atLatch) (old : Bank (regs := regs) m) :
    checked.latchTransfer.eval m (checked.mergeTransfer.eval m (merge.project old)) =
      checked.whole.eval m (merge.project old) := by
  rw [merge_agrees, latch_agrees, Latch.Checked.eval_agrees]
  unfold Nested.Numbered.tail
  exact congrArg (observe p carry) List.foldl_append.symm

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Split.Proofs
