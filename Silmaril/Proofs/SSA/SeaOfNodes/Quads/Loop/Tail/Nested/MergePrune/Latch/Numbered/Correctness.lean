module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Numbered.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.Proofs

open SeaOfNodes.Diamond (Model Val ValueSort)
open RVSDG (Tuple)
open Diamond.Prune (HeaderProjection)
open MergePrune.Numbered (latchPacket)
open Blocks (Bank)
open Blocks.Prune (Mask)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {carry merge : Mask regs}
variable (p : Program src entry) (m : Model.{u, v, w} Op)
variable (projected : HeaderProjection (src p.header).body carry) (checked : Checked p carry merge)

theorem activation_run (fuel : Nat) (old : Bank (regs := regs) m) :
    (thetaBody p projected checked).run (Join.model m) fuel (carry.project old) =
      some (latchPacket p carry m (Nested.Numbered.nextBank p m old)) := by
  apply MergePrune.Numbered.activation_run_for p m projected _ fuel old
  intro left right same
  let toTheta : Tuple (Val m.value) (packetPorts out carry) → _ :=
    fun | .cons test (.cons _ feedback) => RVSDG.Theta.bodyResult (Join.model m) test.down feedback
  exact congrArg toTheta (Checked.observes_eq m checked left right same)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.Proofs
