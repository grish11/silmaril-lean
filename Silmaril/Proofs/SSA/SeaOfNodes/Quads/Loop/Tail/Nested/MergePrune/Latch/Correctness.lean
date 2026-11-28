module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Defs
import Silmaril.SSA.SeaOfNodes.Quads.CFG.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Proofs

open SeaOfNodes.Diamond (Model Ty Val ValueSort dataPorts)
open RVSDG (Locals Tuple Wires)
open Join (Block)
open Blocks (Bank)
open Blocks.Prune (Mask)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {carry merge : Mask regs}
variable (p : Program src entry) (m : Model.{u, v, w} Op)

private theorem observe_read {args : List (Ty Data)} {past : List (List (Ty Data))}
    (bank : Wires args past (dataPorts regs)) (input : Tuple (Val m.value) args)
    (locals : Locals (Val m.value) past) :
    Wires.read (observe p carry bank) input locals = observe p carry (bank.read input locals) := by
  change Tuple.cons (SeaOfNodes.Diamond.read m (bank.get p.again) input locals)
    (.cons (SeaOfNodes.Diamond.read m (bank.get p.result) input locals)
      (Wires.read (carry.project bank) input locals)) = _
  rw [← read_get, ← read_get, carry.project_read m]
  rfl

theorem eval_agrees (checked : Checked p carry merge) (old : Bank (regs := regs) m) :
    checked.eval m (merge.project old) = observe p carry ((Nested.Numbered.tail p).eval m old) := by
  unfold Checked.eval
  rw [merge.projected_flow m old (past := []) PUnit.unit _ _ checked.flow_eq,
    merge.projected_wires m old _ _ _ checked.packet_eq]
  have bank := (CFG.compileBlock_read (past := []) (Nested.Numbered.tail p) m old PUnit.unit (initial regs)).trans
    (congrArg (Block.eval (Nested.Numbered.tail p) m) (read_initial m old))
  exact (observe_read p m (transfer p).outgoing old _).trans (congrArg (observe p carry) bank)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Proofs
