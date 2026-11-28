module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Split.DeadProducer.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Deletion.Thms

/-! # Typed erasure preserves the whole outgoing packet -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Split.DeadProducer

open SeaOfNodes.Diamond (Model Ty ValueSort dataPorts)
open SeaOfNodes.GVN.Cyclic.Deletion (erase_sound)
open RVSDG (Wires extend)
open Join (Block)
open Blocks (Bank)
open Blocks.Prune (Mask)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {body : Block Op regs} {mask : Mask regs}
variable {outputs : List (Ty Data)} {wires : Wires (dataPorts regs) (extend [] body.producers) outputs}
variable {transfer : Transfer body mask wires} (cut : Checked transfer)

theorem Checked.eval_agrees (m : Model.{u, v, w} Op) (input : Bank (regs := mask.kept) m) :
    cut.eval m input = transfer.eval m input :=
  (SeaOfNodes.GVN.Cyclic.Deletion.Route.wires_read m input
    (erase_sound cut.candidate m input PUnit.unit cut.erased_eq) _ cut.outgoing_eq).symm

theorem Checked.shorter : cut.erased.sigs'.length + 1 = body.producers.length :=
  cut.erased.shorter

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Split.DeadProducer
