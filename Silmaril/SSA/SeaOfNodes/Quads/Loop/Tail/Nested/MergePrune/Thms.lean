module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Prune.Thms

/-! # Reconstruct the post-merge bank from any projected occurrence -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune

open SeaOfNodes.Diamond (Model ValueSort)
open Blocks (Bank)
open Blocks.Prune (Mask)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {mask : Mask regs}

theorem incoming_reconstruct (p : Program src entry) (checked : Checked p mask)
    (m : Model.{u, v, w} Op) (old : Bank (regs := regs) m) (occurrence : Occurrence) :
    checked.headerBank m (incoming p mask m old occurrence) =
      (src p.join).body.eval m (p.mergeBank m old occurrence) :=
  checked.header_agrees m (p.mergeBank m old occurrence)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune
