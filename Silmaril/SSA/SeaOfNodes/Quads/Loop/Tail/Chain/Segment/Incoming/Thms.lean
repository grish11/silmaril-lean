module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Segment.Incoming.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Segment.Incoming.Correctness

/-! # The typed final jump packet of a checked segment -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain

open Diamond (ValueSort Signature Model)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {target site : Fin size}
variable (path : Segment src target site) (m : Model.{u, v, w} Op)

/-- The actual last edge transfers the complete final bank of a checked
segment. Only a direct arrival needs a fact about the caller's branch. -/
theorem Segment.final_edge (caller : Fin size) (beforeCaller current : Bank (regs := regs) m)
    (direct : path.blocks = [] →
      (src caller).terminator.select m ((src caller).body.eval m beforeCaller) = .jump site ∧
      (src caller).body.eval m beforeCaller = current) :
    let pred := path.predecessor caller
    let bank := (src pred).body.eval m (path.predecessorBank m beforeCaller current)
    (src pred).terminator.select m bank = .jump target ∧ bank = path.quads.eval m current :=
  Segment.Proofs.final_edge path m caller beforeCaller current direct

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain
