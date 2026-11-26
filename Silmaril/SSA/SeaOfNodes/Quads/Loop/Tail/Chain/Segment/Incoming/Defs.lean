module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Segment.Defs

/-! # Bank at the final predecessor of a checked jump segment -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain

open Diamond (ValueSort Signature Model)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {target site : Fin size}

/-- The bank before the final predecessor executes. A direct arrival
uses the input of its caller. -/
def Segment.predecessorBank (m : Model.{u, v, w} Op) :
    {site : Fin size} → Segment src target site →
      Bank (regs := regs) m → Bank (regs := regs) m → Bank (regs := regs) m
  | _, .empty, beforeCaller, _ => beforeCaller
  | _, .jump site _ rest, _, current =>
    rest.predecessorBank m current ((src site).body.eval m current)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain
