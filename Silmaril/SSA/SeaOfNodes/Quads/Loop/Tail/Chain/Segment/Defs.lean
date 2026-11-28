module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Defs

/-! # A checked jump segment ending just before a given block -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain

open Diamond (ValueSort Signature)
open Join (Block)

universe u v

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {target site header : Fin size}

/-- The body of the destination block is outside this segment. -/
inductive Segment (src : Source Op regs out size) (target : Fin size) : Fin size → Type u
  | empty : Segment src target target
  | jump (site : Fin size) {next : Fin size}
      (edge : (src site).terminator = .transfer (.jump next)) (rest : Segment src target next) :
      Segment src target site

def Segment.blocks : {site : Fin size} → Segment src target site → List (Fin size)
  | _, .empty => []
  | _, .jump site _ rest => site :: rest.blocks

/-- An empty segment reaches the target directly from its caller. -/
def Segment.predecessor : {site : Fin size} → Segment src target site → Fin size → Fin size
  | _, .empty, caller => caller
  | _, .jump site _ rest, _ => rest.predecessor site

def Segment.quads : {site : Fin size} → Segment src target site → Block Op regs
  | _, .empty => []
  | _, .jump site _ rest => (src site).body ++ rest.quads

/-- Cut before a named block. The returned prefix omits the block and the
suffix starts there. Both segments keep their original checked jump edges. -/
def Segment.cutAt : {site : Fin size} → Segment src target site → (meet : Fin size) →
      Option (Segment src meet site × Segment src target meet)
  | site, segment, meet =>
    if same : site = meet then some ⟨same.symm ▸ .empty, same ▸ segment⟩
    else match segment with
    | .empty => none
    | .jump site edge rest => (rest.cutAt meet).map fun (before, after) =>
        (.jump site edge before, after)

/-- Cut a checked jump chain before the destination, including a chain already there. -/
def Path.segmentTo (target : Fin size) :
    {site : Fin size} → Path src header site → Option (Segment src target site)
  | site, path =>
    if ends : site = target then some (ends.symm ▸ .empty)
    else
      match path with
      | .latch .. => none
      | .jump site edge rest => (rest.segmentTo target).map (.jump site edge)

/-- Locate the block immediately before the tested latch on a checked path. -/
def Path.beforeLatch : {site : Fin size} → Path src header site → Option (Fin size)
  | _, .latch .. => none
  | _, .jump site _ rest => rest.beforeLatch.or (some site)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain
