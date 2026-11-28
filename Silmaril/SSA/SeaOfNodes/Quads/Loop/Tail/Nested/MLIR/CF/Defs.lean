module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Defs

/-! # Reuse projected CF emission for the checked nested quad loop -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MLIR.CF

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op)
open Silmaril.MLIR.Arith (Width)
open Blocks.Prune (Mask)
open Diamond.Prune (HeaderProjection carriedMaskFor checkHeader)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}

def carriedMask (p : Program src entry) : Mask regs :=
  carriedMaskFor (src p.header).body p.result

def prune (p : Program src entry) : Option (HeaderProjection (src p.header).body (carriedMask p)) :=
  checkHeader (src p.header).body (carriedMask p)

/-- Keep both split sites and all original merge and feedback edges.
Only the header arguments are projected. -/
def lower (p : Program src entry) {mask : Mask regs} (projected : HeaderProjection (src p.header).body mask) :
    Diamond.MLIR.CF.Pruned.Target p.header mask out :=
  Diamond.MLIR.CF.Pruned.lowerSourceWith src entry p.header projected (Diamond.MLIR.CF.entryNames regs)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MLIR.CF
