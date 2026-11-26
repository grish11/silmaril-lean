module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Defs

/-! # Emit the checked reconvergence as typed full-bank CF -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op)
open Silmaril.MLIR.Arith (Width)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}

/-- Reuse the original table emitter. Both prefix edges supply the same
typed parameter list at the one shared label, using their own version maps. -/
def lower (_p : Program src entry) : Diamond.MLIR.CF.Target regs out size :=
  Diamond.MLIR.CF.lowerSource src entry

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF
