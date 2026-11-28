module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Defs

/-! Emit the original two-route quad table with both feedback labels. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.MLIR.CF

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op)
open Silmaril.MLIR.Arith (Width)

abbrev Target (regs : List (ValueSort Width)) (result : Width) :=
  Tail.Diamond.MLIR.CF.Target regs (.data result) 5

/-- Keep the original header, dispatch and both feedback blocks. -/
def lower {regs : List (ValueSort Width)} {result : Width}
    (p : Program Op regs (.data result)) : Target regs result :=
  Tail.Diamond.MLIR.CF.lowerSource p.source 0

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.MLIR.CF
