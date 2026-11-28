module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Defs

/-! # The identity projection in the compact packet's own scope -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact

open Silmaril.MLIR.Arith (Width)

def Projection.keepAll : (widths : List Width) → Projection widths
  | [] => .nil
  | _ :: tail => .keep (keepAll tail)

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact
