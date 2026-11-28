module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Defs

/-! # Check a supplied ordered projection against the discovered exit slice -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Block)
open Loop.MLIR.CF (TargetOp)

variable {Input bank full results : List Width}

/-- Rewrite the executable backward-demand slice with a supplied typed
projection. Extra slots are allowed. The full compactor additionally
checks that every forwarded argument is used. -/
def Projection.rewriteScanned? (p : Projection full)
    (code : Block TargetOp (ExitLabel bank full) (full ++ Input) results) :
    Option (Block TargetOp (ExitLabel bank p.types) (p.types ++ Input) results) := do
  let scan ← scanExit? code
  rewriteExit? scan.mask p.rename code

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact
