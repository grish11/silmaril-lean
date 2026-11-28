module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.MLIR.CF.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Numbered.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Worklist.Defs

/-! Compile the fixed pure two-route profile at every SCCP marking. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Tuple)

variable {regs : List (ValueSort Width)} {result : Width}

structure OriginalTargets (p : Program Op regs (.data result)) where
  cf : TwoBackedges.MLIR.CF.Target regs result
  numbered : TwoBackedges.Numbered.Target p

def emitOriginal (p : Program Op regs (.data result)) : OriginalTargets p :=
  ⟨TwoBackedges.MLIR.CF.lower p, TwoBackedges.Numbered.lower p⟩

inductive Outcome (p : Program Op regs (.data result)) where
  | specialized (targets : Backends.Targets p)
  | twoLive (targets : OriginalTargets p)
  | neitherMarked (targets : OriginalTargets p)

/-- Run SCCP once. A singleton uses the existing specialized emitters.
Both other markings retain the original dispatch and report their own outcome. -/
def compile [BankDecidableEq Word (dataPorts regs)]
    (p : Program Op regs (.data result)) (facts : Tuple (Fact Word) (dataPorts regs)) : Outcome p :=
  match Worklist.admit model p facts with
  | .ok checked => .specialized (Backends.emit checked)
  | .error .bothMarked => .twoLive (emitOriginal p)
  | .error .neitherMarked => .neitherMarked (emitOriginal p)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total
