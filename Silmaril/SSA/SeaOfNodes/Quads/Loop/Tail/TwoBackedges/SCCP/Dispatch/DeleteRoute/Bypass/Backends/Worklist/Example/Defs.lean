module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Worklist.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Example.Defs

/-! Inspect scheduling and run the two artifacts from the worklist admission. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Worklist.Example

open Bypass.MLIR.CF.Example (facts ports regs word)
open Backends.Example (computesSelector)
open SeaOfNodes.Diamond.SCCP (Fact)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Blocks (Bank)
open RVSDG (Tuple)

def runPrefix (pops : Nat) : SCCP.Worklist.Run Word regs word :=
  SCCP.Worklist.runSteps model computesSelector (facts .overdefined) pops ⊥ SCCP.Worklist.initial

def feedbackMarks (run : SCCP.Worklist.Run Word regs word) : Bool × Bool :=
  (decide (incomingIndex (.feedback true) ∈ run.state.1),
    decide (incomingIndex (.feedback false) ∈ run.state.1))

/-- Run the admitted artifacts at their own budgets for a feedback limit. -/
def observations (p : Program Op regs word) (inputFacts : Tuple (Fact Word) ports)
    (input : Bank (regs := regs) model) (limit : Nat) :
    Except Refusal (Bool × Option Nat × Option Nat) := do
  let targets ← compile p inputFacts
  return (targets.retained,
    (targets.cf.run evalOp (2 * limit + 3) (encodeValues input)).map (fun env => (env.get .here).toNat),
    (targets.numbered.run (Join.model model) limit input).map (fun values => (values.get .head).toNat))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Worklist.Example
