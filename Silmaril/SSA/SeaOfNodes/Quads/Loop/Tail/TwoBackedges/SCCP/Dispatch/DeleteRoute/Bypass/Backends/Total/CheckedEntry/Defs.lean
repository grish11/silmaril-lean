module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Coverage.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Observation.Defs

/-! Opt-in concrete entry validation for the two-route CF and numbered backends. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.CheckedEntry

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact TupleCovers)
open SeaOfNodes.Loop.SCCP (BankDecidableEq decideTupleCovers)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Tuple)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {result : Width} {p : Program Op regs (.data result)}
variable [BankDecidableEq Word (dataPorts regs)]

/-- Cache a compiled outcome together with the exact facts it used. -/
structure Prepared (p : Program Op regs (.data result)) where
  facts : Tuple (Fact Word) (dataPorts regs)
  outcome : Outcome p
  compiled : Total.compile p facts = outcome

def prepare (p : Program Op regs (.data result)) (facts : Tuple (Fact Word) (dataPorts regs)) :
    Prepared p :=
  ⟨facts, Total.compile p facts, rfl⟩

inductive Result (p : Program Op regs (.data result)) where
  | reused (outcome : Outcome p)
  | inputIncompatible (targets : OriginalTargets p)

/-- Reuse either analysis fallback immediately. For a specialization, check its
cached facts against this concrete entry and emit the original loop on failure. -/
def dispatch (prepared : Prepared p) (input : Bank (regs := regs) model) : Result p :=
  match prepared.outcome with
  | .specialized targets =>
    letI := decideTupleCovers prepared.facts input
    if TupleCovers prepared.facts input then .reused (.specialized targets)
    else .inputIncompatible (emitOriginal p)
  | .twoLive targets => .reused (.twoLive targets)
  | .neitherMarked targets => .reused (.neitherMarked targets)

def compile (p : Program Op regs (.data result)) (facts : Tuple (Fact Word) (dataPorts regs))
    (input : Bank (regs := regs) model) : Result p :=
  dispatch (prepare p facts) input

def Result.execution : Result p → Execution regs result
  | .reused outcome => outcome.execution
  | .inputIncompatible targets => targets.execution

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.CheckedEntry
