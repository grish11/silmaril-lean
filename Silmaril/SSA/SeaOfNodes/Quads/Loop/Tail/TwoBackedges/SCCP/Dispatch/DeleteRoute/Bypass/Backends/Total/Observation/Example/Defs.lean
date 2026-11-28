module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Observation.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Example.Defs

/-! Report the budgets and returned words of a compiled outcome. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Observation.Example

open Bypass.MLIR.CF.Example (regs word)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open Blocks (Bank)

/-- Each tuple lists source, CF, and numbered in that order. -/
def report {p : Program Op regs word} (outcome : Outcome p) (input : Bank (regs := regs) model)
    (limit : Nat) : (Nat × Nat × Nat) × (Option Nat × Option Nat × Option Nat) :=
  let budgets := outcome.budgets limit
  ((budgets.source.blocks, budgets.cf.blocks, budgets.theta.activations),
    (runSource p input budgets.source |>.map BitVec.toNat,
      outcome.runCF input budgets.cf |>.map BitVec.toNat,
      outcome.runNumbered input budgets.theta |>.map BitVec.toNat))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Observation.Example
