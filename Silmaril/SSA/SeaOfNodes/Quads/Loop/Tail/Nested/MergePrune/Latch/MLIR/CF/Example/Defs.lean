module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Example.Defs

/-! # Execute the narrowed original CF blocks on the overwritten-decrement fixture -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.Example

open Latch.Example (plan projected checked carry mask source probeBank)
open Diamond.MLIR.CF.Example (input num regs)
open SeaOfNodes.Loop.MLIR.CF (evalOp model)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Blocks (Bank)
open Silmaril.MLIR.CF (Frame)

abbrev atLatch := Split.latchMask plan carry

def cut : Split.Checked plan carry mask atLatch := (Split.prepare plan checked).get (by rfl)

def runCF (fuel : Nat) : Option Nat :=
  ((lower plan projected cut).run evalOp fuel (encodeValues input)).map (fun env => (env.get .here).toNat)

def runSite (frame : Frame (Label plan.header plan.join plan.latch carry mask atLatch num)) :=
  ((lower plan projected cut).block frame.label).eval evalOp (fun term env => term.eval env)
    (frame.args.append (encodeValues input))

/-- Select the source occurrence and execute that actual CF predecessor. -/
def runPredecessor (old : Bank (regs := regs) model) :=
  let occ := plan.selected model old
  runSite (siteFrame plan (plan.predecessor occ) (predecessorBank plan old occ))

/-- Observe the arity sent by each actual incoming edge to the merge. -/
def incomingArities : List (Option Nat) :=
  [probeBank 3, probeBank 2, probeBank 1].map fun old =>
    match runPredecessor old with
    | .inl frame => some frame.argsTy.length
    | .inr _ => none

def latchArity : Option Nat :=
  match runPredecessor (probeBank 2) with
  | .inl frame =>
    match runSite frame with
    | .inl next => some next.argsTy.length
    | .inr _ => none
  | .inr _ => none

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.Example
