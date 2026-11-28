module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Readback.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Example.Defs

/-! # Validate both real packets in the original 152 fixture -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Readback.Example

open Diamond.MLIR.CF (Widths)
open Diamond.MLIR.CF.Example (input regs)
open SeaOfNodes.Loop.MLIR.CF (model)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Env)
open Outer.Numbered.Example (headerStates plan)
open Phi.Example (directPlan origin rows words)
open Blocks (Bank)

def visits : Bool → Bank (regs := regs) model
  | true => headerStates[0]
  | false => headerStates[2]

def environments : (taken : Bool) → Env (Scope plan taken)
  | true => arrivalEnv (p := plan) input (visits true)
  | false => arrivalEnv (p := plan) input (visits false)

/-- Obtain both expected packets independently from the source reaches. -/
def sourceBanks (taken : Bool) : Env (Widths regs) :=
  encodeValues (plan.outerBank model (visits taken) (if taken then .innerTrue else .outerFalse))

def rebuiltBanks : List ((Nat × Nat) × List Nat) :=
  [true, false].map fun taken => (origin taken, words (pack (readBank rows taken (environments taken))))

/-- Swap two unequal same-width slots within just the true packet. -/
def reordered : Bool → Env (Widths regs)
  | false => sourceBanks false
  | true =>
    let .cons count (.cons selector rest) := sourceBanks true
    .cons selector (.cons count rest)

def checks : Bool × Bool × Bool :=
  (checkBanks rows environments sourceBanks, checkBanks rows environments reordered,
    checkBanks rows environments fun taken => sourceBanks (!taken))

/-- Run the actual numbered outer γ on both reached header states. -/
def gammaMatches : Bool :=
  [true, false].all fun taken =>
    match (Outer.Numbered.outerRegion plan).toGraph.run (Join.model model) 0 (visits taken) with
    | some bank => sameBank (readBank rows taken (environments taken)) (encodeValues bank)
    | none => false

/-- Inspect both raw successors of the actual direct-false CF terminator. -/
def directTargets : List (Option Nat) := ([0, 1] : List (Fin 2)).map fun slot =>
  match successor slot (terminal (predecessor directPlan false)).2 with
  | some ⟨.site id, _⟩ => some id.val
  | _ => none

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Readback.Example
