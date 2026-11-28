module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Example.Defs

/-! # Replay the original outer-reconvergence table in typed CF -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Example

open Diamond.MLIR.CF.Example (input)
open Outer.Numbered.Example (headerStates plan)
open SeaOfNodes.Loop.MLIR.CF (model evalOp)
open SeaOfNodes.MLIR.Lowering (encodeValues)

def runCF (fuel : Nat) : Option Nat :=
  ((lower plan).run evalOp fuel (encodeValues input)).map fun output => (output.get .here).toNat

/-- Record original predecessor, outgoing slot, emitted destination, and
the result register read from the actual successor arguments. -/
def arrivals : List (Option (Nat × Nat × Nat × Nat)) :=
  headerStates.map fun old =>
    let occurrence := plan.toControl.selected model old
    let edge := plan.outerEdgeOccurrence (occurrence != .outerFalse)
    match outerArrival plan input old with
    | .inl ⟨.site id, args⟩ => some (edge.1.val, edge.2.val, id.val, (args.get (.there (.there .here))).toNat)
    | _ => none

/-- Feedback reports the actual label, counter and result arguments.
The explicit exit label reports just the returned word. -/
def successors : List (Option ((Nat × Nat × Nat) ⊕ Nat)) :=
  headerStates.map fun old =>
    match latchSuccessor plan input old with
    | .inl ⟨.site id, args⟩ => some (.inl (id.val, (args.get .here).toNat, (args.get (.there (.there .here))).toNat))
    | .inl ⟨.exit, args⟩ => some (.inr (args.get .here).toNat)
    | .inr _ => none

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Example
