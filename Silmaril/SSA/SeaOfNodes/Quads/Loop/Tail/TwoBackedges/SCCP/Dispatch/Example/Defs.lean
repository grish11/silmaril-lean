module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Example.Defs

/-! Run the rewritten source on the typed Boolean/byte loop. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.Example

open SCCP.Example (model program regs word Op facts concrete)
open Semantics.Dataflow (Flat)

/-- Inspect the emitted dispatcher terminator. -/
def jumpTarget (side : Flat (ULift Bool)) : Option Nat :=
  (check model program (facts side)).bind fun checked =>
    match (checked.source 2).terminator with
    | .transfer (.jump target) => some target.val
    | _ => none

/-- The outer option reports admission. The inner option is the native observation. -/
def rewrittenReturn (side : Bool) (fuel : Nat) : Option (Option Nat) :=
  (check model program (facts (.constant ⟨side⟩))).map fun checked =>
    (checked.source.runFrom model fuel 0 (concrete side)).map BitVec.toNat

/-- Keep continuing through the selected feedback block forever. -/
def looping : Program Op regs word := { program with feedback := fun _ => [] }

def loopingReturn (fuel : Nat) : Option (Option Nat) :=
  (check model looping (facts (.constant ⟨false⟩))).map fun checked =>
    (checked.source.runFrom model fuel 0 (concrete false)).map BitVec.toNat

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.Example
