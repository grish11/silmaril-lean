module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.Example.Defs

/-! Inspect and run the actual four-block source. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Example

open SCCP.Example (model program facts concrete)
open Dispatch.Example (looping)
open Semantics.Dataflow (Flat)

/-- Original block indices in compact order, followed by the new dispatcher target. -/
def layout (side : Flat (ULift Bool)) : Option (List Nat × Option Nat) :=
  (check model program (facts side)).map fun checked =>
    let original := (List.finRange 4).map fun i => (keptBlock checked.side i).val
    let target := match ((compact checked) 2).terminator with
      | .transfer (.jump index) => some index.val
      | _ => none
    (original, target)

/-- The outer option reports admission. The inner option is the native result. -/
def compactReturn (side : Bool) (fuel : Nat) : Option (Option Nat) :=
  (rewrite model program (facts (.constant ⟨side⟩))).map fun clean =>
    (clean.runFrom model fuel 0 (concrete side)).map BitVec.toNat

def compactLoop (fuel : Nat) : Option (Option Nat) :=
  (rewrite model looping (facts (.constant ⟨false⟩))).map fun clean =>
    (clean.runFrom model fuel 0 (concrete false)).map BitVec.toNat

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Example
