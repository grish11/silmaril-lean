module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.DeleteExit.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneInfeasibleExit.Example.Defs

/-! Run cleanup on the same mixed-width loop in both pruning directions. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.DeleteExit.Example

open PruneExit.Example.Bank (i8)
open PruneInfeasibleExit.Example (facts graph input)
open SeaOfNodes.MLIR (Word)
open Semantics.Dataflow (Flat)

/-- Report whether the exit block was deleted, and the budgeted word result. -/
def run (flagFact : Flat (Word i8)) (fuel : Nat) (flag : Word i8) : Option (Bool × Option Nat) :=
  (rewrite graph (facts flagFact)).map fun output =>
    let deleted := match output with
      | .kept _ => false
      | .deleted _ => true
    (deleted, (output.run fuel (input flag)).map (fun result => (result.get .here).toNat))

def refusesVarying : Bool :=
  (rewrite PruneExit.Example.Bank.graph PruneExit.Example.Bank.varyingFacts).isNone

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.DeleteExit.Example
