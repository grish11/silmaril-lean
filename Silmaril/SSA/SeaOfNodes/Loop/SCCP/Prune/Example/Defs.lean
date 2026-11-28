module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Prune.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneInfeasibleExit.Example.Defs

/-! Try both pruning directions on the same mixed-width carried bank. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Prune.Example

open PruneInfeasibleExit.Example (facts graph input)
open PruneExit.Example.Bank (i8)
open SeaOfNodes.MLIR (Word)
open Loop.MLIR.CF (evalOp)
open Semantics.Dataflow (Flat)

/-- Outer `none` is refusal. `some none` is exhaustion of the target budget. -/
def run (flagFact : Flat (Word i8)) (fuel : Nat) (flag : Word i8) : Option (Option Nat) :=
  (rewrite graph (facts flagFact)).map fun cfg =>
    (cfg.run evalOp fuel (input flag)).map fun result => (result.get .here).toNat

def refusesVarying : Bool :=
  (rewrite PruneExit.Example.Bank.graph PruneExit.Example.Bank.varyingFacts).isNone

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Prune.Example
