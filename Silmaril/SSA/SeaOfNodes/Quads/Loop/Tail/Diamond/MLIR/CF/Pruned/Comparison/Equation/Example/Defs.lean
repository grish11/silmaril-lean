module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Example.Defs

/-! # An inequation detected after feedback through the unequal arms -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Equation.Example

open CF.Example (source input regs num result stride add)
open Diamond.Prune (Checked carriedMask prune)
open SeaOfNodes.Loop.MLIR.CF (Op evalOp model)
open SeaOfNodes.MLIR.Lowering (encodeValues)

/-- Add the carried stride on the short arm, first selected after feedback. -/
def variantSource : Source Op regs num 7 := fun id =>
  let block := source id
  if id = 0 then { block with body := block.body ++ [add result result stride] } else block

def variant : Program variantSource 4 :=
  (check variantSource 4).get (by rfl)

def projectedVariant : Checked variant (carriedMask variant) :=
  (prune variant).get (by rfl)

def cfResults (fuel : Nat) : Option Nat × Option Nat :=
  (Pruned.Example.runCF fuel,
    ((lower projectedVariant).run evalOp fuel (encodeValues input)).map (fun env => (env.get .here).toNat))

def rvsdgResults (activations : Nat) : Option Nat × Option Nat :=
  (Pruned.Example.runRVSDG activations,
    (projectedVariant.lower.run (Join.model model) activations input).map (fun values => (values.get .head).toNat))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Equation.Example
