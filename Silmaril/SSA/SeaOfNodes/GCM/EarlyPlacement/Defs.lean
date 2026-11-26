module

public import Silmaril.SSA.SeaOfNodes.GCM.LatePlacement.Defs

/-! # The operand-block bound for Schedule Early -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.EarlyPlacement

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}
variable {cfg : Cfg Op Label Input Result}

/-- Choose the deepest operand block and require every operand's resolved
definition cut to be valid and its block to dominate the choice. An empty
operand list has entry as its bound. Local order is checked at a candidate cut. -/
def earlyBound? (tree : DominatorTree cfg) (operands : List (Point Label)) :
    Option (BlockId Label) :=
  match operands.maxOn? (fun operand => (tree.address operand.block).length) with
  | none => some none
  | some deepest =>
    if operands.all (fun operand => operand.valid? tree &&
        (tree.address operand.block).isPrefixOf (tree.address deepest.block)) then
      some deepest.block
    else none

end Silmaril.SSA.SeaOfNodes.GCM.EarlyPlacement
