module

public import Init.Data.List.MinMaxOn
public import Silmaril.SSA.SeaOfNodes.GCM.Discovery.Defs

/-! # Loop-aware choice among checked finite placement cuts -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}
variable {cfg : Cfg Op Label Input Result}

/-- Keep just the cuts admitted by the existing placement checker, in
enumeration order. -/
def acceptedCuts (tree : DominatorTree cfg) (blocks : List (Target Label))
    (operands : List (Point Label)) (uses : List (Use Label)) : List (Point Label) :=
  (candidateCuts cfg blocks).filter (checkPlacement tree operands uses)

/-- Rank a list of admissible cuts by minimum loop depth, then maximum
dominator address length. Equal scores keep the first listed cut. -/
def rankCuts (tree : DominatorTree cfg) (loopDepth : BlockId Label → Nat)
    (cuts : List (Point Label)) : Option (Point Label) := do
  let shallow ← cuts.minOn? fun point => loopDepth point.block
  let atDepth := cuts.filter fun point => decide (loopDepth point.block = loopDepth shallow.block)
  atDepth.maxOn? fun point => (tree.address point.block).length

/-- Rank the cuts accepted by the existing placement checker. The caller
supplies the depth labels, which are the scores being minimized. -/
def chooseLoopPlacement (tree : DominatorTree cfg) (loopDepth : BlockId Label → Nat)
    (blocks : List (Target Label)) (operands : List (Point Label)) (uses : List (Use Label)) :
    Option (Point Label) :=
  rankCuts tree loopDepth (acceptedCuts tree blocks operands uses)

end Silmaril.SSA.SeaOfNodes.GCM
