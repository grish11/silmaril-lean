module

public import Silmaril.SSA.SeaOfNodes.GCM.Defs

/-! # Finite cut discovery for one pure total floating value -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}
variable {cfg : Cfg Op Label Input Result}

/-- Enumerate one block's cuts in local binding order, including both endpoints. -/
def blockCuts (cfg : Cfg Op Label Input Result) (block : BlockId Label) : List (Point Label) :=
  (List.range ((shape cfg block).bindings + 1)).map fun cut => ⟨block, cut⟩

/-- Enumerate the entry cuts, then the cuts of the listed typed blocks in
order. Each block contributes cut zero through its final cut, inclusive.
A typed CFG supplies a body for each label and need not have a finite
label type, so the list fixes the finite search space. -/
def candidateCuts (cfg : Cfg Op Label Input Result) (blocks : List (Target Label)) :
    List (Point Label) :=
  (none :: blocks.map some).flatMap (blockCuts cfg)

/-- Choose the first in-bounds cut accepted by the existing checker.
The checker resolves each Phi occurrence and checks the supplied
reachability, dominance and local order constraints. -/
def discoverPlacement (tree : DominatorTree cfg) (blocks : List (Target Label))
    (operands : List (Point Label)) (uses : List (Use Label)) : Option (Point Label) :=
  (candidateCuts cfg blocks).find? (checkPlacement tree operands uses)

/-- Optional completeness evidence for the tree's reachability mask and
ancestry test. The search itself needs only the sound certificate. -/
structure DominatorTree.Complete (tree : DominatorTree cfg) : Prop where
  reachable_complete : ∀ {b}, Reachable cfg b → tree.reachable b = true
  prefix_complete : ∀ {a b}, Reachable cfg b → Dominates cfg a b →
    List.IsPrefix (tree.address a) (tree.address b)

end Silmaril.SSA.SeaOfNodes.GCM
