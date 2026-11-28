module

public import Silmaril.SSA.SeaOfNodes.GCM.EarlyPlacement.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopForest.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Tree.Synthesis.Defs

/-! # Loop-aware placement within the computed dominator corridor -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.Corridor

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}
variable {cfg : Cfg Op Label Input Result}

/-- Walk the address prefixes from late to early, including both endpoints.
Inverted bounds give an empty corridor. -/
def addresses (early late : List Nat) : List (List Nat) :=
  if early.isPrefixOf late then
    (List.range (late.length - early.length + 1)).map fun steps =>
      late.take (late.length - steps)
  else []

/-- Visit the represented corridor blocks in inventory order. Enumerating
cuts only in those blocks preserves the existing order among accepted cuts. -/
def acceptedCorridorCuts (tree : DominatorTree cfg) (blocks : List (Target Label))
    (early late : BlockId Label) (operands : List (Point Label)) (uses : List (Use Label)) :
    List (Point Label) :=
  let corridor := addresses (tree.address early) (tree.address late)
  let candidates := (NaturalLoop.vertices blocks).filter fun block =>
    decide (tree.address block ∈ corridor)
  (candidates.flatMap (blockCuts cfg)).filter (checkPlacement tree operands uses)

/-- Reuse the existing cut checker and ranking inside the computed corridor.
The empty-use case uses the existing chooser because it has no late bound. -/
def chooseInForest (tree : DominatorTree cfg) (loops : List (LoopForest.HeaderLoop Label))
    (blocks : List (Target Label)) (operands : List (Point Label)) (uses : List (Use Label)) :
    Option (Point Label) :=
  let depth := LoopForest.depth tree loops
  if uses.isEmpty then chooseLoopPlacement tree depth blocks operands uses
  else do
    let early ← EarlyPlacement.earlyBound? tree operands
    let late ← LatePlacement.lateBound? tree blocks uses
    rankCuts tree depth (acceptedCorridorCuts tree blocks early late operands uses)

/-- Discover the same admitted natural-loop forest as the existing chooser. -/
def choosePlacement (tree : DominatorTree cfg) (blocks : List (Target Label))
    (operands : List (Point Label)) (uses : List (Use Label)) : Option (Point Label) := do
  let loops ← LoopForest.forest? tree blocks
  chooseInForest tree loops blocks operands uses

/-- Synthesize the complete tree, then choose one placement for the supplied
definition and use cuts. -/
def chooseSynthesized? [DecidableEq (Target Label)] (cfg : Cfg Op Label Input Result)
    (blocks : List (Target Label)) (number : BlockId Label → Nat)
    (injective : Function.Injective number) (operands : List (Point Label)) (uses : List (Use Label)) :
    Option (Point Label) := do
  let tree ← Dominance.Tree.Synthesis.synthesize? cfg blocks number injective
  choosePlacement tree.1 blocks operands uses

end Silmaril.SSA.SeaOfNodes.GCM.Corridor
