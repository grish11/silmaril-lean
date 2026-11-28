module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Dominance.Emitted.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Example.Defs

/-! # A concrete emitted-CFG dominator tree and a reachable domination query

This takes an actual preheader-hoisted CFG from the existing
`LoopHoist.Corridor.Example` fixture, synthesizes its dominator tree with
`Dominance.Emitted.synthesize?`, and runs one reachable domination query on
it (the header dominates the exit). This checks only reachability and
dominance on the emitted CFG; it says nothing about operand origins or
about moving any existing Φ read. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Dominance.Emitted.Example

open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Example (loop)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Dominance.Emitted (synthesize?)

/-- Synthesize the dominator tree of the actual CFG hoisted by binding 1 of
the invariant variant (`Corridor.Example.observe false`'s successful hoist),
then check that the header is reachable and dominates the exit. -/
def headerDominatesExit : Bool :=
  match Corridor.pickAndHoist? (loop false) 1 with
  | none => false
  | some (_, ⟨_, cfg⟩) =>
    match synthesize? cfg with
    | none => false
    | some ⟨tree, _⟩ =>
      tree.reachable (some ⟨_, .header⟩) && tree.reachable (some ⟨_, .exit⟩) &&
        (tree.address (some ⟨_, .header⟩)).isPrefixOf (tree.address (some ⟨_, .exit⟩))

/-- The preheader (the anonymous entry) is reachable and trivially
dominates every reachable block, including the header. -/
def entryDominatesHeader : Bool :=
  match Corridor.pickAndHoist? (loop false) 1 with
  | none => false
  | some (_, ⟨_, cfg⟩) =>
    match synthesize? cfg with
    | none => false
    | some ⟨tree, _⟩ =>
      tree.reachable none &&
        (tree.address none).isPrefixOf (tree.address (some ⟨_, .header⟩))

/-- The exit does not dominate the header: synthesis is directional, not an
equivalence relation. -/
def exitDoesNotDominateHeader : Bool :=
  match Corridor.pickAndHoist? (loop false) 1 with
  | none => false
  | some (_, ⟨_, cfg⟩) =>
    match synthesize? cfg with
    | none => false
    | some ⟨tree, _⟩ =>
      !((tree.address (some ⟨_, .exit⟩)).isPrefixOf (tree.address (some ⟨_, .header⟩)))

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Dominance.Emitted.Example
