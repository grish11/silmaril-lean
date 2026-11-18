module

public import Silmaril.Automata.Graph.Defs
public import Silmaril.Semantics.Region.Tree.CFG.Defs

/-! Optional finite-graph dominance bridge. The abstract region relation does
not import this module. The selected internal domain is exactly the graph's
reachable vertices; exit labels and outward adjacency are explicit policy. -/

@[expose] public section
namespace Silmaril.Automata.Graph.RegionTree
universe u
open Silmaril.Machine.Graph
open Silmaril.Semantics.Region.Tree

/-- The finite graph supplies internal control flow. The policy supplies all
outgoing labels, including any chosen normal exits beyond that graph. It must
agree on internal edges, cover every target, and separate internal/exit labels.
This is a graph observation policy, not a machine-execution soundness proof. -/
structure ExitPolicy (g : Digraph) where
  exits : Set Nat
  outgoing : Nat → Set Nat
  internal_iff : ∀ a b, g.Reachable a → g.Reachable b → (b ∈ outgoing a ↔ g.Edge a b)
  targets : ∀ a b, g.Reachable a → b ∈ outgoing a → g.Reachable b ∨ b ∈ exits
  disjoint : ∀ b, g.Reachable b → b ∉ exits

def flat (g : Digraph) (policy : ExitPolicy g) : FlatCFG Nat where
  entry := g.entry
  internal := {v | g.Reachable v}
  exits := policy.exits
  successors a := {b | g.Reachable a ∧ b ∈ policy.outgoing a}

/-- Tree labels identify reachable vertex numbers, and only those vertices.
Immediate children agree with actual immediate dominance on this live domain;
`DomExact` also characterizes all strict ancestors. Inactive Nat indices need
not form a rooted tree and carry no exported label. -/
structure Witness {Seg : Type u} (g : Digraph) (policy : ExitPolicy g)
    (r : TreeRow Nat Seg Nat) : Prop where
  root_eq : r.body.shape.root = g.entry
  entry_eq : r.entry = g.entry
  exits_eq : r.exits = policy.exits
  labels : ∀ v l, r.body.labelAt v = some l ↔ g.Reachable v ∧ l = v
  exact : DomExact g r.body.shape.parent
  terminal : r.body.TerminalLeaves

/-- A canonical proposed tree reuses existing `idom`; this is not a canonical
region partition. Each reachable graph vertex is a labeled segment node. -/
noncomputable def proposal {Seg : Type u} (g : Digraph) (policy : ExitPolicy g) (payload : Nat → Seg) :
    TreeRow Nat Seg Nat := by
  classical
  exact ⟨g.entry, policy.exits, ⟨⟨g.entry, g.idom⟩,
    fun v => .segment (payload v) (if g.Reachable v then some v else none)⟩⟩

end Silmaril.Automata.Graph.RegionTree
