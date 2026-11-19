module

public import Silmaril.Automata.Graph.RegionTree.Defs
public import Silmaril.Automata.Graph.Thms
public import Silmaril.Semantics.Region.Tree.CFG.Thms
import Silmaril.Proofs.Automata.Graph.RegionTree

@[expose] public section
namespace Silmaril.Automata.Graph.RegionTree
open Silmaril.Machine.Graph
open Silmaril.Semantics.Region.Tree

theorem witness_cover {Seg} {g : Digraph} {policy : ExitPolicy g} {r : TreeRow Nat Seg Nat}
    (h : Witness g policy r) : LabelCover r (flat g policy) := Proofs.witness_cover h

theorem witness_immediate {Seg} {g : Digraph} {policy : ExitPolicy g} {r : TreeRow Nat Seg Nat}
    (h : Witness g policy r) {p c : Nat} (live : g.Reachable c) :
    r.body.shape.Child p c ↔ g.idom c = some p := by
  unfold Shape.Child
  rw [exact_eq_idom h.exact live]

theorem witness_root_parent {Seg} {g : Digraph} {policy : ExitPolicy g} {r : TreeRow Nat Seg Nat}
    (h : Witness g policy r) : r.body.shape.parent r.body.shape.root = none := by
  rw [h.root_eq, exact_eq_idom h.exact (Digraph.reachable_entry g), Digraph.idom_none_entry]

theorem witness_parent_live {Seg} {g : Digraph} {policy : ExitPolicy g} {r : TreeRow Nat Seg Nat}
    (h : Witness g policy r) {p c : Nat} (live : g.Reachable c) (child : r.body.shape.Child p c) :
    g.Reachable p := Digraph.Dominates.reachable live ((h.exact p c live).mp (.parent child)).1

theorem witness_unique_labels {Seg} {g : Digraph} {policy : ExitPolicy g} {r : TreeRow Nat Seg Nat}
    (h : Witness g policy r) : UniqueLabels r.body :=
  fun v w l hv hw => ((h.labels v l).mp hv).2.symm.trans ((h.labels w l).mp hw).2

theorem witness_ancestors {Seg} {g : Digraph} {policy : ExitPolicy g} {r : TreeRow Nat Seg Nat}
    (h : Witness g policy r) {a b : Nat} (live : g.Reachable b) :
    Ancestor r.body.shape.parent a b ↔ g.StrictlyDominates a b := h.exact a b live

theorem witness_descendants {Seg} {g : Digraph} {policy : ExitPolicy g} {r : TreeRow Nat Seg Nat}
    (h : Witness g policy r) {a b : Nat} (live : g.Reachable b) :
    r.body.shape.Descendant a b ↔ a = b ∨ g.StrictlyDominates a b := by
  rw [Proofs.descendant_iff_ancestor, h.exact a b live]

theorem witness_rooted {Seg} {g : Digraph} {policy : ExitPolicy g} {r : TreeRow Nat Seg Nat}
    (h : Witness g policy r) {v : Nat} (live : g.Reachable v) : r.body.shape.Descendant r.body.shape.root v :=
  Proofs.witness_rooted h live

theorem witness_lift {Seg} {g : Digraph} {policy : ExitPolicy g} {r : TreeRow Nat Seg Nat}
    (h : Witness g policy r) : (SegCFG.lift r (flat g policy)).flatten = flat g policy :=
  flatten_lift r _ (witness_cover h)

theorem proposal_witness {Seg} (g : Digraph) (policy : ExitPolicy g) (payload : Nat → Seg) :
    Witness g policy (proposal g policy payload) := Proofs.proposal_witness g policy payload

/-- A genuine lifting theorem for the selected reachable internal graph and
explicit exit policy, using the repository's existing immediate-dominator proof. -/
theorem exists_dominator_lift {Seg} (g : Digraph) (policy : ExitPolicy g) (payload : Nat → Seg) :
    ∃ tree : SegCFG Nat Seg Nat, Witness g policy tree.region ∧ tree.flatten = flat g policy :=
  ⟨SegCFG.lift (proposal g policy payload) (flat g policy), proposal_witness g policy payload,
    witness_lift (proposal_witness g policy payload)⟩

end Silmaril.Automata.Graph.RegionTree
