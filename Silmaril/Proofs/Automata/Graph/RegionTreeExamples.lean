module

public import Silmaril.Automata.Graph.RegionTree.Examples.Defs
public import Silmaril.Automata.Graph.RegionTree.Thms

@[expose] public section
namespace Silmaril.Automata.Graph.RegionTree.Examples.Proofs
open Silmaril.Machine.Graph
open Silmaril.Semantics.Region.Tree

theorem cross_not_child : 3 ∈ tree.successors 1 ∧ ¬ tree.region.body.shape.Child 1 3 := by
  refine ⟨?_, ?_⟩
  · refine ⟨1, ?_, ?_⟩
    · have live : diamond.Reachable 1 := by decide
      simp [proposal, SegTree.labelAt, live]
    · exact ⟨by decide, show diamond.Edge 1 3 from by decide⟩
  · change ¬ diamond.idom 3 = some 1
    decide

theorem child_not_edge : tree.region.body.shape.Child 0 3 ∧ 3 ∉ tree.successors 0 := by
  refine ⟨?_, ?_⟩
  · change diamond.idom 3 = some 0
    decide
  · rintro ⟨a, ha, hb⟩
    have live : diamond.Reachable 0 := by decide
    have eq : a = 0 := by simpa [tree, SegCFG.lift, proposal, SegTree.labelAt, live] using ha.symm
    subst a
    exact (show ¬ diamond.Edge 0 3 by decide) hb.2

theorem loop_preserved : 3 ∈ tree.flatten.successors 3 := by
  change 3 ∈ (SegCFG.lift (proposal diamond policy (fun _ => ())) (flat diamond policy)).flatten.successors 3
  rw [witness_lift (proposal_witness diamond policy (fun _ => ()))]
  exact ⟨by decide, show diamond.Edge 3 3 from by decide⟩

theorem adjacency_not_determined : tree.region = noEdges.region ∧ tree ≠ noEdges := by
  refine ⟨rfl, ?_⟩
  intro eq
  have h := cross_not_child.1
  rw [eq] at h
  exact h

end Silmaril.Automata.Graph.RegionTree.Examples.Proofs
