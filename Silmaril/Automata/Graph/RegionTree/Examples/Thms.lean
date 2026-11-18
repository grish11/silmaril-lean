module

public import Silmaril.Automata.Graph.RegionTree.Examples.Defs
public import Silmaril.Automata.Graph.RegionTree.Thms
import Silmaril.Proofs.Automata.Graph.RegionTreeExamples

@[expose] public section
namespace Silmaril.Automata.Graph.RegionTree.Examples
open Silmaril.Semantics.Region.Tree

theorem cross_not_child : 3 ∈ tree.successors 1 ∧ ¬ tree.region.body.shape.Child 1 3 := Proofs.cross_not_child

theorem child_not_edge : tree.region.body.shape.Child 0 3 ∧ 3 ∉ tree.successors 0 := Proofs.child_not_edge

theorem loop_preserved : 3 ∈ tree.flatten.successors 3 := Proofs.loop_preserved

theorem adjacency_not_determined : tree.region = noEdges.region ∧ tree ≠ noEdges := Proofs.adjacency_not_determined

theorem diamond_witness : Witness diamond policy tree.region := proposal_witness diamond policy (fun _ => ())

theorem flat_roundtrip : tree.flatten = flat diamond policy := witness_lift diamond_witness

end Silmaril.Automata.Graph.RegionTree.Examples
