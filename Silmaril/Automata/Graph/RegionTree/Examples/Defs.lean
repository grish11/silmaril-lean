module

public import Silmaril.Automata.Graph.RegionTree.Defs

@[expose] public section
namespace Silmaril.Automata.Graph.RegionTree.Examples
open Silmaril.Machine.Graph
open Silmaril.Semantics.Region.Tree

/-- Diamond, with a self-loop at the join. The arcs 1→3 and 2→3 cross
siblings in its exact dominator tree, whose non-root parents are all 0. -/
def diamond : Digraph := ⟨4, fun n => match n with
  | 0 => [1, 2]
  | 1 => [3]
  | 2 => [3]
  | 3 => [3]
  | _ => [], 0⟩

def policy : ExitPolicy diamond where
  exits := ∅
  outgoing a := {b | diamond.Edge a b}
  internal_iff _ _ _ _ := Iff.rfl
  targets _ b ha hb := by
    obtain ⟨path, hp⟩ := ha
    exact Or.inl ⟨path ++ [b], hp.snoc hb⟩
  disjoint _ _ := Set.notMem_empty _

noncomputable def tree : SegCFG Nat Unit Nat :=
  SegCFG.lift (proposal diamond policy (fun _ => ())) (flat diamond policy)

/-- Same primitive region data, different independently supplied adjacency. -/
noncomputable def noEdges : SegCFG Nat Unit Nat := ⟨tree.region, fun _ => ∅⟩

end Silmaril.Automata.Graph.RegionTree.Examples
