module

public import Silmaril.Semantics.Region.Tree.CFG.Defs
public import Silmaril.Semantics.Region.Tree.Thms
import Silmaril.Proofs.Semantics.Region.TreeCFG

@[expose] public section
namespace Silmaril.Semantics.Region.Tree

theorem flatten_lift {V Seg Lab} (r : TreeRow V Seg Lab) (g : FlatCFG Lab) (h : LabelCover r g) :
    (SegCFG.lift r g).flatten = g := Proofs.flatten_lift r g h

theorem flatten_source_closed {V Seg Lab} (g : SegCFG V Seg Lab) : g.flatten.SourceClosed :=
  fun _ _ ⟨v, hv, _⟩ => ⟨v, hv⟩

/-- Exact converse bounds for a fixed proposed region tree. Dominance remains
an additional, independent certificate. -/
theorem lift_exists_iff {V Seg Lab} (r : TreeRow V Seg Lab) (g : FlatCFG Lab) :
    (∃ tree : SegCFG V Seg Lab, tree.region = r ∧ tree.flatten = g) ↔ LabelCover r g :=
  Proofs.lift_exists_iff r g

theorem flatten_successor {V Seg Lab} (g : SegCFG V Seg Lab) (v : V) (a b : Lab)
    (label : g.region.body.labelAt v = some a) (edge : b ∈ g.successors v) : b ∈ g.flatten.successors a :=
  ⟨v, label, edge⟩

theorem flatten_successors_unique {V Seg Lab} (g : SegCFG V Seg Lab) (unique : UniqueLabels g.region.body)
    (v : V) (a : Lab) (hv : g.region.body.labelAt v = some a) : g.flatten.successors a = g.successors v :=
  Proofs.flatten_successors_unique g unique v a hv

theorem eraseCFG_iff {Context V Seg Lab} (M : TreeCFGModel Context V Seg Lab) (c : Context) (g : FlatCFG Lab) :
    (eraseCFG M).Holds c g ↔ ∃ tree, M.Holds c tree ∧ tree.flatten = g := image_holds _ M c g

theorem lift_exists {V Seg Lab} (r : TreeRow V Seg Lab) (g : FlatCFG Lab) (h : LabelCover r g) :
    ∃ tree : SegCFG V Seg Lab, tree.region = r ∧ tree.flatten = g := ⟨SegCFG.lift r g, rfl, flatten_lift r g h⟩

theorem covers_refl {Lab} (g : FlatCFG Lab) : Covers g g := ⟨rfl, Set.Subset.rfl, Set.Subset.rfl, fun _ _ => Set.Subset.rfl⟩

theorem covers_trans {Lab} {a b c : FlatCFG Lab} (ab : Covers a b) (bc : Covers b c) : Covers a c :=
  Proofs.covers_trans ab bc

theorem candidate_region_image {Context V Seg Lab} {M : RegionModel Context (TreeRow V Seg Lab)}
    {context : Context} (candidate : RegionCandidate M context) :
    (image TreeRow.flatten M).Holds context candidate.cfg.region.flatten :=
  tree_yields_image _ M context _ candidate.admitted

theorem covered_successor {Context V Seg Lab} {M : RegionModel Context (TreeRow V Seg Lab)}
    {context : Context} {actual : FlatCFG Lab} (candidate : CoveredCandidate M context actual)
    {a b : Lab} (ha : a ∈ actual.internal) (hb : b ∈ actual.successors a) :
    b ∈ candidate.cfg.flatten.successors a := candidate.coverage.successors a ha hb

example {Context V Seg Lab} : CompleteLattice (TreeCFGModel Context V Seg Lab) := inferInstance
example {Context Lab} : CompleteLattice (FlatCFGModel Context Lab) := inferInstance

end Silmaril.Semantics.Region.Tree
