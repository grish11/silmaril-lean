module

public import Silmaril.Semantics.Region.Tree.Defs
public import Silmaril.Semantics.Region.Defs

@[expose] public section
namespace Silmaril.Semantics.Region.Tree

/-- A finite flat row needs explicit extensional support and exit witnesses.
Arbitrary abstract trees need not have finite support or finite declared exits. -/
structure FiniteView {Seg Lab} (flat : FlatRegion Seg Lab)
    (row : Silmaril.Semantics.Region.SegmentRow Seg Lab) : Prop where
  entry_eq : row.entry = flat.entry
  support_eq : {s | s ∈ row.support} = flat.support
  exits_eq : {l | l ∈ row.exits} = flat.exits

def finiteReg {Img Assum V Seg Lab} (M : RegionModel (Img × Assum) (TreeRow V Seg Lab)) :
    Silmaril.Semantics.Region.SegmentRegPred Img Assum Seg Lab :=
  fun i a support entry exits => ∃ tree, M.Holds (i, a) tree ∧ FiniteView tree.flatten ⟨support, entry, exits⟩

def labelReg {Img Assum V Seg Lab} (M : RegionModel (Img × Assum) (TreeRow V Seg Lab)) :
    Silmaril.Semantics.Region.RegPred Img Assum Lab :=
  fun i a entry exits => ∃ tree, M.Holds (i, a) tree ∧ entry = tree.entry ∧ {l | l ∈ exits} = tree.exits

end Silmaril.Semantics.Region.Tree
