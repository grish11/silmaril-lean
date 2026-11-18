module

public import Silmaril.Semantics.Region.Tree.Finite.Defs
public import Silmaril.Semantics.Region.Tree.Thms
import Silmaril.Proofs.Semantics.Region.TreeFinite

@[expose] public section
namespace Silmaril.Semantics.Region.Tree

theorem finite_implies_label {Img Assum V Seg Lab} {M : RegionModel (Img × Assum) (TreeRow V Seg Lab)}
    {i a ss e xs} (h : finiteReg M i a ss e xs) : labelReg M i a e xs := Proofs.finite_implies_label h

theorem label_to_finite_of_support {Img Assum V Seg Lab} {M : RegionModel (Img × Assum) (TreeRow V Seg Lab)}
    {i a e xs} (h : labelReg M i a e xs)
    (supports : ∀ tree, M.Holds (i, a) tree → ∃ ss : Finset Seg, {s | s ∈ ss} = tree.flatten.support) :
    ∃ ss, finiteReg M i a ss e xs := Proofs.label_to_finite_of_support h supports

end Silmaril.Semantics.Region.Tree
