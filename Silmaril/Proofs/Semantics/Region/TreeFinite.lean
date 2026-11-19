module

public import Silmaril.Semantics.Region.Tree.Finite.Defs

@[expose] public section
namespace Silmaril.Semantics.Region.Tree.Proofs

theorem finite_implies_label {Img Assum V Seg Lab} {M : RegionModel (Img × Assum) (TreeRow V Seg Lab)}
    {i a ss e xs} (h : finiteReg M i a ss e xs) : labelReg M i a e xs := by
  obtain ⟨tree, hm, view⟩ := h
  exact ⟨tree, hm, view.entry_eq, view.exits_eq⟩

theorem label_to_finite_of_support {Img Assum V Seg Lab} {M : RegionModel (Img × Assum) (TreeRow V Seg Lab)}
    {i a e xs} (h : labelReg M i a e xs)
    (supports : ∀ tree, M.Holds (i, a) tree → ∃ ss : Finset Seg, {s | s ∈ ss} = tree.flatten.support) :
    ∃ ss, finiteReg M i a ss e xs := by
  obtain ⟨tree, hm, he, hx⟩ := h
  obtain ⟨ss, hs⟩ := supports tree hm
  exact ⟨ss, tree, hm, he, hs, hx⟩

end Silmaril.Semantics.Region.Tree.Proofs
