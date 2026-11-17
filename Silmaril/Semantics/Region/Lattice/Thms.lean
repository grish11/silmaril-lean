module

public import Silmaril.Semantics.Region.Defs
public import Silmaril.Semantics.Region.Abstract.Named.Thms

@[expose] public section
namespace Silmaril.Semantics.Region
universe u v w z
variable {Img : Type u} {Assum : Type v} {Seg : Type w} {Lab : Type z}

/-- The existing finite profile inherits both raw powerset/product lattices. -/
example : CompleteLattice (SegmentRegionModel Img Assum Seg Lab) := inferInstance
example : CompleteLattice (RegionModel Img Assum Lab) := inferInstance

/-- No law presentation is duplicated: the original law-bearing record is
isomorphic to the positive-rule closed model at the finite boundary profile. -/
def lawfulAtomsEquiv : LawfulSegmentRegionModel Img Assum Seg Lab ≃
    Abstract.ClosedModel (Abstract.CoherenceRules (Img := Img) (Assum := Assum)
      (finiteBoundaryOps (Seg := Seg) (Lab := Lab))) where
  toFun M := ⟨M.toSegmentRegionModel.toAtoms, (Abstract.coherence_iff _ _).mpr M.laws⟩
  invFun M := ⟨Abstract.SegmentRegionModel.ofAtoms M.val,
    (Abstract.coherence_iff _ _).mp (by
      rw [Abstract.segment_to_ofAtoms]
      exact M.property)⟩
  left_inv M := by cases M; rfl
  right_inv M := Subtype.ext (Abstract.segment_to_ofAtoms M.val)

instance : CompleteLattice (LawfulSegmentRegionModel Img Assum Seg Lab) :=
  lawfulAtomsEquiv.completeLattice

theorem lawful_le_iff (M N : LawfulSegmentRegionModel Img Assum Seg Lab) :
    M ≤ N ↔ M.toSegmentRegionModel.toAtoms ⊆ N.toSegmentRegionModel.toAtoms := Iff.rfl

end Silmaril.Semantics.Region
