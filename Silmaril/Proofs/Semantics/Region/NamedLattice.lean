module

public import Silmaril.Semantics.Region.Abstract.Named.Defs

@[expose] public section
namespace Silmaril.Semantics.Region.Abstract.Proofs
universe u v w x y z
variable {Img : Type u} {Assum : Type v} {Seg : Type w} {Support : Type x} {Lab : Type y} {Exits : Type z}

theorem segment_of_toAtoms (M : SegmentRegionModel Img Assum Seg Support Lab Exits) :
    SegmentRegionModel.ofAtoms M.toAtoms = M := by cases M; rfl

theorem segment_to_ofAtoms (M : RawModel (SegmentAtom Img Assum Seg Support Lab Exits)) :
    (SegmentRegionModel.ofAtoms M).toAtoms = M := by
  ext a
  cases a <;> rfl

theorem label_of_toAtoms (M : RegionModel Img Assum Lab Exits) : RegionModel.ofAtoms M.toAtoms = M := by
  cases M; rfl

theorem label_to_ofAtoms (M : RawModel (LabelAtom Img Assum Lab Exits)) :
    (RegionModel.ofAtoms M).toAtoms = M := by ext a; cases a; rfl

theorem coherence_iff (ops : BoundaryOps Seg Support Lab Exits)
    (M : SegmentRegionModel Img Assum Seg Support Lab Exits) :
    Closed (CoherenceRules ops) M.toAtoms ↔ SegmentRegionLaws ops M := by
  constructor
  · intro h
    have unary : ∀ p q, CoherenceRule ops ⟨{p}, q⟩ → p ∈ M.toAtoms → q ∈ M.toAtoms := by
      intro p q hr hp
      exact h _ hr (fun a ha => Set.mem_singleton_iff.mp ha ▸ hp)
    exact ⟨fun i a s e xs => unary _ _ (.bb_seg i a s e xs),
      fun i a s e xs => unary _ _ (.bb_reg i a s e xs),
      fun i a ss e exit => ⟨unary _ _ (.sr_reg i a ss e exit), unary _ _ (.reg_sr i a ss e exit)⟩,
      fun i a ss e exit => ⟨unary _ _ (.optional_reg i a ss e exit), unary _ _ (.reg_optional i a ss e exit)⟩⟩
  · intro h r hr premises
    cases hr with
    | bb_seg i a s e xs => exact h.bb_seg i a s e xs (premises (Set.mem_singleton _))
    | bb_reg i a s e xs => exact h.bb_reg i a s e xs (premises (Set.mem_singleton _))
    | sr_reg i a ss e exit => exact (h.sr_iff i a ss e exit).mp (premises (Set.mem_singleton _))
    | reg_sr i a ss e exit => exact (h.sr_iff i a ss e exit).mpr (premises (Set.mem_singleton _))
    | optional_reg i a ss e exit => exact (h.optional_iff i a ss e exit).mp (premises (Set.mem_singleton _))
    | reg_optional i a ss e exit => exact (h.optional_iff i a ss e exit).mpr (premises (Set.mem_singleton _))
end Silmaril.Semantics.Region.Abstract.Proofs
