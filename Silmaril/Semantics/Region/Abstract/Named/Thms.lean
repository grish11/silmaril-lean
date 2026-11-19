module

public import Silmaril.Semantics.Region.Abstract.Named.Defs
public import Silmaril.Semantics.Region.Abstract.Thms
import Silmaril.Proofs.Semantics.Region.NamedLattice

@[expose] public section
namespace Silmaril.Semantics.Region.Abstract
universe u v w x y z
variable {Img : Type u} {Assum : Type v} {Seg : Type w} {Support : Type x} {Lab : Type y} {Exits : Type z}

theorem segment_of_toAtoms (M : SegmentRegionModel Img Assum Seg Support Lab Exits) :
    SegmentRegionModel.ofAtoms M.toAtoms = M := Proofs.segment_of_toAtoms M

theorem segment_to_ofAtoms (M : RawModel (SegmentAtom Img Assum Seg Support Lab Exits)) :
    (SegmentRegionModel.ofAtoms M).toAtoms = M := Proofs.segment_to_ofAtoms M

theorem label_of_toAtoms (M : RegionModel Img Assum Lab Exits) : RegionModel.ofAtoms M.toAtoms = M :=
  Proofs.label_of_toAtoms M

theorem label_to_ofAtoms (M : RawModel (LabelAtom Img Assum Lab Exits)) :
    (RegionModel.ofAtoms M).toAtoms = M := Proofs.label_to_ofAtoms M

def SegmentRegionModel.atomsEquiv : SegmentRegionModel Img Assum Seg Support Lab Exits ≃
    RawModel (SegmentAtom Img Assum Seg Support Lab Exits) where
  toFun := SegmentRegionModel.toAtoms
  invFun := SegmentRegionModel.ofAtoms
  left_inv := segment_of_toAtoms
  right_inv := segment_to_ofAtoms

def RegionModel.atomsEquiv : RegionModel Img Assum Lab Exits ≃ RawModel (LabelAtom Img Assum Lab Exits) where
  toFun := RegionModel.toAtoms
  invFun := RegionModel.ofAtoms
  left_inv := label_of_toAtoms
  right_inv := label_to_ofAtoms

instance : CompleteLattice (SegmentRegionModel Img Assum Seg Support Lab Exits) :=
  SegmentRegionModel.atomsEquiv.completeLattice
instance : CompleteLattice (RegionModel Img Assum Lab Exits) := RegionModel.atomsEquiv.completeLattice

theorem segment_le_iff (M N : SegmentRegionModel Img Assum Seg Support Lab Exits) :
    M ≤ N ↔ M.toAtoms ⊆ N.toAtoms := Iff.rfl

theorem label_le_iff (M N : RegionModel Img Assum Lab Exits) : M ≤ N ↔ M.toAtoms ⊆ N.toAtoms := Iff.rfl

def lawfulSegmentEquiv (rules : Rules (SegmentAtom Img Assum Seg Support Lab Exits)) :
    LawfulSegmentRegionModel rules ≃ ClosedModel rules where
  toFun M := ⟨M.val.toAtoms, M.property⟩
  invFun M := ⟨SegmentRegionModel.ofAtoms M.val, by
    rw [segment_to_ofAtoms]; exact M.property⟩
  left_inv M := Subtype.ext (segment_of_toAtoms M.val)
  right_inv M := Subtype.ext (segment_to_ofAtoms M.val)

def lawfulLabelEquiv (rules : Rules (LabelAtom Img Assum Lab Exits)) :
    LawfulRegionModel rules ≃ ClosedModel rules where
  toFun M := ⟨M.val.toAtoms, M.property⟩
  invFun M := ⟨RegionModel.ofAtoms M.val, by
    rw [label_to_ofAtoms]; exact M.property⟩
  left_inv M := Subtype.ext (label_of_toAtoms M.val)
  right_inv M := Subtype.ext (label_to_ofAtoms M.val)

instance (rules : Rules (SegmentAtom Img Assum Seg Support Lab Exits)) :
    CompleteLattice (LawfulSegmentRegionModel rules) := (lawfulSegmentEquiv rules).completeLattice
instance (rules : Rules (LabelAtom Img Assum Lab Exits)) :
    CompleteLattice (LawfulRegionModel rules) := (lawfulLabelEquiv rules).completeLattice

theorem lawful_segment_le_iff {rules : Rules (SegmentAtom Img Assum Seg Support Lab Exits)}
    (M N : LawfulSegmentRegionModel rules) : M ≤ N ↔ M.val.toAtoms ⊆ N.val.toAtoms := Iff.rfl

theorem lawful_label_le_iff {rules : Rules (LabelAtom Img Assum Lab Exits)}
    (M N : LawfulRegionModel rules) : M ≤ N ↔ M.val.toAtoms ⊆ N.val.toAtoms := Iff.rfl

/-- The order is literally inclusion of judgments, not an order on encodings. -/
def SegmentRegionModel.atomsOrderIso : SegmentRegionModel Img Assum Seg Support Lab Exits ≃o
    RawModel (SegmentAtom Img Assum Seg Support Lab Exits) where
  toEquiv := SegmentRegionModel.atomsEquiv
  map_rel_iff' := Iff.rfl

def RegionModel.atomsOrderIso : RegionModel Img Assum Lab Exits ≃o RawModel (LabelAtom Img Assum Lab Exits) where
  toEquiv := RegionModel.atomsEquiv
  map_rel_iff' := Iff.rfl

def lawfulSegmentOrderIso (rules : Rules (SegmentAtom Img Assum Seg Support Lab Exits)) :
    LawfulSegmentRegionModel rules ≃o ClosedModel rules where
  toEquiv := lawfulSegmentEquiv rules
  map_rel_iff' := Iff.rfl

def lawfulLabelOrderIso (rules : Rules (LabelAtom Img Assum Lab Exits)) :
    LawfulRegionModel rules ≃o ClosedModel rules where
  toEquiv := lawfulLabelEquiv rules
  map_rel_iff' := Iff.rfl

theorem segment_atomsOrderIso_apply (M : SegmentRegionModel Img Assum Seg Support Lab Exits) :
    SegmentRegionModel.atomsOrderIso M = M.toAtoms := rfl

theorem label_atomsOrderIso_apply (M : RegionModel Img Assum Lab Exits) :
    RegionModel.atomsOrderIso M = M.toAtoms := rfl

theorem lawful_segment_orderIso_apply {rules : Rules (SegmentAtom Img Assum Seg Support Lab Exits)}
    (M : LawfulSegmentRegionModel rules) :
    (lawfulSegmentOrderIso rules M).val = M.val.toAtoms := rfl

theorem lawful_label_orderIso_apply {rules : Rules (LabelAtom Img Assum Lab Exits)}
    (M : LawfulRegionModel rules) :
    (lawfulLabelOrderIso rules M).val = M.val.toAtoms := rfl

theorem raw_segment_sInf (models : Set (SegmentRegionModel Img Assum Seg Support Lab Exits)) :
    (sInf models).toAtoms = sInf (SegmentRegionModel.toAtoms '' models) := by
  have h := (SegmentRegionModel.atomsOrderIso :
    SegmentRegionModel Img Assum Seg Support Lab Exits ≃o RawModel (SegmentAtom Img Assum Seg Support Lab Exits)).map_sInf models
  change (sInf models).toAtoms = ⨅ M ∈ models, M.toAtoms at h
  simpa only [sInf_image] using h

theorem raw_segment_sSup (models : Set (SegmentRegionModel Img Assum Seg Support Lab Exits)) :
    (sSup models).toAtoms = sSup (SegmentRegionModel.toAtoms '' models) := by
  have h := (SegmentRegionModel.atomsOrderIso :
    SegmentRegionModel Img Assum Seg Support Lab Exits ≃o RawModel (SegmentAtom Img Assum Seg Support Lab Exits)).map_sSup models
  change (sSup models).toAtoms = ⨆ M ∈ models, M.toAtoms at h
  simpa only [sSup_image] using h

theorem raw_label_sInf (models : Set (RegionModel Img Assum Lab Exits)) :
    (sInf models).toAtoms = sInf (RegionModel.toAtoms '' models) := by
  have h := (RegionModel.atomsOrderIso :
    RegionModel Img Assum Lab Exits ≃o RawModel (LabelAtom Img Assum Lab Exits)).map_sInf models
  change (sInf models).toAtoms = ⨅ M ∈ models, M.toAtoms at h
  simpa only [sInf_image] using h

theorem raw_label_sSup (models : Set (RegionModel Img Assum Lab Exits)) :
    (sSup models).toAtoms = sSup (RegionModel.toAtoms '' models) := by
  have h := (RegionModel.atomsOrderIso :
    RegionModel Img Assum Lab Exits ≃o RawModel (LabelAtom Img Assum Lab Exits)).map_sSup models
  change (sSup models).toAtoms = ⨆ M ∈ models, M.toAtoms at h
  simpa only [sSup_image] using h

theorem lawful_segment_inf {rules : Rules (SegmentAtom Img Assum Seg Support Lab Exits)}
    (M N : LawfulSegmentRegionModel rules) :
    (M ⊓ N).val.toAtoms = M.val.toAtoms ∩ N.val.toAtoms := segment_to_ofAtoms _

theorem lawful_segment_sup {rules : Rules (SegmentAtom Img Assum Seg Support Lab Exits)}
    (M N : LawfulSegmentRegionModel rules) :
    (M ⊔ N).val.toAtoms = closure rules (M.val.toAtoms ∪ N.val.toAtoms) := segment_to_ofAtoms _

theorem lawful_label_inf {rules : Rules (LabelAtom Img Assum Lab Exits)}
    (M N : LawfulRegionModel rules) :
    (M ⊓ N).val.toAtoms = M.val.toAtoms ∩ N.val.toAtoms := label_to_ofAtoms _

theorem lawful_label_sup {rules : Rules (LabelAtom Img Assum Lab Exits)}
    (M N : LawfulRegionModel rules) :
    (M ⊔ N).val.toAtoms = closure rules (M.val.toAtoms ∪ N.val.toAtoms) := label_to_ofAtoms _

theorem coherence_iff (ops : BoundaryOps Seg Support Lab Exits)
    (M : SegmentRegionModel Img Assum Seg Support Lab Exits) :
    Closed (CoherenceRules ops) M.toAtoms ↔ SegmentRegionLaws ops M := Proofs.coherence_iff ops M

theorem lawful_segment_sInf {rules : Rules (SegmentAtom Img Assum Seg Support Lab Exits)}
    (models : Set (LawfulSegmentRegionModel rules)) :
    (sInf models).val.toAtoms = sInf ((fun M => M.val.toAtoms) '' models) := by
  have h := congrArg (fun M : ClosedModel rules => M.val) ((lawfulSegmentOrderIso rules).map_sInf models)
  rw [← sInf_image, val_sInf, Set.image_image] at h
  exact h

theorem lawful_segment_sSup {rules : Rules (SegmentAtom Img Assum Seg Support Lab Exits)}
    (models : Set (LawfulSegmentRegionModel rules)) :
    (sSup models).val.toAtoms = closure rules (sSup ((fun M => M.val.toAtoms) '' models)) := by
  have h := congrArg (fun M : ClosedModel rules => M.val) ((lawfulSegmentOrderIso rules).map_sSup models)
  rw [← sSup_image, val_sSup, Set.image_image] at h
  exact h

theorem lawful_segment_bot {rules : Rules (SegmentAtom Img Assum Seg Support Lab Exits)} :
    (⊥ : LawfulSegmentRegionModel rules).val.toAtoms = closure rules ∅ := segment_to_ofAtoms _

theorem lawful_segment_top {rules : Rules (SegmentAtom Img Assum Seg Support Lab Exits)} :
    (⊤ : LawfulSegmentRegionModel rules).val.toAtoms = Set.univ := segment_to_ofAtoms _

theorem lawful_label_sInf {rules : Rules (LabelAtom Img Assum Lab Exits)}
    (models : Set (LawfulRegionModel rules)) :
    (sInf models).val.toAtoms = sInf ((fun M => M.val.toAtoms) '' models) := by
  have h := congrArg (fun M : ClosedModel rules => M.val) ((lawfulLabelOrderIso rules).map_sInf models)
  rw [← sInf_image, val_sInf, Set.image_image] at h
  exact h

theorem lawful_label_sSup {rules : Rules (LabelAtom Img Assum Lab Exits)}
    (models : Set (LawfulRegionModel rules)) :
    (sSup models).val.toAtoms = closure rules (sSup ((fun M => M.val.toAtoms) '' models)) := by
  have h := congrArg (fun M : ClosedModel rules => M.val) ((lawfulLabelOrderIso rules).map_sSup models)
  rw [← sSup_image, val_sSup, Set.image_image] at h
  exact h

theorem lawful_label_bot {rules : Rules (LabelAtom Img Assum Lab Exits)} :
    (⊥ : LawfulRegionModel rules).val.toAtoms = closure rules ∅ := label_to_ofAtoms _

theorem lawful_label_top {rules : Rules (LabelAtom Img Assum Lab Exits)} :
    (⊤ : LawfulRegionModel rules).val.toAtoms = Set.univ := label_to_ofAtoms _

end Silmaril.Semantics.Region.Abstract
