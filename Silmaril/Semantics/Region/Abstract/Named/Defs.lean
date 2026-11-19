module

public import Silmaril.Semantics.Region.Abstract.Defs

/-! # The named region predicates over abstract support/exit carriers

Support and Exits have no operations, decidable equality or enumerations.
They need not be sets, finite collections, memory ranges or graphs. Optional
coherence laws receive all boundary operations explicitly. Helpers and
semantic interpretations are absent from the model and law core.
-/

@[expose] public section
namespace Silmaril.Semantics.Region.Abstract
universe u v w x y z

abbrev SegBBPred (Img : Type u) (Assum : Type v) (Seg : Type w) := Img → Assum → Seg → Prop
abbrev BBPred (Img : Type u) (Assum : Type v) (Seg : Type w) (Lab : Type x) (Exits : Type y) :=
  Img → Assum → Seg → Lab → Exits → Prop
abbrev SRPred (Img : Type u) (Assum : Type v) (Support : Type w) (Lab : Type x) :=
  Img → Assum → Support → Lab → Lab → Prop
abbrev OptionalSRPred (Img : Type u) (Assum : Type v) (Support : Type w) (Lab : Type x) :=
  Img → Assum → Support → Lab → Option Lab → Prop
abbrev SegmentRegPred (Img : Type u) (Assum : Type v) (Support : Type w) (Lab : Type x) (Exits : Type y) :=
  Img → Assum → Support → Lab → Exits → Prop
abbrev RegPred (Img : Type u) (Assum : Type v) (Lab : Type w) (Exits : Type x) :=
  Img → Assum → Lab → Exits → Prop

structure SegmentRegionModel (Img : Type u) (Assum : Type v) (Seg : Type w)
    (Support : Type x) (Lab : Type y) (Exits : Type z) where
  SegBB : SegBBPred Img Assum Seg
  BB : BBPred Img Assum Seg Lab Exits
  SR : SRPred Img Assum Support Lab
  SR' : OptionalSRPred Img Assum Support Lab
  Reg : SegmentRegPred Img Assum Support Lab Exits

structure RegionModel (Img : Type u) (Assum : Type v) (Lab : Type w) (Exits : Type x) where
  Reg : RegPred Img Assum Lab Exits

/-- Typed atoms, rather than an untyped encoding with well-formedness tests. -/
inductive SegmentAtom (Img : Type u) (Assum : Type v) (Seg : Type w)
    (Support : Type x) (Lab : Type y) (Exits : Type z) where
  | segBB (i : Img) (a : Assum) (s : Seg)
  | bb (i : Img) (a : Assum) (s : Seg) (e : Lab) (xs : Exits)
  | sr (i : Img) (a : Assum) (ss : Support) (e exit : Lab)
  | optional (i : Img) (a : Assum) (ss : Support) (e : Lab) (exit : Option Lab)
  | reg (i : Img) (a : Assum) (ss : Support) (e : Lab) (xs : Exits)

structure LabelAtom (Img : Type u) (Assum : Type v) (Lab : Type w) (Exits : Type x) where
  image : Img
  iface : Assum
  entry : Lab
  exits : Exits

variable {Img : Type u} {Assum : Type v} {Seg : Type w} {Support : Type x} {Lab : Type y} {Exits : Type z}

def SegmentRegionModel.toAtoms (M : SegmentRegionModel Img Assum Seg Support Lab Exits) :
    RawModel (SegmentAtom Img Assum Seg Support Lab Exits) := .ofPred fun
  | .segBB i a s => M.SegBB i a s
  | .bb i a s e xs => M.BB i a s e xs
  | .sr i a ss e exit => M.SR i a ss e exit
  | .optional i a ss e exit => M.SR' i a ss e exit
  | .reg i a ss e xs => M.Reg i a ss e xs

def SegmentRegionModel.ofAtoms (M : RawModel (SegmentAtom Img Assum Seg Support Lab Exits)) :
    SegmentRegionModel Img Assum Seg Support Lab Exits where
  SegBB i a s := (.segBB i a s) ∈ M
  BB i a s e xs := (.bb i a s e xs) ∈ M
  SR i a ss e exit := (.sr i a ss e exit) ∈ M
  SR' i a ss e exit := (.optional i a ss e exit) ∈ M
  Reg i a ss e xs := (.reg i a ss e xs) ∈ M

def RegionModel.toAtoms (M : RegionModel Img Assum Lab Exits) : RawModel (LabelAtom Img Assum Lab Exits) :=
  .ofPred fun j => M.Reg j.image j.iface j.entry j.exits

def RegionModel.ofAtoms (M : RawModel (LabelAtom Img Assum Lab Exits)) : RegionModel Img Assum Lab Exits :=
  ⟨fun i a e xs => ⟨i, a, e, xs⟩ ∈ M⟩

/-- Optional boundary operations; nothing about their implementation is assumed. -/
structure BoundaryOps (Seg : Type w) (Support : Type x) (Lab : Type y) (Exits : Type z) where
  singletonSupport : Seg → Support
  singletonExit : Lab → Exits
  optionalExit : Option Lab → Exits

/-- Both directions of coherence are positive, single-premise rules. -/
inductive CoherenceRule (ops : BoundaryOps Seg Support Lab Exits) :
    Rule (SegmentAtom Img Assum Seg Support Lab Exits) → Prop
  | bb_seg (i a s e xs) : CoherenceRule ops ⟨{.bb i a s e xs}, .segBB i a s⟩
  | bb_reg (i a s e xs) : CoherenceRule ops ⟨{.bb i a s e xs}, .reg i a (ops.singletonSupport s) e xs⟩
  | sr_reg (i a ss e exit) : CoherenceRule ops ⟨{.sr i a ss e exit}, .reg i a ss e (ops.singletonExit exit)⟩
  | reg_sr (i a ss e exit) : CoherenceRule ops ⟨{.reg i a ss e (ops.singletonExit exit)}, .sr i a ss e exit⟩
  | optional_reg (i a ss e exit) : CoherenceRule ops
      ⟨{.optional i a ss e exit}, .reg i a ss e (ops.optionalExit exit)⟩
  | reg_optional (i a ss e exit) : CoherenceRule ops
      ⟨{.reg i a ss e (ops.optionalExit exit)}, .optional i a ss e exit⟩

def CoherenceRules (ops : BoundaryOps Seg Support Lab Exits) :
    Rules (SegmentAtom Img Assum Seg Support Lab Exits) := {r | CoherenceRule ops r}

/-- Presentation of the same positive coherence rules in the usual fields. -/
structure SegmentRegionLaws (ops : BoundaryOps Seg Support Lab Exits)
    (M : SegmentRegionModel Img Assum Seg Support Lab Exits) : Prop where
  bb_seg : ∀ i a s e xs, M.BB i a s e xs → M.SegBB i a s
  bb_reg : ∀ i a s e xs, M.BB i a s e xs → M.Reg i a (ops.singletonSupport s) e xs
  sr_iff : ∀ i a ss e exit, M.SR i a ss e exit ↔ M.Reg i a ss e (ops.singletonExit exit)
  optional_iff : ∀ i a ss e exit, M.SR' i a ss e exit ↔ M.Reg i a ss e (ops.optionalExit exit)

/-- Arbitrary fixed rules, not just coherence; a client may add positive
composition rules whose wiring and boundary side conditions are fixed. -/
abbrev LawfulSegmentRegionModel (rules : Rules (SegmentAtom Img Assum Seg Support Lab Exits)) :=
  {M : SegmentRegionModel Img Assum Seg Support Lab Exits // Closed rules M.toAtoms}

abbrev LawfulRegionModel (rules : Rules (LabelAtom Img Assum Lab Exits)) :=
  {M : RegionModel Img Assum Lab Exits // Closed rules M.toAtoms}

/-- Fixed two-premise gluing schema. Compatibility is a property of typed
atoms, not of which witnesses happen to be certified by a model. -/
def glueRules {Atom : Type u} (compatible : Atom → Atom → Atom → Prop) : Rules Atom :=
  {r | ∃ left right head, compatible left right head ∧ r = ⟨{left, right}, head⟩}

end Silmaril.Semantics.Region.Abstract
