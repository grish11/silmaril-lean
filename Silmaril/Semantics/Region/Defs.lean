module

public import Mathlib.Data.Finset.Basic

/-! # Raw region judgments

`Assum` is the interface/assumption carrier (called `Int` in the design), not
Lean's integers. Supports and exits are extensional finite sets; a segment
itself may carry an ordered half-open byte or instruction range. `SR` means
one **declared** normal exit, not that this exit is reachable or must occur.
`SegBB` has no boundary. No raw relation implies progress or nonvacuity.
-/

@[expose] public section
namespace Silmaril.Semantics.Region

universe u v w z

abbrev SegBBPred (Img : Type u) (Assum : Type v) (Seg : Type w) :=
  Img → Assum → Seg → Prop
abbrev BBPred (Img : Type u) (Assum : Type v) (Seg : Type w) (Lab : Type z) :=
  Img → Assum → Seg → Lab → Finset Lab → Prop
abbrev SRPred (Img : Type u) (Assum : Type v) (Seg : Type w) (Lab : Type z) :=
  Img → Assum → Finset Seg → Lab → Lab → Prop
abbrev OptionalSRPred (Img : Type u) (Assum : Type v) (Seg : Type w) (Lab : Type z) :=
  Img → Assum → Finset Seg → Lab → Option Lab → Prop
abbrev SegmentRegPred (Img : Type u) (Assum : Type v) (Seg : Type w) (Lab : Type z) :=
  Img → Assum → Finset Seg → Lab → Finset Lab → Prop
abbrev RegPred (Img : Type u) (Assum : Type v) (Lab : Type z) :=
  Img → Assum → Lab → Finset Lab → Prop

/-- Raw signatures impose no laws. -/
structure SegmentRegionModel (Img : Type u) (Assum : Type v) (Seg : Type w) (Lab : Type z) where
  SegBB : SegBBPred Img Assum Seg
  BB : BBPred Img Assum Seg Lab
  SR : SRPred Img Assum Seg Lab
  SR' : OptionalSRPred Img Assum Seg Lab
  Reg : SegmentRegPred Img Assum Seg Lab

structure RegionModel (Img : Type u) (Assum : Type v) (Lab : Type z) where
  Reg : RegPred Img Assum Lab

/-- The optional exit has zero or one declared normal labels. -/
def optionExits {Lab : Type z} : Option Lab → Finset Lab
  | none => ∅
  | some l => {l}

/-- Lawful SR variants are exactly restrictions of Reg, rather than independent
semantic assertions. This does not require exact/reachable exit sets. -/
structure SegmentRegionLaws {Img : Type u} {Assum : Type v} {Seg : Type w} {Lab : Type z}
    (M : SegmentRegionModel Img Assum Seg Lab) : Prop where
  bb_seg : ∀ i a s e x, M.BB i a s e x → M.SegBB i a s
  bb_reg : ∀ i a s e x, M.BB i a s e x → M.Reg i a {s} e x
  sr_iff : ∀ i a ss e x, M.SR i a ss e x ↔ M.Reg i a ss e {x}
  optional_iff : ∀ i a ss e x, M.SR' i a ss e x ↔ M.Reg i a ss e (optionExits x)

structure LawfulSegmentRegionModel (Img : Type u) (Assum : Type v) (Seg : Type w)
    (Lab : Type z) extends SegmentRegionModel Img Assum Seg Lab where
  laws : SegmentRegionLaws toSegmentRegionModel

/-- Build lawful variants from independent BB/SegBB predicates and a general
region relation. SR coherence is derived exactly, not postulated separately. -/
def ofReg {Img : Type u} {Assum : Type v} {Seg : Type w} {Lab : Type z}
    (segBB : SegBBPred Img Assum Seg) (bb : BBPred Img Assum Seg Lab)
    (reg : SegmentRegPred Img Assum Seg Lab)
    (bbSeg : ∀ i a s e x, bb i a s e x → segBB i a s)
    (bbReg : ∀ i a s e x, bb i a s e x → reg i a {s} e x) :
    LawfulSegmentRegionModel Img Assum Seg Lab where
  SegBB := segBB
  BB := bb
  Reg := reg
  SR i a ss e x := reg i a ss e {x}
  SR' i a ss e x := reg i a ss e (optionExits x)
  laws := ⟨bbSeg, bbReg, fun _ _ _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl⟩

/-- A row is exportable data; certification is a separate proof. -/
structure SegmentRow (Seg : Type w) (Lab : Type z) where
  support : Finset Seg
  entry : Lab
  exits : Finset Lab

structure Row (Lab : Type z) where
  entry : Lab
  exits : Finset Lab

structure CertifiedSegmentRow {Img : Type u} {Assum : Type v} {Seg : Type w} {Lab : Type z}
    (M : SegmentRegionModel Img Assum Seg Lab) (image : Img) (iface : Assum) where
  row : SegmentRow Seg Lab
  valid : M.Reg image iface row.support row.entry row.exits

structure CertifiedRow {Img : Type u} {Assum : Type v} {Lab : Type z}
    (M : RegionModel Img Assum Lab) (image : Img) (iface : Assum) where
  row : Row Lab
  valid : M.Reg image iface row.entry row.exits

/-- Ordered serialization adapter. The order is presentation data only;
judgments always consume its extensional `toFinset` projections. -/
structure ListRow (Seg : Type w) (Lab : Type z) where
  support : List Seg
  entry : Lab
  exits : List Lab
  deriving Repr

def ListRow.toRow {Seg : Type w} {Lab : Type z} [DecidableEq Seg] [DecidableEq Lab]
    (r : ListRow Seg Lab) : SegmentRow Seg Lab :=
  ⟨r.support.toFinset, r.entry, r.exits.toFinset⟩

/-- Candidate data and certification remain separate in an exporter. The
proof is erased by Lean; no proof imports are needed to serialize ListRow. -/
structure CertifiedListRow {Img : Type u} {Assum : Type v} {Seg : Type w} {Lab : Type z}
    [DecidableEq Seg] [DecidableEq Lab] (M : SegmentRegionModel Img Assum Seg Lab)
    (image : Img) (iface : Assum) where
  row : ListRow Seg Lab
  valid : M.Reg image iface row.support.toFinset row.entry row.exits.toFinset

/-- Every segment variant has its own existential forgetting. SegBB remains
unlabelled: a boundary must be supplied before constructing a labelled row. -/
def SegmentRegionModel.erase {Img : Type u} {Assum : Type v} {Seg : Type w} {Lab : Type z}
    (M : SegmentRegionModel Img Assum Seg Lab) : RegionModel Img Assum Lab :=
  ⟨fun i a e x => ∃ ss, M.Reg i a ss e x⟩

def SegmentRegionModel.eraseBB {Img : Type u} {Assum : Type v} {Seg : Type w} {Lab : Type z}
    (M : SegmentRegionModel Img Assum Seg Lab) : RegPred Img Assum Lab :=
  fun i a e x => ∃ s, M.BB i a s e x

def SegmentRegionModel.eraseSegBB {Img : Type u} {Assum : Type v} {Seg : Type w} {Lab : Type z}
    (M : SegmentRegionModel Img Assum Seg Lab) (i : Img) (a : Assum) : Prop :=
  ∃ s, M.SegBB i a s

def SegmentRegionModel.eraseSR {Img : Type u} {Assum : Type v} {Seg : Type w} {Lab : Type z}
    (M : SegmentRegionModel Img Assum Seg Lab) (i : Img) (a : Assum) (e x : Lab) : Prop :=
  ∃ ss, M.SR i a ss e x

def SegmentRegionModel.eraseOptional {Img : Type u} {Assum : Type v} {Seg : Type w} {Lab : Type z}
    (M : SegmentRegionModel Img Assum Seg Lab) (i : Img) (a : Assum) (e : Lab)
    (x : Option Lab) : Prop := ∃ ss, M.SR' i a ss e x

/-- Bundled context: the image and interface move together. -/
abbrev Context (Img : Type u) (Assum : Type v) := Img × Assum

/-- Genuine model-record curry/uncurry maps; inverse laws are in Thms. -/
def RegionModel.uncurry {Img : Type u} {Assum : Type v} {Lab : Type z}
    (M : RegionModel Img Assum Lab) : RegionModel (Context Img Assum) Unit Lab :=
  ⟨fun c _ => M.Reg c.1 c.2⟩

def RegionModel.curry {Img : Type u} {Assum : Type v} {Lab : Type z}
    (M : RegionModel (Context Img Assum) Unit Lab) : RegionModel Img Assum Lab :=
  ⟨fun i a => M.Reg (i, a) ()⟩

def SegmentRegionModel.uncurry {Img : Type u} {Assum : Type v} {Seg : Type w} {Lab : Type z}
    (M : SegmentRegionModel Img Assum Seg Lab) :
    SegmentRegionModel (Context Img Assum) Unit Seg Lab where
  SegBB c _ := M.SegBB c.1 c.2
  BB c _ := M.BB c.1 c.2
  SR c _ := M.SR c.1 c.2
  SR' c _ := M.SR' c.1 c.2
  Reg c _ := M.Reg c.1 c.2

def SegmentRegionModel.curry {Img : Type u} {Assum : Type v} {Seg : Type w} {Lab : Type z}
    (M : SegmentRegionModel (Context Img Assum) Unit Seg Lab) :
    SegmentRegionModel Img Assum Seg Lab where
  SegBB i a := M.SegBB (i, a) ()
  BB i a := M.BB (i, a) ()
  SR i a := M.SR (i, a) ()
  SR' i a := M.SR' (i, a) ()
  Reg i a := M.Reg (i, a) ()

/-- Unknown/partial is Top, never an empty finite set. -/
inductive Targets (Lab : Type z) where
  | finite (labels : Finset Lab)
  | top

def Targets.Allows {Lab : Type z} : Targets Lab → Lab → Prop
  | .finite xs, l => l ∈ xs
  | .top, _ => True

/-- Optional helpers make no soundness claim without a semantic certificate.
Entry lookup can be partial and independent of the image. -/
structure Helpers (Img : Type u) (Assum : Type v) (Seg : Type w) (Lab : Type z)
    (Term : Type*) where
  entry : Seg → Option Lab
  exits : Img → Assum → Seg → Targets Lab
  exitsAt : Img → Assum → Lab → Seg → Targets Lab
  terminator : Img → Seg → Option Term
  targets : Img → Assum → Term → Targets Lab

def Helpers.uncurry {Img : Type u} {Assum : Type v} {Seg : Type w} {Lab : Type z}
    {Term : Type*} (h : Helpers Img Assum Seg Lab Term) :
    Helpers (Context Img Assum) Unit Seg Lab Term where
  entry := h.entry
  exits c _ := h.exits c.1 c.2
  exitsAt c _ := h.exitsAt c.1 c.2
  terminator c := h.terminator c.1
  targets c _ := h.targets c.1 c.2

end Silmaril.Semantics.Region
