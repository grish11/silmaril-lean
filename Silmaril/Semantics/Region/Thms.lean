module

public import Silmaril.Semantics.Region.Defs
import Silmaril.Proofs.Semantics.Region.Core

@[expose] public section
namespace Silmaril.Semantics.Region
universe u v w z
variable {Img : Type u} {Assum : Type v} {Seg : Type w} {Lab : Type z}

theorem bb_sr (M : SegmentRegionModel Img Assum Seg Lab) (h : SegmentRegionLaws M)
    {i : Img} {a : Assum} {s : Seg} {e x : Lab} (hb : M.BB i a s e {x}) :
    M.SR i a {s} e x := (h.sr_iff i a {s} e x).mpr (h.bb_reg i a s e {x} hb)

theorem erase_bb (M : SegmentRegionModel Img Assum Seg Lab) (h : SegmentRegionLaws M)
    {i : Img} {a : Assum} {e : Lab} {x : Finset Lab} (hb : M.eraseBB i a e x) :
    M.erase.Reg i a e x := by
  obtain ⟨s, hs⟩ := hb
  exact ⟨{s}, h.bb_reg i a s e x hs⟩

theorem erase_sr (M : SegmentRegionModel Img Assum Seg Lab) (h : SegmentRegionLaws M)
    (i : Img) (a : Assum) (e x : Lab) :
    M.eraseSR i a e x ↔ M.erase.Reg i a e {x} := Proofs.erase_sr M h i a e x

theorem erase_optional (M : SegmentRegionModel Img Assum Seg Lab) (h : SegmentRegionLaws M)
    (i : Img) (a : Assum) (e : Lab) (x : Option Lab) :
    M.eraseOptional i a e x ↔ M.erase.Reg i a e (optionExits x) :=
  Proofs.erase_optional M h i a e x

/-- Independently erased rows can be glued only when compatible witnesses
exist. `join` carries the proved support/boundary wiring law. -/
theorem erase_glue (M : SegmentRegionModel Img Assum Seg Lab)
    {i : Img} {a : Assum} {e m : Lab} {x y z : Finset Lab}
    (compatible : Finset Seg → Finset Seg → Prop) (combine : Finset Seg → Finset Seg → Finset Seg)
    (join : ∀ ss tt, M.Reg i a ss e x → M.Reg i a tt m y → compatible ss tt →
      M.Reg i a (combine ss tt) e z)
    (witnesses : ∃ ss tt, M.Reg i a ss e x ∧ M.Reg i a tt m y ∧ compatible ss tt) :
    M.erase.Reg i a e z := by
  obtain ⟨ss, tt, hs, ht, hc⟩ := witnesses
  exact ⟨combine ss tt, join ss tt hs ht hc⟩

theorem curry_uncurry (M : RegionModel Img Assum Lab) : M.uncurry.curry = M :=
  Proofs.curry_uncurry M
theorem uncurry_curry (M : RegionModel (Context Img Assum) Unit Lab) :
    M.curry.uncurry = M := Proofs.uncurry_curry M

/-- Record equivalence, with actual inverse laws (including the Unit argument). -/
def contextEquiv : RegionModel Img Assum Lab ≃ RegionModel (Context Img Assum) Unit Lab where
  toFun := RegionModel.uncurry
  invFun := RegionModel.curry
  left_inv := curry_uncurry
  right_inv := uncurry_curry

theorem predicate_curry_uncurry (p : Img → Assum → Prop) :
    Function.curry (Function.uncurry p) = p := rfl
theorem predicate_uncurry_curry (p : Context Img Assum → Prop) :
    Function.uncurry (Function.curry p) = p := rfl

theorem segment_curry_uncurry (M : SegmentRegionModel Img Assum Seg Lab) :
    M.uncurry.curry = M := by cases M; rfl
theorem segment_uncurry_curry (M : SegmentRegionModel (Context Img Assum) Unit Seg Lab) :
    M.curry.uncurry = M := by cases M; rfl

def segmentContextEquiv : SegmentRegionModel Img Assum Seg Lab ≃
    SegmentRegionModel (Context Img Assum) Unit Seg Lab where
  toFun := SegmentRegionModel.uncurry
  invFun := SegmentRegionModel.curry
  left_inv := segment_curry_uncurry
  right_inv := segment_uncurry_curry

theorem uncurry_laws (M : SegmentRegionModel Img Assum Seg Lab) (h : SegmentRegionLaws M) :
    SegmentRegionLaws M.uncurry :=
  ⟨fun c _ => h.bb_seg c.1 c.2, fun c _ => h.bb_reg c.1 c.2,
    fun c _ => h.sr_iff c.1 c.2, fun c _ => h.optional_iff c.1 c.2⟩

theorem erase_uncurry (M : SegmentRegionModel Img Assum Seg Lab) :
    M.uncurry.erase = M.erase.uncurry := rfl

/-- Fixed-context certification survives forgetting the support. -/
def CertifiedSegmentRow.erase {M : SegmentRegionModel Img Assum Seg Lab} {i : Img} {a : Assum}
    (c : CertifiedSegmentRow M i a) : CertifiedRow M.erase i a :=
  ⟨⟨c.row.entry, c.row.exits⟩, ⟨c.row.support, c.valid⟩⟩
theorem erase_segBB_of_bb (M : SegmentRegionModel Img Assum Seg Lab) (h : SegmentRegionLaws M)
    {i : Img} {a : Assum} {e : Lab} {x : Finset Lab} (hb : M.eraseBB i a e x) :
    M.eraseSegBB i a := by
  obtain ⟨s, hs⟩ := hb
  exact ⟨s, h.bb_seg i a s e x hs⟩

/-- A SegBB can acquire an audited boundary through a BB witness, never by
inventing a boundary for the existentially forgotten segment. -/
theorem erase_with_boundary (M : SegmentRegionModel Img Assum Seg Lab) (h : SegmentRegionLaws M)
    {i : Img} {a : Assum} {s : Seg} {e : Lab} {x : Finset Lab}
    (boundary : M.BB i a s e x) : M.erase.Reg i a e x :=
  ⟨{s}, h.bb_reg i a s e x boundary⟩

def CertifiedListRow.certify {Img : Type u} {Assum : Type v} {Seg : Type w} {Lab : Type z}
    [DecidableEq Seg] [DecidableEq Lab] {M : SegmentRegionModel Img Assum Seg Lab}
    {i : Img} {a : Assum} (c : CertifiedListRow M i a) : CertifiedSegmentRow M i a :=
  ⟨c.row.toRow, c.valid⟩

end Silmaril.Semantics.Region
