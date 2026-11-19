module

public import Silmaril.Semantics.Region.Defs

@[expose] public section
namespace Silmaril.Semantics.Region.Proofs
universe u v w z
variable {Img : Type u} {Assum : Type v} {Seg : Type w} {Lab : Type z}

theorem erase_sr (M : SegmentRegionModel Img Assum Seg Lab) (h : SegmentRegionLaws M)
    (i : Img) (a : Assum) (e x : Lab) :
    M.eraseSR i a e x ↔ M.erase.Reg i a e {x} := by
  constructor
  · rintro ⟨ss, hs⟩
    exact ⟨ss, (h.sr_iff i a ss e x).mp hs⟩
  · rintro ⟨ss, hs⟩
    exact ⟨ss, (h.sr_iff i a ss e x).mpr hs⟩

theorem erase_optional (M : SegmentRegionModel Img Assum Seg Lab) (h : SegmentRegionLaws M)
    (i : Img) (a : Assum) (e : Lab) (x : Option Lab) :
    M.eraseOptional i a e x ↔ M.erase.Reg i a e (optionExits x) := by
  constructor
  · rintro ⟨ss, hs⟩
    exact ⟨ss, (h.optional_iff i a ss e x).mp hs⟩
  · rintro ⟨ss, hs⟩
    exact ⟨ss, (h.optional_iff i a ss e x).mpr hs⟩

theorem curry_uncurry (M : RegionModel Img Assum Lab) : M.uncurry.curry = M := by
  cases M
  rfl

theorem uncurry_curry (M : RegionModel (Context Img Assum) Unit Lab) :
    M.curry.uncurry = M := by
  cases M with
  | mk r =>
    rfl
end Silmaril.Semantics.Region.Proofs
