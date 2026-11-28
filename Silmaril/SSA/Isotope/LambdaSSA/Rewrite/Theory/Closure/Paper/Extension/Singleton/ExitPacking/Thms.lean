module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.CfgEta.Thms

/-! # Exit packing reflects every contextual extension

A guarded region with one capture and any ordered exits is determined, in
any extension of the Paper relation, by its packed singleton arrow.
-/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

open Silmaril.Isotope.LambdaSSA (VCtx LCtx)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

/-- Tagging the exits and decoding them again is an inherited equation. -/
theorem unpack_packExits {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ} (hr : ValueBranches Γ r L) :
    Extension.Eqv Seed Γ (r.packExits.lsubst (fun _ => unpackExits L)) r L :=
  .paper (.cfgEta (.native hr.unpack_packExits))

/-- Two guarded regions are equivalent exactly when their packed singleton
arrows are equal. The exit list is arbitrary. -/
theorem ofRegion_packExits_eq_iff {X : τ} {L : LCtx τ} {r s : Region Φ}
    (hr : ValueBranches [X] r L) (hs : ValueBranches [X] s L) :
    ofRegion Seed hr.packExits = ofRegion Seed hs.packExits ↔ Extension.Eqv Seed [X] r s L := by
  rw [ofRegion_eq_iff]
  refine ⟨fun h => ?_, fun h => .lsubstPost h hr hs
    (fun _ _ hi => (packExits_valueFamily [X] L hi).hasType)⟩
  exact (unpack_packExits Seed hr).symm.trans ((Extension.Eqv.lsubstPost h hr.packExits hs.packExits
    (fun _ _ hi => (unpackExits_valueFamily [X] L hi).hasType)).trans (unpack_packExits Seed hs))

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
