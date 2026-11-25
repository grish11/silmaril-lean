module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.Reification.Thms

/-! # Reflecting native typing derivations in the projected computation homs -/

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

open Silmaril.Isotope.LetIter.LocallyNameless (AbortEquiv Derivation Tm)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]

local instance : Thesis.LambdaIter.TypeFormers τ := Bridge.thesisTypeFormers τ
local instance : Thesis.LambdaIter.HasTy Φ τ := Bridge.thesisHasTy Φ τ

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem repairedProjection_packedNative_eq_iff_proof (pe : ε)
    {n : Nat} {β : BoundCtx τ n} {a b : Tm Empty Φ n} {A : τ}
    (da : Derivation Φ (Ctx.nil : Ctx Empty τ) β a A)
    (db : Derivation Φ (Ctx.nil : Ctx Empty τ) β b A) :
    (repairedProjection pe).map (packedNative pe da) =
      (repairedProjection pe).map (packedNative pe db) ↔
      AbortEquiv pe (Ctx.nil : Ctx Empty τ) β a b A := by
  obtain ⟨ha⟩ := (Bridge.hasType_iff (Bridge.TypeCompat.canonical τ)
    (Bridge.InstrCompat.canonical Φ τ)).mp da.toHasType
  obtain ⟨hb⟩ := (Bridge.hasType_iff (Bridge.TypeCompat.canonical τ)
    (Bridge.InstrCompat.canonical Φ τ)).mp db.toHasType
  rw [repairedProjection_map_eq_iff, packedNative_repaired_reification pe da ha,
    packedNative_repaired_reification pe db hb]
  simpa only [RepairedEqv, Bridge.ofThesis_toThesis] using
    repairedHomClass_packedArrow_eq_iff pe (β := β) ha hb

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
