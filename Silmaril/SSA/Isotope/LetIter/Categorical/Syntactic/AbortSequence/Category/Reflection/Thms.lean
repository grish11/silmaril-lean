module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.Reification.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.CategoryReflection

/-! # Reflection in the projected LetIter computation homs -/

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

open Silmaril.Isotope.LetIter.LocallyNameless (AbortEquiv Derivation Tm)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]

/-- Projected native packed denotations agree exactly when the terms are abort-equivalent.
This statement is for an empty free context and any finite bound context. -/
theorem repairedProjection_packedNative_eq_iff (pe : ε)
    {n : Nat} {β : BoundCtx τ n} {a b : Tm Empty Φ n} {A : τ}
    (da : Derivation Φ (Ctx.nil : Ctx Empty τ) β a A)
    (db : Derivation Φ (Ctx.nil : Ctx Empty τ) β b A) :
    (repairedProjection pe).map (packedNative pe da) =
      (repairedProjection pe).map (packedNative pe db) ↔
      AbortEquiv pe (Ctx.nil : Ctx Empty τ) β a b A :=
  repairedProjection_packedNative_eq_iff_proof pe da db

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
