module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Model.LocallySmallValidity.Defs
public import Silmaril.SSA.Isotope.LetIter.AbortSequence.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.CategoryLocallySmallValidity

/-! # Soundness and reflection at the locally small universe split -/

public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

open Silmaril.Isotope.LetIter.LocallyNameless (AbortEquiv Derivation Tm)

variable {τ Φ ε : Type} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] (pe : ε)

/-- For a small LetIter signature, validity in the coherent shared-tensor model
class with `Type 1` objects and `Type 0` homs is exactly abort equivalence. -/
theorem abortEquiv_iff_repairedLocallySmallValidity
    {n : Nat} {β : BoundCtx τ n} {a b : Tm Empty Φ n} {A : τ}
    (da : Derivation Φ (Ctx.nil : Ctx Empty τ) β a A)
    (db : Derivation Φ (Ctx.nil : Ctx Empty τ) β b A) :
    AbortEquiv pe (Ctx.nil : Ctx Empty τ) β a b A ↔ RepairedLocallySmallValidity pe da db :=
  LocallySmallValidityProofs.abortEquiv_iff_repairedLocallySmallValidity pe da db

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
