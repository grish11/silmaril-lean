module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Model.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Model.Validity.Defs
public import Silmaril.SSA.Isotope.LetIter.AbortSequence.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.CategoryValidity

/-! # Soundness and reflection for abort-extended LetIter at empty free context -/

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

open CategoryTheory
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.LocallyNameless (AbortEquiv Derivation Tm)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]
variable (pe : ε)

local notation "Jq" => repairedValues (τ := τ) (Φ := Φ) pe
local notation "TyModel" => typeModel (τ := τ) (Φ := Φ) pe

/-- The repaired model is typing-coherent at every free context over the empty name type. -/
theorem repairedTypingCoherent_empty :
    letI := repairedInstructionModel (τ := τ) (Φ := Φ) pe
    TypingCoherent (ν := Empty) Jq TyModel Φ :=
  ValidityProofs.repairedTypingCoherent_empty pe

/-- Empty-free-context validity over the coherent model class is exactly abort equivalence. -/
theorem abortEquiv_iff_repairedCategoricalValidity {n : Nat} {β : BoundCtx τ n}
    {a b : Tm Empty Φ n} {A : τ}
    (da : Derivation Φ (Ctx.nil : Ctx Empty τ) β a A)
    (db : Derivation Φ (Ctx.nil : Ctx Empty τ) β b A) :
    AbortEquiv pe (Ctx.nil : Ctx Empty τ) β a b A ↔ RepairedCategoricalValidity pe da db :=
  ValidityProofs.abortEquiv_iff_repairedCategoricalValidity pe da db

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
