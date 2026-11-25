module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Model.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Model.Validity.Defs
public import Silmaril.SSA.Isotope.LetIter.Categorical.Coherence.FreeContext.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.AbortSequence.Thms

/-! # Coherence and categorical validity of the repaired LetIter model -/

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.ValidityProofs

open CategoryTheory
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.LocallyNameless (AbortEquiv Derivation Tm)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]
variable (pe : ε)

local notation "Jq" => repairedValues (τ := τ) (Φ := Φ) pe
local notation "TyModel" => typeModel (τ := τ) (Φ := Φ) pe

theorem repairedTypingCoherent_empty :
    letI := repairedInstructionModel (τ := τ) (Φ := Φ) pe
    TypingCoherent (ν := Empty) Jq TyModel Φ := by
  let := repairedInstructionModel (τ := τ) (Φ := Φ) pe
  apply typingCoherent_empty_of_nil (Jq) (TyModel)
  intro n β t A d e
  exact repairedDenoteInSyntax_typing_nil pe d e

/-- Empty-free-context validity over the coherent model class is exactly abort equivalence. -/
theorem abortEquiv_iff_repairedCategoricalValidity {n : Nat} {β : BoundCtx τ n}
    {a b : Tm Empty Φ n} {A : τ}
    (da : Derivation Φ (Ctx.nil : Ctx Empty τ) β a A)
    (db : Derivation Φ (Ctx.nil : Ctx Empty τ) β b A) :
    AbortEquiv pe (Ctx.nil : Ctx Empty τ) β a b A ↔ RepairedCategoricalValidity pe da db := by
  constructor
  · intro h V C catV catC cart symm pre symmC copV copC distV distC it elgot J strong central model inst
      coherent shared pureInstr
    exact denote_abortEquiv_of_coherent_shared_tensor J model coherent shared pureInstr h da db
  · intro valid
    let := repairedInstructionModel (τ := τ) (Φ := Φ) pe
    have eq := valid (Jq) (TyModel) (repairedTypingCoherent_empty pe)
      (repairedValues_sharedTensor pe) (repairedInstructionModel_pure pe)
    exact (repairedDenoteInSyntax_eq_iff pe da db).mp eq

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.ValidityProofs
