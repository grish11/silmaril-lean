module

public import Silmaril.ProofFormats.LeanNDJSON.MLTT.Bounded.Defs
public import Silmaril.ProofFormats.LeanNDJSON.MLTT.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Logic.Thms

public section

namespace Silmaril.ProofFormats.LeanNDJSON.MLTT

open CategoryTheory Silmaril.Logic.Institution.Metatheory
open Silmaril.Logic.TypeTheory.ExtensionalMLTT

universe u

variable {Name : Type} {S : Signature Name}

/-- Forgetting derivations recovers the fixed-budget institution. -/
@[simp] theorem fixedLogic_toInst (Name : Type) (levels : Nat) :
    (fixedLogic.{u} Name levels).toInst = fixedBudget.{u} Name levels := rfl

/-- The finite MLTT comparison also reflects derivations between translated
events. -/
theorem toFiniteMLTTLogic_conservative (Name : Type) (levels : Nat) :
    (toFiniteMLTTLogic.{u} Name levels).Conservative :=
  fun _ _ _ h => h

/-- The fixed-bandwidth logic borrows soundness from the actual finite MLTT
logic via the identity tower reduct. -/
theorem fixedLogic_sound (Name : Type) (levels : Nat) : (fixedLogic.{u} Name levels).Sound :=
  (toFiniteMLTTLogic.{u} Name levels).sound_of_sound
    (toFiniteMLTT_modelExpansive Name levels) (Finite.logic_sound levels)

/-- The variable-bandwidth model validates the fixed logic at its own budget
under satisfied event hypotheses. -/
theorem BudgetModel.satisfies_of_fixed_derivation (M : BudgetModel.{u})
    {H : Set (BoundedSentence M.levels S)} {s : BoundedSentence M.levels S}
    (proof : fixedDerives H s) (hH : ∀ q ∈ H, M.Satisfies q.val) :
    M.Satisfies s.val :=
  ⟨s.property, fixedLogic_sound Name M.levels S H s proof (Discrete.mk M.tower)
    (fun q hq => (hH q hq).2)⟩

end Silmaril.ProofFormats.LeanNDJSON.MLTT
