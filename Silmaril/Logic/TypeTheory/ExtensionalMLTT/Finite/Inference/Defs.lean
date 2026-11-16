module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Derivation.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inference.Thms

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

open CategoryTheory Silmaril.Logic.Metatheory

/-- Actual closed extensional derivations at one common finite rule budget. -/
def boundedInferenceSystem (levels : ℕ) : InferenceSystemCat where
  Conclusion := EJdg
  Derivation j := PLift (ECtx.JEqB levels ∅ j.Γ j.A j.a j.b)

/-- Actual closed extensional derivations that inhabit some finite rule budget. -/
def finiteProofInferenceSystem : InferenceSystemCat where
  Conclusion := EJdg
  Derivation j := PLift (∃ levels, ECtx.JEqB levels ∅ j.Γ j.A j.a j.b)

/-- Enlarge the rule budget of the actual derivation without changing its judgment. -/
def boundedInferenceInclusion {n m : ℕ} (h : n ≤ m) :
    boundedInferenceSystem n ⟶ boundedInferenceSystem m where
  map := id
  mapDerivation d := ⟨d.down.weakenLevels h⟩

/-- Every fixed-budget derivation inhabits the actual finite-proof object. -/
def boundedToFiniteProofInference (levels : ℕ) :
    boundedInferenceSystem levels ⟶ finiteProofInferenceSystem where
  map := id
  mapDerivation d := ⟨levels, d.down⟩

/-- Erase the witnessed finite rule budget to the existing actual closed calculus. -/
def finiteProofInferenceErasure : finiteProofInferenceSystem ⟶ closedInferenceSystem where
  map := id
  mapDerivation d := ⟨by obtain ⟨levels, h⟩ := d.down; exact h.forget⟩

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
