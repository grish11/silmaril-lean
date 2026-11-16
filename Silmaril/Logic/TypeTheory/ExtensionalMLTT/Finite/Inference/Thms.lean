module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Inference.Defs

public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

open CategoryTheory

/-- Fixed-stage packaging retains exactly the actual bounded derivations. -/
theorem boundedInferenceSystem_derivable (levels : ℕ) (j : EJdg) :
    Nonempty ((boundedInferenceSystem levels).Derivation j) ↔ ECtx.JEqB levels ∅ j.Γ j.A j.a j.b :=
  ⟨fun ⟨h⟩ => h.down, fun h => ⟨⟨h⟩⟩⟩

/-- Existential-stage packaging retains exactly actual proofs with a common finite budget. -/
theorem finiteProofInferenceSystem_derivable (j : EJdg) :
    Nonempty (finiteProofInferenceSystem.Derivation j) ↔
      ∃ levels, ECtx.JEqB levels ∅ j.Γ j.A j.a j.b :=
  ⟨fun ⟨h⟩ => h.down, fun h => ⟨⟨h⟩⟩⟩

/-- Fixed rule-budget inclusion is the identity at an unchanged stage. -/
theorem boundedInferenceInclusion_refl (n : ℕ) :
    boundedInferenceInclusion (Nat.le_refl n) = 𝟙 (boundedInferenceSystem n) := rfl

/-- Fixed rule-budget inclusions compose on actual derivations. -/
theorem boundedInferenceInclusion_trans {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k) :
    boundedInferenceInclusion h ≫ boundedInferenceInclusion h' =
      boundedInferenceInclusion (h.trans h') := rfl

/-- Each fixed-budget inclusion commutes with the map into finite proofs. -/
theorem boundedToFiniteProofInference_naturality {n m : ℕ} (h : n ≤ m) :
    boundedInferenceInclusion h ≫ boundedToFiniteProofInference m = boundedToFiniteProofInference n := rfl

/-- Erasure retains the judgment and provides an actual original extensional derivation. -/
theorem finiteProofInferenceErasure_derivable (j : EJdg)
    (d : finiteProofInferenceSystem.Derivation j) : ECtx.JEqH ∅ j.Γ j.A j.a j.b :=
  (finiteProofInferenceErasure.mapDerivation d).down

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
