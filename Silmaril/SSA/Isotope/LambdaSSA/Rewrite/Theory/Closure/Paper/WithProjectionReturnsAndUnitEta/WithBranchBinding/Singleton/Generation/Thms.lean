module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Singleton.Generation.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.NormalizedRawGeneration

/-! # Branch normalization preserves and reflects literal raw generation -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Singleton.Generation

open CategoryTheory
open Paper.Extension.Singleton (ofType ofRegion)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (S : NormalizedSeed τ Φ) {A B : τ}

/-- The same generators act on the raw syntax classes and on the guarded classes. -/
theorem generated_iff_normalize (f : RawHom S A B) :
    Generated S f ↔ Extension.Singleton.Generation.Generated S.step (normalizeHom S f) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.NormalizedRawGeneration.generated_iff_normalize S f

/-- Restrict the strict homwise comparison to generated arrows. -/
noncomputable def generatedHomEquiv :
    {f : RawHom S A B // Generated S f} ≃
      {g : ofType S.step A ⟶ ofType S.step B // Extension.Singleton.Generation.Generated S.step g} :=
  (homEquiv S A B).subtypeEquiv (generated_iff_normalize S)

/-- For an already guarded representative, the raw side is its literal class. -/
theorem generated_rawClass_iff {r : Region Φ} (hr : ValueBranches [A] r [B]) :
    Generated S (rawClass S hr.hasType) ↔
      Extension.Singleton.Generation.Generated S.step (ofRegion S.step hr) :=
  (generated_iff_normalize S _).trans (iff_of_eq (congrArg _ (normalize_guarded S hr)))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Singleton.Generation
