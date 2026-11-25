module

public import Silmaril.SSA.Isotope.LambdaSSA.Subtyping.Categorical.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Subtyping.Monadic.Thms

/-! # The proof-relevant λSSA Kleisli model -/

@[expose] public section

universe u v q r

namespace Silmaril.Isotope.LambdaSSA.Subtyping.Semantics.Agreement

open CategoryTheory Silmaril.Elgot
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (typeJ ofTypeModel ofInstructionModel)

variable {τ : Type u} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ] [TypeModel.{u, v} τ]
  {Φ : Type q} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε] [Bot ε]
  {m : Type v → Type v} [Monad m] [LawfulMonad m] [InstructionModel Φ τ ε m]

/-- The categorical term interpretation in the proof-relevant Kleisli model. -/
noncomputable def categoricalTermDenote {Γ : VCtx τ} {t : Tm Φ} {A : τ}
    (h : Tm.HasType Γ t A) :=
  letI := ofInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  Categorical.denote (typeJ (m := m)) (ofTypeModel (τ := τ)) h

variable [Iterate m] [LawfulElgotMonad m]

/-- Coherence of categorical witnesses for each fixed region typing derivation. -/
noncomputable def RegionCoherent : Prop :=
  letI := ofInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  Categorical.RegionTypingCoherent (Φ := Φ) (typeJ (m := m)) (ofTypeModel (τ := τ))

/-- The chosen categorical region interpretation in the proof-relevant Kleisli model. -/
noncomputable def categoricalRegionDenote {Γ : VCtx τ} {region : Region Φ} {L : LCtx τ}
    (h : Region.HasType Γ region L) :=
  letI := ofInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  Categorical.denoteRegion (typeJ (m := m)) (ofTypeModel (τ := τ)) h

end Silmaril.Isotope.LambdaSSA.Subtyping.Semantics.Agreement
