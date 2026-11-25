module

public import Silmaril.SSA.Isotope.LambdaSSA.Subtyping.Monadic.Defs

import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Subtyping.Monadic

/-! # Structural witnesses for the subtyped λSSA monadic semantics -/

public section

namespace Silmaril.Isotope.LambdaSSA.Subtyping.Semantics.Monadic

open CategoryTheory CategoryTheory.Limits Silmaril.Elgot
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics

universe u v q r

variable {τ : Type u} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ] [TypeModel.{u, v} τ]
variable {Φ : Type q} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [InstructionModel Φ τ ε m]

omit [LawfulMonad m] in
theorem denote_spec {Γ : VCtx τ} {t : LambdaSSA.Tm Φ} {A : τ}
    (h : Tm.HasType Γ t A) :
    Denotes ε h (denote (ε := ε) (m := m) h) :=
  denote_spec_proof h

variable [Iterate m] [LawfulElgotMonad m]

omit [LawfulMonad m] [LawfulElgotMonad m] in
theorem regionDenotes_exists {Γ : VCtx τ} {region : LambdaSSA.Region Φ}
    {L : LCtx τ} (h : Region.HasType Γ region L) :
    ∃ f, RegionDenotes (m := m) ε h f :=
  regionDenotes_exists_proof h

noncomputable def denoteRegion {Γ : VCtx τ} {region : LambdaSSA.Region Φ}
    {L : LCtx τ} (h : Region.HasType Γ region L) : Env Γ → m (LabelDen L) :=
  (regionDenotes_exists (ε := ε) (m := m) h).choose

omit [LawfulMonad m] [LawfulElgotMonad m] in
theorem denoteRegion_spec {Γ : VCtx τ} {region : LambdaSSA.Region Φ}
    {L : LCtx τ} (h : Region.HasType Γ region L) :
    RegionDenotes ε h (denoteRegion (ε := ε) (m := m) h) :=
  (regionDenotes_exists (ε := ε) (m := m) h).choose_spec

end Silmaril.Isotope.LambdaSSA.Subtyping.Semantics.Monadic
