module

public import Silmaril.SSA.Isotope.LambdaSSA.Subtyping.Kleisli.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Subtyping.Kleisli

/-! # Agreement of the proof-relevant λSSA denotations -/

public section

universe u v q r

namespace Silmaril.Isotope.LambdaSSA.Subtyping.Semantics.Agreement

open CategoryTheory Silmaril.Elgot
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (typeJ ofTypeModel ofInstructionModel)
open LambdaSSA.Semantics.Agreement (envToCategorical)

variable {τ : Type u} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ] [TypeModel.{u, v} τ]
  {Φ : Type q} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε] [Bot ε]
  {m : Type v → Type v} [Monad m] [LawfulMonad m] [InstructionModel Φ τ ε m]

/-- For a fixed subtyped term derivation, the categorical Kleisli arrow and
direct monadic interpretation agree on corresponding inputs. -/
theorem denote_agrees {Γ : VCtx τ} {t : Tm Φ} {A : τ}
    (h : Tm.HasType Γ t A) :
    (fun ρ => (categoricalTermDenote (ε := ε) (m := m) h).of (envToCategorical ρ)) =
      Monadic.denote (ε := ε) (m := m) h :=
  denote_agrees_proof h

/-- Under categorical witness coherence, the chosen region denotations agree
after transporting the exit label and its payload. -/
theorem denoteRegion_agrees [Iterate m] [LawfulElgotMonad m]
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m))
    {Γ : VCtx τ} {region : Region Φ} {L : LCtx τ}
    (h : Region.HasType Γ region L) (ρ : Monadic.Env Γ) :
    (categoricalRegionDenote (ε := ε) (m := m) h).of (envToCategorical ρ) =
      (Monadic.denoteRegion (ε := ε) (m := m) h ρ >>= fun x =>
        pure (LambdaSSA.Semantics.Monadic.LabelValue.categoricalEquiv L x)) :=
  denoteRegion_agrees_proof coherent h ρ

/-- The subtyped region derivation determines the categorical witness, so the
two denotations agree for each fixed derivation. -/
theorem denoteRegion_agrees_of_derivation [Iterate m] [LawfulElgotMonad m]
    {Γ : VCtx τ} {region : Region Φ} {L : LCtx τ}
    (h : Region.HasType Γ region L) (ρ : Monadic.Env Γ) :
    (categoricalRegionDenote (ε := ε) (m := m) h).of (envToCategorical ρ) =
      (Monadic.denoteRegion (ε := ε) (m := m) h ρ >>= fun x =>
        pure (LambdaSSA.Semantics.Monadic.LabelValue.categoricalEquiv L x)) :=
  denoteRegion_agrees (by
    let := ofInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    exact Categorical.regionTypingCoherent (typeJ (m := m)) (ofTypeModel (τ := τ))) h ρ

end Silmaril.Isotope.LambdaSSA.Subtyping.Semantics.Agreement
