module

public import Silmaril.SSA.Isotope.LambdaSSA.Renaming.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Subtyping.Monadic.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Renaming.Monadic

/-! # Monadic λSSA denotation under typed variable renaming -/

public section

universe u v q r

namespace Silmaril.Isotope.LambdaSSA.Semantics.Monadic

open Silmaril.Isotope.LetIter.ProofRelevant.Semantics
open Silmaril.Elgot

variable {τ : Type u} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ] [TypeModel.{u, v} τ]

@[simp] theorem Env.rename_get {Γ Δ : LambdaSSA.VCtx τ} {ρ : Nat → Nat}
    (hρ : LambdaSSA.Ren Γ Δ ρ) (δ : Env Δ) (i : Nat) {A : τ}
    (h : LambdaSSA.At Γ i A) :
    Env.get (Env.rename hρ δ) i h = Env.get δ (ρ i) (hρ h) :=
  Env.rename_get_proof hρ δ i h

@[simp] theorem Env.rename_lift {Γ Δ : LambdaSSA.VCtx τ} {ρ : Nat → Nat}
    (hρ : LambdaSSA.Ren Γ Δ ρ) (δ : Env Δ) (A : τ) (a : TyDen A) :
    Env.rename (hρ.lift A) (δ, a) = (Env.rename hρ δ, a) :=
  Env.rename_lift_proof hρ δ A a

variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m]
variable [InstructionModel Φ τ ε m]

/-- Term denotation is contravariantly natural in its variable context. -/
theorem Denotes.renameVars {Γ Δ : LambdaSSA.VCtx τ} {ρ : Nat → Nat}
    (hρ : LambdaSSA.Ren Γ Δ ρ) {a : LambdaSSA.Tm Φ} {A : τ}
    {ha : LambdaSSA.Tm.HasType Γ a A} {f : Env Γ → m (TyDen A)}
    (d : Denotes ε ha f) :
    Denotes ε (ha.rename hρ) (fun δ => f (Env.rename hρ δ)) :=
  Denotes.renameVars_proof hρ d

variable [Iterate m]

/-- Region denotation is contravariantly natural in its variable context. -/
theorem RegionDenotes.renameVars {Γ Δ : LambdaSSA.VCtx τ} {ρ : Nat → Nat}
    (hρ : LambdaSSA.Ren Γ Δ ρ) {region : LambdaSSA.Region Φ}
    {L : LambdaSSA.LCtx τ} {hr : LambdaSSA.Region.HasType Γ region L}
    {f : Env Γ → m (LabelDen L)} (d : RegionDenotes ε hr f) :
    RegionDenotes ε (hr.renameVars hρ) (fun δ => f (Env.rename hρ δ)) :=
  RegionDenotes.renameVars_proof hρ d

end Silmaril.Isotope.LambdaSSA.Semantics.Monadic

namespace Silmaril.Isotope.LambdaSSA.Subtyping.Semantics.Monadic

open Silmaril.Isotope.LetIter.ProofRelevant.Semantics
open Silmaril.Elgot

variable {τ : Type u} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ] [TypeModel.{u, v} τ]

open LambdaSSA.Semantics.Monadic (Env.rename FiniteLabelDen)

variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m]
variable [InstructionModel Φ τ ε m]

/-- A renamed proof-relevant term uses the pulled-back environment and the same coercions. -/
theorem Denotes.renameVars {Γ Δ : LambdaSSA.VCtx τ} {ρ : Nat → Nat}
    (hρ : LambdaSSA.Ren Γ Δ ρ) {a : LambdaSSA.Tm Φ} {A : τ}
    {ha : LambdaSSA.Subtyping.Tm.HasType Γ a A}
    {f : Env Γ → m (TyDen A)} (d : Denotes ε ha f) :
    Denotes ε (ha.rename hρ) (fun δ => f (LambdaSSA.Semantics.Monadic.Env.rename hρ δ)) :=
  Denotes.renameVars_proof hρ d

variable [Iterate m]

/-- A renamed proof-relevant region uses the pulled-back environment, including in local blocks. -/
theorem RegionDenotes.renameVars {Γ Δ : LambdaSSA.VCtx τ} {ρ : Nat → Nat}
    (hρ : LambdaSSA.Ren Γ Δ ρ) {region : LambdaSSA.Region Φ}
    {L : LambdaSSA.LCtx τ}
    {hr : LambdaSSA.Subtyping.Region.HasType Γ region L}
    {f : Env Γ → m (LabelDen L)} (d : RegionDenotes ε hr f) :
    RegionDenotes ε (hr.renameVars hρ) (fun δ => f (LambdaSSA.Semantics.Monadic.Env.rename hρ δ)) :=
  RegionDenotes.renameVars_proof hρ d

end Silmaril.Isotope.LambdaSSA.Subtyping.Semantics.Monadic
