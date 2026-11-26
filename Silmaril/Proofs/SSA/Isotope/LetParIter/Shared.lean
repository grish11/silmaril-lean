module

public import Silmaril.SSA.Isotope.LetParIter.Shared.Defs

public section

namespace Silmaril.Isotope.LetParIter.Proofs

open Parallel LetIter.ProofRelevant.Semantics

universe u v w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν] {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m] [Elgot.Iterate m] [InstructionModel Φ τ ε m]
variable (P : Elgot.ParallelPairing m)
variable {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {A : τ}

private theorem snoc_get (ρ : BoundDen β) (a : TyDen A) :
    Isotope.Semantics.BoundEnv.snoc (D := TyDen (τ := τ)) (BoundDen.get ρ) a =
      BoundDen.get (β := .snoc β A) (ρ, a) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem interpret_eq_denote (d : Derivation Φ Γ β a A) (γ : CtxDen Γ) (ρ : BoundDen β) :
    interpret (ε := ε) P d γ ρ = denote (ε := ε) P d γ ρ := by
  induction d with
  | fv | bv => rw [interpret, Derivation.denote, denote]
  | unit =>
      rw [interpret, Derivation.denote, denote]
      rfl
  | op _ ih =>
      simp only [interpret] at ih
      rw [interpret, Derivation.denote, denote, ih]
  | inl _ ih | inr _ ih =>
      simp only [interpret] at ih
      rw [interpret, Derivation.denote, denote, ih]
      rfl
  | let₁ _ _ iha ihb =>
      simp only [interpret] at iha ihb
      simp only [interpret, Derivation.denote, denote, snoc_get, iha, ihb]
  | let₂ _ _ iha ihb =>
      simp only [interpret] at iha ihb
      simp only [interpret, Derivation.denote, denote, snoc_get, iha, ihb]
      rfl
  | pair _ _ iha ihb =>
      simp only [interpret] at iha ihb
      simp only [interpret, Derivation.denote, denote, iha, ihb]
      rfl
  | case _ _ _ ihe ihl ihr =>
      simp only [interpret] at ihe ihl ihr
      simp only [interpret, Derivation.denote, denote, snoc_get, ihe, ihl, ihr]
      simp only [nativeControl]
      apply bind_congr
      intro e
      cases TypeModel.coprodEquiv _ _ e <;> rfl
  | abort da ih =>
      simp only [interpret] at ih
      rw [interpret, Derivation.denote, denote, ih]
      apply bind_congr
      intro z
      exact Empty.elim (TypeModel.emptyEquiv z)
  | iter da db iha ihb =>
      simp only [interpret] at iha ihb
      simp only [interpret, Derivation.denote, denote, evalIter, snoc_get, iha, ihb]
      rfl
  | par da db iha ihb =>
      simp only [interpret] at iha ihb
      simp only [interpret, Derivation.denote, denote, evalPar, iha, ihb, bind_pure_comp]
      rfl

end Silmaril.Isotope.LetParIter.Proofs
