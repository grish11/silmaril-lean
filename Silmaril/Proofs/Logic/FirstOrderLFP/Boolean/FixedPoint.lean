module

public import Silmaril.Proofs.Logic.FirstOrderLFP.Boolean.Conservative

@[expose] public section
namespace Silmaril.Logic.FirstOrderLFP.Boolean
open Silmaril.Logic.Institution.Examples

noncomputable def lfpSet {S : Signature} (M : Model S) {r k : Nat}
    {P' : Fin (r + 1) → Profile S} {Γ : Fin k → S.S} {σ : Fin r → Bool}
    {Δ : Fin ((P' 0).arity + k) → S.S}
    (body : Formula S P' Δ (Fin.cases true σ)) (η : RelEnv M (P' ∘ Fin.succ)) (ρ : ObjEnv M Γ) :
    Set (Tuple M (P' 0)) := (bodyOperator M body η ρ).lfp

/-- The operator really evaluates the body at the unique combined assignment. -/
theorem bodyOperator_iff {S : Signature} (M : Model S) {r k : Nat}
    {P' : Fin (r + 1) → Profile S} {Γ : Fin k → S.S} {σ : Fin r → Bool}
    {Δ : Fin ((P' 0).arity + k) → S.S}
    (ht : Δ ∘ Fin.castAdd k = (P' 0).sorts)
    (hp : Δ ∘ Fin.natAdd (P' 0).arity = Γ)
    (body : Formula S P' Δ (Fin.cases true σ)) (η : RelEnv M (P' ∘ Fin.succ)) (ρ : ObjEnv M Γ)
    (X : Set (Tuple M (P' 0))) (x : Tuple M (P' 0))
    (θ : ObjEnv M Δ) (hθ : Extends θ x ρ) :
    x ∈ bodyOperator M body η ρ X ↔ θ ∈ body.denote M (insertRel M P' η X) := by
  constructor
  · exact fun h => h θ hθ
  · intro h τ hτ
    obtain ⟨ξ, _, hξ⟩ := extends_exists_unique M ht hp x ρ
    have he : τ = θ := (hξ τ hτ).trans (hξ θ hθ).symm
    exact he ▸ h

/-- Actual least fixed points unfold on every carrier, including infinite ones. -/
theorem lfpSet_unfold {S : Signature} (M : Model S) {r k : Nat}
    {P' : Fin (r + 1) → Profile S} {Γ : Fin k → S.S} {σ : Fin r → Bool}
    {Δ : Fin ((P' 0).arity + k) → S.S}
    (body : Formula S P' Δ (Fin.cases true σ)) (η : RelEnv M (P' ∘ Fin.succ)) (ρ : ObjEnv M Γ) :
    lfpSet M body η ρ = bodyOperator M body η ρ (lfpSet M body η ρ) :=
  (bodyOperator M body η ρ).map_lfp.symm

/-- Induction is the prefixed-point principle, with no iteration cutoff. -/
theorem lfpSet_induction {S : Signature} (M : Model S) {r k : Nat}
    {P' : Fin (r + 1) → Profile S} {Γ : Fin k → S.S} {σ : Fin r → Bool}
    {Δ : Fin ((P' 0).arity + k) → S.S}
    (body : Formula S P' Δ (Fin.cases true σ)) (η : RelEnv M (P' ∘ Fin.succ)) (ρ : ObjEnv M Γ)
    (X : Set (Tuple M (P' 0))) (h : bodyOperator M body η ρ X ⊆ X) :
    lfpSet M body η ρ ⊆ X := (bodyOperator M body η ρ).lfp_le h

theorem Formula.denote_lfp {S : Signature} (M : Model S) {r k : Nat}
    {P' : Fin (r + 1) → Profile S} {Γ : Fin k → S.S} {σ : Fin r → Bool}
    {Δ : Fin ((P' 0).arity + k) → S.S}
    (ht : Δ ∘ Fin.castAdd k = (P' 0).sorts)
    (hp : Δ ∘ Fin.natAdd (P' 0).arity = Γ)
    (body : Formula S P' Δ (Fin.cases true σ)) (args : ∀ j, EQ.Term S.toSignature Γ ((P' 0).sorts j))
    (η : RelEnv M (P' ∘ Fin.succ)) (ρ : ObjEnv M Γ) :
    ρ ∈ (Formula.lfp ht hp body args).denote M η ↔
      (fun j => (args j).eval M.toStructure.toAlgebra ρ) ∈ lfpSet M body η ρ := Iff.rfl

end Silmaril.Logic.FirstOrderLFP.Boolean
