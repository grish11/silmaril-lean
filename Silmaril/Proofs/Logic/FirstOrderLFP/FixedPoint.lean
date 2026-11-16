module

public import Silmaril.Logic.FirstOrderLFP.Defs

@[expose] public section
namespace Silmaril.Logic.FirstOrderLFP
open CategoryTheory Silmaril.Logic.Institution.Examples

/-- A well-sorted tuple and ambient assignment determine exactly one body assignment. -/
theorem extends_exists_unique {S : Signature} (M : Model S) {n k : Nat}
    {Δ : Fin (n + k) → S.S} {w : Fin n → S.S} {Γ : Fin k → S.S}
    (ht : Δ ∘ Fin.castAdd k = w) (hp : Δ ∘ Fin.natAdd n = Γ)
    (x : ObjEnv M w) (ρ : ObjEnv M Γ) : ∃! θ : ObjEnv M Δ, Extends θ x ρ := by
  have hΔ : Δ = Fin.addCases w Γ := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa using congrFun ht j
    · intro j
      simpa using congrFun hp j
  subst Δ
  let θ₀ : ObjEnv M (Fin.addCases w Γ) := fun i =>
    Fin.addCases (fun j => by simpa using x j) (fun j => by simpa using ρ j) i
  have hθ₀ : Extends θ₀ x ρ := by
    constructor
    · intro j
      simp [θ₀]
    · intro j
      simp [θ₀]
  refine ⟨θ₀, hθ₀, ?_⟩
  intro θ hθ
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    exact eq_of_heq ((hθ.1 j).trans (hθ₀.1 j).symm)
  · intro j
    exact eq_of_heq ((hθ.2 j).trans (hθ₀.2 j).symm)

/-- This is the actual body transformer, including captured object parameters. -/
noncomputable def bodyOperator {S : Signature} (M : Model S) {r k : Nat}
    {P' : Fin (r + 1) → Profile S} {Γ : Fin k → S.S}
    {Δ : Fin ((P' 0).arity + k) → S.S}
    (body : Formula S P' Δ) (η : RelEnv M (P' ∘ Fin.succ)) (ρ : ObjEnv M Γ) :
    Set (Tuple M (P' 0)) →o Set (Tuple M (P' 0)) where
  toFun X := {x | ∀ θ : ObjEnv M Δ, Extends θ x ρ → θ ∈ body.denote M (insertRel M P' η X)}
  monotone' := by
    intro X Y h x hx θ hθ
    exact (body.denote M).monotone ((insertRel M P' η).monotone h) (hx θ hθ)

noncomputable def lfpSet {S : Signature} (M : Model S) {r k : Nat}
    {P' : Fin (r + 1) → Profile S} {Γ : Fin k → S.S}
    {Δ : Fin ((P' 0).arity + k) → S.S}
    (body : Formula S P' Δ) (η : RelEnv M (P' ∘ Fin.succ)) (ρ : ObjEnv M Γ) :
    Set (Tuple M (P' 0)) := (bodyOperator M body η ρ).lfp

/-- The operator really evaluates the body at the unique combined assignment. -/
theorem bodyOperator_iff {S : Signature} (M : Model S) {r k : Nat}
    {P' : Fin (r + 1) → Profile S} {Γ : Fin k → S.S}
    {Δ : Fin ((P' 0).arity + k) → S.S}
    (ht : Δ ∘ Fin.castAdd k = (P' 0).sorts)
    (hp : Δ ∘ Fin.natAdd (P' 0).arity = Γ)
    (body : Formula S P' Δ) (η : RelEnv M (P' ∘ Fin.succ)) (ρ : ObjEnv M Γ)
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
    {P' : Fin (r + 1) → Profile S} {Γ : Fin k → S.S}
    {Δ : Fin ((P' 0).arity + k) → S.S}
    (body : Formula S P' Δ) (η : RelEnv M (P' ∘ Fin.succ)) (ρ : ObjEnv M Γ) :
    lfpSet M body η ρ = bodyOperator M body η ρ (lfpSet M body η ρ) :=
  (bodyOperator M body η ρ).map_lfp.symm

/-- Induction is the prefixed-point principle, with no iteration cutoff. -/
theorem lfpSet_induction {S : Signature} (M : Model S) {r k : Nat}
    {P' : Fin (r + 1) → Profile S} {Γ : Fin k → S.S}
    {Δ : Fin ((P' 0).arity + k) → S.S}
    (body : Formula S P' Δ) (η : RelEnv M (P' ∘ Fin.succ)) (ρ : ObjEnv M Γ)
    (X : Set (Tuple M (P' 0))) (h : bodyOperator M body η ρ X ⊆ X) :
    lfpSet M body η ρ ⊆ X := (bodyOperator M body η ρ).lfp_le h

theorem Formula.denote_lfp {S : Signature} (M : Model S) {r k : Nat}
    {P' : Fin (r + 1) → Profile S} {Γ : Fin k → S.S}
    {Δ : Fin ((P' 0).arity + k) → S.S}
    (ht : Δ ∘ Fin.castAdd k = (P' 0).sorts)
    (hp : Δ ∘ Fin.natAdd (P' 0).arity = Γ)
    (body : Formula S P' Δ) (args : ∀ j, EQ.Term S.toSignature Γ ((P' 0).sorts j))
    (η : RelEnv M (P' ∘ Fin.succ)) (ρ : ObjEnv M Γ) :
    ρ ∈ (Formula.lfp ht hp body args).denote M η ↔
      (fun j => (args j).eval M.toStructure.toAlgebra ρ) ∈ lfpSet M body η ρ := Iff.rfl

end Silmaril.Logic.FirstOrderLFP
