module

public import Silmaril.Logic.FirstOrderLFP.Boolean.Defs

@[expose] public section
namespace Silmaril.Logic.FirstOrderLFP.Boolean
open Silmaril.Logic.Institution.Examples

/-- The operator fixes the captured object assignment and varies only the fresh
positive tuple relation. All outer relation variances remain unchanged. -/
noncomputable def bodyOperator {S : Signature} (M : Model S) {r k : Nat}
    {P' : Fin (r + 1) → Profile S} {Γ : Fin k → S.S} {σ : Fin r → Bool}
    {Δ : Fin ((P' 0).arity + k) → S.S}
    (p : Formula S P' Δ (Fin.cases true σ))
    (η : RelEnv M (P' ∘ Fin.succ)) (ρ : ObjEnv M Γ) :
    Set (Tuple M (P' 0)) →o Set (Tuple M (P' 0)) where
  toFun X := {x | ∀ θ : ObjEnv M Δ, Extends θ x ρ → θ ∈ p.denote M (insertRel M P' η X)}
  monotone' := by
    intro X Y h x hx θ hθ
    apply (p.denote M).monotone ?_ (hx θ hθ)
    intro i
    refine Fin.cases h (fun j => ?_) i
    change if σ j then η j ⊆ η j else η j ⊆ η j
    split <;> exact le_rfl

/-- Conservative inclusion preserves the independently defined open denotation,
for every public structure, relation valuation and captured object assignment. -/
theorem positiveWith_denote {S : Signature} (M : Model S) {r k : Nat}
    {P : Fin r → Profile S} {Γ : Fin k → S.S} (p : FirstOrderLFP.Formula S P Γ)
    (σ : Fin r → Bool) (hσ : ∀ i, σ i = true) (η : RelEnv M P) :
    (positiveWith p σ hσ).denote M η = p.denote M η := by
  induction p with
  | base p => rfl
  | pred i args => rfl
  | conj p q hp hq =>
      change (positiveWith p σ hσ).denote M η ∩ (positiveWith q σ hσ).denote M η = _
      rw [hp, hq]
      rfl
  | disj p q hp hq =>
      change (positiveWith p σ hσ).denote M η ∪ (positiveWith q σ hσ).denote M η = _
      rw [hp, hq]
      rfl
  | @all r k P Δ p hp =>
      apply Set.ext
      intro ρ
      change (∀ x : M.toStructure.carrier (Δ 0),
        Fin.cases x ρ ∈ (positiveWith p σ hσ).denote M η) ↔ _
      rw [hp]
      rfl
  | @ex r k P Δ p hp =>
      apply Set.ext
      intro ρ
      change (∃ x : M.toStructure.carrier (Δ 0),
        Fin.cases x ρ ∈ (positiveWith p σ hσ).denote M η) ↔ _
      rw [hp]
      rfl
  | @lfp r k P' Γ Δ ht hpar p args hp =>
      apply Set.ext
      intro ρ
      have hF : bodyOperator M (positiveWith p (Fin.cases true σ)
          (fun i => Fin.cases rfl hσ i)) η ρ = FirstOrderLFP.bodyOperator M p η ρ := by
        apply OrderHom.ext
        funext X
        apply Set.ext
        intro x
        change (∀ θ, Extends θ x ρ → θ ∈
          (positiveWith p (Fin.cases true σ) (fun i => Fin.cases rfl hσ i)).denote M
            (insertRel M P' η X)) ↔ _
        rw [hp]
        rfl
      change _ ∈ (bodyOperator M (positiveWith p (Fin.cases true σ)
        (fun i => Fin.cases rfl hσ i)) η ρ).lfp ↔
        _ ∈ (FirstOrderLFP.bodyOperator M p η ρ).lfp
      rw [hF]

theorem positive_denote {S : Signature} (M : Model S) {r k : Nat}
    {P : Fin r → Profile S} {Γ : Fin k → S.S} (p : FirstOrderLFP.Formula S P Γ)
    (η : RelEnv M P) : (positive p).denote M η = p.denote M η :=
  positiveWith_denote M p _ _ η

end Silmaril.Logic.FirstOrderLFP.Boolean
