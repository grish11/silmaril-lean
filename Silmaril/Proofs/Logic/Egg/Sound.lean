module

public import Silmaril.Logic.Egg.Core.Explanation

@[expose] public section

namespace Silmaril.Proofs.Logic.Egg

open Silmaril.Logic.Egg.Core
open Silmaril.Logic.Institution.Examples

theorem explanation_sound {S : Signature} {m : Nat} {Δ : Fin m → S.S}
    {rules : Set (Rule S)} {premises : Set (Equality S Δ)} (M : Model S)
    (ρ : ∀ i, M.carrier (Δ i)) (hrules : ∀ r ∈ rules, r.Holds M)
    (hpremises : StateHolds M ρ premises) {s : S.S} {a b : EQ.Term S Δ s}
    (certificate : Explanation rules premises a b) : a.eval M ρ = b.eval M ρ := by
  induction certificate with
  | premise h => exact hpremises _ h
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | congr o a b _ ih =>
    show M.op o (fun i => (a i).eval M ρ) = M.op o (fun i => (b i).eval M ρ)
    exact congrArg (M.op o) (funext ih)
  | rewrite r hr δ _ ih =>
    show (Pattern.instantiate δ r.conclusion.lhs).eval M ρ =
      (Pattern.instantiate δ r.conclusion.rhs).eval M ρ
    rw [Pattern.eval_instantiate, Pattern.eval_instantiate]
    apply hrules r hr
    intro e he
    show e.lhs.eval M (fun i => (δ i).eval M ρ) = e.rhs.eval M (fun i => (δ i).eval M ρ)
    rw [← Pattern.eval_instantiate, ← Pattern.eval_instantiate]
    exact ih e he

theorem unionStep_sound {S : Signature} {m : Nat} {Δ : Fin m → S.S}
    {rules : Set (Rule S)} {before after : Set (Equality S Δ)} (M : Model S)
    (ρ : ∀ i, M.carrier (Δ i)) (hrules : ∀ r ∈ rules, r.Holds M)
    (hbefore : StateHolds M ρ before) (step : UnionStep rules before after) :
    StateHolds M ρ after := by
  rw [step.result]
  intro e he
  rcases Set.mem_insert_iff.mp he with rfl | h
  · exact explanation_sound M ρ hrules hbefore step.certificate
  · exact hbefore e h

end Silmaril.Proofs.Logic.Egg
