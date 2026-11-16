module

public import Silmaril.Logic.Egg.Core.FirstOrder
public import Silmaril.Logic.Egg.Core.Explanation
import Silmaril.Proofs.Logic.Egg.Sound

@[expose] public section

namespace Silmaril.Logic.Egg.Core
open Silmaril.Logic.Institution.Examples

theorem explanation_sound {S : Signature} {m : Nat} {Δ : Fin m → S.S}
    {rules : Set (Rule S)} {premises : Set (Equality S Δ)} (M : Model S)
    (ρ : ∀ i, M.carrier (Δ i)) (hrules : ∀ r ∈ rules, r.Holds M)
    (hpremises : StateHolds M ρ premises) {s : S.S} {a b : EQ.Term S Δ s}
    (certificate : Explanation rules premises a b) : a.eval M ρ = b.eval M ρ :=
  Silmaril.Proofs.Logic.Egg.explanation_sound M ρ hrules hpremises certificate

theorem unionStep_sound {S : Signature} {m : Nat} {Δ : Fin m → S.S}
    {rules : Set (Rule S)} {before after : Set (Equality S Δ)} (M : Model S)
    (ρ : ∀ i, M.carrier (Δ i)) (hrules : ∀ r ∈ rules, r.Holds M)
    (hbefore : StateHolds M ρ before) (step : UnionStep rules before after) :
    StateHolds M ρ after :=
  Silmaril.Proofs.Logic.Egg.unionStep_sound M ρ hrules hbefore step

theorem fromEquations_modelExpansive : fromEquations.ModelExpansive := fun _ M => ⟨M,rfl⟩

end Silmaril.Logic.Egg.Core
