module

public import Silmaril.Logic.Egglog.Core.Derivation

@[expose] public section

namespace Silmaril.Proofs.Logic.Egglog

open Silmaril.Logic.Egglog.Core

theorem derivation_sound {S : Signature} {m : Nat} {Δ : Fin m → S.S}
    {rules : Set (Rule S)} {facts : Set (Atom S Δ)} (M : Model S)
    (ρ : ∀ i, M.carrier (Δ i)) (hrules : ∀ r ∈ rules, r.Holds M)
    (hfacts : StateHolds M ρ facts) {a : Atom S Δ} (d : Derivation rules facts a) : a.Holds M ρ := by
  induction d with
  | input h => exact hfacts _ h
  | fire r hr δ _ ih =>
    apply (Atom.instantiate_holds δ M ρ r.head).mpr
    apply hrules r hr
    intro a ha
    exact (Atom.instantiate_holds δ M ρ a).mp (ih a ha)
  | collision f args x y _ _ hx hy => exact M.functional f _ _ _ hx hy

theorem insertStep_sound {S : Signature} {m : Nat} {Δ : Fin m → S.S}
    {rules : Set (Rule S)} {before after : Set (Atom S Δ)} (M : Model S)
    (ρ : ∀ i, M.carrier (Δ i)) (hrules : ∀ r ∈ rules, r.Holds M)
    (hbefore : StateHolds M ρ before) (step : InsertStep rules before after) : StateHolds M ρ after := by
  rw [step.result]
  intro a ha
  rcases Set.mem_insert_iff.mp ha with rfl | h
  · exact derivation_sound M ρ hrules hbefore step.certificate
  · exact hbefore a h

end Silmaril.Proofs.Logic.Egglog
