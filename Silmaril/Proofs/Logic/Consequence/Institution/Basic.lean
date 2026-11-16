module

public import Silmaril.Logic.Consequence.Institution.Defs
public import Silmaril.Logic.Consequence.Structural.Defs

/-! Proofs for `Silmaril.Logic.Consequence.Institution.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Logic.Consequence.Institution

open Silmaril.Consequence Silmaril.Consequence.Structural Silmaril.Logic.Institution

universe w

/-- A Tarskian entailment relation on lists is reflexive, weakens along `⊆` and has multi-cut. -/
theorem listSys_closed (E : Metatheory.ER.{w}) : Closed tarskiRules (ER.listSys E) where
  refl _ _ _ hc := E.mono (fun _ hx => (Set.mem_singleton_iff.1 hx) ▸ hc) (E.refl _)
  weak _ _ _ hw hd := E.mono (fun _ hx => hw hx) hd
  cut _ ps c hps hc := by
    refine E.trans (Δ := {x | x ∈ ps.map Prod.snd}) ?_ (E.mono (fun _ hx => Or.inr hx) hc)
    intro φ hφ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hφ
    exact E.mono (fun x hx => List.mem_flatMap.2 ⟨p, hp, hx⟩) (hps p hp)

end Silmaril.Proofs.Logic.Consequence.Institution
