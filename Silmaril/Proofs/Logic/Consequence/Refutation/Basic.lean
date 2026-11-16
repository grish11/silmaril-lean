module

public import Silmaril.Logic.Consequence.Refutation.Defs

/-! Proofs for `Silmaril.Logic.Consequence.Refutation.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Logic.Consequence.Refutation

open Silmaril.Consequence Silmaril.Consequence.Refutation Silmaril.Consequence.Structural

universe u v

variable {M : Type v} {C : Type u} {sat : M → C → Prop}

theorem satAll_append {m : M} {Γ Δ : List C} :
    SatAll sat m (Γ ++ Δ) ↔ SatAll sat m Γ ∧ SatAll sat m Δ := by
  simp only [SatAll, List.mem_append]
  exact ⟨fun h => ⟨fun x hx => h x (.inl hx), fun x hx => h x (.inr hx)⟩,
    fun ⟨h₁, h₂⟩ x hx => hx.elim (h₁ x) (h₂ x)⟩

theorem entails_of_unsat {neg : C → List C} (hn : NegComplete sat neg) {Γ : List C} {c : C}
    (h : Unsat sat (Γ ++ neg c)) : Entails sat Γ c := by
  intro m hm
  by_contra hc
  exact h m (satAll_append.2 ⟨hm, hn m c hc⟩)

theorem unsat_of_entails {neg : C → List C} (hn : NegSound sat neg) {Γ : List C} {c : C}
    (h : Entails sat Γ c) : Unsat sat (Γ ++ neg c) := by
  intro m hm
  obtain ⟨hΓ, hc⟩ := satAll_append.1 hm
  exact hn m c hc (h m hΓ)

theorem entails_closed : Closed tarskiRules (Entails sat) where
  refl _ _ _ hc _ hm := hm _ hc
  weak _ _ _ hw hd m hm := hd m fun x hx => hm x (hw hx)
  cut _ ps c hps hd m hm := hd m (by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact hps p hp m fun y hy => hm y (List.mem_flatMap.2 ⟨p, hp, hy⟩))

end Silmaril.Proofs.Logic.Consequence.Refutation
