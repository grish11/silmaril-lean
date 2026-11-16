module

public import Silmaril.Logic.Consequence.Gentzen.Defs

/-! Proofs for `Silmaril.Logic.Consequence.Gentzen.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Logic.Consequence.Gentzen

open Silmaril.Consequence Silmaril.Consequence.Gentzen
open Silmaril.Consequence.Refutation (SatAll Unsat)

universe u v

variable {C : Type u} {M : Type v}

theorem derives_least {rs : Rules C} {R S : Seq C} (hRS : R ≤ S) (hS : Closed rs S) :
    Derives rs R ≤ S := by
  intro Γ Δ hd
  induction hd with
  | base h => exact hRS _ _ h
  | refl h hΓ hΔ => exact hS.refl h hΓ hΔ
  | weak h₁ h₂ _ ih => exact hS.weak h₁ h₂ ih
  | cut h _ _ ih₁ ih₂ => exact hS.cut h ih₁ ih₂

theorem satAll_append {sat : M → C → Prop} {m : M} {Γ Δ : List C} :
    SatAll sat m (Γ ++ Δ) ↔ SatAll sat m Γ ∧ SatAll sat m Δ := by
  simp only [SatAll, List.mem_append]
  exact ⟨fun h => ⟨fun x hx => h x (.inl hx), fun x hx => h x (.inr hx)⟩,
    fun ⟨h₁, h₂⟩ x hx => hx.elim (h₁ x) (h₂ x)⟩

theorem valid_closed {sat : M → C → Prop} : Closed defaultRules (Valid sat) where
  refl _ _ _ c hΓ hΔ m hm := ⟨c, hΔ, hm c hΓ⟩
  weak _ _ _ _ hΓ hΔ h m hm := by
    obtain ⟨d, hd, hs⟩ := h m fun x hx => hm x (hΓ hx)
    exact ⟨d, hΔ hd, hs⟩
  cut _ Γ Γ' Δ Δ' a h₁ h₂ m hm := by
    obtain ⟨hΓ, hΓ'⟩ := satAll_append.1 hm
    obtain ⟨d, hd, hs⟩ := h₁ m hΓ
    rcases List.mem_cons.1 hd with rfl | hd
    · obtain ⟨e, he, hs'⟩ := h₂ m (by
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hs
        · exact hΓ' x hx)
      exact ⟨e, List.mem_append_right _ he, hs'⟩
    · exact ⟨d, List.mem_append_left _ hd, hs⟩

theorem unsat_of_valid {sat : M → C → Prop} {neg : C → C} (hn : NegSound sat neg)
    {Γ Δ : List C} (h : Valid sat Γ Δ) : Unsat sat (Γ ++ Δ.map neg) := by
  intro m hm
  obtain ⟨hΓ, hΔ⟩ := satAll_append.1 hm
  obtain ⟨d, hd, hs⟩ := h m hΓ
  exact hn m d (hΔ _ (List.mem_map_of_mem hd)) hs

theorem valid_of_unsat {sat : M → C → Prop} {neg : C → C} (hn : NegComplete sat neg)
    {Γ Δ : List C} (h : Unsat sat (Γ ++ Δ.map neg)) : Valid sat Γ Δ := by
  intro m hm
  by_contra hno
  refine h m (satAll_append.2 ⟨hm, ?_⟩)
  intro x hx
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hx
  exact hn m d fun hs => hno ⟨d, hd, hs⟩

theorem taut_of_valid {sat : M → C → Prop} {neg : C → C} (hn : NegComplete sat neg)
    {Γ Δ : List C} (h : Valid sat Γ Δ) : Taut sat (Γ.map neg ++ Δ) := by
  intro m _
  by_cases hm : SatAll sat m Γ
  · obtain ⟨d, hd, hs⟩ := h m hm
    exact ⟨d, List.mem_append_right _ hd, hs⟩
  · simp only [SatAll, not_forall] at hm
    obtain ⟨g, hg, hs⟩ := hm
    exact ⟨neg g, List.mem_append_left _ (List.mem_map_of_mem hg), hn m g hs⟩

theorem valid_of_taut {sat : M → C → Prop} {neg : C → C} (hn : NegSound sat neg)
    {Γ Δ : List C} (h : Taut sat (Γ.map neg ++ Δ)) : Valid sat Γ Δ := by
  intro m hm
  obtain ⟨d, hd, hs⟩ := h m (fun _ hx => absurd hx List.not_mem_nil)
  rcases List.mem_append.1 hd with hd | hd
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hd
    exact absurd (hm g hg) (hn m g hs)
  · exact ⟨d, hd, hs⟩

end Silmaril.Proofs.Logic.Consequence.Gentzen
