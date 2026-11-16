module

public import Silmaril.Logic.Consequence.Gentzen.Translate.Defs

/-! Proofs for `Silmaril.Logic.Consequence.Gentzen.Translate.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Logic.Consequence.Gentzen.Translate

open Silmaril.Consequence Silmaril.Consequence.Gentzen

universe u v w

variable {C : Type u} {D : Type v}

theorem closed_pullback {f : C → D} {rs : Rules C} {rs' : Rules D} (h : rs.Hom f rs')
    {T : Seq D} (hT : Closed rs' T) :
    Closed rs (System.pullback (List.map f) (List.map f) T) where
  refl hr _ _ c hΓ hΔ := hT.refl (h.refl hr) (List.mem_map_of_mem hΓ) (List.mem_map_of_mem hΔ)
  weak _ _ _ _ h₁ h₂ hd := hT.weak (h.weak h₁) (h.weak h₂) hd
  cut hc Γ Γ' Δ Δ' a h₁ h₂ := by
    simp only [System.pullback, List.map_append, List.map_cons] at h₁ h₂ ⊢
    exact hT.cut (h.cut hc) h₁ h₂

variable {A : Type u}

theorem mem_posAtoms {a : A} {Γ : List (Signed A)} : a ∈ posAtoms Γ ↔ Signed.pos a ∈ Γ := by
  simp only [posAtoms, List.mem_filterMap]
  constructor
  · rintro ⟨s, hs, h⟩
    cases s with
    | pos b => cases h; exact hs
    | neg b => cases h
  · intro h; exact ⟨_, h, rfl⟩

theorem mem_negAtoms {a : A} {Γ : List (Signed A)} : a ∈ negAtoms Γ ↔ Signed.neg a ∈ Γ := by
  simp only [negAtoms, List.mem_filterMap]
  constructor
  · rintro ⟨s, hs, h⟩
    cases s with
    | pos b => cases h
    | neg b => cases h; exact hs
  · intro h; exact ⟨_, h, rfl⟩

theorem posAtoms_map_pos (Γ : List A) : posAtoms (Γ.map Signed.pos) = Γ := by
  induction Γ <;> simp_all [posAtoms]

theorem negAtoms_map_pos (Γ : List A) : negAtoms (Γ.map Signed.pos) = [] := by
  induction Γ <;> simp_all [negAtoms]

theorem posAtoms_append (Γ Δ : List (Signed A)) :
    posAtoms (Γ ++ Δ) = posAtoms Γ ++ posAtoms Δ := List.filterMap_append

theorem negAtoms_append (Γ Δ : List (Signed A)) :
    negAtoms (Γ ++ Δ) = negAtoms Γ ++ negAtoms Δ := List.filterMap_append

theorem signedLift_valid {M : Type w} (τ : M → A → Prop) :
    signedLift (Valid τ) = Valid (signedSat τ) := by
  funext Γ Δ
  apply propext
  simp only [signedLift, Valid, Refutation.SatAll]
  refine forall_congr' fun m => ?_
  constructor
  · intro hL hΓ
    by_contra hn
    push Not at hn
    obtain ⟨d, hd, hτ⟩ := hL (by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hΓ _ (mem_posAtoms.1 hx)
      · exact not_not.1 (hn _ (mem_negAtoms.1 hx)))
    rcases List.mem_append.1 hd with hd | hd
    · exact hn _ (mem_posAtoms.1 hd) hτ
    · exact hΓ _ (mem_negAtoms.1 hd) hτ
  · intro hR hL
    by_contra hn
    push Not at hn
    obtain ⟨s, hs, hσ⟩ := hR (by
      intro s hs
      cases s with
      | pos a => exact hL a (List.mem_append_left _ (mem_posAtoms.2 hs))
      | neg a => exact hn a (List.mem_append_right _ (mem_negAtoms.2 hs)))
    cases s with
    | pos a => exact hn a (List.mem_append_left _ (mem_posAtoms.2 hs)) hσ
    | neg a => exact hσ (hL a (List.mem_append_right _ (mem_negAtoms.2 hs)))

theorem closed_signedLift {S : Seq A} (hS : Closed defaultRules S) :
    Closed defaultRules (signedLift S) where
  refl _ Γ Δ s hΓ hΔ := by
    cases s with
    | pos a =>
      exact hS.refl trivial (List.mem_append_left _ (mem_posAtoms.2 hΓ))
        (List.mem_append_left _ (mem_posAtoms.2 hΔ))
    | neg a =>
      exact hS.refl trivial (List.mem_append_right _ (mem_negAtoms.2 hΔ))
        (List.mem_append_right _ (mem_negAtoms.2 hΓ))
  weak Γ Γ' Δ Δ' h₁ h₂ hd := by
    refine hS.weak ?_ ?_ hd <;> intro x hx <;>
      simp only [List.mem_append, mem_posAtoms, mem_negAtoms] at hx ⊢
    · exact hx.imp (fun h => h₁ h) (fun h => h₂ h)
    · exact hx.imp (fun h => h₂ h) (fun h => h₁ h)
  cut _ Γ Γ' Δ Δ' s h₁ h₂ := by
    unfold signedLift at h₁ h₂ ⊢
    cases s with
    | pos a =>
      have k₁ : S (posAtoms Γ ++ negAtoms Δ) (a :: (posAtoms Δ ++ negAtoms Γ)) :=
        hS.weak (by intro x hx; simpa [mem_posAtoms, mem_negAtoms] using hx)
          (by intro x hx; simp [mem_posAtoms, mem_negAtoms] at hx ⊢; tauto) h₁
      have k₂ : S (a :: (posAtoms Γ' ++ negAtoms Δ')) (posAtoms Δ' ++ negAtoms Γ') :=
        hS.weak (by intro x hx; simp [mem_posAtoms, mem_negAtoms] at hx ⊢; tauto)
          (by intro x hx; simpa [mem_posAtoms, mem_negAtoms] using hx) h₂
      refine hS.weak ?_ ?_ (hS.cut trivial k₁ k₂) <;> intro x hx <;>
        simp [mem_posAtoms, mem_negAtoms] at hx ⊢ <;> tauto
    | neg a =>
      have k₁ : S (posAtoms Γ' ++ negAtoms Δ') (a :: (posAtoms Δ' ++ negAtoms Γ')) :=
        hS.weak (by intro x hx; simpa [mem_posAtoms, mem_negAtoms] using hx)
          (by intro x hx; simp [mem_posAtoms, mem_negAtoms] at hx ⊢; tauto) h₂
      have k₂ : S (a :: (posAtoms Γ ++ negAtoms Δ)) (posAtoms Δ ++ negAtoms Γ) :=
        hS.weak (by intro x hx; simp [mem_posAtoms, mem_negAtoms] at hx ⊢; tauto)
          (by intro x hx; simpa [mem_posAtoms, mem_negAtoms] using hx) h₁
      refine hS.weak ?_ ?_ (hS.cut trivial k₁ k₂) <;> intro x hx <;>
        simp [mem_posAtoms, mem_negAtoms] at hx ⊢ <;> tauto

end Silmaril.Proofs.Logic.Consequence.Gentzen.Translate
