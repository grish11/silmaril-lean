module

public import Silmaril.Logic.Consequence.Gentzen.Finitary.Defs
public import Silmaril.Logic.Consequence.Multi.Defs
public import Silmaril.Logic.Consequence.Structural.Finitary.Defs

/-! Proofs for `Silmaril.Logic.Consequence.Gentzen.Finitary.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Logic.Consequence.Gentzen.Finitary

open Silmaril.Consequence Silmaril.Consequence.Gentzen

universe u v

variable {C : Type u} {S : Seq C}

theorem onSet_list (hw : WeakSubset S) (Γ Δ : List C) :
    onSet S {x | x ∈ Γ} {x | x ∈ Δ} ↔ S Γ Δ :=
  ⟨fun ⟨_, _, h₁, h₂, h⟩ => hw h₁ h₂ h, fun h => ⟨Γ, Δ, fun _ h => h, fun _ h => h, h⟩⟩

theorem onFinset_iff_onSet (hw : WeakSubset S) (s t : Finset C) :
    onFinset S s t ↔ onSet S ↑s ↑t := by
  rw [show (↑s : Set C) = {x | x ∈ s.toList} by ext; simp,
    show (↑t : Set C) = {x | x ∈ t.toList} by ext; simp, onSet_list hw]; rfl

theorem onSet_single (hw : MultiSystem.WeakR S) (A : Set C) (c : C) :
    onSet S A {c} ↔ Structural.onSet (MultiSystem.single S) A c := by
  constructor
  · rintro ⟨Γ, Δ, h₁, h₂, h⟩
    exact ⟨Γ, h₁, hw (fun x hx => by simpa using h₂ x hx) h⟩
  · rintro ⟨Γ, h₁, h⟩
    exact ⟨Γ, [c], h₁, by simp, h⟩

variable {M : Type v} {sat : M → C → Prop}

theorem onSet_valid_sound {A B : Set C} (h : onSet (Valid sat) A B) : InfValid sat A B := by
  obtain ⟨Γ, Δ, h₁, h₂, h⟩ := h
  intro m hm
  obtain ⟨d, hd, hs⟩ := h m fun x hx => hm x (h₁ x hx)
  exact ⟨d, h₂ d hd, hs⟩

theorem onSet_valid_finset (s t : Finset C) : onSet (Valid sat) ↑s ↑t ↔ InfValid sat ↑s ↑t :=
  ⟨onSet_valid_sound, fun h => ⟨s.toList, t.toList, by simp, by simp,
    fun m hm => by
      obtain ⟨b, hb, hs⟩ := h m fun a ha => hm a (by simpa using ha)
      exact ⟨b, by simpa using hb, hs⟩⟩⟩

end Silmaril.Proofs.Logic.Consequence.Gentzen.Finitary
