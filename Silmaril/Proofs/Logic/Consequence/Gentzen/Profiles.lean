module

public import Silmaril.Logic.Consequence.Gentzen.Profiles.Defs

/-! Proofs for `Silmaril.Logic.Consequence.Gentzen.Profiles.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Logic.Consequence.Gentzen.Profiles

open Silmaril.Consequence Silmaril.Consequence.Gentzen

universe u v

variable {C : Type u} {M : Type v} {sat : M → C → Prop}

theorem valid_conjL {and : C → C → C} (h : ∀ m a b, sat m (and a b) → sat m a ∧ sat m b) :
    ConjL and (Valid sat) := by
  intro a b Γ Δ hd m hm
  obtain ⟨ha, hb⟩ := h m a b (hm _ List.mem_cons_self)
  refine hd m fun x hx => ?_
  rcases List.mem_cons.1 hx with rfl | hx
  · exact ha
  rcases List.mem_cons.1 hx with rfl | hx
  · exact hb
  · exact hm x (List.mem_cons_of_mem _ hx)

theorem valid_conjR {and : C → C → C} (h : ∀ m a b, sat m a → sat m b → sat m (and a b)) :
    ConjR and (Valid sat) := by
  intro a b Γ Δ ha hb m hm
  obtain ⟨d, hd, hs⟩ := ha m hm
  obtain ⟨e, he, ht⟩ := hb m hm
  rcases List.mem_cons.1 hd with rfl | hd
  · rcases List.mem_cons.1 he with rfl | he
    · exact ⟨_, List.mem_cons_self, h m _ _ hs ht⟩
    · exact ⟨e, List.mem_cons_of_mem _ he, ht⟩
  · exact ⟨d, List.mem_cons_of_mem _ hd, hs⟩

theorem valid_disjL {or : C → C → C} (h : ∀ m a b, sat m (or a b) → sat m a ∨ sat m b) :
    DisjL or (Valid sat) := by
  intro a b Γ Δ ha hb m hm
  have hΓ : ∀ x ∈ Γ, sat m x := fun x hx => hm x (List.mem_cons_of_mem _ hx)
  rcases h m a b (hm _ List.mem_cons_self) with h' | h'
  · exact ha m fun x hx => (List.mem_cons.1 hx).elim (· ▸ h') (hΓ x)
  · exact hb m fun x hx => (List.mem_cons.1 hx).elim (· ▸ h') (hΓ x)

theorem valid_disjR {or : C → C → C} (h : ∀ m a b, sat m a ∨ sat m b → sat m (or a b)) :
    DisjR or (Valid sat) := by
  intro a b Γ Δ hd m hm
  obtain ⟨d, hd, hs⟩ := hd m hm
  rcases List.mem_cons.1 hd with rfl | hd
  · exact ⟨_, List.mem_cons_self, h m _ _ (.inl hs)⟩
  rcases List.mem_cons.1 hd with rfl | hd
  · exact ⟨_, List.mem_cons_self, h m _ _ (.inr hs)⟩
  · exact ⟨d, List.mem_cons_of_mem _ hd, hs⟩

end Silmaril.Proofs.Logic.Consequence.Gentzen.Profiles
