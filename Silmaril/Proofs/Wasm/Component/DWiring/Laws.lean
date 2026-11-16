module

public import Silmaril.Proofs.Wasm.Component.DWiring.Count

/-!
# Composition with one-call handlers: divergence and infinite plays

* `comp_ofHandler_div`, `comp_ofHandler_inf`: with a one-call handler on top,
  the composite has no hidden chatter; it diverges exactly where the strategy
  below diverges (along the handler), and every infinite interaction is an
  infinite play.
* `ofHandler_comp_div`: with a handler below, divergence is local divergence of
  the strategy on top, or hidden chatter.
* `oneCall_widenH`, `oneCall_narrowH`, `oneCall_splitH`, `oneCall_selectH`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DWiring

open Silmaril.Games Silmaril.Wasm.Component

universe u

variable {X E F G : Sig.{u}}

theorem comp_ofHandler_div {h : Handler E F} (hh : OneCall h) (δ : DStrategy X E) :
    (δ.comp (DStrategy.ofHandler h)).div =
      {p | ∃ s t, Zip s t p ∧ s ∈ δ.div ∧ t ∈ Strategy.ofHandler h} := by
  ext p
  rw [DStrategy.mem_div_comp]
  constructor
  · rintro (⟨s, t, hz, ⟨hs, ht⟩ | ⟨-, ht⟩⟩ | ⟨i, hi⟩)
    · exact ⟨s, t, hz, hs, ht⟩
    · rw [DStrategy.ofHandler_div] at ht
      exact ht.elim
    · obtain ⟨n, hn⟩ := unbounded_p hh i (p.length + 1)
      rw [hi n] at hn
      omega
  · rintro ⟨s, t, hz, hs, ht⟩
    exact .inl ⟨s, t, hz, .inl ⟨hs, ht⟩⟩

theorem comp_ofHandler_inf {h : Handler E F} (hh : OneCall h) (δ : DStrategy X E) :
    (δ.comp (DStrategy.ofHandler h)).inf =
      {I | ∃ i : DStrategy.InfInteraction δ (DStrategy.ofHandler h), I = i.p.lim} := by
  ext I
  rw [DStrategy.mem_inf_comp]
  exact ⟨fun ⟨i, _, hI⟩ => ⟨i, hI⟩, fun ⟨i, hI⟩ => ⟨i, unbounded_p hh i, hI⟩⟩

theorem ofHandler_comp_div (h : Handler E F) (σ : DStrategy F G) :
    ((DStrategy.ofHandler h).comp σ).div =
      {p | ∃ s t, Zip s t p ∧ s ∈ Strategy.ofHandler h ∧ t ∈ σ.div} ∪
      {p | ∃ i : DStrategy.InfInteraction (DStrategy.ofHandler h) σ, ∀ n, i.p n = p} := by
  ext p
  rw [DStrategy.mem_div_comp]
  constructor
  · rintro (⟨s, t, hz, ⟨hs, -⟩ | ⟨hs, ht⟩⟩ | hc)
    · rw [DStrategy.ofHandler_div] at hs
      exact hs.elim
    · exact .inl ⟨s, t, hz, hs, ht⟩
    · exact .inr hc
  · rintro (⟨s, t, hz, hs, ht⟩ | hc)
    · exact .inl ⟨s, t, hz, .inr ⟨hs, ht⟩⟩
    · exact .inr hc

theorem oneCall_widenH (n : Nat) : OneCall (widenH n) := by
  intro q
  unfold widenH
  split
  · exact .inr ⟨_, _, rfl, fun r => ⟨r, rfl⟩⟩
  · exact .inl ⟨_, rfl⟩

theorem oneCall_narrowH (k : Nat) : OneCall (narrowH k) :=
  fun _ => .inr ⟨_, _, rfl, fun r => ⟨r, rfl⟩⟩

theorem oneCall_splitH (e : Nat) : OneCall (splitH e) := by
  intro q
  unfold splitH
  split
  · exact .inr ⟨_, _, rfl, fun r => ⟨r, rfl⟩⟩
  · exact .inr ⟨_, _, rfl, fun r => ⟨r, rfl⟩⟩

theorem oneCall_selectH (obs : List Nat) : OneCall (selectH obs) := by
  intro q
  unfold selectH
  split
  · exact .inr ⟨_, _, rfl, fun r => ⟨r, rfl⟩⟩
  · exact .inl ⟨_, rfl⟩

end Silmaril.Proofs.Wasm.Component.DWiring
