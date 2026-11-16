module

public import Silmaril.Wasm.Component.OutOfRangeSession.Defs
public import Silmaril.Games.Abstract.SessionTrap.Thms
public import Silmaril.Games.AnsMap.Thms
public import Silmaril.Games.AnsPull.Thms
public import Silmaril.Games.DPull.Defs

/-!
# Trap propagation through the `sigU` relabelling

A session node `σ : DStrategy sigS sigS` is seen on `sigU` as `ofSession σ =
(ofHandler ofU).comp (σ.comp (ofHandler toU))`: its answers relabelled by `toOpt` above
(`DStrategy.comp_ansH`) and the answers it receives by `ofOpt` below
(`DStrategy.ofHandler_ansH_comp`). A play of the relabelled node with a lower answer `none`
followed by `y` is the relabelling of a play of `σ` with the lower answer `.inr ()` followed by
a move relabelled to `y`; if that move is the trap answer `.inr ()` then `y` is `none`
(`relabel_trapAborting`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.OutOfRangeSession

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.SessionTrap
open Silmaril.Wasm.Component

/-- A list mapped onto two final elements. -/
theorem map_eq_append_pair' {α β : Type} {f : α → β} {l : List α} {L : List β} {b c : β}
    (h : l.map f = L ++ [b, c]) : ∃ l₀ x y, l = l₀ ++ [x, y] ∧ f x = b ∧ f y = c := by
  obtain ⟨l₁, l₂, rfl, -, h₂⟩ := List.map_eq_append_iff.1 h
  obtain ⟨x, l₃, rfl, hx, h₃⟩ := List.map_eq_cons_iff.1 h₂
  obtain ⟨y, l₄, rfl, hy, h₄⟩ := List.map_eq_cons_iff.1 h₃
  obtain rfl := List.map_eq_nil_iff.1 h₄
  exact ⟨l₁, x, y, rfl, hx, hy⟩

/-- The node seen on `sigU`, as relabellings. -/
theorem relabel_eq (σ : DStrategy sigS sigS) :
    ofSession σ =
      (σ.mapAns (B' := fun _ => Option Payload) fun _ => toOpt).pullAns
        (B' := fun _ => Payload ⊕ PUnit.{1}) (fun _ => ofOpt) := by
  unfold ofSession
  rw [show σ.comp (DStrategy.ofHandler toU) = σ.mapAns (B' := fun _ => Option Payload)
      (fun _ => toOpt) from DStrategy.comp_ansH _ σ]
  exact DStrategy.ofHandler_ansH_comp _

/-- **The trap answer propagates through the relabelling.** -/
theorem relabel_trapAborting {σ : DStrategy sigS sigS}
    (hσ : TrapAbortsBelow IsTrapS σ) : TrapAborting (ofSession σ) := by
  intro p m y hp
  rw [relabel_eq] at hp
  obtain ⟨q, hq, hqp⟩ := hp
  simp only [List.map_append, List.map_cons, List.map_nil] at hqp
  obtain ⟨q₀, x, z, rfl, hx, hz⟩ := map_eq_append_pair' hqp
  obtain ⟨e, rfl⟩ : ∃ e, x = .inl e := by
    rcases x with e | (_ | _) <;> simp [ansMove, lowMove] at hx ⊢
  simp only [ansMove, lowMove, Sum.inl.injEq] at hx
  subst hx
  obtain ⟨a, rfl⟩ := hσ q₀ m _ z rfl hq
  rcases y with (_ | _) | o <;> simp [ansMove, lowMove] at hz
  exact ⟨a, by rw [← hz]; rfl⟩

end Silmaril.Proofs.Wasm.Component.OutOfRangeSession
