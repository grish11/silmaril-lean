module

public import Silmaril.Proofs.Games.Abstract.SessionHost.Plays

/-!
# Store determinism of the linked triple (proofs)

A component deterministic given answers (`AFun.Det`) against a host with at most one answer per
call gives a store-deterministic linked triple: two behaviours with the same component calls
agree on every host answer (the host has one) and every component answer (they are visible), so
they agree on their end, final store included.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionHost

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.SessionHost
  Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.StratThread

universe u

variable {E F : Sig.{u}} {S A B : Type u} {R : HostRel E}

theorem agree_eq (hR : ∀ m n n', R m (.answer n) → R m (.answer n') → n = n') :
    ∀ {c₁ c₂ : List (Call (E ⊕ₛ F))} {e₁ e₂ : End S B}, AFun.Agree c₁ e₁ c₂ e₂ → Ok R F c₁ →
      Ok R F c₂ → fCalls c₁ = fCalls c₂ → e₁ = e₂ := by
  intro c₁
  induction c₁ with
  | nil =>
    intro c₂ e₁ e₂ h _ _ _
    rcases c₂ with _ | ⟨⟨m, n⟩, c₂⟩
    · exact h
    · exact (h : False).elim
  | cons x c₁ ih =>
    intro c₂ e₁ e₂ h h₁ h₂ hf
    rcases x with ⟨μ, n₁⟩
    rcases c₂ with _ | ⟨⟨μ', n₂⟩, c₂⟩
    · exact (h : False).elim
    · obtain ⟨rfl, h⟩ := (h : μ = μ' ∧ (HEq n₁ n₂ → AFun.Agree c₁ e₁ c₂ e₂))
      have ht₁ : Ok R F c₁ := fun y hy => h₁ y (.tail _ hy)
      have ht₂ : Ok R F c₂ := fun y hy => h₂ y (.tail _ hy)
      rcases μ with m | m
      · have hn : n₁ = n₂ := hR m n₁ n₂ (h₁ _ (.head _)) (h₂ _ (.head _))
        subst hn
        exact ih (h HEq.rfl) ht₁ ht₂ hf
      · have hf' : (⟨m, n₁⟩ : Call F) :: fCalls c₁ = ⟨m, n₂⟩ :: fCalls c₂ := hf
        obtain ⟨hx, hft⟩ := List.cons.inj hf'
        cases hx
        exact ih (h HEq.rfl) ht₁ ht₂ hft

/-- **A deterministic component against a host with at most one answer per call has a
store-deterministic linked triple.** -/
theorem storeDet_hostLinkS {t : ObsTriple (E ⊕ₛ F) S A B}
    (hR : ∀ m n n', R m (.answer n) → R m (.answer n') → n = n') (ht : AFun.Det t.1) :
    StoreDet (hostLinkS R t) := by
  rintro s a c b s₁ s₂ (⟨c₁, hc₁, hok₁, rfl⟩ | ⟨hd, -⟩) (⟨c₂, hc₂, hok₂, hf⟩ | ⟨hd, -⟩)
  · have := agree_eq hR (ht s a _ _ hc₁ hc₂) hok₁ hok₂ hf
    cases this; rfl
  all_goals cases hd

end Silmaril.Proofs.Games.Abstract.SessionHost
