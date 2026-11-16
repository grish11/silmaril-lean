module

public import Silmaril.Games.Accept.Defs
public import Mathlib.Data.List.Infix

/-! # Accepted sets of trace models: theorems

Acceptance is monotone in the trace model, is determined by the observable traces (so any
observable-trace equivalence preserves it), transports along move maps that commute with the
observations, and, on prefix-closed models such as strategies, is witnessed by a trace ending
in the accepting move.
-/

@[expose] public section

namespace Silmaril.Games.Accept

universe u v w

variable {M : Type u} {N : Type v} {α : Type w} {obs : M → Option α} {T T' : Set (List M)}

theorem mem_observed {a : α} : a ∈ observed obs T ↔ ∃ s ∈ T, ∃ m ∈ s, obs m = some a := Iff.rfl

/-- Acceptance reads the observable traces: a value is accepted when it occurs in one. -/
theorem observed_eq_obsTraces (obs : M → Option α) (T : Set (List M)) :
    observed obs T = {a | ∃ t ∈ obsTraces obs T, a ∈ t} := by
  ext a
  constructor
  · rintro ⟨s, hs, m, hm, ho⟩; exact ⟨_, ⟨s, hs, rfl⟩, List.mem_filterMap.2 ⟨m, hm, ho⟩⟩
  · rintro ⟨_, ⟨s, hs, rfl⟩, ha⟩
    obtain ⟨m, hm, ho⟩ := List.mem_filterMap.1 ha
    exact ⟨s, hs, m, hm, ho⟩

/-- Observable-trace refinement refines acceptance. -/
theorem observed_subset_of_obsRefines {obs' : N → Option α} {T' : Set (List N)}
    (h : ObsRefines obs obs' T T') : observed obs T ⊆ observed obs' T' := by
  rw [observed_eq_obsTraces, observed_eq_obsTraces]
  exact fun _ ⟨t, ht, ha⟩ => ⟨t, h ht, ha⟩

/-- **Observable-trace equivalent models accept the same values.** -/
theorem observed_eq_of_obsEquiv {obs' : N → Option α} {T' : Set (List N)}
    (h : ObsEquiv obs obs' T T') : observed obs T = observed obs' T' :=
  Set.Subset.antisymm (observed_subset_of_obsRefines h.subset)
    (observed_subset_of_obsRefines h.symm.subset)

/-- More traces accept more. -/
theorem observed_mono (h : T ⊆ T') : observed obs T ⊆ observed obs T' :=
  fun _ ⟨s, hs, m, hm, ho⟩ => ⟨s, h hs, m, hm, ho⟩

/-- Acceptance of a union of models is the union of acceptances. -/
theorem observed_union : observed obs (T ∪ T') = observed obs T ∪ observed obs T' := by
  ext a
  simp only [observed, Set.mem_union]
  constructor
  · rintro ⟨s, hs | hs, h⟩
    · exact .inl ⟨s, hs, h⟩
    · exact .inr ⟨s, hs, h⟩
  · rintro (⟨s, hs, h⟩ | ⟨s, hs, h⟩)
    · exact ⟨s, .inl hs, h⟩
    · exact ⟨s, .inr hs, h⟩

/-- A move map that commutes with the observations preserves observable traces. -/
theorem obsEquiv_map (f : M → N) {obs' : N → Option α} (h : ∀ m, obs' (f m) = obs m) :
    ObsEquiv obs' obs (List.map f '' T) T := by
  have hc : obs' ∘ f = obs := funext h
  ext t
  simp only [obsTraces, Set.mem_image]
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s, hs, by rw [List.filterMap_map, hc]⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨_, ⟨s, hs, rfl⟩, by rw [List.filterMap_map, hc]⟩

/-- Acceptance transports along a move map that commutes with the observations. -/
theorem observed_map (f : M → N) {obs' : N → Option α} (h : ∀ m, obs' (f m) = obs m) :
    observed obs' (List.map f '' T) = observed obs T :=
  observed_eq_of_obsEquiv (obsEquiv_map f h)

/-- On a prefix-closed model, an accepted value is accepted by a trace ending in the
accepting move. -/
theorem mem_observed_iff_last (hT : ∀ {s t}, t ∈ T → s <+: t → s ∈ T) {a : α} :
    a ∈ observed obs T ↔ ∃ s m, s ++ [m] ∈ T ∧ obs m = some a := by
  constructor
  · rintro ⟨t, ht, m, hm, ho⟩
    obtain ⟨s, u, rfl⟩ := List.append_of_mem hm
    exact ⟨s, m, hT ht ⟨u, by simp⟩, ho⟩
  · rintro ⟨s, m, hs, ho⟩
    exact ⟨_, hs, m, by simp, ho⟩

end Silmaril.Games.Accept

namespace Silmaril.Games.Strategy

universe u w

variable {E F : Sig.{u}} {α : Type w} {obs : Move E F → Option α}

/-- **Refinement refines acceptance**: a strategy refining another accepts no more. -/
theorem accepted_mono {σ τ : Strategy E F} (h : σ ≤ τ) : σ.accepted obs ⊆ τ.accepted obs :=
  Accept.observed_mono fun _ hs => h hs

/-- Strategies with the same observable plays accept the same values. -/
theorem accepted_eq_of_obsEquiv {σ τ : Strategy E F}
    (h : Accept.ObsEquiv obs obs σ.plays τ.plays) : σ.accepted obs = τ.accepted obs :=
  Accept.observed_eq_of_obsEquiv h

/-- A strategy accepts `a` iff some play ends in a move observed as `a`. -/
theorem mem_accepted_iff (σ : Strategy E F) {a : α} :
    a ∈ σ.accepted obs ↔ ∃ s m, s ++ [m] ∈ σ.plays ∧ obs m = some a :=
  Accept.mem_observed_iff_last σ.of_prefix

/-- **Acceptance of a generated strategy through Proponent moves** is read off its generators:
the Opponent moves `generate` adds for receptiveness are never observed. -/
theorem accepted_generate {S : Set (List (Move E F))}
    (hP : ∀ m a, obs m = some a → ¬ m.IsO) :
    (generate S).accepted obs = Accept.observed obs {s | s ∈ S ∧ Legal s} := by
  ext a
  constructor
  · rintro ⟨p, ⟨-, u, hu, hp⟩, m, hm, ho⟩
    have hmu : m ∈ u := by
      rcases hp with hp | ⟨p₀, o, rfl, hp₀, hO⟩
      · exact hp.subset hm
      · rcases List.mem_append.1 hm with hm | hm
        · exact hp₀.subset hm
        · rw [List.mem_singleton.1 hm] at ho
          exact absurd hO (hP o a ho)
    rcases hu with rfl | hu
    · cases hmu
    · exact ⟨u, hu, m, hmu, ho⟩
  · rintro ⟨s, ⟨hs, hl⟩, m, hm, ho⟩
    exact ⟨s, subset_generate hs hl, m, hm, ho⟩

end Silmaril.Games.Strategy
