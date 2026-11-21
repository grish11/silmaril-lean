module

public import Silmaril.Semantics.Operational.Policy.Defs

public section

namespace Silmaril.Proofs.Semantics.Operational.Policy

open Silmaril.Semantics.Operational

universe u v
variable {S : Type u} {Obs : Type v} {left right other : WithUB S Obs}

theorem included_refl (sem : WithUB S Obs) : sem.Included sem :=
  ⟨⟨fun {_ _} edge => edge, fun {_ _} obs => obs⟩, fun {_} bad => bad⟩

theorem included_trans (first : left.Included right) (second : right.Included other) : left.Included other :=
  ⟨⟨fun {_ _} edge => second.1.1 (first.1.1 edge), fun {_ _} obs => second.1.2 (first.1.2 obs)⟩,
    fun {_} bad => second.2 (first.2 bad)⟩

theorem included_antisymm (first : left.Included right) (second : right.Included left) : left = right := by
  have step : left.step = right.step := by
    funext source target
    exact propext ⟨fun edge => first.1.1 edge, fun edge => second.1.1 edge⟩
  have obs : left.observe = right.observe := by
    funext source outcome
    exact propext ⟨fun obs => first.1.2 obs, fun obs => second.1.2 obs⟩
  have ub : left.ub = right.ub := by
    funext source
    exact propext ⟨fun bad => first.2 bad, fun bad => second.2 bad⟩
  rcases left with ⟨⟨_, _⟩, _⟩
  rcases right with ⟨⟨_, _⟩, _⟩
  cases step; cases obs; cases ub; rfl

theorem included_meet : other.Included (left.meet right) ↔ other.Included left ∧ other.Included right := by
  constructor
  · intro both
    exact ⟨⟨⟨fun {_ _} edge => (both.1.1 edge).1, fun {_ _} obs => (both.1.2 obs).1⟩,
      fun {_} bad => (both.2 bad).1⟩, ⟨⟨fun {_ _} edge => (both.1.1 edge).2,
      fun {_ _} obs => (both.1.2 obs).2⟩, fun {_} bad => (both.2 bad).2⟩⟩
  · rintro ⟨first, second⟩
    exact ⟨⟨fun {_ _} edge => ⟨first.1.1 edge, second.1.1 edge⟩,
      fun {_ _} obs => ⟨first.1.2 obs, second.1.2 obs⟩⟩, fun {_} bad => ⟨first.2 bad, second.2 bad⟩⟩

theorem join_included : (left.join right).Included other ↔ left.Included other ∧ right.Included other := by
  constructor
  · intro both
    exact ⟨⟨⟨fun {_ _} edge => both.1.1 (.inl edge), fun {_ _} obs => both.1.2 (.inl obs)⟩,
      fun {_} bad => both.2 (.inl bad)⟩, ⟨⟨fun {_ _} edge => both.1.1 (.inr edge),
      fun {_ _} obs => both.1.2 (.inr obs)⟩, fun {_} bad => both.2 (.inr bad)⟩⟩
  · rintro ⟨first, second⟩
    exact ⟨⟨fun {_ _} edge => edge.elim (fun h => first.1.1 h) (fun h => second.1.1 h),
      fun {_ _} obs => obs.elim (fun h => first.1.2 h) (fun h => second.1.2 h)⟩,
      fun {_} bad => bad.elim (fun h => first.2 h) (fun h => second.2 h)⟩

end Silmaril.Proofs.Semantics.Operational.Policy
