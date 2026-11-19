module

public import Silmaril.Semantics.Region.Queries.Examples.Defs

@[expose] public section
namespace Silmaril.Semantics.Region.Queries.Examples

/-- The existing diverging fixture satisfies every conditional target and
has no normal-exit witness. Must-exit therefore fails, despite partial WP. -/
theorem loop_partial (target : Unit → Nat → Prop) :
    partialWP Region.Examples.loop (fun l => l = 0) target () :=
  fun es t exits => (Region.Examples.empty_exits_loop () es t trivial exits).elim

theorem loop_not_may (target : Unit → Nat → Prop) :
    ¬ mayWP Region.Examples.loop (fun l => l = 0) target () :=
  fun ⟨es, t, exits, _⟩ => Region.Examples.empty_exits_loop () es t trivial exits

theorem loop_not_must (target : Unit → Nat → Prop) :
    ¬ mustWP Region.Examples.loop (fun l => l = 0) target () :=
  fun h => loop_not_may target (must_implies_may h)

theorem fork_may : mayWP fork (fun l => l = 0) (label 1) 0 :=
  ⟨[], 1, .leave rfl ⟨rfl, rfl, Or.inl rfl⟩ (by decide), rfl⟩

theorem fork_not_partial : ¬ partialWP fork (fun l => l = 0) (label 1) 0 :=
  fun h => (by decide : (2 : Nat) ≠ 1) (h [] 2 (.leave rfl ⟨rfl, rfl, Or.inr rfl⟩ (by decide)))

end Silmaril.Semantics.Region.Queries.Examples
