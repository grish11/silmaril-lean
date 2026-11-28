module

import Silmaril.Semantics.ConcurrentTrace.Parallel.Thms

namespace Silmaril.Semantics.ConcurrentTrace.Parallel.Regression

private abbrev Action := Letter Bool Nat

private def a : Action := .event false 2
private def b : Action := .event true 3
private def barrier : Action := .sync [false, true]

-- Two separately lifted words can use the same ID. Their two output orders are distinct.
example :
    ofWord [a, .event false 3] ∈
        parallel {liftThread false (FreeMonoid.of 2)} {liftThread false (FreeMonoid.of 3)} ∧
    ofWord [.event false 3, a] ∈
        parallel {liftThread false (FreeMonoid.of 2)} {liftThread false (FreeMonoid.of 3)} ∧
    ofWord [a, .event false 3] ≠ ofWord [.event false 3, a] := by
  simp only [liftThread_of]
  refine ⟨mem_parallel_ofWord.mpr ⟨[a], [.event false 3], rfl, rfl, .left _ (.right _ .nil)⟩,
    mem_parallel_ofWord.mpr ⟨[a], [.event false 3], rfl, rfl, .right _ (.left _ .nil)⟩, ?_⟩
  intro h
  rcases (swap_eq_iff a (.event false 3)).mp h with heq | hind
  · cases heq
  · cases hind with
    | events hne => exact hne rfl

-- Each input synchronization contributes its own occurrence.
example : ofWord [barrier, barrier] ∈ parallel {singleton barrier} {singleton barrier} :=
  mem_parallel_ofWord.mpr ⟨[barrier], [barrier], rfl, rfl, .left _ (.right _ .nil)⟩

-- Swapping a and b in the left input allows b before the barrier and a after it.
example : ofWord [b, barrier, a] ∈ parallel {ofWord [a, b]} {singleton barrier} := by
  apply mem_parallel_ofWord.mpr
  refine ⟨[b, a], [barrier], Set.mem_singleton_iff.mpr ?_, rfl, .left _ (.right _ (.left _ .nil))⟩
  exact swap (.events (by decide : true ≠ false))

-- Fixing the left word to [a,b] loses this trace even after taking the quotient image.
example : ofWord [b, barrier, a] ∉ toTraces (shuffleWords ({[a, b]} : Set (List Action)) {[barrier]}) := by
  rintro ⟨w, ⟨x, hx, y, hy, merge⟩, hq⟩
  obtain rfl := Set.mem_singleton_iff.mp hx
  obtain rfl := Set.mem_singleton_iff.mp hy
  have atFalse := congrArg (fun z => (observe false z).toList) hq
  have atTrue := congrArg (fun z => (observe true z).toList) hq
  cases merge <;> rename_i rest
  all_goals cases rest <;> rename_i rest
  all_goals (cases rest; rename_i rest)
  all_goals cases rest
  all_goals simp [a, b, barrier, ofWord_cons, map_mul, observeLetter] at atFalse atTrue

end Silmaril.Semantics.ConcurrentTrace.Parallel.Regression
