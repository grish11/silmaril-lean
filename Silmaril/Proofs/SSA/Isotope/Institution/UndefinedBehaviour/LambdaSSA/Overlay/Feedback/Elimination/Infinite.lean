module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Elimination.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Elimination.Finite
import Mathlib.Data.Nat.Find

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.Elimination

open Silmaril.Isotope.LambdaSSA.UB.Overlay.Feedback (Graph)
open Relation (ReflTransGen TransGen)

universe u v

variable {P : Type u} {O : Type v} {g : Graph P O} {inside : P → Prop} {p q : P}

private abbrev InfinitePath (r : P → P → Prop) (p : P) :=
  ∃ path : Nat → P, path 0 = p ∧ ∀ n, r (path n) (path (n + 1))

private theorem path_prepend {r : P → P → Prop} (reach : ReflTransGen r p q)
    (rest : InfinitePath r q) : InfinitePath r p := by
  induction reach using Relation.ReflTransGen.head_induction_on with
  | refl => exact rest
  | @head a _ edge _ ih =>
    obtain ⟨path, start, steps⟩ := ih
    let pathFromStart : Nat → P
      | 0 => a
      | n + 1 => path n
    refine ⟨pathFromStart, rfl, ?_⟩
    intro n
    cases n with
    | zero =>
      change r _ (path 0)
      exact start.symm ▸ edge
    | succ n => exact steps n

private theorem path_between {r : P → P → Prop} (path : Nat → P) {lo hi : Nat} (le : lo ≤ hi)
    (edges : ∀ n, lo ≤ n → n < hi → r (path n) (path (n + 1))) :
    ReflTransGen r (path lo) (path hi) := by
  induction hi with
  | zero =>
    have : lo = 0 := by omega
    subst lo
    exact .refl
  | succ hi ih =>
    by_cases eq : lo = hi + 1
    · subst lo
      exact .refl
    · exact (ih (by omega) (fun n low high => edges n low (by omega))).tail
        (edges hi (by omega) (by omega))

private theorem path_of_serial {r : P → P → Prop} {live : P → Prop}
    (step : ∀ p, live p → ∃ q, r p q ∧ live q) (hp : live p) : InfinitePath r p := by
  let advance (p : {p // live p}) : {p // live p} :=
    ⟨(step p.val p.property).choose, (step p.val p.property).choose_spec.2⟩
  let path (n : Nat) : {p // live p} := Nat.rec ⟨p, hp⟩ (fun _ p => advance p) n
  exact ⟨fun n => (path n).val, rfl, fun n => (step (path n).val (path n).property).choose_spec.1⟩

private theorem first_of_positive {r : P → P → Prop} (h : TransGen r p q) :
    ∃ next, r p next ∧ ReflTransGen r next q := by
  induction h using Relation.TransGen.head_induction_on with
  | single edge => exact ⟨_, edge, .refl⟩
  | head edge rest _ => exact ⟨_, edge, rest.to_reflTransGen⟩

/-- Reflect an infinite sequence of nonempty segments. The live set contains
points with a finite suffix to a segment boundary. At a boundary the next
segment supplies a real step, even if its endpoints coincide. Classical
choice then selects a successor at each flat step. -/
theorem path_of_segments {r : P → P → Prop} (boundary : Nat → P)
    (segments : ∀ n, TransGen r (boundary n) (boundary (n + 1))) :
    ∃ path : Nat → P, path 0 = boundary 0 ∧ ∀ n, r (path n) (path (n + 1)) := by
  apply path_of_serial (live := fun q => ∃ n, ReflTransGen r q (boundary n)) _ ⟨0, .refl⟩
  rintro q ⟨n, suffix⟩
  rcases suffix.cases_head with rfl | ⟨t, edge, rest⟩
  · obtain ⟨t, edge, rest⟩ := first_of_positive (segments n)
    exact ⟨t, edge, n + 1, rest⟩
  · exact ⟨t, edge, n, rest⟩

theorem inner_infinite_reflect (outerPath : (g.outer inside).Reaches p q)
    (replay : (g.inner inside).Infinite q) : g.Infinite p := by
  obtain ⟨path, start, steps⟩ := replay
  exact path_prepend (outer_reaches_flat outerPath) ⟨path, start, fun n => (steps n).1⟩

theorem outer_infinite_reflect (replay : (g.outer inside).Infinite p) : g.Infinite p := by
  obtain ⟨path, start, steps⟩ := replay
  exact start ▸ path_of_segments path (fun n => outer_step_progress (steps n))

/-- Split a selected infinite flat path into a final inner suffix or an
infinite sequence of positive outer segments. Under safety no selected
segment is suppressed by inner UB. -/
theorem infinite_split (safe : ¬ g.ReachesUB p) (replay : g.Infinite p) :
    (∃ q, (g.outer inside).Reaches p q ∧ (g.inner inside).Infinite q) ∨
      (g.outer inside).Infinite p := by
  classical
  obtain ⟨path, start, steps⟩ := replay
  have reached (n : Nat) : g.Reaches p (path n) := by
    exact start ▸ path_between path (Nat.zero_le n) (fun j _ _ => steps j)
  by_cases often : ∀ n, ∃ m, n < m ∧ ¬ inside (path m)
  · let next (n : Nat) : Nat := Nat.find (often n)
    have progress (n : Nat) : n < next n := (Nat.find_spec (often n)).1
    have outside (n : Nat) : ¬ inside (path (next n)) := (Nat.find_spec (often n)).2
    have interval (n j : Nat) (lo : n < j) (hi : j < next n) : inside (path j) := by
      by_contra h
      exact Nat.not_le_of_lt hi (Nat.find_min' (often n) ⟨lo, h⟩)
    have segment (n : Nat) : (g.outer inside).step (path n) (path (next n)) := by
      let last := next n - 1
      have strict := progress n
      have endl : last + 1 = next n := by dsimp [last]; omega
      have beforeExit : (g.inner inside).Reaches (path n) (path last) := by
        refine path_between path (by dsimp [last]; omega) ?_
        intro j lo hi
        exact ⟨steps j, interval n (j + 1) (by omega) (by omega)⟩
      have exit : g.step (path last) (path (next n)) := by
        rw [← endl]
        exact steps last
      exact outer_step_iff.mpr ⟨inner_safe safe (reached n), path last, beforeExit, exit, outside n⟩
    let visits (n : Nat) : Nat := Nat.rec 0 (fun _ m => next m) n
    exact Or.inr ⟨fun n => path (visits n), start, fun n => segment (visits n)⟩
  · obtain ⟨n, bound⟩ := not_forall.mp often
    have stays (j : Nat) (gt : n < j) : inside (path j) :=
      not_not.mp (fun out => bound ⟨j, gt, out⟩)
    have suffix : (g.inner inside).Infinite (path n) :=
      ⟨fun j => path (n + j), rfl, fun j => ⟨steps (n + j), stays (n + j + 1) (by omega)⟩⟩
    rcases split_reaches (inside := inside) (reached n) with ub | ⟨b, outerPath, innerPath⟩
    · exact (safe (reachesUB_outer_iff.mp ub)).elim
    · exact Or.inl ⟨b, outerPath, path_prepend innerPath suffix⟩

theorem infinite_outer_iff (safe : ¬ g.ReachesUB p) :
    g.Infinite p ↔
      (∃ q, (g.outer inside).Reaches p q ∧ (g.inner inside).Infinite q) ∨
        (g.outer inside).Infinite p :=
  ⟨infinite_split safe, fun h => h.elim
    (fun ⟨_, path, replay⟩ => inner_infinite_reflect path replay) outer_infinite_reflect⟩

theorem outcomes_outer_iff {o : O} (safe : ¬ g.ReachesUB p) :
    o ∈ (g.outer inside).outcomes p ↔ o ∈ g.outcomes p := by
  constructor
  · rintro (⟨b, path, finish⟩ | ⟨rfl, replay⟩)
    · rcases (outer_finish_iff.mp finish).2 with ⟨c, pending, obs⟩ | ⟨rfl, replay⟩
      · exact Or.inl ⟨c, (outer_reaches_flat path).trans (inner_reaches_flat pending), obs⟩
      · exact Or.inr ⟨rfl, inner_infinite_reflect path replay⟩
    · exact Or.inr ⟨rfl, outer_infinite_reflect replay⟩
  · rintro (finite | ⟨rfl, replay⟩)
    · exact Or.inl (finite_to_outer safe finite)
    · rcases infinite_split (inside := inside) safe replay with ⟨b, path, innerReplay⟩ | outerReplay
      · exact Or.inl ⟨b, path, outer_finish_iff.mpr
          ⟨inner_safe safe (outer_reaches_flat path), Or.inr ⟨rfl, innerReplay⟩⟩⟩
      · exact Or.inr ⟨rfl, outerReplay⟩

theorem close_outer : (g.outer inside).close p = g.close p := by
  by_cases ub : g.ReachesUB p
  · exact (close_top_iff.mpr (reachesUB_outer_iff.mpr ub)).trans (close_top_iff.mpr ub).symm
  · rw [close_of_safe (fun h => ub (reachesUB_outer_iff.mp h)), close_of_safe ub]
    exact congrArg WithTop.some (Set.ext fun _ => outcomes_outer_iff ub)

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.Elimination
