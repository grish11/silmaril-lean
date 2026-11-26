module

public import Silmaril.Semantics.ConcurrentTrace.Parallel.Defs
import Silmaril.Semantics.Brookes.Thms
import Silmaril.Semantics.ConcurrentTrace.Thms

public section

namespace Silmaril.Proofs.Semantics.ConcurrentTrace.Parallel

open Silmaril.Semantics
open Silmaril.Semantics.ConcurrentTrace

variable {T E : Type*}

private theorem swap_cons (a : Letter T E) {x y : Word T E} (h : AdjacentSwap x y) :
    AdjacentSwap (a :: x) (a :: y) := by
  cases h with
  | inContext h pre post => exact .inContext h (a :: pre) post

theorem shuffle_swap {x y w w' : Word T E} (merge : Brookes.Shuffle x y w)
    (step : AdjacentSwap w w') :
    ∃ x' y', Brookes.Shuffle x' y' w' ∧
      ((x' = x ∧ y' = y) ∨ (AdjacentSwap x x' ∧ y' = y) ∨ (x' = x ∧ AdjacentSwap y y')) := by
  cases step with
  | @inContext a b h pre post =>
    induction pre generalizing x y with
    | nil =>
      cases merge with
      | left _ merge =>
        cases merge with
        | left _ tail => exact ⟨_, _, .left b (.left a tail),
            .inr (.inl ⟨.inContext h [] _, rfl⟩)⟩
        | right _ tail => exact ⟨_, _, .right b (.left a tail), .inl ⟨rfl, rfl⟩⟩
      | right _ merge =>
        cases merge with
        | left _ tail => exact ⟨_, _, .left b (.right a tail), .inl ⟨rfl, rfl⟩⟩
        | right _ tail => exact ⟨_, _, .right b (.right a tail),
            .inr (.inr ⟨rfl, .inContext h [] _⟩)⟩
    | cons a pre ih =>
      cases merge with
      | left _ tail =>
        obtain ⟨x', y', tail', outcome⟩ := ih tail
        refine ⟨a :: x', y', .left a tail', ?_⟩
        rcases outcome with ⟨rfl, rfl⟩ | ⟨hx, rfl⟩ | ⟨rfl, hy⟩
        · exact .inl ⟨rfl, rfl⟩
        · exact .inr (.inl ⟨swap_cons a hx, rfl⟩)
        · exact .inr (.inr ⟨rfl, hy⟩)
      | right _ tail =>
        obtain ⟨x', y', tail', outcome⟩ := ih tail
        refine ⟨x', a :: y', .right a tail', ?_⟩
        rcases outcome with ⟨rfl, rfl⟩ | ⟨hx, rfl⟩ | ⟨rfl, hy⟩
        · exact .inl ⟨rfl, rfl⟩
        · exact .inr (.inl ⟨hx, rfl⟩)
        · exact .inr (.inr ⟨rfl, swap_cons a hy⟩)

private theorem equivalent_of_adjacentSwap {x y : Word T E} (h : AdjacentSwap x y) :
    Equivalent x y := by
  cases h with
  | inContext h pre post =>
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      Equivalent.swap_in_context h pre post

private theorem independent_symm {a b : Letter T E} (h : a.Independent b) :
    b.Independent a := by
  cases h with
  | events h => exact .events (Ne.symm h)
  | eventSync h => exact .syncEvent h
  | syncEvent h => exact .eventSync h

private theorem saturated_of_swap_closed {s : Set (Word T E)}
    (closed : ∀ ⦃x y⦄, AdjacentSwap x y → x ∈ s → y ∈ s) : Saturated s := by
  have inContext {x y : FreeMonoid (Letter T E)} (h : ConGen.Rel Swap x y)
      (pre post : Word T E) :
      pre ++ x.toList ++ post ∈ s ↔ pre ++ y.toList ++ post ∈ s := by
    induction h generalizing pre post with
    | of x y step =>
      cases step with
      | pair h =>
        simp only [List.append_assoc, List.cons_append, List.nil_append]
        exact ⟨closed (.inContext h pre post), closed (.inContext (independent_symm h) pre post)⟩
    | refl => rfl
    | symm _ ih => exact (ih pre post).symm
    | trans _ _ ih₁ ih₂ => exact (ih₁ pre post).trans (ih₂ pre post)
    | @mul x x' y y' _ _ ih₁ ih₂ =>
      simpa only [FreeMonoid.toList_mul, List.append_assoc] using
        (ih₁ pre (y.toList ++ post)).trans (by
          simpa only [List.append_assoc] using ih₂ (pre ++ x'.toList) post)
  intro x y hx h
  change ConGen.Rel Swap (.ofList x) (.ofList y) at h
  have same : x ∈ s ↔ y ∈ s := by simpa using inContext h [] []
  exact same.mp hx

theorem shuffleWords_saturated {s t : Set (Word T E)} (hs : Saturated s) (ht : Saturated t) :
    Saturated (shuffleWords s t) := by
  apply saturated_of_swap_closed
  rintro w w' step ⟨x, hx, y, hy, merge⟩
  obtain ⟨x', y', merge', outcome⟩ := shuffle_swap merge step
  rcases outcome with ⟨rfl, rfl⟩ | ⟨step, rfl⟩ | ⟨rfl, step⟩
  · exact ⟨_, hx, _, hy, merge'⟩
  · exact ⟨_, hs hx (equivalent_of_adjacentSwap step), _, hy, merge'⟩
  · exact ⟨_, hx, _, ht hy (equivalent_of_adjacentSwap step), merge'⟩

theorem ofTraces_parallel (s t : Set (Trace T E)) :
    ofTraces (parallel s t) = shuffleWords (ofTraces s) (ofTraces t) :=
  (saturate_eq_iff _).mpr (shuffleWords_saturated (ofTraces_saturated s) (ofTraces_saturated t))

private theorem shuffle_assoc {Step : Type*} {x y z xy w : List Step}
    (inner : Brookes.Shuffle x y xy) (outer : Brookes.Shuffle xy z w) :
    ∃ yz, Brookes.Shuffle y z yz ∧ Brookes.Shuffle x yz w := by
  induction outer generalizing x y with
  | nil =>
    cases inner
    exact ⟨[], .nil, .nil⟩
  | left a _ ih =>
    cases inner with
    | left _ tail =>
      obtain ⟨yz, hyz, hw⟩ := ih tail
      exact ⟨yz, hyz, .left a hw⟩
    | right _ tail =>
      obtain ⟨yz, hyz, hw⟩ := ih tail
      exact ⟨a :: yz, .left a hyz, .right a hw⟩
  | right a _ ih =>
    obtain ⟨yz, hyz, hw⟩ := ih inner
    exact ⟨a :: yz, .right a hyz, .right a hw⟩

private theorem shuffleWords_assoc (r s t : Set (Word T E)) :
    shuffleWords (shuffleWords r s) t = shuffleWords r (shuffleWords s t) := by
  ext w
  constructor
  · rintro ⟨xy, ⟨x, hx, y, hy, hxy⟩, z, hz, hw⟩
    obtain ⟨yz, hyz, hw'⟩ := shuffle_assoc hxy hw
    exact ⟨x, hx, yz, ⟨y, hy, z, hz, hyz⟩, hw'⟩
  · rintro ⟨x, hx, yz, ⟨y, hy, z, hz, hyz⟩, hw⟩
    obtain ⟨yx, hyx, hw'⟩ := shuffle_assoc hyz.comm hw.comm
    exact ⟨yx, ⟨x, hx, y, hy, hyx.comm⟩, z, hz, hw'.comm⟩

theorem parallel_assoc (r s t : Set (Trace T E)) :
    parallel (parallel r s) t = parallel r (parallel s t) := by
  change toTraces (shuffleWords (ofTraces (parallel r s)) (ofTraces t)) =
    toTraces (shuffleWords (ofTraces r) (ofTraces (parallel s t)))
  simp only [ofTraces_parallel, shuffleWords_assoc]

theorem parallel_comm (s t : Set (Trace T E)) : parallel s t = parallel t s := by
  have swap (s t : Set (Word T E)) : shuffleWords s t ⊆ shuffleWords t s := by
    rintro w ⟨x, hx, y, hy, hw⟩
    exact ⟨y, hy, x, hx, hw.comm⟩
  exact congrArg toTraces (Set.Subset.antisymm (swap _ _) (swap _ _))

private theorem shuffle_nil_left {x w : Word T E} (h : Brookes.Shuffle [] x w) : w = x := by
  induction x generalizing w with
  | nil => cases h; rfl
  | cons a x ih =>
    cases h with
    | right _ tail => exact congrArg (a :: ·) (ih tail)

private theorem ofTraces_unit : ofTraces ({1} : Set (Trace T E)) = {[]} := by
  have sat : Saturated ({[]} : Set (Word T E)) := by
    apply saturated_of_swap_closed
    rintro _ _ ⟨_, pre, post⟩ hx
    simp at hx
  have emptyImage : toTraces ({[]} : Set (Word T E)) = {1} := by
    simp [toTraces]
  rw [← emptyImage]
  exact (saturate_eq_iff _).mpr sat

theorem parallel_unit_left (s : Set (Trace T E)) : parallel {1} s = s := by
  have unit : shuffleWords ({[]} : Set (Word T E)) (ofTraces s) = ofTraces s := by
    ext w
    constructor
    · rintro ⟨x, hx, y, hy, merge⟩
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact shuffle_nil_left merge ▸ hy
    · intro hw
      exact ⟨[], rfl, w, hw, Brookes.Shuffle.append [] w⟩
  rw [parallel, ofTraces_unit, unit, toTraces_ofTraces]

theorem parallel_union_left (r s t : Set (Trace T E)) :
    parallel (r ∪ s) t = parallel r t ∪ parallel s t := by
  ext tr
  constructor
  · rintro ⟨w, ⟨x, hx | hx, y, hy, hw⟩, rfl⟩
    · exact .inl ⟨w, ⟨x, hx, y, hy, hw⟩, rfl⟩
    · exact .inr ⟨w, ⟨x, hx, y, hy, hw⟩, rfl⟩
  · rintro (⟨w, ⟨x, hx, y, hy, hw⟩, rfl⟩ | ⟨w, ⟨x, hx, y, hy, hw⟩, rfl⟩)
    · exact ⟨w, ⟨x, .inl hx, y, hy, hw⟩, rfl⟩
    · exact ⟨w, ⟨x, .inr hx, y, hy, hw⟩, rfl⟩

end Silmaril.Proofs.Semantics.ConcurrentTrace.Parallel
